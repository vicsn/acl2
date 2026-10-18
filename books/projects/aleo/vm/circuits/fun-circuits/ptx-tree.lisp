; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Circuit plaintexts as wire trees, and the constraint-free Plaintext
; circuits: find and from_bit_array
; (snarkVM circuit/program/src/data/plaintext/{find.rs,mod.rs}).
;
; A circuit Plaintext is a tree whose shape and member names are fixed at
; synthesis time; only the literal leaves carry wires.  A wire tree is
;
;   (:lit . w)                 a literal leaf with leaf descriptor w
;   (:struct . ((id . wt)...)) members; id is a constant identifierp
;   (:array . (wt ...))        elements
;
; Member names are constants: Plaintext::new injects them with
; Identifier::constant, and Plaintext::from_bits builds them from the
; constant parse.  The leaf descriptor is abstract.  ptx-leaf-val is the
; literal the leaf's wires denote in an assignment (Literal::eject_value);
; the only facts used about it are that it is a literal, and that a boolean
; leaf (:boolean . b) denotes the boolean literal of the wire b.  The
; theorems below hold for every such ejection, so they apply to each arm
; of Literal (the per-arm wire layouts are those of literal-new-r1cs.lisp).
;
; find walks the path at synthesis time (indices must be constant, member
; lookup is IndexMap::get on constant identifiers), so it emits no
; constraint and returns a subtree of its input.  from_bit_array wraps each
; input bit as a boolean literal and emits no constraint.

(in-package "ALEOVM")

(include-book "../fun-specs/values-plaintext")
(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf ejection.

; ptx-leaf-typed is the condition that the leaf's wires satisfy Literal::new
; (the R1CS-SOUND-IF of the Plaintext rows).  The variant and the size in
; bits of a leaf are fixed at synthesis time (Literal::variant and
; Literal::size_in_bits return constants; a string's size is that of its
; constant-length byte vector).

(encapsulate
  (((ptx-leaf-val * *) => *)
   ((ptx-leaf-typed * *) => *)
   ((ptx-leaf-variant *) => *)
   ((ptx-leaf-size *) => *))

  (local
   (defun ptx-leaf-val (w asg)
     (if (and (consp w)
              (eq (car w) :boolean)
              (bitp (lookup-equal (cdr w) asg)))
         (literal-boolean (lookup-equal (cdr w) asg))
       (literal-boolean 0))))

  (local (defun ptx-leaf-typed (w asg) (declare (ignore w asg)) t))
  (local (defun ptx-leaf-variant (w) (declare (ignore w)) 1))
  (local (defun ptx-leaf-size (w) (declare (ignore w)) 1))

  (defrule ptx-literalp-of-leaf-val
    (literalp (ptx-leaf-val w asg)))

  (defruled ptx-leaf-variant-correct
    (implies (ptx-leaf-typed w asg)
             (equal (literal-variant (ptx-leaf-val w asg))
                    (ptx-leaf-variant w)))
    :enable literal-variant)

  (defruled ptx-leaf-size-correct
    (implies (ptx-leaf-typed w asg)
             (equal (literal-size-in-bits (ptx-leaf-val w asg))
                    (ptx-leaf-size w)))
    :enable literal-size-in-bits)

  (defruled ptx-leaf-val-of-boolean
    (implies (and (consp w)
                  (eq (car w) :boolean)
                  (bitp (lookup-equal (cdr w) asg)))
             (equal (ptx-leaf-val w asg)
                    (literal-boolean (lookup-equal (cdr w) asg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wire trees.

(defines ptx-wtp
  :flag-local nil

  (define ptx-wtp (x)
    :measure (acl2-count x)
    (and (consp x)
         (case (car x)
           (:lit t)
           (:struct (ptx-wmsp (cdr x)))
           (:array (ptx-wtsp (cdr x)))
           (otherwise nil))))

  (define ptx-wmsp (x)
    :measure (acl2-count x)
    (if (atom x)
        (null x)
      (and (consp (car x))
           (identifierp (caar x))
           (ptx-wtp (cdar x))
           (ptx-wmsp (cdr x)))))

  (define ptx-wtsp (x)
    :measure (acl2-count x)
    (if (atom x)
        (null x)
      (and (ptx-wtp (car x))
           (ptx-wtsp (cdr x))))))

(defines ptx-val
  :flag-local nil
  :short "The plaintext a wire tree denotes in an assignment
          (Plaintext::eject_value)."

  (define ptx-val (wt asg)
    :returns (pt plaintextp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (plaintext-struct (ptx-mval (cdr wt) asg)))
      (:array (plaintext-array (ptx-lval (cdr wt) asg)))
      (otherwise (plaintext-literal (ptx-leaf-val (cdr wt) asg)))))

  (define ptx-mval (wms asg)
    :returns (members plaintext-member-listp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (cons (make-plaintext-member :name (identifier-fix (car (car wms)))
                                   :value (ptx-val (cdr (car wms)) asg))
            (ptx-mval (cdr wms) asg))))

  (define ptx-lval (wts asg)
    :returns (elements plaintext-listp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (cons (ptx-val (car wts) asg)
            (ptx-lval (cdr wts) asg)))))

(defrule ptx-mval-when-atom
  (implies (atom wms) (equal (ptx-mval wms asg) nil))
  :expand ((ptx-mval wms asg)))

(defrule ptx-lval-when-atom
  (implies (atom wts) (equal (ptx-lval wts asg) nil))
  :expand ((ptx-lval wts asg)))

(defrule ptx-len-of-lval
  (equal (len (ptx-lval wts asg)) (len wts))
  :induct (len wts)
  :expand ((ptx-lval wts asg)))

(defrule ptx-len-of-mval
  (equal (len (ptx-mval wms asg)) (len wms))
  :induct (len wms)
  :expand ((ptx-mval wms asg)))

(defrule ptx-nth-of-lval
  (implies (< (nfix n) (len wts))
           (equal (nth n (ptx-lval wts asg))
                  (ptx-val (nth n wts) asg)))
  :induct (nth n wts)
  :expand ((ptx-lval wts asg))
  :enable nth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; find: the synthesis-time walk.

(define ptx-wms-lookup ((name identifierp) wms)
  :short "IndexMap::get on the constant member names (by the field of the
          identifier, as @(tsee values-plaintext-members-lookup))."
  (b* (((when (atom wms)) nil)
       (member (car wms)))
    (if (equal (identifier->field (identifier-fix (car member)))
               (identifier->field name))
        (cdr member)
      (ptx-wms-lookup name (cdr wms))))
  ///
  (defrule ptx-wtp-of-wms-lookup
    (implies (and (ptx-wmsp wms)
                  (ptx-wms-lookup name wms))
             (ptx-wtp (ptx-wms-lookup name wms)))
    :enable ptx-wmsp)

  (defrule ptx-mval-lookup
    (implies (ptx-wmsp wms)
             (equal (values-plaintext-members-lookup name (ptx-mval wms asg))
                    (and (ptx-wms-lookup name wms)
                         (ptx-val (ptx-wms-lookup name wms) asg))))
    :induct (ptx-wms-lookup name wms)
    :expand ((ptx-mval wms asg)
             (:free (x y) (values-plaintext-members-lookup name (cons x y)))
             (values-plaintext-members-lookup name nil)
             (ptx-wms-lookup name wms))
    :enable (ptx-wmsp ptx-wtp)))

(define ptx-find-aux (wt (path access-listp))
  :short "The subtree at @('path'), or @(':error') where snarkVM bails."
  :measure (len path)
  (b* (((when (endp path)) wt)
       (access (car path)))
    (cond ((and (eq (car wt) :struct) (acl2::access-case access :member))
           (b* ((member (ptx-wms-lookup (acl2::access-member->name access)
                                        (cdr wt)))
                ((unless member) :error))
             (ptx-find-aux member (cdr path))))
          ((and (eq (car wt) :array) (acl2::access-case access :index))
           (b* ((index (acl2::access-index->index access))
                (elements (cdr wt))
                ((unless (< index (len elements))) :error))
             (ptx-find-aux (nth index elements) (cdr path))))
          (t :error))))

(define ptx-find (wt (path access-listp))
  :short "Plaintext::find (an empty path or a literal halts)."
  (b* (((when (endp path)) :error)
       ((unless (member-eq (car wt) '(:struct :array))) :error))
    (ptx-find-aux wt path)))

(define ptx-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Plaintext::find emits no constraint."
  nil)

(local
 (defrule ptx-wtp-nth
   (implies (and (ptx-wtsp wts) (< (nfix n) (len wts)))
            (ptx-wtp (nth n wts)))
   :induct (nth n wts)
   :enable (nth ptx-wtsp)))

(defruled ptx-find-aux-correct
  (implies (ptx-wtp wt)
           (b* ((out (ptx-find-aux wt path))
                (spec (values-plaintext-find-aux (ptx-val wt asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (ptx-wtp out)
                                (equal (ptx-val out asg) spec))))))
  :induct (ptx-find-aux wt path)
  :in-theory (enable (:induction ptx-find-aux))
  :expand ((ptx-find-aux wt path)
           (:free (x) (values-plaintext-find-aux x path))
           (ptx-val wt asg)
           (ptx-wtp wt))
  :enable (spec-error))

(defruled ptx-find-sound
  :short "R1CS-SOUND (and the success condition) of Plaintext::find: the
          constraints (none) hold, and the output subtree denotes exactly
          the funspec's result on the plaintext the input wires denote."
  (implies (and (ptx-wtp wt)
                (r1cs::r1cs-constraints-holdp (ptx-find-gadget) asg p))
           (b* ((out (ptx-find wt path))
                (spec (plaintext-find (ptx-val wt asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (ptx-wtp out)
                                (plaintextp (ptx-val out asg))
                                (equal (ptx-val out asg) spec))))))
  :use ptx-find-aux-correct
  :expand ((ptx-val wt asg) (ptx-wtp wt))
  :enable (ptx-find plaintext-find spec-error))

(defruled ptx-find-complete
  (r1cs::r1cs-constraints-holdp (ptx-find-gadget) asg p)
  :enable ptx-find-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; from_bit_array.

(define ptx-bits-to-leaves ((bs symbol-listp))
  :short "Plaintext::from(Literal::Boolean(bit)) on each bit wire."
  (if (endp bs)
      nil
    (cons (cons :lit (cons :boolean (car bs)))
          (ptx-bits-to-leaves (cdr bs))))
  ///
  (defrule ptx-wtsp-of-bits-to-leaves
    (ptx-wtsp (ptx-bits-to-leaves bs))
    :enable (ptx-wtsp ptx-wtp))
  (defrule ptx-len-of-bits-to-leaves
    (equal (len (ptx-bits-to-leaves bs)) (len bs))))

(define ptx-from-bit-array ((bs symbol-listp) (length natp))
  :short "Plaintext::from_bit_array (a length mismatch bails)."
  (if (equal (len bs) (nfix length))
      (cons :array (ptx-bits-to-leaves bs))
    :error))

(define ptx-from-bit-array-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Plaintext::from_bit_array emits no constraint."
  nil)

(local
 (defrule ptx-lval-of-bits-to-leaves
   (implies (bit-listp (lookup-equal-list bs asg))
            (equal (ptx-lval (ptx-bits-to-leaves bs) asg)
                   (values-bits-to-boolean-plaintexts
                    (lookup-equal-list bs asg))))
   :induct (len bs)
   :expand ((ptx-bits-to-leaves bs)
            (lookup-equal-list bs asg)
            (:free (x y) (ptx-lval (cons x y) asg))
            (:free (b) (ptx-val (cons :lit b) asg))
            (ptx-lval nil asg)
            (:free (x y) (values-bits-to-boolean-plaintexts (cons x y))))
   :enable (ptx-leaf-val-of-boolean values-bits-to-boolean-plaintexts)))

(defruled ptx-from-bit-array-sound
  :short "R1CS-SOUND of Plaintext::from_bit_array, given Boolean::new on
          each input bit wire."
  (implies (and (symbol-listp bs)
                (ubyte32p length)
                (bit-listp (lookup-equal-list bs asg))
                (r1cs::r1cs-constraints-holdp (ptx-from-bit-array-gadget) asg p))
           (b* ((out (ptx-from-bit-array bs length))
                (spec (plaintext-from-bit-array (lookup-equal-list bs asg)
                                                length)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (ptx-wtp out)
                                (equal (ptx-val out asg) spec))))))
  :expand ((:free (x) (ptx-val (cons :array x) asg))
           (:free (x) (ptx-wtp (cons :array x))))
  :enable (ptx-from-bit-array plaintext-from-bit-array spec-error
                              acl2::ubyte32p acl2::ubyte32-fix))

(defruled ptx-from-bit-array-complete
  (r1cs::r1cs-constraints-holdp (ptx-from-bit-array-gadget) asg p)
  :enable ptx-from-bit-array-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal::new on every leaf.

(defines ptx-typed
  :flag-local nil

  (define ptx-typed (wt asg)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-mtyped (cdr wt) asg))
      (:array (ptx-ltyped (cdr wt) asg))
      (otherwise (and (ptx-leaf-typed (cdr wt) asg) t))))

  (define ptx-mtyped (wms asg)
    :measure (acl2-count wms)
    (if (atom wms)
        t
      (and (ptx-typed (cdr (car wms)) asg)
           (ptx-mtyped (cdr wms) asg))))

  (define ptx-ltyped (wts asg)
    :measure (acl2-count wts)
    (if (atom wts)
        t
      (and (ptx-typed (car wts) asg)
           (ptx-ltyped (cdr wts) asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean terms: a wire (a symbol) or a constant bit.

(define ptx-term-val (x asg)
  (if (symbolp x) (lookup-equal x asg) x))

(define ptx-terms-val (xs asg)
  (if (atom xs)
      nil
    (cons (ptx-term-val (car xs) asg)
          (ptx-terms-val (cdr xs) asg)))
  ///
  (defrule ptx-terms-val-of-append
    (equal (ptx-terms-val (append xs ys) asg)
           (append (ptx-terms-val xs asg) (ptx-terms-val ys asg))))
  (defrule ptx-len-of-terms-val
    (equal (len (ptx-terms-val xs asg)) (len xs)))
  (defrule ptx-terms-val-when-bit-listp
    (implies (bit-listp xs)
             (equal (ptx-terms-val xs asg) xs))
    :enable (ptx-term-val bit-listp bitp))
  (defrule ptx-terms-val-of-take
    (implies (<= (nfix n) (len xs))
             (equal (ptx-terms-val (take n xs) asg)
                    (take n (ptx-terms-val xs asg))))
    :induct (take n xs)
    :enable (take))
  (defrule ptx-terms-val-of-nthcdr
    (equal (ptx-terms-val (nthcdr n xs) asg)
           (nthcdr n (ptx-terms-val xs asg)))
    :enable nthcdr))

(defrule ptx-term-val-when-not-symbol
  (implies (not (symbolp x))
           (equal (ptx-term-val x asg) x))
  :enable ptx-term-val)

(defrule ptx-terms-val-of-cons
  (equal (ptx-terms-val (cons x xs) asg)
         (cons (ptx-term-val x asg) (ptx-terms-val xs asg)))
  :enable ptx-terms-val)

(defrule ptx-terms-val-of-true-list-fix
  (equal (ptx-terms-val (true-list-fix xs) asg)
         (ptx-terms-val xs asg))
  :enable ptx-terms-val)
