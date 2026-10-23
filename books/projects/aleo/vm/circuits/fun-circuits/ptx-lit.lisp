; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A concrete Literal wire representation, and the Plaintext (and Entry) write_bits /
; write_bits_raw / to_fields / to_fields_raw / size_in_fields /
; num_randomizers theorems of ptx-bits.lisp and ptx-entry.lisp functionally instantiated with
; it.
;
; Covered arms: Boolean and the ten Integer types.  A leaf wire is
;   (:boolean . b)          b a Boolean wire,
;   (kind . xs)             kind one of :i8 ... :u128, xs its n bit wires
;                           (little-endian), as in snarkVM's Integer.
; The leaf is typed (Literal::new established) when the Boolean wire holds a
; bit, or the n integer wires hold bits.  Literal::write_bits_le / _be on
; these arms is lit-literal-write-bits-empty-gadget of
; lit-literal-dispatch.lisp (no constraints; the bits are the wires), and
; its soundness is the dispatch's per-arm theorems
; lit-literal-write-bits-boolean-sound / lit-literal-write-bits-<int>-sound.
;
; Every other leaf (Address, Field, Group, Scalar, Signature, String,
; Identifier) is untyped here, so the instantiated theorems apply to
; plaintexts whose leaves are all Booleans or Integers.  The per-type
; write_bits theorems of the other arms carry their own wire layouts and
; hypotheses and are not yet composed into this representation; nor are
; the is_equal arms, whose per-type theorems assume facts about internal
; wires (e.g. the integer arms assume the output wire is a bit and a wire
; holds the constant one) that are not prior circuits.

(in-package "ALEOVM")

(include-book "ptx-entry")
(include-book "lit-literal-dispatch")
(include-book "int-support")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The integer arms: kind, signedness, width, variant.

(defconst *ptx-c-ints*
  '((:i8 t 8 4) (:i16 t 16 5) (:i32 t 32 6) (:i64 t 64 7) (:i128 t 128 8)
    (:u8 nil 8 9) (:u16 nil 16 10) (:u32 nil 32 11) (:u64 nil 64 12)
    (:u128 nil 128 13)))

(defun ptx-c-int-lit (kind x)
  (case kind
    (:i8 (literal-i8 x)) (:i16 (literal-i16 x)) (:i32 (literal-i32 x))
    (:i64 (literal-i64 x)) (:i128 (literal-i128 x))
    (:u8 (literal-u8 x)) (:u16 (literal-u16 x)) (:u32 (literal-u32 x))
    (:u64 (literal-u64 x)) (otherwise (literal-u128 x))))

(defun ptx-c-leaf-val (w asg)
  (b* ((info (assoc-equal (car w) *ptx-c-ints*)))
    (cond ((eq (car w) :boolean)
           (if (bitp (lookup-equal (cdr w) asg))
               (literal-boolean (lookup-equal (cdr w) asg))
             (literal-boolean 0)))
          (info (ptx-c-int-lit (car w)
                               (lebits->int (lookup-equal-list (cdr w) asg)
                                            (second info))))
          (t (literal-boolean 0)))))

(defun ptx-c-leaf-typed (w asg)
  (b* ((info (assoc-equal (car w) *ptx-c-ints*)))
    (cond ((eq (car w) :boolean)
           (and (symbolp (cdr w))
                (bitp (lookup-equal (cdr w) asg))))
          (info (and (symbol-listp (cdr w))
                     (equal (len (cdr w)) (third info))
                     (bit-listp (lookup-equal-list (cdr w) asg))))
          (t nil))))

(defun ptx-c-leaf-variant (w)
  (b* ((info (assoc-equal (car w) *ptx-c-ints*)))
    (if info (fourth info) 1)))

(defun ptx-c-leaf-size (w)
  (b* ((info (assoc-equal (car w) *ptx-c-ints*)))
    (if info (third info) 1)))

(defun ptx-c-leaf-bits-gadget (w bigp)
  (declare (ignore w bigp))
  (lit-literal-write-bits-empty-gadget))

(defun ptx-c-leaf-bits-out (w bigp)
  (cond ((eq (car w) :boolean) (list (cdr w)))
        ((assoc-equal (car w) *ptx-c-ints*)
         (if bigp (rev (cdr w)) (cdr w)))
        (t nil)))

(defun ptx-c-leaf-bits-witnessp (w bigp asg p)
  (declare (ignore w bigp asg p))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The leaf constraints of ptx-tree.lisp and ptx-bits.lisp.

(defruled ptx-c-int->lebits-of-lebits->int
  (implies (and (bit-listp bits)
                (equal (len bits) n))
           (equal (int->lebits (lebits->int bits signedp) n) bits))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound (digits bits))
        (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits)))
  :enable (int->lebits lebits->int acl2::mod-when-<)
  :disable acl2::nat=>lebits-of-lebits=>nat)

(defrule ptx-c-terms-val-of-symbol-list
  (implies (symbol-listp xs)
           (equal (ptx-terms-val xs asg)
                  (lookup-equal-list xs asg)))
  :induct (len xs)
  :enable (ptx-terms-val ptx-term-val lookup-equal-list))

(defrule ptx-c-symbol-listp-of-rev
  (implies (symbol-listp xs) (symbol-listp (rev xs)))
  :enable rev)

(defrule ptx-c-lookup-equal-list-of-append
  (equal (lookup-equal-list (append xs ys) asg)
         (append (lookup-equal-list xs asg) (lookup-equal-list ys asg)))
  :induct (len xs)
  :enable lookup-equal-list)

(defrule ptx-c-lookup-equal-list-of-rev
  (equal (lookup-equal-list (rev xs) asg)
         (rev (lookup-equal-list xs asg)))
  :induct (len xs)
  :enable (rev lookup-equal-list))

(defmacro ptx-c-int-arm (kind lit signedp n arm)
  (b* ((name (intern-in-package-of-symbol
              (concatenate 'string "PTX-C-BITS-" (symbol-name kind)) 'ptx-c-int-arm)))
    `(defruled ,name
       (implies (and (symbol-listp xs)
                     (equal (len xs) ,n)
                     (bit-listp (lookup-equal-list xs asg)))
                (and (equal (lookup-equal-list xs asg)
                            (literal-to-bits-le
                             (,lit (lebits->int (lookup-equal-list xs asg) ,signedp))))
                     (equal (rev (lookup-equal-list xs asg))
                            (literal-to-bits-be
                             (,lit (lebits->int (lookup-equal-list xs asg) ,signedp))))))
       :use ((:instance ,arm
              (x (lebits->int (lookup-equal-list xs asg) ,signedp))
              (p 0))
             (:instance int-valuep-of-lebits->int
              (bits (lookup-equal-list xs asg)) (signedp ,signedp) (n ,n))
             (:instance ptx-c-int->lebits-of-lebits->int
              (bits (lookup-equal-list xs asg)) (signedp ,signedp) (n ,n)))
       :enable lit-literal-write-bits-empty-gadget-complete)))

(ptx-c-int-arm i8 literal-i8 t 8 lit-literal-write-bits-i8-sound)
(ptx-c-int-arm i16 literal-i16 t 16 lit-literal-write-bits-i16-sound)
(ptx-c-int-arm i32 literal-i32 t 32 lit-literal-write-bits-i32-sound)
(ptx-c-int-arm i64 literal-i64 t 64 lit-literal-write-bits-i64-sound)
(ptx-c-int-arm i128 literal-i128 t 128 lit-literal-write-bits-i128-sound)
(ptx-c-int-arm u8 literal-u8 nil 8 lit-literal-write-bits-u8-sound)
(ptx-c-int-arm u16 literal-u16 nil 16 lit-literal-write-bits-u16-sound)
(ptx-c-int-arm u32 literal-u32 nil 32 lit-literal-write-bits-u32-sound)
(ptx-c-int-arm u64 literal-u64 nil 64 lit-literal-write-bits-u64-sound)
(ptx-c-int-arm u128 literal-u128 nil 128 lit-literal-write-bits-u128-sound)

(in-theory (disable ptx-c-leaf-val ptx-c-leaf-typed ptx-c-leaf-bits-out))

(defruled ptx-c-leaf-constraints
  (and (literalp (ptx-c-leaf-val w asg))
       (implies (ptx-c-leaf-typed w asg)
                (equal (literal-variant (ptx-c-leaf-val w asg))
                       (ptx-c-leaf-variant w)))
       (implies (ptx-c-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-c-leaf-val w asg))
                       (ptx-c-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-c-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :enable (literal-variant literal-size-in-bits ptx-c-leaf-val ptx-c-leaf-typed))

(defmacro ptx-c-leaf-bits-sound-arm (kind)
  (b* ((name (intern-in-package-of-symbol
              (concatenate 'string "PTX-C-LEAF-BITS-SOUND-" (symbol-name kind))
              'ptx-c-int-arm))
       (arm (intern-in-package-of-symbol
             (concatenate 'string "PTX-C-BITS-" (symbol-name kind)) 'ptx-c-int-arm)))
    `(defruled ,name
       (implies (and (equal (car w) ,(intern (symbol-name kind) "KEYWORD"))
                     (ptx-c-leaf-typed w asg))
                (equal (ptx-terms-val (ptx-c-leaf-bits-out w bigp) asg)
                       (if bigp
                           (literal-to-bits-be (ptx-c-leaf-val w asg))
                         (literal-to-bits-le (ptx-c-leaf-val w asg)))))
       :use ((:instance ,arm (xs (cdr w))))
       :enable (ptx-c-leaf-typed ptx-c-leaf-val ptx-c-leaf-bits-out))))

(ptx-c-leaf-bits-sound-arm i8)
(ptx-c-leaf-bits-sound-arm i16)
(ptx-c-leaf-bits-sound-arm i32)
(ptx-c-leaf-bits-sound-arm i64)
(ptx-c-leaf-bits-sound-arm i128)
(ptx-c-leaf-bits-sound-arm u8)
(ptx-c-leaf-bits-sound-arm u16)
(ptx-c-leaf-bits-sound-arm u32)
(ptx-c-leaf-bits-sound-arm u64)
(ptx-c-leaf-bits-sound-arm u128)

(defruled ptx-c-leaf-bits-sound-boolean
  (implies (and (equal (car w) :boolean)
                (ptx-c-leaf-typed w asg))
           (equal (ptx-terms-val (ptx-c-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-c-leaf-val w asg))
                    (literal-to-bits-le (ptx-c-leaf-val w asg)))))
  :use ((:instance lit-literal-write-bits-boolean-sound (b (cdr w)) (p 0)))
  :enable (ptx-c-leaf-typed ptx-c-leaf-val ptx-c-leaf-bits-out ptx-terms-val
                            ptx-term-val lookup-equal-list
                            lit-literal-write-bits-empty-gadget-complete))

(defruled ptx-c-kind-when-typed
  (implies (ptx-c-leaf-typed w asg)
           (member-equal (car w) '(:boolean :i8 :i16 :i32 :i64 :i128
                                   :u8 :u16 :u32 :u64 :u128)))
  :enable ptx-c-leaf-typed)

(defruled ptx-c-leaf-bits-sound
  (implies (ptx-c-leaf-typed w asg)
           (equal (ptx-terms-val (ptx-c-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-c-leaf-val w asg))
                    (literal-to-bits-le (ptx-c-leaf-val w asg)))))
  :use ptx-c-kind-when-typed
  :enable (ptx-c-leaf-bits-sound-boolean
           ptx-c-leaf-bits-sound-i8 ptx-c-leaf-bits-sound-i16
           ptx-c-leaf-bits-sound-i32 ptx-c-leaf-bits-sound-i64
           ptx-c-leaf-bits-sound-i128 ptx-c-leaf-bits-sound-u8
           ptx-c-leaf-bits-sound-u16 ptx-c-leaf-bits-sound-u32
           ptx-c-leaf-bits-sound-u64 ptx-c-leaf-bits-sound-u128))

(defruled ptx-c-leaf-bits-complete
  (r1cs::r1cs-constraints-holdp (ptx-c-leaf-bits-gadget w bigp) asg p)
  :enable lit-literal-write-bits-empty-gadget-complete)

(in-theory (disable ptx-c-leaf-val ptx-c-leaf-typed ptx-c-leaf-variant
                    ptx-c-leaf-size ptx-c-leaf-bits-gadget ptx-c-leaf-bits-out
                    ptx-c-leaf-bits-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Copies of the ptx- functions that call the leaf interface, with the
;; concrete leaf functions (ptx-X becomes ptx-c-X), and the functional
;; instances of the ptx-bits.lisp theorems.

(defconst *ptx-c-cliques*
  '((ptx-val ptx-mval ptx-lval)
    (ptx-typed ptx-mtyped ptx-ltyped)
    (ptx-bits-out ptx-mbits-out ptx-lbits-out)
    (ptx-bits-gadget ptx-mbits-gadget ptx-lbits-gadget)
    (ptx-bits-witnessp ptx-mbits-witnessp ptx-lbits-witnessp)
    (ptx-raw-out ptx-mraw-out ptx-lraw-out)
    (ptx-size-in-fields)
    (ptx-eval)
    (ptx-entry-bits-out)
    (ptx-entry-bits-gadget)
    (ptx-entry-to-fields-out)
    (ptx-entry-num-randomizers)))

(defconst *ptx-c-leaves*
  '(ptx-leaf-val ptx-leaf-typed ptx-leaf-variant ptx-leaf-size
    ptx-leaf-bits-gadget ptx-leaf-bits-out ptx-leaf-bits-witnessp))

(defun ptx-c-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string "PTX-C-" (subseq (symbol-name fn) 4 nil))
   'ptx-c-name))

(defun ptx-c-alist (fns)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (cons (cons (car fns) (ptx-c-name (car fns)))
          (ptx-c-alist (cdr fns)))))

(defun ptx-c-flatten (x)
  (declare (xargs :mode :program))
  (if (endp x) nil (append (car x) (ptx-c-flatten (cdr x)))))

(defun ptx-c-defun (fn recp alist wrld)
  (declare (xargs :mode :program))
  (b* ((formals (acl2::formals fn wrld))
       (body (acl2::sublis-fn-simple
              alist (getpropc fn 'acl2::unnormalized-body nil wrld))))
    `(defun ,(ptx-c-name fn) ,formals
       (declare (xargs ,@(and recp `(:measure (acl2-count ,(car formals))))
                       :verify-guards nil)
                (ignorable ,@formals))
       ,body)))

(defun ptx-c-defuns (fns recp alist wrld)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (cons (ptx-c-defun (car fns) recp alist wrld)
          (ptx-c-defuns (cdr fns) recp alist wrld))))

(defun ptx-c-copy-events (cliques alist wrld)
  (declare (xargs :mode :program))
  (if (endp cliques)
      nil
    (b* ((clique (car cliques))
         (recp (getpropc (car clique) 'acl2::recursivep nil wrld))
         (defs (ptx-c-defuns clique recp alist wrld)))
      (cons (if (cdr defs) `(mutual-recursion ,@defs) (car defs))
            (ptx-c-copy-events (cdr cliques) alist wrld)))))

(make-event
 (b* ((alist (ptx-c-alist (append *ptx-c-leaves* (ptx-c-flatten *ptx-c-cliques*)))))
   `(progn ,@(ptx-c-copy-events *ptx-c-cliques* alist (w state)))))

(defun ptx-c-fi-pairs (alist)
  (declare (xargs :mode :program))
  (if (endp alist)
      nil
    (cons (list (caar alist) (cdar alist))
          (ptx-c-fi-pairs (cdr alist)))))

(defun ptx-c-instance-event (thm wrld)
  (declare (xargs :mode :program))
  (b* ((all (append *ptx-c-leaves* (ptx-c-flatten *ptx-c-cliques*)))
       (alist (ptx-c-alist all))
       (formula (acl2::sublis-fn-simple alist (acl2::formula thm nil wrld))))
    `(defthm ,(ptx-c-name thm)
       ,formula
       :hints (("Goal"
                :do-not-induct t
                :use ((:functional-instance ,thm ,@(ptx-c-fi-pairs alist)))
                :in-theory (enable ptx-c-leaf-constraints
                                   ptx-c-leaf-bits-sound
                                   ptx-c-leaf-bits-complete
                                   ptx-c-leaf-bits-gadget
                                   ptx-c-leaf-bits-witnessp
                                   lit-literal-write-bits-empty-gadget)))
       :rule-classes nil)))

(defmacro ptx-c-instance (thm)
  `(make-event (ptx-c-instance-event ',thm (w state))))

(ptx-c-instance ptx-write-bits-le-sound)
(ptx-c-instance ptx-write-bits-be-sound)
(ptx-c-instance ptx-write-bits-complete)
(ptx-c-instance ptx-write-bits-raw-le-sound)
(ptx-c-instance ptx-write-bits-raw-be-sound)
(ptx-c-instance ptx-write-bits-raw-complete)
(ptx-c-instance ptx-to-fields-sound)
(ptx-c-instance ptx-to-fields-raw-sound)
(ptx-c-instance ptx-size-in-fields-sound)
(ptx-c-instance ptx-num-randomizers-sound)
(ptx-c-instance ptx-entry-write-bits-le-sound)
(ptx-c-instance ptx-entry-write-bits-be-sound)
(ptx-c-instance ptx-entry-write-bits-complete)
(ptx-c-instance ptx-entry-to-fields-sound)
(ptx-c-instance ptx-entry-num-randomizers-sound)
