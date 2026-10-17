; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::is_equal and Plaintext::is_not_equal
; (snarkVM circuit/program/src/data/plaintext/equal.rs), by induction over
; the two wire trees of ptx-tree.lisp.
;
; A Boolean is a linear combination: here either a constant bit (0 or 1)
; or a non-empty R1CS sparse vector.  Boolean AND and OR fold constants at
; synthesis time exactly as snarkVM's BitAndAssign / BitOrAssign do: a
; constant operand returns the other operand or a constant, and only two
; non-constant operands allocate a fresh private variable z with the
; constraint
;   AND:  x * y = z
;   OR:   (1 - x) * (1 - y) = (1 - z).
;
; is_equal of two structs of the same length folds
;   equal = equal & name_a.is_equal(name_b) & a.is_equal(b)
; over the members starting from the constant true.  The member names are
; constants, so the name equality is a constant and the first AND always
; folds; the second AND allocates a variable unless an operand is a
; constant.  Arrays fold equal &= a.is_equal(b).  Different lengths or
; kinds give the constant false.  is_not_equal is the dual with OR,
; is_not_equal and the constant false.
;
; The leaf circuit Literal::is_equal / is_not_equal is abstract
; (ptx-leaf-eq-*); it may consume fresh variable names from the supply
; NAMES.  Each folded AND/OR position also takes one name from the supply,
; whether or not it is used.

(in-package "ALEOVM")

(include-book "ptx-tree")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-and")

(set-verify-guards-eagerness 0)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean linear combinations.

(define ptx-bval (x asg p)
  (if (consp x) (r1cs::dot-product x asg p) x))

(define ptx-neg (x)
  (if (atom x)
      nil
    (cons (list (- (ifix (first (car x)))) (second (car x)))
          (ptx-neg (cdr x)))))

(defrule ptx-dot-product-of-neg
  (implies (and (posp p) (r1cs::sparse-vectorp x))
           (equal (r1cs::dot-product (ptx-neg x) asg p)
                  (pfield::neg (r1cs::dot-product x asg p) p)))
  :induct (ptx-neg x)
  :enable (ptx-neg r1cs::dot-product r1cs::sparse-vectorp
                   r1cs::sparse-vector-elementp)
  :prep-lemmas
  ((defrule mod-of-minus
     (implies (and (integerp c) (posp p))
              (equal (mod (- c) p) (pfield::neg (mod c p) p)))
     :enable pfield::neg)))

(defconst *ptx-one*
  '((1 1)))

(define ptx-one-minus (x)
  (cons (list 1 1) (ptx-neg x)))

(define ptx-and (x y z)
  :short "Boolean BitAndAssign: (cons constraints output)."
  (cond ((atom x) (if (equal x 1) (cons nil y) (cons nil 0)))
        ((atom y) (if (equal y 1) (cons nil x) (cons nil 0)))
        (t (cons (list (r1cs::make-r1cs-constraint
                        :a x :b y :c (list (list 1 z))))
                 (list (list 1 z))))))

(define ptx-or (x y z)
  :short "Boolean BitOrAssign: (cons constraints output)."
  (cond ((atom x) (if (equal x 1) (cons nil 1) (cons nil y)))
        ((atom y) (if (equal y 1) (cons nil 1) (cons nil x)))
        (t (cons (list (r1cs::make-r1cs-constraint
                        :a (ptx-one-minus x)
                        :b (ptx-one-minus y)
                        :c (ptx-one-minus (list (list 1 z)))))
                 (list (list 1 z))))))

(define ptx-bop (neq x y z)
  (if neq (ptx-or x y z) (ptx-and x y z)))

(define ptx-bop-spec (neq x y)
  (if neq (bitor x y) (bitand x y)))

(define ptx-bop-witnessp (neq x y z asg p)
  :short "The fresh variable of a non-folded AND/OR holds its value."
  (or (atom x)
      (atom y)
      (equal (lookup-equal z asg)
             (ptx-bop-spec neq (ptx-bval x asg p) (ptx-bval y asg p)))))

(defrule ptx-bval-of-atom
  (implies (atom x) (equal (ptx-bval x asg p) x))
  :enable ptx-bval)

(defrule ptx-sparse-vectorp-of-neg
  (implies (r1cs::sparse-vectorp x)
           (r1cs::sparse-vectorp (ptx-neg x)))
  :enable (ptx-neg r1cs::sparse-vectorp r1cs::sparse-vector-elementp))

(defruled ptx-dot-product-of-singleton
  (implies (posp p)
           (equal (r1cs::dot-product (list (list 1 z)) asg p)
                  (if (equal z 1)
                      (mod 1 p)
                    (mod (ifix (lookup-equal z asg)) p))))
  :enable (r1cs::dot-product pfield::mul pfield::add lookup-equal))

(defruled ptx-and-sound
  (implies (and (primep p)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (r1cs::sparse-vectorp (and (consp x) x))
                (r1cs::sparse-vectorp (and (consp y) y))
                (r1cs::r1cs-constraints-holdp (car (ptx-and x y z)) asg p))
           (equal (ptx-bval (cdr (ptx-and x y z)) asg p)
                  (bitand (ptx-bval x asg p) (ptx-bval y asg p))))
  :enable (ptx-and ptx-bval r1cs::r1cs-constraint-holdsp
                   r1cs::r1cs-constraints-holdp bitp pfield::mul))

(defrule ptx-dot-product-of-one-cons
  (implies (primep p)
           (equal (r1cs::dot-product (cons '(1 1) v) asg p)
                  (pfield::add 1 (r1cs::dot-product v asg p) p)))
  :expand ((r1cs::dot-product (cons '(1 1) v) asg p))
  :enable primep
  :prep-lemmas
  ((defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod)))

(defrule ptx-add-1-equal-mod-2
  (implies (and (primep p) (pfield::fep v p))
           (equal (equal (pfield::add 1 v p) (mod 2 p))
                  (equal v 1)))
  :cases ((equal v (+ -1 p)) (< v (+ -1 p)))
  :enable (pfield::add pfield::fep primep)
  :prep-lemmas
  ((defrule mod-small
     (implies (and (natp x) (posp p) (< x p))
              (equal (mod x p) x)))
   (defrule mod-2-when-2
     (equal (mod 2 2) 0))
   (defrule mod-2-when-big
     (implies (and (integerp p) (< 2 p))
              (equal (mod 2 p) 2)))
   (defrule mod-2-not-1
     (implies (and (integerp p) (<= 2 p))
              (not (equal (mod 2 p) 1)))
     :cases ((equal p 2)))))

(defruled ptx-or-sound
  (implies (and (primep p)
                (symbolp z)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (r1cs::sparse-vectorp (and (consp x) x))
                (r1cs::sparse-vectorp (and (consp y) y))
                (r1cs::r1cs-constraints-holdp (car (ptx-or x y z)) asg p))
           (equal (ptx-bval (cdr (ptx-or x y z)) asg p)
                  (bitor (ptx-bval x asg p) (ptx-bval y asg p))))
  :enable (ptx-or ptx-bval ptx-one-minus r1cs::r1cs-constraint-holdsp
                  r1cs::r1cs-constraints-holdp bitp
                  r1cs::sparse-vectorp r1cs::sparse-vector-elementp)
  :prep-lemmas
  ((defrule lemma
     (implies (and (primep p)
                   (pfield::fep v p)
                   (equal (pfield::mul (pfield::add 1 (pfield::neg a p) p)
                                       (pfield::add 1 (pfield::neg b p) p)
                                       p)
                          (pfield::add 1 (pfield::neg v p) p))
                   (bitp a) (bitp b))
              (equal (bitor a b) v))
     :enable bitp
     :cases ((equal a 0))
     :hints (("Goal" :use ((:instance neg-eq (w (bitor a b))))))
     :prep-lemmas
     ((defrule neg-eq
        (implies (and (primep p) (pfield::fep v p) (pfield::fep w p)
                      (equal (pfield::add 1 (pfield::neg v p) p)
                             (pfield::add 1 (pfield::neg w p) p)))
                 (equal v w))
        :rule-classes nil)))))

(defruled ptx-bop-sound
  (implies (and (primep p)
                (symbolp z)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (r1cs::sparse-vectorp (and (consp x) x))
                (r1cs::sparse-vectorp (and (consp y) y))
                (r1cs::r1cs-constraints-holdp (car (ptx-bop neq x y z)) asg p))
           (equal (ptx-bval (cdr (ptx-bop neq x y z)) asg p)
                  (ptx-bop-spec neq (ptx-bval x asg p) (ptx-bval y asg p))))
  :enable (ptx-bop ptx-bop-spec)
  :use (ptx-and-sound ptx-or-sound))

(defruled ptx-bop-complete
  (implies (and (primep p)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (r1cs::r1cs-valuationp asg p)
                (symbolp z)
                (r1cs::sparse-vectorp (and (consp x) x))
                (r1cs::sparse-vectorp (and (consp y) y))
                (ptx-bop-witnessp neq x y z asg p))
           (and (r1cs::r1cs-constraints-holdp (car (ptx-bop neq x y z)) asg p)
                (equal (ptx-bval (cdr (ptx-bop neq x y z)) asg p)
                       (ptx-bop-spec neq (ptx-bval x asg p) (ptx-bval y asg p)))))
  :enable (ptx-bop ptx-bop-spec ptx-bop-witnessp ptx-and ptx-or ptx-bval
                   ptx-one-minus r1cs::r1cs-constraint-holdsp
                   r1cs::r1cs-constraints-holdp bitp
                   ptx-dot-product-of-singleton primep
                   r1cs::sparse-vectorp r1cs::sparse-vector-elementp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf interface: Literal::is_equal (neq nil) / is_not_equal (neq t).

(defconst *ptx-eq-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-leaf-eq-gadget * * * *) => *)
   ((ptx-leaf-eq-out * * * *) => *)
   ((ptx-leaf-eq-nvars * * *) => *)
   ((ptx-leaf-eq-witnessp * * * * * *) => *))

  (local (defun ptx-leaf-eq-gadget (wa wb neq names)
           (declare (ignore wa wb neq names))
           (list *ptx-eq-false-constraint*)))
  (local (defun ptx-leaf-eq-out (wa wb neq names)
           (declare (ignore wa wb neq names))
           0))
  (local (defun ptx-leaf-eq-nvars (wa wb neq)
           (declare (ignore wa wb neq))
           0))
  (local (defun ptx-leaf-eq-witnessp (wa wb neq names asg p)
           (declare (ignore wa wb neq names asg p))
           nil))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defrule ptx-natp-of-leaf-eq-nvars
    (natp (ptx-leaf-eq-nvars wa wb neq))
    :rule-classes :type-prescription)

  (defrule ptx-sparse-vectorp-of-leaf-eq-out
    (r1cs::sparse-vectorp (and (consp (ptx-leaf-eq-out wa wb neq names))
                               (ptx-leaf-eq-out wa wb neq names))))

  (defruled ptx-leaf-eq-sound
    (implies (and (primep p)
                  (ptx-leaf-typed wa asg)
                  (ptx-leaf-typed wb asg)
                  (r1cs::r1cs-constraints-holdp
                   (ptx-leaf-eq-gadget wa wb neq names) asg p))
             (equal (ptx-bval (ptx-leaf-eq-out wa wb neq names) asg p)
                    (values-bool-to-bit
                     (if neq
                         (not (values-literal-equalp (ptx-leaf-val wa asg)
                                                     (ptx-leaf-val wb asg)))
                       (values-literal-equalp (ptx-leaf-val wa asg)
                                              (ptx-leaf-val wb asg))))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-leaf-eq-complete
    (implies (and (primep p)
                  (ptx-leaf-typed wa asg)
                  (ptx-leaf-typed wb asg)
                  (ptx-leaf-eq-witnessp wa wb neq names asg p))
             (r1cs::r1cs-constraints-holdp
              (ptx-leaf-eq-gadget wa wb neq names) asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The circuit.

(define ptx-kind (wt)
  :enabled t
  (case (car wt) (:struct :struct) (:array :array) (otherwise :lit)))

(defines ptx-eq-count
  :flag-local nil
  :short "The number of fresh names is_equal / is_not_equal takes."

  (define ptx-eq-count (a b neq)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-kind a) (ptx-kind b))) 0)
          ((not (equal (ptx-kind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-kind a) :struct)
                   (ptx-meq-count (cdr a) (cdr b) neq)
                 (ptx-leq-count (cdr a) (cdr b) neq))
             0))
          (t (ptx-leaf-eq-nvars (cdr a) (cdr b) neq))))

  (define ptx-meq-count (ams bms neq)
    :measure (acl2-count ams)
    (if (or (atom ams) (atom bms))
        0
      (+ (ptx-eq-count (cdr (car ams)) (cdr (car bms)) neq)
         1
         (ptx-meq-count (cdr ams) (cdr bms) neq))))

  (define ptx-leq-count (aes bes neq)
    :measure (acl2-count aes)
    (if (or (atom aes) (atom bes))
        0
      (+ (ptx-eq-count (car aes) (car bes) neq)
         1
         (ptx-leq-count (cdr aes) (cdr bes) neq)))))

(defrule ptx-natp-of-eq-count
  (natp (ptx-eq-count a b neq))
  :rule-classes :type-prescription
  :expand ((ptx-eq-count a b neq)))

(define ptx-name-bit (ida idb neq)
  :short "Identifier::is_equal / is_not_equal of two constant names."
  (if (equal (identifier->field (identifier-fix ida))
             (identifier->field (identifier-fix idb)))
      (if neq 0 1)
    (if neq 1 0)))

(defines ptx-eq
  :flag-local nil
  :short "Plaintext::is_equal (neq nil) / is_not_equal (neq t):
          (cons constraints output)."

  (define ptx-eq (a b neq names)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-kind a) (ptx-kind b))) (cons nil (if neq 1 0)))
          ((not (equal (ptx-kind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-kind a) :struct)
                   (ptx-meq (cdr a) (cdr b) neq (if neq 0 1) names)
                 (ptx-leq (cdr a) (cdr b) neq (if neq 0 1) names))
             (cons nil (if neq 1 0))))
          (t (cons (ptx-leaf-eq-gadget (cdr a) (cdr b) neq names)
                   (ptx-leaf-eq-out (cdr a) (cdr b) neq names)))))

  (define ptx-meq (ams bms neq acc names)
    :measure (acl2-count ams)
    (b* (((when (or (atom ams) (atom bms))) (cons nil acc))
         (r1 (ptx-bop neq acc (ptx-name-bit (car (car ams)) (car (car bms)) neq)
                      nil))
         (sub (ptx-eq (cdr (car ams)) (cdr (car bms)) neq names))
         (k (ptx-eq-count (cdr (car ams)) (cdr (car bms)) neq))
         (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names)))
         (rest (ptx-meq (cdr ams) (cdr bms) neq (cdr r2) (nthcdr (1+ k) names))))
      (cons (append (car r1) (car sub) (car r2) (car rest))
            (cdr rest))))

  (define ptx-leq (aes bes neq acc names)
    :measure (acl2-count aes)
    (b* (((when (or (atom aes) (atom bes))) (cons nil acc))
         (sub (ptx-eq (car aes) (car bes) neq names))
         (k (ptx-eq-count (car aes) (car bes) neq))
         (r (ptx-bop neq acc (cdr sub) (nth k names)))
         (rest (ptx-leq (cdr aes) (cdr bes) neq (cdr r) (nthcdr (1+ k) names))))
      (cons (append (car sub) (car r) (car rest))
            (cdr rest)))))

(defines ptx-eq-witnessp
  :flag-local nil
  :short "Each leaf carries its Literal::is_equal witness and each
          non-folded AND / OR variable holds its value."

  (define ptx-eq-witnessp (a b neq names asg p)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-kind a) (ptx-kind b))) t)
          ((not (equal (ptx-kind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-kind a) :struct)
                   (ptx-meq-witnessp (cdr a) (cdr b) neq (if neq 0 1) names asg p)
                 (ptx-leq-witnessp (cdr a) (cdr b) neq (if neq 0 1) names asg p))
             t))
          (t (and (ptx-leaf-eq-witnessp (cdr a) (cdr b) neq names asg p) t))))

  (define ptx-meq-witnessp (ams bms neq acc names asg p)
    :measure (acl2-count ams)
    (b* (((when (or (atom ams) (atom bms))) t)
         (r1 (ptx-bop neq acc (ptx-name-bit (car (car ams)) (car (car bms)) neq)
                      nil))
         (sub (ptx-eq (cdr (car ams)) (cdr (car bms)) neq names))
         (k (ptx-eq-count (cdr (car ams)) (cdr (car bms)) neq))
         (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names))))
      (and (ptx-eq-witnessp (cdr (car ams)) (cdr (car bms)) neq names asg p)
           (ptx-bop-witnessp neq (cdr r1) (cdr sub) (nth k names) asg p)
           (ptx-meq-witnessp (cdr ams) (cdr bms) neq (cdr r2)
                             (nthcdr (1+ k) names) asg p))))

  (define ptx-leq-witnessp (aes bes neq acc names asg p)
    :measure (acl2-count aes)
    (b* (((when (or (atom aes) (atom bes))) t)
         (sub (ptx-eq (car aes) (car bes) neq names))
         (k (ptx-eq-count (car aes) (car bes) neq))
         (r (ptx-bop neq acc (cdr sub) (nth k names))))
      (and (ptx-eq-witnessp (car aes) (car bes) neq names asg p)
           (ptx-bop-witnessp neq acc (cdr sub) (nth k names) asg p)
           (ptx-leq-witnessp (cdr aes) (cdr bes) neq (cdr r)
                             (nthcdr (1+ k) names) asg p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(define ptx-blcp (x)
  :short "A Boolean term: a constant or a sparse vector."
  :enabled t
  (r1cs::sparse-vectorp (and (consp x) x)))

(defrule ptx-blcp-of-bop
  (implies (and (ptx-blcp x) (ptx-blcp y) (symbolp z))
           (ptx-blcp (cdr (ptx-bop neq x y z))))
  :enable (ptx-bop ptx-and ptx-or r1cs::sparse-vectorp
                   r1cs::sparse-vector-elementp))

(defrule ptx-bitp-of-bop-spec
  (bitp (ptx-bop-spec neq x y))
  :enable ptx-bop-spec)

(defrule ptx-symbolp-of-nth-when-symbol-listp
  (implies (symbol-listp names)
           (symbolp (nth k names)))
  :enable nth)

(defrule ptx-symbol-listp-of-nthcdr
  (implies (symbol-listp names)
           (symbol-listp (nthcdr k names)))
  :enable nthcdr)

(defrule ptx-bitp-of-name-bit
  (bitp (ptx-name-bit ida idb neq))
  :enable ptx-name-bit)

(defruled ptx-plaintext-equalp-openers
  (and (implies (and (literalp x) (literalp y))
                (equal (values-plaintext-equalp (plaintext-literal x)
                                                (plaintext-literal y))
                       (values-literal-equalp x y)))
       (implies (and (plaintext-member-listp x) (plaintext-member-listp y))
                (equal (values-plaintext-equalp (plaintext-struct x)
                                                (plaintext-struct y))
                       (and (equal (len x) (len y))
                            (values-plaintext-members-equalp x y))))
       (implies (and (plaintext-listp x) (plaintext-listp y))
                (equal (values-plaintext-equalp (plaintext-array x)
                                                (plaintext-array y))
                       (and (equal (len x) (len y))
                            (values-plaintext-elements-equalp x y))))
       (equal (values-plaintext-equalp (plaintext-literal x) (plaintext-struct y)) nil)
       (equal (values-plaintext-equalp (plaintext-literal x) (plaintext-array y)) nil)
       (equal (values-plaintext-equalp (plaintext-struct x) (plaintext-literal y)) nil)
       (equal (values-plaintext-equalp (plaintext-struct x) (plaintext-array y)) nil)
       (equal (values-plaintext-equalp (plaintext-array x) (plaintext-literal y)) nil)
       (equal (values-plaintext-equalp (plaintext-array x) (plaintext-struct y)) nil))
  :expand ((:free (x y) (values-plaintext-equalp x y))))

(defruled ptx-members-equalp-openers
  (and (implies (or (atom xs) (atom ys))
                (equal (values-plaintext-members-equalp xs ys) t))
       (equal (values-plaintext-members-equalp (cons x xs) (cons y ys))
              (and (equal (identifier->field (plaintext-member->name x))
                          (identifier->field (plaintext-member->name y)))
                   (values-plaintext-equalp (plaintext-member->value x)
                                            (plaintext-member->value y))
                   (values-plaintext-members-equalp xs ys))))
  :expand ((values-plaintext-members-equalp xs ys)
           (values-plaintext-members-equalp (cons x xs) (cons y ys))))

(defruled ptx-elements-equalp-openers
  (and (implies (or (atom xs) (atom ys))
                (equal (values-plaintext-elements-equalp xs ys) t))
       (equal (values-plaintext-elements-equalp (cons x xs) (cons y ys))
              (and (values-plaintext-equalp x y)
                   (values-plaintext-elements-equalp xs ys))))
  :expand ((values-plaintext-elements-equalp xs ys)
           (values-plaintext-elements-equalp (cons x xs) (cons y ys))))

(define ptx-eq-spec (neq yes)
  :enabled t
  (values-bool-to-bit (if neq (not yes) yes)))

(local (in-theory (enable ptx-plaintext-equalp-openers
                          ptx-members-equalp-openers
                          ptx-elements-equalp-openers
                          values-bool-to-bit)))

(defrule ptx-blcp-of-name-bit
  (ptx-blcp (ptx-name-bit ida idb neq))
  :enable ptx-name-bit)

(defrule ptx-blcp-of-consts
  (and (ptx-blcp 0) (ptx-blcp 1)))

(defrule ptx-blcp-of-leaf-eq-out
  (ptx-blcp (ptx-leaf-eq-out wa wb neq names))
  :use ptx-sparse-vectorp-of-leaf-eq-out
  :disable ptx-sparse-vectorp-of-leaf-eq-out)

(defrule ptx-blcp-of-if
  (implies (and (ptx-blcp x) (ptx-blcp y))
           (ptx-blcp (if c x y))))

(in-theory (disable ptx-blcp))


(defthm-ptx-eq-flag
  (defthm ptx-blcp-of-eq
    (implies (symbol-listp names)
             (ptx-blcp (cdr (ptx-eq a b neq names))))
    :flag ptx-eq)
  (defthm ptx-blcp-of-meq
    (implies (and (symbol-listp names) (ptx-blcp acc))
             (ptx-blcp (cdr (ptx-meq ams bms neq acc names))))
    :flag ptx-meq)
  (defthm ptx-blcp-of-leq
    (implies (and (symbol-listp names) (ptx-blcp acc))
             (ptx-blcp (cdr (ptx-leq aes bes neq acc names))))
    :flag ptx-leq)
  :hints (("Goal"
           :in-theory (disable ptx-name-bit ptx-bop)
           :expand ((:free (neq) (ptx-eq a b neq names))
                    (:free (neq acc) (ptx-meq ams bms neq acc names))
                    (:free (neq acc) (ptx-leq aes bes neq acc names))))))

(defrule ptx-bop-sound-rw
  (implies (and (primep p)
                (symbolp z)
                (ptx-blcp x)
                (ptx-blcp y)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (r1cs::r1cs-constraints-holdp (car (ptx-bop neq x y z)) asg p))
           (equal (ptx-bval (cdr (ptx-bop neq x y z)) asg p)
                  (ptx-bop-spec neq (ptx-bval x asg p) (ptx-bval y asg p))))
  :use ptx-bop-sound
  :enable ptx-blcp)


(defthm-ptx-eq-flag
  (defthm ptx-eq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (ptx-typed a asg)
                  (ptx-typed b asg)
                  (r1cs::r1cs-constraints-holdp (car (ptx-eq a b neq names)) asg p))
             (and (equal (ptx-bval (cdr (ptx-eq a b neq names)) asg p)
                         (ptx-eq-spec neq (values-plaintext-equalp
                                           (ptx-val a asg) (ptx-val b asg))))))
    :flag ptx-eq)
  (defthm ptx-meq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (ptx-mtyped ams asg)
                  (ptx-mtyped bms asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car (ptx-meq ams bms neq acc names))
                                                asg p))
             (and (equal (ptx-bval (cdr (ptx-meq ams bms neq acc names)) asg p)
                         (ptx-bop-spec neq (ptx-bval acc asg p)
                                       (ptx-eq-spec neq
                                                    (values-plaintext-members-equalp
                                                     (ptx-mval ams asg)
                                                     (ptx-mval bms asg)))))))
    :flag ptx-meq)
  (defthm ptx-leq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (ptx-ltyped aes asg)
                  (ptx-ltyped bes asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car (ptx-leq aes bes neq acc names))
                                                asg p))
             (and (equal (ptx-bval (cdr (ptx-leq aes bes neq acc names)) asg p)
                         (ptx-bop-spec neq (ptx-bval acc asg p)
                                       (ptx-eq-spec neq
                                                    (values-plaintext-elements-equalp
                                                     (ptx-lval aes asg)
                                                     (ptx-lval bes asg)))))))
    :flag ptx-leq)
  :hints (("Goal"
           :in-theory (e/d (ptx-leaf-eq-sound ptx-bop-spec bitand bitor ptx-name-bit)
                            (ptx-bop))
           :expand ((:free (neq) (ptx-eq a b neq names))
                    (:free (neq acc) (ptx-meq ams bms neq acc names))
                    (:free (neq acc) (ptx-leq aes bes neq acc names))
                    (ptx-typed a asg) (ptx-typed b asg)
                    (ptx-mtyped ams asg) (ptx-mtyped bms asg)
                    (ptx-ltyped aes asg) (ptx-ltyped bes asg)
                    (ptx-val a asg) (ptx-val b asg)
                    (ptx-mval ams asg) (ptx-mval bms asg)
                    (ptx-lval aes asg) (ptx-lval bes asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defrule ptx-bop-complete-rw
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp z)
                (ptx-blcp x)
                (ptx-blcp y)
                (bitp (ptx-bval x asg p))
                (bitp (ptx-bval y asg p))
                (ptx-bop-witnessp neq x y z asg p))
           (r1cs::r1cs-constraints-holdp (car (ptx-bop neq x y z)) asg p))
  :use ptx-bop-complete
  :enable ptx-blcp)

(defrule ptx-bop-witnessp-when-const
  (and (ptx-bop-witnessp neq x 0 z asg p)
       (ptx-bop-witnessp neq x 1 z asg p))
  :enable ptx-bop-witnessp)

(defthm-ptx-eq-flag
  (defthm ptx-eq-complete
    (implies (and (primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (ptx-typed a asg)
                  (ptx-typed b asg)
                  (ptx-eq-witnessp a b neq names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-eq a b neq names)) asg p))
    :flag ptx-eq)
  (defthm ptx-meq-complete
    (implies (and (primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (ptx-mtyped ams asg)
                  (ptx-mtyped bms asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (ptx-meq-witnessp ams bms neq acc names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-meq ams bms neq acc names))
                                           asg p))
    :flag ptx-meq)
  (defthm ptx-leq-complete
    (implies (and (primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (ptx-ltyped aes asg)
                  (ptx-ltyped bes asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (ptx-leq-witnessp aes bes neq acc names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-leq aes bes neq acc names))
                                           asg p))
    :flag ptx-leq)
  :hints (("Goal"
           :in-theory (e/d (ptx-leaf-eq-complete ptx-name-bit)
                           (ptx-bop ptx-bop-witnessp))
           :expand ((:free (neq) (ptx-eq a b neq names))
                    (:free (neq acc) (ptx-meq ams bms neq acc names))
                    (:free (neq acc) (ptx-leq aes bes neq acc names))
                    (:free (neq) (ptx-eq-witnessp a b neq names asg p))
                    (:free (neq acc) (ptx-meq-witnessp ams bms neq acc names asg p))
                    (:free (neq acc) (ptx-leq-witnessp aes bes neq acc names asg p))
                    (ptx-typed a asg) (ptx-typed b asg)
                    (ptx-mtyped ams asg) (ptx-mtyped bms asg)
                    (ptx-ltyped aes asg) (ptx-ltyped bes asg)))))
