; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean wires with constant folding, as snarkVM's Boolean type builds them
; (circuit/types/boolean/src/{not,xor,and}.rs).
;
; A wire (HKEC-TERM-P) is either a constant bit or a non-constant linear
; combination (an R1CS sparse vector).  The circuit is a list of R1CS
; constraints, newest first; the next private variable is (HKEC-VAR n) with n
; the number of constraints so far, since every non-constant AND and XOR
; allocates exactly one variable and emits exactly one constraint:
;   not a      constant 1 - a, or the linear combination 1 - a (no constraint)
;   a xor b    a constant operand folds (b, or not b); otherwise
;              (a + a) * b = a + b - w
;   a and b    a constant operand folds (the other operand, or constant 0);
;              otherwise a * b = w
;
; Soundness (HKEC-XOR-SOUND, HKEC-AND-SOUND): in every assignment that
; satisfies the constraints and gives the operands bit values, the output is
; the bit XOR / AND of the operands.
;
; Completeness: HKEC-SOLVE computes the private variables from any input
; assignment, constraint by constraint, and HKEC-SOLVE-HOLDS shows that it
; satisfies every well-formed constraint list (HKEC-WF), which the gadgets
; maintain (HKEC-XOR-WF, HKEC-AND-WF).

(in-package "ALEOVM")

(include-book "../fun-specs/hash-keccak")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/strings/decimal" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Private variables.

(defund hkec-var (n)
  (intern-in-package-of-symbol (str::nat-to-dec-string (nfix n)) :hkec))

(defrule symbolp-of-hkec-var
  (symbolp (hkec-var n))
  :rule-classes (:rewrite :type-prescription)
  :enable hkec-var)

(defrule hkec-var-not-1
  (not (equal (hkec-var n) 1))
  :use symbolp-of-hkec-var
  :disable symbolp-of-hkec-var)

(defund hkec-var-index (v)
  (if (symbolp v)
      (str::dec-digit-chars-value (acl2::explode (symbol-name v)))
    0))

(defrule natp-of-hkec-var-index
  (natp (hkec-var-index v))
  :rule-classes (:rewrite :type-prescription)
  :enable hkec-var-index)

(defrule hkec-var-index-of-hkec-var
  (equal (hkec-var-index (hkec-var n))
         (nfix n))
  :enable (hkec-var hkec-var-index))

(defrule hkec-var-one-to-one
  (equal (equal (hkec-var n) (hkec-var m))
         (equal (nfix n) (nfix m)))
  :use ((:instance hkec-var-index-of-hkec-var (n n))
        (:instance hkec-var-index-of-hkec-var (n m)))
  :disable hkec-var-index-of-hkec-var
  :enable hkec-var)

(define hkec-old-p (v (n natp))
  :short "@('v') is not one of the private variables numbered @('n') or above."
  (or (not (equal v (hkec-var (hkec-var-index v))))
      (< (hkec-var-index v) (nfix n)))
  ///
  (defrule hkec-old-p-mono
    (implies (and (hkec-old-p v n)
                  (natp n) (natp m) (<= n m))
             (hkec-old-p v m)))
  (defrule hkec-old-p-of-hkec-var
    (equal (hkec-old-p (hkec-var k) n)
           (< (nfix k) (nfix n))))
  (defrule hkec-var-not-old
    (implies (and (hkec-old-p v n)
                  (natp n) (natp m) (<= n m))
             (not (equal v (hkec-var m))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Linear combinations.

(defun hkec-lc-old-p (lc n)
  ;; every pseudo-variable is the constant 1 or not a variable numbered >= n
  (if (atom lc)
      t
    (and (or (equal (cadr (car lc)) 1)
             (hkec-old-p (cadr (car lc)) n))
         (hkec-lc-old-p (cdr lc) n))))

(defrule hkec-lc-old-p-mono
  (implies (and (hkec-lc-old-p lc n)
                (natp n) (natp m) (<= n m))
           (hkec-lc-old-p lc m))
  :induct (hkec-lc-old-p lc n)
  :enable hkec-old-p)

(defrule hkec-lc-old-p-of-append
  (equal (hkec-lc-old-p (append x y) n)
         (and (hkec-lc-old-p x n)
              (hkec-lc-old-p y n))))

(defun hkec-lc-neg (lc p)
  (if (atom lc)
      nil
    (cons (list (pfield::neg (car (car lc)) p) (cadr (car lc)))
          (hkec-lc-neg (cdr lc) p))))

(defrule sparse-vectorp-of-hkec-lc-neg
  (implies (r1cs::sparse-vectorp lc)
           (r1cs::sparse-vectorp (hkec-lc-neg lc p)))
  :enable r1cs::sparse-vectorp)

(defrule hkec-lc-old-p-of-hkec-lc-neg
  (equal (hkec-lc-old-p (hkec-lc-neg lc p) n)
         (hkec-lc-old-p lc n)))

(defrule dot-product-of-hkec-lc-neg
  (implies (and (primep p)
                (r1cs::sparse-vectorp lc))
           (equal (r1cs::dot-product (hkec-lc-neg lc p) asg p)
                  (pfield::neg (r1cs::dot-product lc asg p) p)))
  :enable (r1cs::dot-product r1cs::sparse-vectorp))

(defrule hkec-lookup-of-acons-when-old
  (implies (hkec-old-p v n)
           (equal (lookup-equal v (cons (cons (hkec-var n) val) asg))
                  (lookup-equal v asg)))
  :enable lookup-equal
  :use ((:instance hkec-var-not-old (m n))))

(defrule hkec-lookup-of-cons-same
  (equal (lookup-equal v (cons (cons v val) asg))
         val)
  :enable lookup-equal)

(defrule dot-product-of-acons-when-old
  (implies (hkec-lc-old-p lc n)
           (equal (r1cs::dot-product lc (cons (cons (hkec-var n) val) asg) p)
                  (r1cs::dot-product lc asg p)))
  :enable r1cs::dot-product)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wires.

(define hkec-term-p (x)
  (or (bitp x)
      (and (consp x)
           (r1cs::sparse-vectorp x))))

(define hkec-term-ok (x (n natp))
  :short "A wire whose variables exist once @('n') private variables are allocated."
  (and (hkec-term-p x)
       (or (bitp x)
           (hkec-lc-old-p x n)))
  ///
  (defrule hkec-term-ok-mono
    (implies (and (hkec-term-ok x n)
                  (natp n) (natp m) (<= n m))
             (hkec-term-ok x m))
    :use ((:instance hkec-lc-old-p-mono (lc x)))
    :disable hkec-lc-old-p-mono
    :do-not-induct t)
  (defrule hkec-term-ok-when-bitp
    (implies (bitp x)
             (hkec-term-ok x n))
    :enable hkec-term-p))

(define hkec-eval (x asg (p primep))
  :short "The value of a wire."
  (if (bitp x)
      x
    (r1cs::dot-product x asg p))
  ///
  (defrule hkec-eval-when-bitp
    (implies (bitp x)
             (equal (hkec-eval x asg p) x))))

(defun hkec-terms-ok (xs n)
  (if (atom xs)
      t
    (and (hkec-term-ok (car xs) n)
         (hkec-terms-ok (cdr xs) n))))

(defrule hkec-terms-ok-mono
  (implies (and (hkec-terms-ok xs n)
                (natp n) (natp m) (<= n m))
           (hkec-terms-ok xs m))
  :induct (hkec-terms-ok xs n))

(defun hkec-eval-list (xs asg p)
  (if (atom xs)
      nil
    (cons (hkec-eval (car xs) asg p)
          (hkec-eval-list (cdr xs) asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Well-formed constraint lists and their solution.

(defun hkec-wf (cs p)
  (if (atom cs)
      (null cs)
    (let* ((c (car cs))
           (n (len (cdr cs)))
           (cc (r1cs::r1cs-constraint->c c))
           (e (car cc)))
      (and (r1cs::r1cs-constraintp c)
           (consp cc)
           (or (equal (car e) 1) (equal (car e) (1- p)))
           (equal (cadr e) (hkec-var n))
           (hkec-lc-old-p (r1cs::r1cs-constraint->a c) n)
           (hkec-lc-old-p (r1cs::r1cs-constraint->b c) n)
           (hkec-lc-old-p (cdr cc) n)
           (hkec-wf (cdr cs) p)))))

(defun hkec-solve (cs asg p)
  (if (atom cs)
      asg
    (let* ((asg1 (hkec-solve (cdr cs) asg p))
           (c (car cs))
           (cc (r1cs::r1cs-constraint->c c))
           (e (car cc))
           (val (pfield::mul
                 (mod (ifix (car e)) p)
                 (pfield::sub
                  (pfield::mul (r1cs::dot-product (r1cs::r1cs-constraint->a c) asg1 p)
                               (r1cs::dot-product (r1cs::r1cs-constraint->b c) asg1 p)
                               p)
                  (r1cs::dot-product (cdr cc) asg1 p)
                  p)
                 p)))
      (acons (cadr e) val asg1))))

(defun hkec-cs-old-p (cs n)
  (if (atom cs)
      t
    (and (hkec-lc-old-p (r1cs::r1cs-constraint->a (car cs)) n)
         (hkec-lc-old-p (r1cs::r1cs-constraint->b (car cs)) n)
         (hkec-lc-old-p (r1cs::r1cs-constraint->c (car cs)) n)
         (hkec-cs-old-p (cdr cs) n))))

(defrule hkec-cs-old-p-mono
  (implies (and (hkec-cs-old-p cs n)
                (natp n) (natp m) (<= n m))
           (hkec-cs-old-p cs m))
  :induct (hkec-cs-old-p cs n))

(defrule hkec-cs-old-p-when-wf
  (implies (hkec-wf cs p)
           (hkec-cs-old-p cs (len cs)))
  :induct (hkec-wf cs p))

(defrule hkec-constraints-holdp-of-acons-when-old
  (implies (hkec-cs-old-p cs n)
           (equal (r1cs::r1cs-constraints-holdp cs (cons (cons (hkec-var n) val) asg) p)
                  (r1cs::r1cs-constraints-holdp cs asg p)))
  :enable r1cs::r1cs-constraint-holdsp)

(defruledl hkec-k-squared
  (implies (and (primep p)
                (or (equal k 1) (equal k (1- p))))
           (equal (pfield::mul (mod k p) (pfield::mul (mod k p) x p) p)
                  (pfield::fep-fix x p)))
  :cases ((equal k 1))
  :enable (pfield::fep-fix))

(defrule hkec-solve-holds
  (implies (and (primep p)
                (hkec-wf cs p))
           (r1cs::r1cs-constraints-holdp cs (hkec-solve cs asg p) p))
  :hints (("Goal" :induct (hkec-solve cs asg p)
           :in-theory (enable r1cs::r1cs-constraint-holdsp r1cs::dot-product))
          ("Subgoal *1/2" :use ((:instance hkec-k-squared
                                 (k (car (car (r1cs::r1cs-constraint->c (car cs)))))
                                 (x (pfield::sub
                                     (pfield::mul (r1cs::dot-product (r1cs::r1cs-constraint->a (car cs))
                                                                     (hkec-solve (cdr cs) asg p) p)
                                                  (r1cs::dot-product (r1cs::r1cs-constraint->b (car cs))
                                                                     (hkec-solve (cdr cs) asg p) p)
                                                  p)
                                     (r1cs::dot-product (cdr (r1cs::r1cs-constraint->c (car cs)))
                                                        (hkec-solve (cdr cs) asg p) p)
                                     p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extensions of a constraint list.

(defun hkec-ext (new old)
  (if (equal new old)
      t
    (and (consp new)
         (hkec-ext (cdr new) old))))

(defrule hkec-ext-refl
  (hkec-ext x x))

(defrule hkec-ext-of-cons
  (implies (hkec-ext cs old)
           (hkec-ext (cons c cs) old)))

(defrule hkec-holdp-when-ext
  (implies (and (r1cs::r1cs-constraints-holdp new asg p)
                (hkec-ext new old))
           (r1cs::r1cs-constraints-holdp old asg p))
  :induct (hkec-ext new old))

(defrule hkec-len-when-ext
  (implies (hkec-ext new old)
           (<= (len old) (len new)))
  :induct (hkec-ext new old)
  :rule-classes (:rewrite :linear))

(defrule hkec-wf-when-ext
  (implies (and (hkec-wf new p)
                (hkec-ext new old))
           (hkec-wf old p))
  :induct (hkec-ext new old))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wires with bit values.

(define hkec-wire-p (x asg (p primep))
  (and (hkec-term-p x)
       (bitp (hkec-eval x asg p))))

(defun hkec-wires-p (xs asg p)
  (if (atom xs)
      t
    (and (hkec-wire-p (car xs) asg p)
         (hkec-wires-p (cdr xs) asg p))))

(defrule hkec-wire-p-when-bitp
  (implies (bitp x)
           (hkec-wire-p x asg p))
  :enable (hkec-wire-p hkec-term-p))

(defrule bitp-of-hkec-eval-when-hkec-wire-p
  (implies (hkec-wire-p x asg p)
           (bitp (hkec-eval x asg p)))
  :enable hkec-wire-p)

(defrule bit-listp-of-hkec-eval-list
  (implies (hkec-wires-p xs asg p)
           (bit-listp (hkec-eval-list xs asg p))))

(defrule len-of-hkec-eval-list
  (equal (len (hkec-eval-list xs asg p))
         (len xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean::not.

(define hkec-not (x (p primep))
  (if (bitp x)
      (if (equal x 1) 0 1)
    (cons (list 1 1) (hkec-lc-neg x p))))

(defrule hkec-term-ok-of-hkec-not
  (implies (hkec-term-ok x n)
           (hkec-term-ok (hkec-not x p) n))
  :enable (hkec-not hkec-term-ok hkec-term-p))

(defrule hkec-wire-p-of-hkec-not
  (implies (and (primep p)
                (hkec-wire-p x asg p))
           (and (hkec-wire-p (hkec-not x p) asg p)
                (equal (hkec-eval (hkec-not x p) asg p)
                       (hkec-bnot (hkec-eval x asg p)))))
  :enable (hkec-not hkec-wire-p hkec-term-p hkec-eval r1cs::dot-product)
  :cases ((equal (r1cs::dot-product x asg p) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean::bitxor.

(define hkec-xor (a b cs (p primep))
  :returns (mv out new-cs)
  (cond ((bitp a) (mv (if (equal a 1) (hkec-not b p) b) cs))
        ((bitp b) (mv (if (equal b 1) (hkec-not a p) a) cs))
        (t (let ((w (hkec-var (len cs))))
             (mv (list (list 1 w))
                 (cons (r1cs::r1cs-constraint (append a a)
                                              b
                                              (cons (list (1- p) w)
                                                    (append a b)))
                       cs))))))

(defrule hkec-xor-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-xor a b cs p)) old))
  :enable hkec-xor)

(defrule hkec-xor-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-xor a b cs p))))
  :rule-classes :linear
  :enable hkec-xor)

(defrule hkec-xor-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-term-ok a (len cs))
                (hkec-term-ok b (len cs)))
           (hkec-wf (mv-nth 1 (hkec-xor a b cs p)) p))
  :enable (hkec-xor hkec-not hkec-term-ok hkec-term-p r1cs::sparse-vectorp)
  :do-not-induct t)

(defrule hkec-xor-ok
  (implies (and (hkec-term-ok a (len cs))
                (hkec-term-ok b (len cs))
                (natp m)
                (<= (len (mv-nth 1 (hkec-xor a b cs p))) m))
           (hkec-term-ok (mv-nth 0 (hkec-xor a b cs p)) m))
  :enable (hkec-xor hkec-not hkec-term-ok hkec-term-p r1cs::sparse-vectorp)
  :do-not-induct t)

(defruledl hkec-add-k-cancel
  (implies (and (posp p)
                (integerp k))
           (equal (equal (pfield::add k w p) (mod k p))
                  (equal (mod (ifix w) p) 0)))
  :enable pfield::add)

(defruledl hkec-xor-field-lemma
  (implies (and (primep p)
                (bitp x)
                (bitp y)
                (equal (pfield::mul (pfield::add x x p) y p)
                       (pfield::add (pfield::mul (1- p) w p)
                                    (pfield::add x y p)
                                    p)))
           (equal (pfield::mul 1 w p)
                  (acl2::bitxor x y)))
  :cases ((and (equal x 0) (equal y 0))
          (and (equal x 0) (equal y 1))
          (and (equal x 1) (equal y 0))
          (and (equal x 1) (equal y 1)))
  :enable (bitp hkec-add-k-cancel))

(defruledl hkec-xor-sound-var
  (implies (and (primep p)
                (not (bitp a))
                (not (bitp b))
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-xor a b cs p)) asg p)
                (hkec-wire-p a asg p)
                (hkec-wire-p b asg p))
           (and (hkec-wire-p (mv-nth 0 (hkec-xor a b cs p)) asg p)
                (equal (hkec-eval (mv-nth 0 (hkec-xor a b cs p)) asg p)
                       (acl2::bitxor (hkec-eval a asg p) (hkec-eval b asg p)))))
  :enable (hkec-xor hkec-wire-p hkec-term-p hkec-eval
                    r1cs::r1cs-constraint-holdsp r1cs::dot-product)
  :use ((:instance hkec-xor-field-lemma
                   (x (r1cs::dot-product a asg p))
                   (y (r1cs::dot-product b asg p))
                   (w (lookup-equal (hkec-var (len cs)) asg)))))

(defrule hkec-xor-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-xor a b cs p)) asg p)
                (hkec-wire-p a asg p)
                (hkec-wire-p b asg p))
           (and (hkec-wire-p (mv-nth 0 (hkec-xor a b cs p)) asg p)
                (equal (hkec-eval (mv-nth 0 (hkec-xor a b cs p)) asg p)
                       (acl2::bitxor (hkec-eval a asg p) (hkec-eval b asg p)))))
  :cases ((and (not (bitp a)) (not (bitp b))))
  :hints (("Subgoal 2" :in-theory (enable hkec-xor bitp))
          ("Subgoal 1" :use hkec-xor-sound-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean::bitand.

(define hkec-and (a b cs (p primep))
  :returns (mv out new-cs)
  (declare (ignorable p))
  (cond ((bitp a) (mv (if (equal a 1) b a) cs))
        ((bitp b) (mv (if (equal b 1) a b) cs))
        (t (let ((w (hkec-var (len cs))))
             (mv (list (list 1 w))
                 (cons (r1cs::r1cs-constraint a b (list (list 1 w)))
                       cs))))))

(defrule hkec-and-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-and a b cs p)) old))
  :enable hkec-and)

(defrule hkec-and-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-and a b cs p))))
  :rule-classes :linear
  :enable hkec-and)

(defrule hkec-and-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-term-ok a (len cs))
                (hkec-term-ok b (len cs)))
           (hkec-wf (mv-nth 1 (hkec-and a b cs p)) p))
  :enable (hkec-and hkec-term-ok hkec-term-p r1cs::sparse-vectorp)
  :do-not-induct t)

(defrule hkec-and-ok
  (implies (and (hkec-term-ok a (len cs))
                (hkec-term-ok b (len cs))
                (natp m)
                (<= (len (mv-nth 1 (hkec-and a b cs p))) m))
           (hkec-term-ok (mv-nth 0 (hkec-and a b cs p)) m))
  :enable (hkec-and hkec-term-ok hkec-term-p r1cs::sparse-vectorp)
  :do-not-induct t)

(defruledl hkec-and-sound-var
  (implies (and (primep p)
                (not (bitp a))
                (not (bitp b))
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-and a b cs p)) asg p)
                (hkec-wire-p a asg p)
                (hkec-wire-p b asg p))
           (and (hkec-wire-p (mv-nth 0 (hkec-and a b cs p)) asg p)
                (equal (hkec-eval (mv-nth 0 (hkec-and a b cs p)) asg p)
                       (acl2::bitand (hkec-eval a asg p) (hkec-eval b asg p)))))
  :enable (hkec-and hkec-wire-p hkec-term-p hkec-eval
                    r1cs::r1cs-constraint-holdsp r1cs::dot-product)
  :cases ((and (equal (r1cs::dot-product a asg p) 0) (equal (r1cs::dot-product b asg p) 0))
          (and (equal (r1cs::dot-product a asg p) 0) (equal (r1cs::dot-product b asg p) 1))
          (and (equal (r1cs::dot-product a asg p) 1) (equal (r1cs::dot-product b asg p) 0))
          (and (equal (r1cs::dot-product a asg p) 1) (equal (r1cs::dot-product b asg p) 1))))

(defrule hkec-and-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-and a b cs p)) asg p)
                (hkec-wire-p a asg p)
                (hkec-wire-p b asg p))
           (and (hkec-wire-p (mv-nth 0 (hkec-and a b cs p)) asg p)
                (equal (hkec-eval (mv-nth 0 (hkec-and a b cs p)) asg p)
                       (acl2::bitand (hkec-eval a asg p) (hkec-eval b asg p)))))
  :cases ((and (not (bitp a)) (not (bitp b))))
  :hints (("Subgoal 2" :in-theory (enable hkec-and bitp))
          ("Subgoal 1" :use hkec-and-sound-var)))
