; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shared R1CS pieces for the string, collections, environment, and network
; circuit functions in val-*.lisp.
;
; Boolean negation is the linear combination 1 - x.  It is never a
; constraint.  assert_eq of a variable against a constant k is the
; constraint (k) * (1) = (x), i.e. the constant sits on the ONE wire.
; Field equality of two variables is the is_not_equal pair
; (a - b) * m = r, (a - b) * (1 - r) = 0, and the boolean result is 1 - r.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-environment")
(include-book "../fun-specs/primitives-field")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define val-not-lc ((x symbolp) (p primep))
  :returns (lc true-listp :hyp :guard)
  :short "Linear combination @($1 - x$).  Boolean @('not') adds no witness."
  (list (list 1 1)
        (list (1- p) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (k) * (1) = (x), with k a constant coefficient of ONE.

(define const-assert-eq-gadget ((k natp) (x symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraint added by @('assert_eq') of a constant against a variable."
  (list (r1cs::make-r1cs-constraint
         :a (list (list k 1))
         :b (list (list 1 1))
         :c (list (list 1 x)))))

(defruled const-assert-eq-gadget-to-eq
  (implies (and (natp k)
                (< k p)
                (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp
                   (const-assert-eq-gadget k x) asg p)
                  (equal (lookup-equal x asg) k)))
  :enable (const-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled const-assert-eq-gadget-sound
  (implies (and (natp k)
                (< k p)
                (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::r1cs-constraints-holdp
                 (const-assert-eq-gadget k x) asg p))
           (equal (lookup-equal x asg) k))
  :enable const-assert-eq-gadget-to-eq)

(defruled const-assert-eq-gadget-complete
  (implies (and (natp k)
                (< k p)
                (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (equal (lookup-equal x asg) k))
           (r1cs::r1cs-constraints-holdp
            (const-assert-eq-gadget k x) asg p))
  :enable const-assert-eq-gadget-to-eq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (x) * (1) = (0)

(define assert-zero-gadget ((x symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('assert_eq(x, 0)'), variable against the constant zero."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c nil)))

(defruled assert-zero-gadget-to-eq
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp
                   (assert-zero-gadget x) asg p)
                  (equal (lookup-equal x asg) 0)))
  :enable (assert-zero-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled assert-zero-gadget-sound
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::r1cs-constraints-holdp (assert-zero-gadget x) asg p))
           (equal (lookup-equal x asg) 0))
  :enable assert-zero-gadget-to-eq)

(defruled assert-zero-gadget-complete
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (equal (lookup-equal x asg) 0))
           (r1cs::r1cs-constraints-holdp (assert-zero-gadget x) asg p))
  :enable assert-zero-gadget-to-eq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field is_equal of two variables (neither side constant).
; Result boolean is the linear combination 1 - r.

(define field-var-is-equal-gadget ((a symbolp) (b symbolp)
                                   (m symbolp) (r symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::is_not_equal'); the @('is_equal') bit is @($1 - r$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a)
                  (list (1- p) b))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 a)
                  (list (1- p) b))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c nil)))

(defruled field-var-is-equal-gadget-to-spec
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg))
                (delta (pfield::sub a$ b$ p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (field-var-is-equal-gadget a b m r p) asg p)
                    (and (equal (pfield::mul delta m$ p) r$)
                         (equal (pfield::mul delta
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (field-var-is-equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled field-var-is-equal-bit-when-constraints
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (bitp r)
                (pfield::fep m p)
                (equal (pfield::mul (pfield::sub a b p) m p) r)
                (equal (pfield::mul (pfield::sub a b p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (equal (pfield::sub 1 r p)
                  (if (equal a b) 1 0)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (fieldp bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub a b p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x a)
                            (y b))
                 (:instance pfield::mul-of-0-arg1
                            (x (pfield::sub a b p))
                            (y m))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub a b p)))))))

(defruled field-var-is-equal-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (field-var-is-equal-gadget a b m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (if (equal (lookup-equal a asg) (lookup-equal b asg))
                      1
                    0)))
  :hints (("Goal"
           :in-theory (e/d (field-var-is-equal-gadget-to-spec
                            field-var-is-equal-bit-when-constraints
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled field-var-is-equal-constraints-when-witness
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (equal r (if (equal a b) 0 1))
                (equal m (if (equal a b)
                             0
                           (pfield::inv (pfield::sub a b p) p))))
           (and (equal (pfield::mul (pfield::sub a b p) m p) r)
                (equal (pfield::mul (pfield::sub a b p)
                                    (pfield::sub 1 r p)
                                    p)
                       0)
                (equal (pfield::sub 1 r p)
                       (if (equal a b) 1 0))))
  :hints (("Goal"
           :cases ((equal a b))
           :in-theory (e/d (fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub a b p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x a)
                            (y b))
                 (:instance pfield::mul-of-0-arg1
                            (x (pfield::sub a b p))
                            (y m))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub a b p)))))))

(defruled field-var-is-equal-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal a asg)
                                  (lookup-equal b asg))
                           0
                         1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal a asg)
                                  (lookup-equal b asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal a asg)
                                                   (lookup-equal b asg)
                                                   p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (field-var-is-equal-gadget a b m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (if (equal (lookup-equal a asg)
                                  (lookup-equal b asg))
                           1
                         0))))
  :hints (("Goal"
           :in-theory (e/d (field-var-is-equal-gadget-to-spec
                            field-var-is-equal-constraints-when-witness
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sum of named bits, as a linear combination.  No constraint.

(define val-sum-lc ((xs symbol-listp))
  :returns (lc true-listp :hyp :guard)
  (if (endp xs)
      nil
    (cons (list 1 (car xs))
          (val-sum-lc (cdr xs)))))

; (sum xs) * (1) = (0).  Used by Boolean::assert_bits_are_zero.

(define assert-bits-sum-zero-gadget ((xs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single constraint of @('Boolean::assert_bits_are_zero')."
  (list (r1cs::make-r1cs-constraint
         :a (val-sum-lc xs)
         :b (list (list 1 1))
         :c nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Merkle child ordering.  The indicator is the linear combination 1 - bit,
; where bit is the leaf-index bit.  Boolean not is not a witness.
;   left  = (1 - bit) ? current : sibling
;   right = (1 - bit) ? sibling : current
; so a 0 index bit puts the running hash on the left, matching
; MerklePath::verify.

(define merkle-path-left-gadget ((bit symbolp) (cur symbolp) (sib symbolp)
                                 (left symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 cur)
                  (list (1- p) sib))
         :b (val-not-lc bit p)
         :c (list (list 1 left)
                  (list (1- p) sib)))))

(define merkle-path-right-gadget ((bit symbolp) (cur symbolp) (sib symbolp)
                                  (right symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 sib)
                  (list (1- p) cur))
         :b (val-not-lc bit p)
         :c (list (list 1 right)
                  (list (1- p) cur)))))

(defruled merkle-path-left-gadget-to-spec
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib) (symbolp left)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg left))
           (equal (r1cs::r1cs-constraints-holdp
                   (merkle-path-left-gadget bit cur sib left p) asg p)
                  (equal (pfield::mul (pfield::sub (lookup-equal cur asg)
                                                   (lookup-equal sib asg)
                                                   p)
                                      (pfield::sub 1 (lookup-equal bit asg) p)
                                      p)
                         (pfield::sub (lookup-equal left asg)
                                      (lookup-equal sib asg)
                                      p))))
  :enable (merkle-path-left-gadget
           val-not-lc
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled merkle-path-right-gadget-to-spec
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib) (symbolp right)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg right))
           (equal (r1cs::r1cs-constraints-holdp
                   (merkle-path-right-gadget bit cur sib right p) asg p)
                  (equal (pfield::mul (pfield::sub (lookup-equal sib asg)
                                                   (lookup-equal cur asg)
                                                   p)
                                      (pfield::sub 1 (lookup-equal bit asg) p)
                                      p)
                         (pfield::sub (lookup-equal right asg)
                                      (lookup-equal cur asg)
                                      p))))
  :enable (merkle-path-right-gadget
           val-not-lc
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled merkle-path-order-when-bit
  (implies (and (equal p (base-prime))
                (bitp bit)
                (fieldp cur)
                (fieldp sib)
                (fieldp left)
                (fieldp right)
                (equal (pfield::mul (pfield::sub cur sib p)
                                    (pfield::sub 1 bit p)
                                    p)
                       (pfield::sub left sib p))
                (equal (pfield::mul (pfield::sub sib cur p)
                                    (pfield::sub 1 bit p)
                                    p)
                       (pfield::sub right cur p)))
           (and (equal left (if (equal bit 0) cur sib))
                (equal right (if (equal bit 0) sib cur))))
  :hints (("Goal"
           :cases ((equal bit 0))
           :in-theory (e/d (fieldp bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-sub
                            (x cur) (y sib) (p p))
                 (:instance pfield::equal-of-0-and-sub
                            (x sib) (y cur) (p p))
                 (:instance pfield::equal-of-0-and-sub
                            (x left) (y sib) (p p))
                 (:instance pfield::equal-of-0-and-sub
                            (x right) (y cur) (p p))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub cur sib p)) (p p))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub sib cur p)) (p p))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub cur sib p)) (p p))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub sib cur p)) (p p))))))
