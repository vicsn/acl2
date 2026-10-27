; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Square-root soundness, completeness, and a sample.
;
; A square has two roots, r and -r.  At most one of them is <= (p-1)/2,
; and exactly one of them is even, because p is odd.  The existing
; field-square-root gadget enforces the square and the lesser-root bound.
; even_square_root enforces the square, the canonical bits, and a zero
; least significant bit.
;
; square_roots_flagged_nondeterministic is not proved equal to the ordered
; funspec.  The separate theorem below is only the unordered relation:
; the second output is the negation of the first, the first squares to x
; when the flag is 0, and both outputs are 0 when the flag is 1.

(in-package "ALEOVM")

(include-book "fb-field-sqrt")
(include-book "fb2-boolean-lte")
(include-book "../r1cs/field-square-root")
(include-book "../r1cs/field-pow-const")
(include-book "../r1cs/boolean-and")
(include-book "../library-extensions/digits")
(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-diff-of-squares
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b))
           (equal (pfield::sub (pfield::mul a a p)
                               (pfield::mul b b p)
                               p)
                  (pfield::mul (pfield::sub a b p)
                               (pfield::add a b p)
                               p)))
  :enable fieldp)

(defthm fb2-add-zero-implies-neg
  (implies (and (primep p)
                (pfield::fep a p)
                (pfield::fep b p)
                (equal (pfield::add a b p) 0))
           (equal (pfield::neg b p) a))
  :rule-classes nil)

(defthm fb2-sub-zero-implies-equal
  (implies (and (primep p)
                (pfield::fep a p)
                (pfield::fep b p)
                (equal (pfield::sub a b p) 0))
           (equal b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pfield::sub pfield::add pfield::neg
                                     acl2::mod-sum-cases))))

(defruled fb2-equal-squares-implies-equal-or-neg
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (or (equal a b)
               (equal a (pfield::neg b p))))
  :do-not-induct t
  :enable fieldp
  :use ((:instance fb2-diff-of-squares)
        (:instance pfield::equal-of-0-and-mul
                   (x (pfield::sub a b (base-prime)))
                   (y (pfield::add a b (base-prime)))
                   (p (base-prime)))
        (:instance fb2-add-zero-implies-neg (p (base-prime)))
        (:instance fb2-sub-zero-implies-equal (p (base-prime)))))

(defrule fb2-lesser-square-root-unique
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (<= a (field-modulus-minus-one-div-two))
                (<= b (field-modulus-minus-one-div-two))
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (equal b a))
  :rule-classes nil
  :enable (field-modulus-minus-one-div-two
           fieldp
           pfield::neg)
  :use fb2-equal-squares-implies-equal-or-neg)

(defthm fb2-neg-at-most-half
  (implies (and (pfield::fep r (base-prime))
                (< (field-modulus-minus-one-div-two) r))
           (<= (pfield::neg r (base-prime))
               (field-modulus-minus-one-div-two)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pfield::neg
                                     field-modulus-minus-one-div-two))))

(defruled fb2-field-lesser-square-root-props
  (implies (and (fieldp x)
                (ecurve::pfield-squarep x (base-prime)))
           (and (<= (field-lesser-square-root x)
                    (field-modulus-minus-one-div-two))
                (equal (pfield::mul (field-lesser-square-root x)
                                    (field-lesser-square-root x)
                                    (base-prime))
                       x)))
  :enable (field-lesser-square-root
           ecurve::pfield-squarep
           fieldp
           pfield::fep-fix-when-fep)
  :use (:instance fb2-neg-at-most-half
                  (r (ecurve::pfield-square->root x (base-prime)))))

(defruled fb2-field-square-root-gadget-sound
  (implies (and (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (field-square-root-gadget x y ys rs p) asg p))
           (equal (lookup-equal y asg)
                  (field-square-root-funspec (lookup-equal x asg))))
  :do-not-induct t
  :enable (field-square-root-funspec
           fieldp)
  :use (fb-field-square-root-gadget-bound
        (:instance ecurve::pfield-squarep-suff
                   (r (lookup-equal y asg))
                   (x (lookup-equal x asg))
                   (p (base-prime)))
        (:instance fb2-field-lesser-square-root-props
                   (x (lookup-equal x asg)))
        (:instance fb2-lesser-square-root-unique
                   (a (field-lesser-square-root (lookup-equal x asg)))
                   (b (lookup-equal y asg)))))

(defthm fb2-integerp-half-of-plus
  (implies (and (integerp (* 1/2 a))
                (integerp (* 1/2 b)))
           (integerp (* 1/2 (+ a b))))
  :rule-classes nil)

(defthm fb2-not-evenp-of-neg
  (implies (and (pfield::fep b (base-prime))
                (not (equal b 0))
                (evenp b))
           (not (evenp (pfield::neg b (base-prime)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pfield::neg evenp)
           :use (:instance fb2-integerp-half-of-plus
                           (a (- (base-prime) b))
                           (b b)))))

(defrule fb2-even-root-unique
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (evenp a)
                (evenp b)
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (equal b a))
  :rule-classes nil
  :enable fieldp
  :disable (evenp pfield::equal-of-neg)
  :use (fb2-equal-squares-implies-equal-or-neg
        fb2-not-evenp-of-neg))

(defruled fb2-even-root-lsb-constraint
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (r1cs::r1cs-constraint-holdsp
                 (r1cs::make-r1cs-constraint
                  :a (list (list 1 1)
                           (list (1- p) b))
                  :b (list (list 1 1))
                  :c (list (list 1 1)))
                 asg p))
           (equal (lookup-equal b asg) 0))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled fb2-evenp-of-lebits=>nat
  (implies (and (bit-listp bs)
                (consp bs)
                (equal (car bs) 0))
           (evenp (lebits=>nat bs)))
  :enable (lebits=>nat evenp)
  :expand ((acl2::lendian=>nat 2 bs))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled fb2-field-even-square-root-gadget-sound
  (implies (and (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (consp ys)
                (equal (len ys) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-even-square-root-gadget x y ys rs u p) asg p))
           (equal (lookup-equal y asg)
                  (field-even-square-root-funspec (lookup-equal x asg))))
  :do-not-induct t
  :enable (fb-field-even-square-root-gadget
           field-even-square-root-funspec
           fieldp
           pfield::fep-fix-when-fep
           car-of-lookup-equal-list)
  :disable (evenp
            ecurve::pfield-even-squarep)
  :use ((:instance field-square-gadget-correctness
                   (x y) (r x))
        (:instance field-to-bits-soundness
                   (x y) (xs ys))
        (:instance fb2-even-root-lsb-constraint
                   (b (car ys)))
        (:instance fb2-evenp-of-lebits=>nat
                   (bs (lookup-equal-list ys asg)))
        (:instance ecurve::pfield-even-squarep-suff
                   (r (lookup-equal y asg))
                   (x (lookup-equal x asg))
                   (p (base-prime)))
        (:instance ecurve::pfield-even-squarep
                   (x (lookup-equal x asg))
                   (p (base-prime)))
        (:instance fb2-even-root-unique
                   (a (ecurve::pfield-square->even-root (lookup-equal x asg)
                                                        (base-prime)))
                   (b (lookup-equal y asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime 5, 1^2 = 1, and 1 <= (5-1)/2.  Bits (1 0 0).  The bound 2 is
; bits (0 1); the high bit is zero and the fold bit r is 0.

(defconst *fb2-field-square-root-asg*
  '((x . 1) (y . 1) (b0 . 1) (b1 . 0) (b2 . 0) (r . 0)))

(defconst *fb2-field-square-root-prime* 5)

(defrule fb2-field-square-root-sample
  (r1cs::r1cs-constraints-holdp
   (field-square-root-gadget 'x 'y '(b0 b1 b2) '(r)
                             *fb2-field-square-root-prime*)
   *fb2-field-square-root-asg*
   *fb2-field-square-root-prime*)
  :enable (field-square-root-gadget
           field-square-root-rlen
           field-square-root-bound
           field-square-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           bits-lte-const-check-gadget
           bits-lte-const-check-rlen
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-gadget
           zero-gadget-list
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-flagged-roots-unordered
  :short "Unordered reading of @('square_roots_flagged_nondeterministic').
          Not the ordered funspec: either root may be returned first."
  (implies (and (symbolp x)
                (posp e)
                (not (equal e 1))
                (equal e (field-modulus-minus-one-div-two))
                (symbol-listp ss)
                (symbol-listp pow-rs)
                (equal (len ss) (field-pow-const-slen e))
                (equal (len pow-rs) (field-pow-const-rlen e))
                (consp pow-rs)
                (symbolp one-m)
                (symbolp one-r)
                (symbolp square)
                (symbolp root)
                (symbolp zero-m)
                (symbolp zero-r)
                (symbolp err)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg pow-rs)
                (r1cs::valuation-bindsp asg one-m)
                (r1cs::valuation-bindsp asg one-r)
                (r1cs::valuation-bindsp asg square)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg zero-m)
                (r1cs::valuation-bindsp asg zero-r)
                (r1cs::valuation-bindsp asg err)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal root asg))
                (bitp (lookup-equal one-r asg))
                (bitp (lookup-equal zero-r asg))
                (bitp (lookup-equal err asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-square-roots-flagged-gadget
                  x e ss pow-rs one-m one-r square root
                  zero-m zero-r err p)
                 asg p))
           (b* ((x$ (lookup-equal x asg))
                (root$ (lookup-equal root asg))
                (flag$ (lookup-equal err asg))
                (second$ (pfield::neg root$ p)))
             (and (bitp flag$)
                  (if (equal flag$ 1)
                      (and (equal root$ 0)
                           (equal second$ 0))
                    (equal (pfield::mul root$ root$ p) x$)))))
  :do-not-induct t
  :cases ((equal (lookup-equal err asg) 1))
  :enable (fb-field-square-roots-flagged-gadget
           field-is-one-funspec
           field-is-zero-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           boolean-and-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           fieldp
           bitp)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use ((:instance field-pow-const-soundness
                   (x x) (c e) (ss ss) (rs pow-rs) (p p))
        (:instance field-is-one-gadget-sound
                   (x (car pow-rs)) (m one-m) (r one-r) (p p))
        (:instance field-is-zero-gadget-sound
                   (x x) (m zero-m) (r zero-r) (p p))
        (:instance field-square-gadget-correctness
                   (x root) (r square) (p p))
        (:instance boolean-and-gadget-to-bitand
                   (x zero-r) (y one-r) (z err) (p p))
        (:instance pfield::equal-of-0-and-mul
                   (x (lookup-equal root asg))
                   (y (lookup-equal root asg))
                   (p p))))
