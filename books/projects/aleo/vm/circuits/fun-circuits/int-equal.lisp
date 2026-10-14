; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Equal::is_equal, Equal::is_not_equal, Zero::is_zero, One::is_one.
;
; In the variable case, is_equal converts both integers to field elements
; (a linear combination of the bits; no constraint, because n <= 128 < 253)
; and calls Field::is_equal, which is boolean negation of Field::is_not_equal.
; Negation is the linear combination 1 - r.  The two constraints are
; r1cs/unsigned-small-neq (the same constraints for signed integers;
; r1cs/signed-small-neq is that gadget read with lebits=>int).
;
; is_not_equal returns r itself.  is_zero and is_one are is_equal against
; the constant 0 and the constant 1.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-neq")
(include-book "../r1cs/signed-small-neq")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-is-not-equal-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (z symbolp)
                                 (w symbolp)
                                 (one symbolp)
                                 (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Variable-case @('Integer::is_not_equal').  @('z') is the result bit."
  (unsigned-small-neq-gadget xs ys z w one p))

(define int-is-equal-gadget ((xs symbol-listp)
                             (ys symbol-listp)
                             (z symbolp)
                             (w symbolp)
                             (one symbolp)
                             (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as not-equal.  The result is the linear
          combination @($1 - z$), not a further constraint."
  (int-is-not-equal-gadget xs ys z w one p))

(defruled int-is-equal-gadget-is-not-equal
  (equal (int-is-equal-gadget xs ys z w one p)
         (int-is-not-equal-gadget xs ys z w one p))
  :enable (int-is-equal-gadget int-is-not-equal-gadget))

(define int-is-zero-gadget ((xs symbol-listp)
                            (ys symbol-listp)
                            (z symbolp)
                            (w symbolp)
                            (one symbolp)
                            (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('is_zero') is @('is_equal') against the zero bit list."
  (int-is-equal-gadget xs ys z w one p))

(define int-is-one-gadget ((xs symbol-listp)
                           (ys symbol-listp)
                           (z symbolp)
                           (w symbolp)
                           (one symbolp)
                           (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('is_one') is @('is_equal') against the bits of 1."
  (int-is-equal-gadget xs ys z w one p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-is-not-equal-gadget-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-is-not-equal-gadget xs ys z w one p) asg p))
           (equal (lookup-equal z asg)
                  (int-is-not-equal-spec x y signedp n)))
  :enable (int-is-not-equal-gadget
           int-is-not-equal-spec
           int-spec-bool
           int-width-lt-prime-bits
           bit-listp-of-int->lebits-explicit
           lebits=>nat-of-int->lebits
           lebits->int-of-int->lebits)
  :use (unsigned-small-neq-gadget-soundness))

(defruled int-is-equal-gadget-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (int-is-equal-gadget xs ys z w one p) asg p))
           (equal (pfield::sub 1 (lookup-equal z asg) p)
                  (int-is-equal-spec x y signedp n)))
  :enable (int-is-equal-gadget-is-not-equal
           int-is-not-equal-gadget-sound
           int-is-not-equal-spec-is-not-equal
           int-is-equal-spec
           int-spec-bool
           bitp))

(defruled int-is-zero-gadget-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits 0 n))
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (int-is-zero-gadget xs ys z w one p) asg p))
           (equal (pfield::sub 1 (lookup-equal z asg) p)
                  (int-is-zero-spec x signedp n)))
  :enable (int-is-zero-gadget
           int-is-equal-gadget-sound
           int-is-zero-spec-is-equal-zero))

(defruled int-is-one-gadget-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits 1 n))
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (int-is-one-gadget xs ys z w one p) asg p))
           (equal (pfield::sub 1 (lookup-equal z asg) p)
                  (int-is-one-spec x signedp n)))
  :enable (int-is-one-gadget
           int-is-equal-gadget-sound
           int-is-one-spec-is-equal-one))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness: the snarkVM witness is z = 0 and w = 0 when the integers
; agree, and z = 1 and w = (x - y)^{-1} when they differ.  The two
; constraints are the field not-equal of the weighted bit sums.

(defruled int-is-not-equal-witness
  (implies (and (equal p (base-prime))
                (natp x) (natp y)
                (< x p) (< y p)
                (equal z (if (equal x y) 0 1))
                (equal w (if (equal x y)
                             0
                           (pfield::inv (pfield::sub x y p) p))))
           (and (equal (pfield::mul (pfield::sub x y p) w p) z)
                (equal (pfield::mul (pfield::sub x y p)
                                    (pfield::sub 1 z p)
                                    p)
                       0)))
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d (fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub x y (base-prime)))
                            (p (base-prime)))
                 (:instance pfield::mul-of-0-arg1 (y w) (p (base-prime)))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub x y (base-prime)))
                            (p (base-prime)))))))

(defruled int-is-not-equal-gadget-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal z asg)
                       (int-is-not-equal-spec x y signedp n))
                (equal (lookup-equal w asg)
                       (if (equal x y)
                           0
                         (pfield::inv
                          (pfield::sub (int-spec-unsigned x n)
                                       (int-spec-unsigned y n)
                                       p)
                          p))))
           (r1cs::r1cs-constraints-holdp
            (int-is-not-equal-gadget xs ys z w one p) asg p))
  :enable (int-is-not-equal-gadget
           unsigned-small-neq-gadget
           boolean-check-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
           int-is-not-equal-spec
           int-spec-bool
           int-spec-unsigned
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           int-is-not-equal-witness))

(defruled int-is-equal-gadget-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal z asg)
                       (int-is-not-equal-spec x y signedp n))
                (equal (lookup-equal w asg)
                       (if (equal x y)
                           0
                         (pfield::inv
                          (pfield::sub (int-spec-unsigned x n)
                                       (int-spec-unsigned y n)
                                       p)
                          p))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-equal-gadget xs ys z w one p) asg p)
                (equal (pfield::sub 1 (lookup-equal z asg) p)
                       (int-is-equal-spec x y signedp n))))
  :enable (int-is-equal-gadget-is-not-equal
           int-is-not-equal-gadget-complete
           int-is-not-equal-spec-is-not-equal
           int-is-equal-spec
           int-is-not-equal-spec
           int-spec-bool))

(defruled int-is-zero-gadget-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits 0 n))
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal z asg)
                       (if (equal x 0) 0 1))
                (equal (lookup-equal w asg)
                       (if (equal x 0)
                           0
                         (pfield::inv (int-spec-unsigned x n) p))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-zero-gadget xs ys z w one p) asg p)
                (equal (pfield::sub 1 (lookup-equal z asg) p)
                       (int-is-zero-spec x signedp n))))
  :enable (int-is-zero-gadget
           int-is-equal-gadget-complete
           int-is-zero-spec-is-equal-zero
           int-is-not-equal-spec
           int-spec-bool
           int-spec-unsigned))

(defruled int-is-one-gadget-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits 1 n))
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal z asg)
                       (if (equal x 1) 0 1))
                (equal (lookup-equal w asg)
                       (if (equal x 1)
                           0
                         (pfield::inv (pfield::sub (int-spec-unsigned x n)
                                                   1 p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-one-gadget xs ys z w one p) asg p)
                (equal (pfield::sub 1 (lookup-equal z asg) p)
                       (int-is-one-spec x signedp n))))
  :enable (int-is-one-gadget
           int-is-equal-gadget-complete
           int-is-one-spec-is-equal-one
           int-is-not-equal-spec
           int-spec-bool
           int-spec-unsigned))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 1 != 0, so z = 1 and w = 1 (the inverse of 1 - 0).

(defconst *int-is-not-equal-sample*
  '((x0 . 1) (x1 . 0)
    (y0 . 0) (y1 . 0)
    (z . 1) (w . 1) (one . 1)))

(defruled int-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-not-equal-gadget '(x0 x1) '(y0 y1) 'z 'w 'one (base-prime))
   *int-is-not-equal-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-is-not-equal-gadget
                                     unsigned-small-neq-gadget
                                     boolean-check-gadget
                                     pow2sum-vector
                                     pow2sum-neg-prime-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-equal-gadget '(x0 x1) '(y0 y1) 'z 'w 'one (base-prime))
   *int-is-not-equal-sample*
   (base-prime))
  :enable (int-is-equal-gadget-is-not-equal
           int-is-not-equal-sample-holds))

(defruled int-is-zero-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-zero-gadget '(x0 x1) '(y0 y1) 'z 'w 'one (base-prime))
   *int-is-not-equal-sample*
   (base-prime))
  :enable (int-is-zero-gadget int-is-equal-sample-holds))

(defconst *int-is-one-sample*
  '((x0 . 1) (x1 . 0)
    (y0 . 1) (y1 . 0)
    (z . 0) (w . 0) (one . 1)))

(defruled int-is-one-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-one-gadget '(x0 x1) '(y0 y1) 'z 'w 'one (base-prime))
   *int-is-one-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-is-one-gadget
                                     int-is-equal-gadget
                                     int-is-not-equal-gadget
                                     unsigned-small-neq-gadget
                                     boolean-check-gadget
                                     pow2sum-vector
                                     pow2sum-neg-prime-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Field not-equal of the two integer field images."
  (pfcs::parse-def
   "int_is_not_equal(x, y, w, r, one) := {
    (1 - r) * (r) == (0),
    (x - y) * (w) == (r),
    (x - y) * (one - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-not-equal-circuit)
            :pred int-is-not-equal-pred
            :prime prime)

(defruled int-is-not-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (pfield::fep w prime)
                (pfield::fep r prime)
                (equal one 1)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (int-is-not-equal-pred xu yu w r one prime))
           (equal r (int-is-not-equal-spec x y signedp n)))
  :enable (int-is-not-equal-pred
           int-is-not-equal-spec
           int-spec-bool
           int-spec-unsigned
           int-is-not-equal-witness))

(defruled int-is-not-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal one 1)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal r (int-is-not-equal-spec x y signedp n))
                (equal w (if (equal x y)
                             0
                           (pfield::inv (pfield::sub xu yu prime) prime))))
           (int-is-not-equal-pred xu yu w r one prime))
  :enable (int-is-not-equal-pred
           int-is-not-equal-spec
           int-spec-bool
           int-is-not-equal-witness
           int-spec-unsigned))

(define int-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Same constraints as not-equal.  The equal bit is @($1 - r$)."
  (pfcs::parse-def
   "int_is_equal(x, y, w, r, one) := {
    (1 - r) * (r) == (0),
    (x - y) * (w) == (r),
    (x - y) * (one - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-equal-circuit)
            :pred int-is-equal-pred
            :prime prime)

(defruled int-is-equal-pred-to-not-equal-pred
  (equal (int-is-equal-pred x y w r one prime)
         (int-is-not-equal-pred x y w r one prime))
  :enable (int-is-equal-pred int-is-not-equal-pred))

(defruled int-is-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (bitp r)
                (pfield::fep w prime)
                (equal one 1)
                (int-is-equal-pred (int-spec-unsigned x n)
                                   (int-spec-unsigned y n)
                                   w r one prime))
           (equal (pfield::sub 1 r prime)
                  (int-is-equal-spec x y signedp n)))
  :enable (int-is-equal-pred-to-not-equal-pred
           int-is-not-equal-pred-sound
           int-is-not-equal-spec-is-not-equal
           int-spec-unsigned))
