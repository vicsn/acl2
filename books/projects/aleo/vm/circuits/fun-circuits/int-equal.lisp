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

(local
 (defthm int-values-equal-when-same-bits
   (implies (and (posp n)
                 (int-valuep x signedp n)
                 (int-valuep y signedp n)
                 (equal (int->lebits x n)
                        (int->lebits y n)))
            (equal x y))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable int-valuep
                               acl2::ifix-when-integerp
                               lebits->int-of-int->lebits)
            :use ((:instance lebits->int-of-int->lebits
                             (x x) (n n) (signedp signedp))
                  (:instance lebits->int-of-int->lebits
                             (x y) (n n) (signedp signedp)))))))

(defruledl int-is-not-equal-spec-from-bit-nats
  (implies (and (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int-is-not-equal-spec x y signedp n)
                  (if (equal (int->lebits x n)
                             (int->lebits y n))
                      0
                    1)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal (int->lebits x n)
                          (int->lebits y n)))
           :in-theory (enable int-is-not-equal-spec
                              int-spec-bool
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::ifix-when-integerp
                              int-valuep))
          ("Subgoal 1"
           :use (:instance int-values-equal-when-same-bits))))

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
  :do-not-induct t
  :enable (int-is-not-equal-gadget
           int-is-not-equal-spec-from-bit-nats
           bit-listp-of-int->lebits-explicit
           acl2::bit-list-fix-when-bit-listp
           acl2::lebits=>nat-injectivity
           int-width-lt-prime-bits
           integer-length-of-base-prime
           integer-widthp
           len-of-int->lebits)
  :use unsigned-small-neq-gadget-soundness)

(local (in-theory (disable acl2::lebits=>nat-injectivity
                           int-is-not-equal-spec-from-bit-nats
                           int-is-not-equal-gadget
                           int-is-equal-gadget
                           bit-listp-of-int->lebits-explicit
                           acl2::bit-list-fix-when-bit-listp
                           len-of-int->lebits
                           int-width-lt-prime-bits
                           integer-length-of-base-prime
                           integer-widthp)))

(defruledl int-one-minus-not-equal-bit
  (implies (and (equal p (base-prime))
                (bitp b))
           (equal (pfield::sub 1 b p)
                  (if (equal b 0) 1 0)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (e/d (bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1)))))

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
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-not-equal-gadget-sound)
           :in-theory (e/d (int-is-equal-gadget-is-not-equal
                            int-one-minus-not-equal-bit
                            int-is-not-equal-spec-is-not-equal
                            int-is-equal-spec
                            int-spec-bool
                            bitp)
                           (int-is-not-equal-gadget-sound
                            int-is-not-equal-gadget
                            int-is-equal-gadget
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1)))))

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
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-equal-gadget-sound (y 0))
           :in-theory (e/d (int-is-zero-gadget
                            int-is-zero-spec-is-equal-zero
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-is-equal-gadget-sound
                            int-is-equal-gadget
                            int-is-not-equal-gadget)))))

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
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-equal-gadget-sound (y 1))
           :in-theory (e/d (int-is-one-gadget
                            int-is-one-spec-is-equal-one
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-is-equal-gadget-sound
                            int-is-equal-gadget
                            int-is-not-equal-gadget)))))

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

(deflabel int-equal-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (current-theory 'int-equal-before-mod)))

(defruledl int-neq-weighted-sum-is-sub
  (implies (and (equal p (base-prime))
                (equal d1 (mod a p))
                (equal d2 (mod (- b) p))
                (natp a) (natp b)
                (< a p) (< b p))
           (equal (pfield::add d1 d2 p)
                  (pfield::sub a b p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (pfield::sub pfield::add pfield::neg
                            acl2::mod-of-+-of-mod-arg1
                            acl2::mod-of-+-of-mod-arg2
                            acl2::integerp-of-mod
                            acl2::integerp-of-mod-type)
                           (pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(local (defthmd int-add-of-minus-is-add-of-neg
         (implies (and (equal p (base-prime))
                       (natp b)
                       (< b p)
                       (integerp a))
                  (equal (pfield::add a (- b) p)
                         (pfield::add a (pfield::neg b p) p)))
         :hints (("Goal"
                  :do-not-induct t
                  :in-theory (enable pfield::add
                                     pfield::neg
                                     acl2::mod-of-+-of-mod-arg1
                                     acl2::mod-of-+-of-mod-arg2
                                     acl2::integerp-of-mod
                                     acl2::integerp-of-mod-type
                                     acl2::ifix-when-integerp)))))

(local (defthmd int-mul-of-minus-is-mul-of-neg
         (implies (and (equal p (base-prime))
                       (natp b)
                       (< b p)
                       (integerp w))
                  (equal (pfield::mul (- b) w p)
                         (pfield::mul (pfield::neg b p) w p)))
         :hints (("Goal"
                  :do-not-induct t
                  :in-theory (enable pfield::mul
                                     pfield::neg
                                     acl2::mod-of-*-of-mod
                                     acl2::mod-of-*-of-mod-2
                                     acl2::integerp-of-mod
                                     acl2::integerp-of-mod-type
                                     acl2::ifix-when-integerp)))))

(defruledl int-neq-witness-product
  (implies (and (equal p (base-prime))
                (primep p)
                (natp a) (natp b)
                (< a p) (< b p)
                (not (equal a b))
                (equal w (pfield::inv (pfield::sub a b p) p)))
           (equal (pfield::add (pfield::mul a w p)
                               (pfield::mul (- b) w p)
                               p)
                  1))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub a b p))
                            (p p))
                 (:instance pfield::mul-of-add-arg1
                            (y1 a)
                            (y2 (pfield::neg b p))
                            (x w)
                            (p p)))
           :in-theory (e/d (pfield::sub
                            int-mul-of-minus-is-mul-of-neg
                            pfield::equal-of-0-and-add-of-neg-arg2
                            acl2::ifix-when-integerp)
                           (pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))))

(local
 (defthm int-equal-when-same-mod
  (implies (and (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (mod (ifix x) (expt 2 n))
                       (mod (ifix y) (expt 2 n))))
           (equal x y))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance int-values-equal-when-same-bits)
                 (:instance acl2::lebits=>nat-injectivity
                            (digits1 (int->lebits x n))
                            (digits2 (int->lebits y n))))
           :in-theory (e/d (lebits=>nat-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            acl2::bit-list-fix-when-bit-listp
                            len-of-int->lebits
                            integer-widthp
                            posp-when-integer-widthp
                            int-valuep
                            acl2::ifix-when-integerp)
                           (int-min int-max))))))

(defruledl int-integerp-when-int-valuep
  (implies (int-valuep x signedp n)
           (integerp x))
  :rule-classes :forward-chaining
  :enable int-valuep)

(local (in-theory (disable int-valuep)))

; A one-term sparse vector (1 * v) is the lookup of v.  Opening dot-product
; on a symbolic-length vector splits on every width, so these stay closed
; there and are used only at these concrete shapes.

(deflabel int-equal-before-dot-lemmas)

(defruledl int-dot-product-of-nil
  (equal (r1cs::dot-product nil asg p)
         0)
  :enable r1cs::dot-product)

(defruledl int-dot-product-of-one-var
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v))
           (equal (r1cs::dot-product (list (list 1 v)) asg p)
                  (lookup-equal v asg)))
  :do-not-induct t
  :enable (r1cs::dot-product
           primep
           acl2::mod-when-<))

(defruledl int-dot-product-of-one-minus-and-one
  (implies (and (primep p)
                (equal c (1- p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1))
           (equal (r1cs::dot-product (list (list c z)
                                           (list 1 one))
                                     asg p)
                  (pfield::sub 1 (lookup-equal z asg) p)))
  :do-not-induct t
  :enable (r1cs::dot-product
           pfield::sub
           pfield::add
           pfield::mul
           pfield::neg
           primep
           acl2::mod-when-<))

(local (in-theory (current-theory 'int-equal-before-dot-lemmas)))

(defruledl int-is-not-equal-gadget-complete-core
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
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat
                            (i 0))
                 (:instance pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
                            (xs ys)
                            (i 0))
                 (:instance int-neq-weighted-sum-is-sub
                            (d1 (r1cs::dot-product (pow2sum-vector xs 0) asg p))
                            (d2 (r1cs::dot-product
                                 (pow2sum-neg-prime-vector ys 0 p) asg p))
                            (a (lebits=>nat (lookup-equal-list xs asg)))
                            (b (lebits=>nat (lookup-equal-list ys asg))))
                 (:instance int-is-not-equal-witness
                            (x (lebits=>nat (lookup-equal-list xs asg)))
                            (y (lebits=>nat (lookup-equal-list ys asg)))
                            (z (lookup-equal z asg))
                            (w (lookup-equal w asg))
                            (p p))
                 (:instance int-neq-witness-product
                            (a (mod (ifix x) (expt 2 n)))
                            (b (mod (ifix y) (expt 2 n)))
                            (w (lookup-equal w asg))
                            (p p))
                 (:instance lebits=>nat-less-when-len-less
                            (bs (lookup-equal-list xs asg))
                            (p p))
                 (:instance lebits=>nat-less-when-len-less
                            (bs (lookup-equal-list ys asg))
                            (p p))
                 (:instance boolean-check-gadget-to-bitp
                            (x z)
                            (p p)
                            (asg asg))
                 (:instance int-equal-when-same-mod
                            (n n)
                            (x x)
                            (y y)
                            (signedp signedp)))
           :in-theory (disable r1cs::dot-product
                               boolean-check-gadget)))
  :enable (int-is-not-equal-gadget
           unsigned-small-neq-gadget
           boolean-check-gadget-to-bitp
           r1cs::r1cs-constraint-holdsp
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
           int-is-not-equal-spec
           int-spec-bool
           int-spec-unsigned
           lebits=>nat-of-int->lebits
           lebits=>nat-less-when-len-less
           bit-listp-of-int->lebits-explicit
           int-is-not-equal-witness
           int-dot-product-of-nil
           int-dot-product-of-one-var
           int-dot-product-of-one-minus-and-one
           int-integerp-when-int-valuep
           int-width-lt-prime-bits
           integer-length-of-base-prime
           integer-widthp
           len-of-int->lebits
           len-of-lookup-equal-list
           posp-when-integer-widthp
           acl2::mod-when-<
           acl2::integerp-of-mod
           acl2::integerp-of-mod-type
           acl2::nonneg-of-mod-type-2))

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
  :do-not-induct t
  :hints (("Goal" :use int-is-not-equal-gadget-complete-core))
  :enable (int-is-not-equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           int-is-not-equal-spec
           int-spec-bool))

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

(local (in-theory (disable int-is-not-equal-gadget-complete
                           int-is-equal-gadget-complete
                           r1cs::dot-product
                           int-is-not-equal-gadget
                           int-is-equal-gadget)))

(defruledl int-valuep-of-zero
  (implies (integer-widthp n)
           (int-valuep 0 signedp n))
  :do-not-induct t
  :enable (int-valuep int-min int-max
           integer-widthp posp-when-integer-widthp))

(defruledl int-valuep-of-one
  (implies (integer-widthp n)
           (int-valuep 1 signedp n))
  :do-not-induct t
  :enable (int-valuep int-min int-max
           integer-widthp posp-when-integer-widthp))

(defruledl int-spec-unsigned-of-zero
  (implies (posp n)
           (equal (int-spec-unsigned 0 n) 0))
  :do-not-induct t
  :enable (int-spec-unsigned acl2::mod-of-0-arg1))

(defruledl int-spec-unsigned-of-one
  (implies (integer-widthp n)
           (equal (int-spec-unsigned 1 n) 1))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))))
  :enable (int-spec-unsigned integer-widthp))

(local (in-theory (disable int-valuep int-min int-max
                           int-spec-unsigned)))

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
                         (pfield::inv
                          (pfield::sub (int-spec-unsigned x n)
                                       (int-spec-unsigned 0 n)
                                       p)
                          p))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-zero-gadget xs ys z w one p) asg p)
                (equal (pfield::sub 1 (lookup-equal z asg) p)
                       (int-is-zero-spec x signedp n))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-equal-gadget-complete (y 0))
           :in-theory (disable int-is-equal-gadget-complete
                               int-is-not-equal-gadget-complete
                               r1cs::dot-product)))
  :enable (int-is-zero-gadget
           int-valuep-of-zero
           int-is-zero-spec-is-equal-zero
           int-is-not-equal-spec
           int-is-equal-spec
           int-spec-bool
           posp-when-integer-widthp))

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
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-equal-gadget-complete (y 1))
           :in-theory (disable int-is-equal-gadget-complete
                               int-is-not-equal-gadget-complete
                               r1cs::dot-product)))
  :enable (int-is-one-gadget
           int-valuep-of-one
           int-spec-unsigned-of-one
           int-is-one-spec-is-equal-one
           int-is-not-equal-spec
           int-is-equal-spec
           int-spec-bool
           posp-when-integer-widthp))

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

(defruledl int-expt-width-below-prime
  (implies (and (equal p (base-prime))
                (integer-widthp n))
           (< (expt 2 n) p))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl int-spec-unsigned-fep
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n))
           (pfield::fep (int-spec-unsigned x n) p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance acl2::mod-bound-linear-arg2
                            (x (ifix x))
                            (y (expt 2 n)))
                 (:instance acl2::nonneg-of-mod-type-2
                            (x (ifix x))
                            (y (expt 2 n)))
                 (:instance int-expt-width-below-prime (p p) (n n)))
           :in-theory (e/d (pfield::fep
                            int-spec-unsigned
                            int-integerp-when-int-valuep
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            acl2::integerp-of-mod
                            acl2::nonneg-of-mod-type-2
                            acl2::mod-bound-linear-arg2)
                           (pfield::sub pfield::mul pfield::add)))))

(defruledl int-is-not-equal-pred-to-muls
  (equal (int-is-not-equal-pred xu yu w r one prime)
         (and (equal (pfield::mul (pfield::sub (mod 1 prime) r prime)
                                  r prime)
                     (mod 0 prime))
              (equal (pfield::mul (pfield::sub xu yu prime) w prime)
                     r)
              (equal (pfield::mul (pfield::sub xu yu prime)
                                  (pfield::sub one r prime)
                                  prime)
                     (mod 0 prime))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (disable pfield::mul-commutative
                               pfield::mul-commutative-2
                               pfield::mul-associative
                               (:definition pfield::sub)
                               (:definition pfield::mul))))
  :enable int-is-not-equal-pred)

(local
 (defthm int-neq-bit-when-constraints
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep xu p)
                (pfield::fep yu p)
                (pfield::fep w p)
                (pfield::fep r p)
                (equal one 1)
                (equal (pfield::mul (pfield::sub (mod 1 p) r p) r p)
                       (mod 0 p))
                (equal (pfield::mul (pfield::sub xu yu p) w p) r)
                (equal (pfield::mul (pfield::sub xu yu p)
                                    (pfield::sub one r p)
                                    p)
                       (mod 0 p)))
           (equal (if (equal xu yu) 0 1) r))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal r 0))
           :in-theory (e/d (bitp
                            acl2::mod-of-0-arg1
                            acl2::mod-when-<
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q))
                           ((:definition pfield::sub)
                            (:definition primep)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::equal-of-0-and-mul
                            pfield::equal-of-0-and-sub
                            pfield::mul-of-1-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub (mod 1 p) r p))
                            (y r)
                            (p p))
                 (:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub xu yu p))
                            (y (pfield::sub one r p))
                            (p p))
                 (:instance pfield::equal-of-0-and-sub
                            (x xu) (y yu) (p p))
                 (:instance pfield::equal-of-0-and-sub
                            (x 1) (y r) (p p))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub xu yu p))
                            (p p)))))))

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
           (equal (int-is-not-equal-spec x y signedp n) r))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-is-not-equal-pred-to-muls
                            (xu xu) (yu yu) (w w) (r r)
                            (one one) (prime prime))
                 (:instance int-neq-bit-when-constraints
                            (xu xu) (yu yu) (w w) (r r)
                            (one one) (p prime))
                 (:instance int-spec-unsigned-fep
                            (x x) (signedp signedp) (n n) (p prime))
                 (:instance int-spec-unsigned-fep
                            (x y) (signedp signedp) (n n) (p prime))
                 (:instance int-equal-when-same-mod
                            (x x) (y y) (signedp signedp) (n n)))
           :in-theory (e/d (int-is-not-equal-spec
                            int-spec-bool
                            int-spec-unsigned
                            int-integerp-when-int-valuep
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q))
                           (int-is-not-equal-pred
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

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
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-is-not-equal-pred-to-muls
                            (xu xu) (yu yu) (w w) (r r)
                            (one one) (prime prime))
                 (:instance int-is-not-equal-witness
                            (x xu) (y yu) (z r) (w w) (p prime))
                 (:instance int-spec-unsigned-fep
                            (x x) (signedp signedp) (n n) (p prime))
                 (:instance int-spec-unsigned-fep
                            (x y) (signedp signedp) (n n) (p prime))
                 (:instance int-equal-when-same-mod
                            (x x) (y y) (signedp signedp) (n n)))
           :in-theory (e/d (int-is-not-equal-spec
                            int-spec-bool
                            int-spec-unsigned
                            int-integerp-when-int-valuep
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q))
                           (int-is-not-equal-pred
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

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
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-is-not-equal-pred-sound
                            (xu (int-spec-unsigned x n))
                            (yu (int-spec-unsigned y n)))
                 (:instance int-one-minus-not-equal-bit
                            (p prime)
                            (b r)))
           :in-theory (disable int-is-not-equal-pred-sound)))
  :enable (int-is-equal-pred-to-not-equal-pred
           int-is-not-equal-spec-is-not-equal
           int-integerp-when-int-valuep
           int-spec-bool
           bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_zero and is_one are is_equal against the constant field elements 0
; and 1.  The constraints are the field not-equal; the second operand is
; that constant.

(define int-is-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Field not-equal of the integer's field image and 0."
  (pfcs::parse-def
   "int_is_zero(x, y, w, r, one) := {
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

(pfcs::lift (int-is-zero-circuit)
            :pred int-is-zero-pred
            :prime prime)

(defruled int-is-zero-pred-is-equal-pred
  (equal (int-is-zero-pred x y w r one prime)
         (int-is-equal-pred x y w r one prime))
  :enable (int-is-zero-pred int-is-equal-pred))

(defruled int-is-zero-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n)
                (bitp r)
                (pfield::fep w prime)
                (equal one 1)
                (int-is-zero-pred (int-spec-unsigned x n)
                                  0 w r one prime))
           (equal (pfield::sub 1 r prime)
                  (int-is-zero-spec x signedp n)))
  :do-not-induct t
  :enable (int-is-zero-pred-is-equal-pred
           int-is-equal-pred-sound
           int-is-zero-spec-is-equal-zero
           int-is-equal-spec
           int-spec-bool
           int-spec-unsigned
           int-valuep
           int-min
           int-max
           integer-widthp
           posp-when-integer-widthp)
  :hints (("Goal" :use (:instance int-is-equal-pred-sound (y 0)))))

(define int-is-one-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Field not-equal of the integer's field image and 1."
  (pfcs::parse-def
   "int_is_one(x, y, w, r, one) := {
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

(pfcs::lift (int-is-one-circuit)
            :pred int-is-one-pred
            :prime prime)

(defruled int-is-one-pred-is-equal-pred
  (equal (int-is-one-pred x y w r one prime)
         (int-is-equal-pred x y w r one prime))
  :enable (int-is-one-pred int-is-equal-pred))

(defruled int-is-one-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (int-valuep x signedp n)
                (bitp r)
                (pfield::fep w prime)
                (equal one 1)
                (int-is-one-pred (int-spec-unsigned x n)
                                 1 w r one prime))
           (equal (pfield::sub 1 r prime)
                  (int-is-one-spec x signedp n)))
  :do-not-induct t
  :enable (int-is-one-pred-is-equal-pred
           int-is-equal-pred-sound
           int-is-one-spec-is-equal-one
           int-is-equal-spec
           int-spec-bool
           int-spec-unsigned
           int-valuep
           int-min
           int-max
           integer-widthp
           posp-when-integer-widthp)
  :hints (("Goal" :use (:instance int-is-equal-pred-sound (y 1)))))
