; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mul_and_check for every integer width and both signednesses, and
; unsigned mul_checked (Mul, MulAssign) for every width.
;
; snarkVM (mul_checked.rs, Integer::mul_and_check):
;   2n < 252 (8 to 64 bits): witness the product bits zs (Boolean::new on
;     each) and enforce X * Y = Z on the bit sums.  int-mul-and-check-gadget.
;   n = 128: karatsuba_multiply with ws = zs ++ carry, then
;     assert_bits_are_zero(carry): (sum of carry bits) * 1 = 0, and
;     assert_eq(z2, 0): z2 * 1 = 0.
; Both read only bit patterns, so they are the same circuit for both
; signednesses; the funspec int-mul-and-check-spec also reads bit patterns.
; For unsigned types mul_checked is mul_and_check.  For signed types
; mul_checked wraps mul_and_check with abs_wrapped, sign checks, and a
; ternary, which is not formalized here.

(in-package "ALEOVM")

(include-book "int-mulpow-karatsuba")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-mulpow-ones-vector ((xs symbol-listp))
  :verify-guards nil
  (if (endp xs)
      nil
    (cons (list 1 (car xs))
          (int-mulpow-ones-vector (cdr xs)))))

(define int-mul-and-check-large-gadget ((xs symbol-listp)
                                        (ys symbol-listp)
                                        (z0 symbolp)
                                        (z2 symbolp)
                                        (m symbolp)
                                        (zs symbol-listp)
                                        (carry symbol-listp)
                                        (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len carry) (1+ (floor (len xs) 2)))
              (< (+ (len xs) (len carry)) (integer-length p)))
  :verify-guards nil
  :short "mul_and_check for 128-bit types: Karatsuba, carry bits zero, and
          @($z_2 = 0$)."
  (append (int-karatsuba-multiply-gadget xs ys z0 z2 m (append zs carry) p)
          (list (r1cs::make-r1cs-constraint
                 :a (int-mulpow-ones-vector carry)
                 :b (list (list 1 1))
                 :c nil)
                (r1cs::make-r1cs-constraint
                 :a (list (list 1 z2))
                 :b (list (list 1 1))
                 :c nil))))

(define int-mul-and-check-any-gadget ((xs symbol-listp)
                                      (ys symbol-listp)
                                      (z0 symbolp)
                                      (z2 symbolp)
                                      (m symbolp)
                                      (zs symbol-listp)
                                      (carry symbol-listp)
                                      (p primep))
  :verify-guards nil
  :short "mul_and_check for any width: the field product for @($2n < 252$),
          Karatsuba otherwise.  z0, z2, m, carry are unused in the first case."
  (if (< (* 2 (len xs)) 252)
      (int-mul-and-check-gadget xs ys zs p)
    (int-mul-and-check-large-gadget xs ys z0 z2 m zs carry p)))

(define int-mul-checked-unsigned-any-gadget ((xs symbol-listp)
                                             (ys symbol-listp)
                                             (z0 symbolp)
                                             (z2 symbolp)
                                             (m symbolp)
                                             (zs symbol-listp)
                                             (carry symbol-listp)
                                             (p primep))
  :verify-guards nil
  :short "Unsigned mul_checked (also Mul and MulAssign) is mul_and_check."
  (int-mul-and-check-any-gadget xs ys z0 z2 m zs carry p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-mulpow-sum ((xs acl2-number-listp))
  :returns (s acl2-numberp)
  (if (endp xs) 0 (+ (car xs) (int-mulpow-sum (cdr xs)))))

(defruled int-mulpow-dot-product-of-ones-vector
  (implies (and (primep p)
                (symbol-listp cs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg cs))
           (equal (r1cs::dot-product (int-mulpow-ones-vector cs) asg p)
                  (mod (int-mulpow-sum (lookup-equal-list cs asg)) p)))
  :induct (len cs)
  :hints (("Subgoal *1/2" :in-theory (enable r1cs::dot-product lookup-equal-list
                                              int-mulpow-ones-vector int-mulpow-sum))
          ("Subgoal *1/1"
           :expand ((int-mulpow-ones-vector cs)
                    (:free (v) (r1cs::dot-product (cons v (int-mulpow-ones-vector (cdr cs))) asg p))
                    (int-mulpow-sum (lookup-equal-list cs asg))
                    (lookup-equal-list cs asg))
           :use ((:instance acl2::mod-of-+-of-mod-arg2
                            (acl2::x1 (lookup-equal (car cs) asg))
                            (acl2::x2 (int-mulpow-sum (lookup-equal-list (cdr cs) asg)))
                            (acl2::y p)))))
  :enable (r1cs::valuation-binds-allp int-mulpow-sum
           pfield::add pfield::mul)
  :disable (r1cs::dot-product))

(defruled int-mulpow-sum-of-bits-bound
  (implies (bit-listp bs)
           (and (<= 0 (int-mulpow-sum bs))
                (<= (int-mulpow-sum bs) (len bs))))
  :rule-classes :linear
  :induct (len bs)
  :enable (int-mulpow-sum bit-listp))

(defruled int-mulpow-sum-of-bits-zero
  (implies (bit-listp bs)
           (equal (equal (int-mulpow-sum bs) 0)
                  (equal (lebits=>nat bs) 0)))
  :induct (len bs)
  :enable (int-mulpow-sum bit-listp acl2::lebits=>nat-of-cons
           int-mulpow-sum-of-bits-bound))

(defruled int-mulpow-natp-sum-of-bits
  (implies (bit-listp bs)
           (natp (int-mulpow-sum bs)))
  :induct (len bs)
  :enable (int-mulpow-sum bit-listp))

(defruled int-mulpow-carry-constraint
  (implies (and (primep p)
                (symbol-listp carry)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg carry)
                (bit-listp (lookup-equal-list carry asg))
                (< (len carry) p))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (int-mulpow-ones-vector carry)
                    :b (list (list 1 1))
                    :c nil)
                   asg p)
                  (equal (lebits=>nat (lookup-equal-list carry asg)) 0)))
  :do-not-induct t
  :use ((:instance int-mulpow-sum-of-bits-bound
                   (bs (lookup-equal-list carry asg)))
        (:instance int-mulpow-sum-of-bits-zero
                   (bs (lookup-equal-list carry asg)))
        (:instance int-mulpow-natp-sum-of-bits
                   (bs (lookup-equal-list carry asg))))
  :enable (r1cs::r1cs-constraint-holdsp
           int-mulpow-dot-product-of-ones-vector
           int-mulpow-dot-product-of-one
           acl2::mod-when-<)
  :disable r1cs::dot-product
  :expand ((r1cs::dot-product nil asg p)))

(defruled int-mulpow-zero-constraint
  (implies (and (primep p)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list 1 z))
                    :b (list (list 1 1))
                    :c nil)
                   asg p)
                  (equal (lookup-equal z asg) 0)))
  :do-not-induct t
  :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product))

(defruled int-mul-and-check-spec-when-128
  (implies (equal n 128)
           (equal (int-mul-and-check-spec x y signedp n)
                  (b* ((kspec (int-karatsuba-multiply-spec x y signedp n)))
                    (if (and (equal (lebits=>nat (second kspec)) 0)
                             (equal (third kspec) 0))
                        (first kspec)
                      (spec-error)))))
  :enable (int-mul-and-check-spec int-spec-field-data-bits
           base-field-size-in-bits))

(defruled int-mul-and-check-spec-when-small
  (implies (and (integer-widthp n) (not (equal n 128)))
           (equal (int-mul-and-check-spec x y signedp n)
                  (if (< (* (int-spec-unsigned x n) (int-spec-unsigned y n))
                         (expt 2 n))
                      (int-wrap (* (int-spec-unsigned x n)
                                   (int-spec-unsigned y n))
                                signedp n)
                    (spec-error))))
  :enable (int-mul-and-check-spec int-spec-field-data-bits
           base-field-size-in-bits integer-widthp))

(defruled int-mulpow-nthcdr-of-append
  (implies (equal (len a) n)
           (equal (nthcdr n (append a b)) b))
  :induct (nthcdr n a)
  :enable nthcdr)

(defruled int-mulpow-take-of-append
  (implies (and (equal (len a) n) (true-listp a))
           (equal (take n (append a b)) a))
  :induct (nthcdr n a)
  :enable (take nthcdr))

(defruled int-mul-and-check-large-gadget-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (equal n 128)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-large-gadget xs ys z0 z2 m zs carry p)
                 asg p))
           (and (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n)
                                    n))))
  :do-not-induct t
  :use ((:instance int-karatsuba-multiply-gadget-sound
                   (ws (append zs carry)))
        (:instance int-mulpow-carry-constraint)
        (:instance int-mulpow-zero-constraint (z z2)))
  :in-theory (e/d (int-mul-and-check-large-gadget
                   int-mul-and-check-spec-when-128
                   int-karatsuba-multiply-spec-components
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   int-mulpow-nthcdr-of-append
                   int-mulpow-take-of-append
                   bit-listp-of-int->lebits-explicit
                   not-spec-error-when-integerp
                   (:e base-prime) (:e integer-widthp))
                  (int-karatsuba-multiply-gadget
                   r1cs::r1cs-constraint-holdsp)))

(defruled int-mulpow-small-width-facts
  (implies (and (integer-widthp n) (not (equal n 128)))
           (and (< (* (expt 2 n) (expt 2 n)) (base-prime))
                (< (expt 2 n) (base-prime))
                (< (* 2 n) 252)
                (posp n)))
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
  :enable (integer-widthp (:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruled int-mulpow-lebits=>nat-of-int->lebits-is-unsigned
  (implies (natp n)
           (equal (lebits=>nat (int->lebits x n))
                  (int-spec-unsigned x n)))
  :enable (lebits=>nat-of-int->lebits int-spec-unsigned))

(defruled int-mulpow-unsigned-bound
  (implies (natp n)
           (< (int-spec-unsigned x n) (expt 2 n)))
  :rule-classes :linear
  :enable int-spec-unsigned)

(defruled int-mul-and-check-small-gadget-facts
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-gadget xs ys zs p) asg p))
           (and (bit-listp (lookup-equal-list zs asg))
                (equal (lebits=>nat (lookup-equal-list zs asg))
                       (* (int-spec-unsigned x n) (int-spec-unsigned y n)))))
  :do-not-induct t
  :use ((:instance int-mul-and-check-gadget-to-product)
        (:instance int-mulpow-small-width-facts)
        (:instance int-mulpow-unsigned-bound)
        (:instance int-mulpow-unsigned-bound (x y))
        (:instance int-mulpow-times-mono
                   (x (int-spec-unsigned x n)) (y (int-spec-unsigned y n))
                   (a (expt 2 n)) (b (expt 2 n)))
        (:instance acl2::lebits=>nat-upper-bound
                   (acl2::digits (lookup-equal-list zs asg))))
  :in-theory (e/d (int-mulpow-lebits=>nat-of-int->lebits-is-unsigned
                   bit-listp-of-int->lebits-explicit
                   acl2::mod-when-<)
                  (integer-widthp int-mul-and-check-gadget int->lebits
                   int-spec-unsigned int-mul-and-check-spec)))

(defruled int-mul-and-check-small-gadget-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-gadget xs ys zs p) asg p))
           (and (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n)
                                    n))))
  :do-not-induct t
  :use ((:instance int-mul-and-check-small-gadget-facts)
        (:instance int-mulpow-small-width-facts)
        (:instance acl2::lebits=>nat-upper-bound
                   (acl2::digits (lookup-equal-list zs asg)))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (lookup-equal-list zs asg)) (k n)
                   (v (* (int-spec-unsigned x n) (int-spec-unsigned y n)))))
  :in-theory (e/d (int-mul-and-check-spec-when-small
                   int->lebits-of-int-wrap
                   not-spec-error-when-integerp)
                  (integer-widthp int-mul-and-check-gadget int->lebits
                   int-spec-unsigned)))

(defruled int-mulpow-append-int->lebits
  (implies (and (natp s) (natp n) (natp k)
                (< s (expt 2 (+ n k))))
           (equal (append (int->lebits s n)
                          (int->lebits (floor s (expt 2 n)) k))
                  (int->lebits s (+ n k))))
  :do-not-induct t
  :use ((:instance int-mulpow-bit-list-is-int->lebits
                   (b (append (int->lebits s n)
                              (int->lebits (floor s (expt 2 n)) k)))
                   (k (+ n k))
                   (v s))
        (:instance int-mulpow-mod-plus-floor (k (expt 2 n)))
        (:instance acl2::<-of-floor-arg1 (acl2::i s) (acl2::j (expt 2 n))
                   (acl2::k (expt 2 k))))
  :enable (acl2::lebits=>nat-of-append
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::expt-of-+
           acl2::mod-when-<))

(defruled int-mul-and-check-large-gadget-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (equal n 128)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal z0 asg)
                       (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                (equal (lookup-equal z2 asg)
                       (* (int-mulpow-hi x n) (int-mulpow-hi y n)))
                (equal (lookup-equal m asg)
                       (* (+ (int-mulpow-hi x n) (int-mulpow-lo x n))
                          (+ (int-mulpow-hi y n) (int-mulpow-lo y n))))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n) n))
                (equal (lookup-equal-list carry asg)
                       (second (int-karatsuba-multiply-spec x y signedp n))))
           (r1cs::r1cs-constraints-holdp
            (int-mul-and-check-large-gadget xs ys z0 z2 m zs carry p)
            asg p))
  :do-not-induct t
  :use ((:instance int-karatsuba-multiply-gadget-complete
                   (ws (append zs carry)))
        (:instance int-mulpow-carry-constraint)
        (:instance int-mulpow-zero-constraint (z z2))
        (:instance int-mul-wrapped-sum-bound)
        (:instance int-mulpow-append-int->lebits
                   (s (int-mul-wrapped-sum x y n)) (k (+ (floor n 2) 1))))
  :in-theory (e/d (int-mul-and-check-large-gadget
                   int-mul-and-check-spec-when-128
                   int-karatsuba-multiply-spec-components
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   int->lebits-of-int-wrap
                   bit-listp-of-int->lebits-explicit
                   (:e base-prime) (:e integer-widthp))
                  (int-karatsuba-multiply-gadget
                   int-mul-wrapped-sum
                   int->lebits
                   r1cs::r1cs-constraint-holdsp)))

(defruled int-mulpow-unsigned-when-below
  (implies (and (natp v) (natp n) (< v (expt 2 n)))
           (equal (int-spec-unsigned v n) v))
  :enable (int-spec-unsigned acl2::mod-when-<))

(defruled int-mulpow-lebits=>nat-of-lookup
  (implies (and (equal (lookup-equal-list xs asg) (int->lebits x n))
                (natp n))
           (and (equal (lebits=>nat (lookup-equal-list xs asg))
                       (int-spec-unsigned x n))
                (bit-listp (lookup-equal-list xs asg))))
  :enable (int-mulpow-lebits=>nat-of-int->lebits-is-unsigned
           bit-listp-of-int->lebits-explicit))

(defruled int-mul-and-check-small-gadget-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n)
                                    n)))
           (r1cs::r1cs-constraints-holdp
            (int-mul-and-check-gadget xs ys zs p) asg p))
  :do-not-induct t
  :use ((:instance int-mul-and-check-gadget-to-product)
        (:instance int-mulpow-small-width-facts)
        (:instance int-mulpow-lebits=>nat-of-lookup)
        (:instance int-mulpow-lebits=>nat-of-lookup (xs ys) (x y))
        (:instance int-mulpow-lebits=>nat-of-lookup
                   (xs zs)
                   (x (* (int-spec-unsigned x n) (int-spec-unsigned y n)))))
  :in-theory (e/d (int-mul-and-check-spec-when-small
                   int-mulpow-unsigned-when-below
                   int->lebits-of-int-wrap
                   int-mulpow-lebits=>nat-of-int->lebits-is-unsigned
                   bit-listp-of-int->lebits-explicit
                   acl2::mod-when-<)
                  (integer-widthp int-mul-and-check-gadget int->lebits
                   int-spec-unsigned)))

(defruledl int-mulpow-poly-split
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp c)
                (acl2-numberp d) (acl2-numberp k))
           (equal (* (+ a (* k b)) (+ c (* k d)))
                  (+ (* a c) (* k (+ (* b c) (* a d))) (* k k b d)))))

(defruledl int-mulpow-product-split-abstract
  (implies (and (natp ux) (natp uy) (natp h))
           (equal (* ux uy)
                  (+ (int-mulpow-babbage-sum (mod ux (expt 2 h)) (floor ux (expt 2 h))
                                             (mod uy (expt 2 h)) (floor uy (expt 2 h)) h)
                     (* (expt 2 h) (expt 2 h)
                        (floor ux (expt 2 h)) (floor uy (expt 2 h))))))
  :do-not-induct t
  :use ((:instance int-mulpow-mod-plus-floor (s ux) (k (expt 2 h)))
        (:instance int-mulpow-mod-plus-floor (s uy) (k (expt 2 h)))
        (:instance int-mulpow-poly-split
                   (a (mod ux (expt 2 h))) (b (floor ux (expt 2 h)))
                   (c (mod uy (expt 2 h))) (d (floor uy (expt 2 h)))
                   (k (expt 2 h))))
  :enable int-mulpow-babbage-sum
  :disable (acl2::+-of-mod-and-*-of-floor-same distributivity))

(defruled int-mulpow-product-split
  (implies (integer-widthp n)
           (equal (* (int-spec-unsigned x n) (int-spec-unsigned y n))
                  (+ (int-mul-wrapped-sum x y n)
                     (* (expt 2 n) (int-mulpow-hi x n) (int-mulpow-hi y n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-product-split-abstract
                   (ux (int-spec-unsigned x n)) (uy (int-spec-unsigned y n))
                   (h (floor n 2)))
        (:instance int-mulpow-karatsuba-width-facts)
        (:instance acl2::expt-of-+ (acl2::r 2)
                   (acl2::i1 (floor n 2)) (acl2::i2 (floor n 2))))
  :enable (int-mul-wrapped-sum int-mulpow-lo int-mulpow-hi int-spec-unsigned)
  :disable (acl2::expt-of-+ int-mulpow-babbage-sum integer-widthp))

(defruledl int-mulpow-product-pos
  (implies (and (natp a) (natp b) (not (equal a 0)) (not (equal b 0)))
           (<= 1 (* a b)))
  :hints (("Goal" :nonlinearp t)))

(defruledl int-mulpow-overflow-lemma
  (implies (and (natp s) (natp hx) (natp hy) (posp c)
                (not (equal hx 0)) (not (equal hy 0)))
           (<= c (+ s (* c hx hy))))
  :do-not-induct t
  :use ((:instance int-mulpow-product-pos (a hx) (b hy))
        (:instance int-mulpow-times-mono (x 1) (y c) (a (* hx hy)) (b c))))

(defruled int-mul-and-check-spec-is-mul-checked-when-unsigned
  (implies (and (integer-widthp n)
                (int-valuep x nil n)
                (int-valuep y nil n))
           (equal (int-mul-and-check-spec x y nil n)
                  (int-mul-checked-spec x y nil n)))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 2"
           :in-theory (e/d (int-mul-and-check-spec-when-small
                            int-mul-checked-spec int-wrap int-valuep
                            int-min int-max int-spec-unsigned
                            acl2::mod-when-< posp-when-integer-widthp)
                           (integer-widthp)))
          ("Subgoal 1"
           :use ((:instance int-mulpow-product-split)
                 (:instance int-mul-wrapped-sum-bound)
                 (:instance int-mulpow-karatsuba-width-facts)
                 (:instance int-mulpow-floor-bound
                            (s (int-mul-wrapped-sum x y n)) (h (floor n 2)))
                 (:instance int-mulpow-product-pos
                            (a (int-mulpow-hi x n)) (b (int-mulpow-hi y n)))
                 (:instance natp-of-int-mul-wrapped-sum)
                 (:instance int-mulpow-overflow-lemma
                            (s (int-mul-wrapped-sum x y n))
                            (hx (int-mulpow-hi x n)) (hy (int-mulpow-hi y n))
                            (c (expt 2 n)))
                 (:instance acl2::<-of-floor-arg1
                            (acl2::i (int-mul-wrapped-sum x y n))
                            (acl2::j (expt 2 n)) (acl2::k 1)))
           :in-theory (e/d (int-mul-and-check-spec-when-128
                            int-karatsuba-multiply-spec-components
                            lebits=>nat-of-int->lebits
                            int-mul-checked-spec int-wrap int-valuep
                            int-min int-max int-spec-unsigned
                            acl2::mod-when-< acl2::floor-when-<)
                           (int-mul-wrapped-sum int-mulpow-hi)))))

(defruled int-mul-and-check-any-gadget-sound
  :short "Every width including 128, both signednesses."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-any-gadget xs ys z0 z2 m zs carry p)
                 asg p))
           (and (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n)
                                    n))))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 1" :use int-mul-and-check-large-gadget-sound)
          ("Subgoal 2" :use (int-mul-and-check-small-gadget-sound
                             int-mulpow-small-width-facts)))
  :in-theory (e/d (int-mul-and-check-any-gadget)
                  (integer-widthp int-mul-and-check-gadget
                   int-mul-and-check-large-gadget)))

(defruled int-mul-and-check-any-gadget-complete
  :short "Every width including 128, both signednesses.  The Karatsuba
          witnesses z0, z2, m, carry are only read when @($n = 128$)."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (not (equal (int-mul-and-check-spec x y signedp n)
                            (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-and-check-spec x y signedp n) n))
                (implies (equal n 128)
                         (and (equal (lookup-equal z0 asg)
                                     (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                              (equal (lookup-equal z2 asg)
                                     (* (int-mulpow-hi x n) (int-mulpow-hi y n)))
                              (equal (lookup-equal m asg)
                                     (* (+ (int-mulpow-hi x n) (int-mulpow-lo x n))
                                        (+ (int-mulpow-hi y n) (int-mulpow-lo y n))))
                              (equal (lookup-equal-list carry asg)
                                     (second (int-karatsuba-multiply-spec
                                              x y signedp n))))))
           (r1cs::r1cs-constraints-holdp
            (int-mul-and-check-any-gadget xs ys z0 z2 m zs carry p)
            asg p))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 1" :use int-mul-and-check-large-gadget-complete)
          ("Subgoal 2" :use (int-mul-and-check-small-gadget-complete
                             int-mulpow-small-width-facts)))
  :in-theory (e/d (int-mul-and-check-any-gadget)
                  (integer-widthp int-mul-and-check-gadget
                   int-mul-and-check-large-gadget)))

(defruled int-mul-checked-unsigned-any-gadget-sound
  :short "Unsigned mul_checked (Mul, MulAssign), every width including 128."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-any-gadget xs ys z0 z2 m zs carry p)
                 asg p))
           (and (not (equal (int-mul-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-checked-spec x y nil n) n))))
  :do-not-induct t
  :use ((:instance int-mul-and-check-any-gadget-sound (signedp nil))
        (:instance int-mul-and-check-spec-is-mul-checked-when-unsigned))
  :in-theory (e/d (int-mul-checked-unsigned-any-gadget)
                  (integer-widthp int-mul-and-check-any-gadget)))

(defruled int-mul-checked-unsigned-any-gadget-complete
  :short "Unsigned mul_checked (Mul, MulAssign), every width including 128."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp zs) (symbol-listp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len carry) (+ (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-mul-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-checked-spec x y nil n) n))
                (implies (equal n 128)
                         (and (equal (lookup-equal z0 asg)
                                     (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                              (equal (lookup-equal z2 asg)
                                     (* (int-mulpow-hi x n) (int-mulpow-hi y n)))
                              (equal (lookup-equal m asg)
                                     (* (+ (int-mulpow-hi x n) (int-mulpow-lo x n))
                                        (+ (int-mulpow-hi y n) (int-mulpow-lo y n))))
                              (equal (lookup-equal-list carry asg)
                                     (second (int-karatsuba-multiply-spec
                                              x y nil n))))))
           (r1cs::r1cs-constraints-holdp
            (int-mul-checked-unsigned-any-gadget xs ys z0 z2 m zs carry p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mul-and-check-any-gadget-complete (signedp nil))
        (:instance int-mul-and-check-spec-is-mul-checked-when-unsigned))
  :in-theory (e/d (int-mul-checked-unsigned-any-gadget)
                  (integer-widthp int-mul-and-check-any-gadget)))
