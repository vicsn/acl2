; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; karatsuba_multiply for every integer width and both signednesses.
;
; snarkVM (mul_checked.rs, Integer::karatsuba_multiply), with
; h = n/2 and X0, X1, Y0, Y1 the bit sums of the halves:
;   z0 = X0 * Y0                       (one constraint)
;   z2 = X1 * Y1                       (one constraint)
;   m  = (X1 + X0) * (Y1 + Y0)         (one constraint)
;   z1 = m - z2 - z0                   (linear combination)
;   z0 + 2^h z1 = sum of ws            (n + h + 1 boolean witnesses
;                                       and one assert_eq, a * 1 = c)
; The outputs are the low n bits of ws, the h + 1 high bits of ws, and z2.
; The circuit only reads bit patterns, so it is the same for both
; signednesses.

(in-package "ALEOVM")

(include-book "int-mulpow-wrapped")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-karatsuba-multiply-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (z0 symbolp)
                                       (z2 symbolp)
                                       (m symbolp)
                                       (ws symbol-listp)
                                       (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len ws) (+ (len xs) (floor (len xs) 2) 1))
              (< (len ws) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (b* ((h (floor (len xs) 2))
       (low-xs (take h xs))
       (high-xs (nthcdr h xs))
       (low-ys (take h ys))
       (high-ys (nthcdr h ys)))
    (append (bits-mul-field-gadget low-xs low-ys z0 p)
            (bits-mul-field-gadget high-xs high-ys z2 p)
            (list (r1cs::make-r1cs-constraint
                   :a (append (pow2sum-vector high-xs 0)
                              (pow2sum-vector low-xs 0))
                   :b (append (pow2sum-vector high-ys 0)
                              (pow2sum-vector low-ys 0))
                   :c (list (list 1 m))))
            (boolean-check-gadget-list ws p)
            (list (r1cs::make-r1cs-constraint
                   :a (list (list (- 1 (expt 2 h)) z0)
                            (list (expt 2 h) m)
                            (list (- (expt 2 h)) z2))
                   :b (list (list 1 1))
                   :c (pow2sum-vector ws 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-mulpow-middle-constraint
  (implies (and (primep p)
                (symbol-listp xs1) (symbol-listp xs0)
                (symbol-listp ys1) (symbol-listp ys0)
                (symbolp m)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs1)
                (r1cs::valuation-binds-allp asg xs0)
                (r1cs::valuation-binds-allp asg ys1)
                (r1cs::valuation-binds-allp asg ys0)
                (r1cs::valuation-bindsp asg m)
                (bit-listp (lookup-equal-list xs1 asg))
                (bit-listp (lookup-equal-list xs0 asg))
                (bit-listp (lookup-equal-list ys1 asg))
                (bit-listp (lookup-equal-list ys0 asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (append (pow2sum-vector xs1 0)
                               (pow2sum-vector xs0 0))
                    :b (append (pow2sum-vector ys1 0)
                               (pow2sum-vector ys0 0))
                    :c (list (list 1 m)))
                   asg p)
                  (equal (lookup-equal m asg)
                         (mod (* (+ (lebits=>nat (lookup-equal-list xs1 asg))
                                    (lebits=>nat (lookup-equal-list xs0 asg)))
                                 (+ (lebits=>nat (lookup-equal-list ys1 asg))
                                    (lebits=>nat (lookup-equal-list ys0 asg))))
                              p))))
  :do-not-induct t
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::add pfield::mul
           acl2::mod-of-+-of-mod-arg1
           acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-*-of-mod
           acl2::mod-of-*-of-mod-2))

(defruled int-mulpow-field-lc-aux
  (implies (and (posp p) (integerp k) (integerp a) (integerp b) (integerp c))
           (equal (mod (+ (* (+ p 1 (- k)) a)
                          (* k b)
                          (* (+ p (- k)) c))
                       p)
                  (mod (+ a (* k (- b (+ a c)))) p)))
  :use ((:instance acl2::mod-of-+-of-*-same-arg2-arg1
                   (acl2::x1 (+ a (* k (- b (+ a c)))))
                   (acl2::x2 (+ a c))
                   (acl2::y p))))

(defruledl int-mulpow-mod-of-+-+-mod
  (implies (and (integerp x) (integerp y) (integerp z) (posp p))
           (equal (mod (+ x y (mod z p)) p)
                  (mod (+ x y z) p)))
  :use ((:instance acl2::mod-of-+-of-mod-arg2 (acl2::x1 (+ x y)) (acl2::x2 z) (acl2::y p))))

(defruled int-mulpow-field-lc
  (implies (and (posp p) (integerp k) (< 1 k) (< k p)
                (integerp a) (integerp b) (integerp c))
           (equal (pfield::add (pfield::mul (mod (- 1 k) p) a p)
                               (pfield::add (pfield::mul (mod k p) b p)
                                            (pfield::add (pfield::mul (mod (- k) p) c p)
                                                         0 p)
                                            p)
                               p)
                  (mod (+ a (* k (- b (+ a c)))) p)))
  :do-not-induct t
  :use int-mulpow-field-lc-aux
  :cases ((and (equal (mod (- 1 k) p) (+ p 1 (- k)))
               (equal (mod (- k) p) (+ p (- k)))
               (equal (mod k p) k)))
  :hints (("Subgoal 2" :in-theory (enable acl2::mod-when-< mod)))
  :enable (pfield::add pfield::mul
           acl2::mod-of-+-of-mod-arg1
           acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-*-of-mod
           acl2::mod-of-*-of-mod-2
           int-mulpow-mod-of-+-+-mod)
  :disable (acl2::mod-of-minus-arg1))

(defruled int-mulpow-lc-dot-product
  (implies (and (primep p) (posp h) (< 1 (expt 2 h)) (< (expt 2 h) p)
                (symbolp z0) (symbolp m) (symbolp z2)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m))
           (equal (r1cs::dot-product (list (list (- 1 (expt 2 h)) z0)
                                           (list (expt 2 h) m)
                                           (list (- (expt 2 h)) z2))
                                     asg p)
                  (mod (+ (lookup-equal z0 asg)
                          (* (expt 2 h)
                             (- (lookup-equal m asg)
                                (+ (lookup-equal z0 asg)
                                   (lookup-equal z2 asg)))))
                       p)))
  :do-not-induct t
  :use ((:instance int-mulpow-field-lc
                   (k (expt 2 h))
                   (a (lookup-equal z0 asg))
                   (b (lookup-equal m asg))
                   (c (lookup-equal z2 asg))))
  :in-theory '(r1cs::dot-product car-cons cdr-cons endp
               (:e expt) posp natp fix
               int-mulpow-field-lc acl2::lookup-eq-becomes-lookup-equal
               r1cs::integerp-of-lookup-equal r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type
               acl2::primep-forward-to-posp
               (:compound-recognizer acl2::posp-compound-recognizer)
               (:compound-recognizer acl2::natp-compound-recognizer)
               (:t expt) acl2::integerp-of-expt-type))

(defruled int-mulpow-dot-product-of-one
  (implies (primep p)
           (equal (r1cs::dot-product '((1 1)) asg p) 1))
  :enable r1cs::dot-product)

(defruled int-mulpow-last-constraint
  (implies (and (primep p)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp ws)
                (posp h)
                (< 1 (expt 2 h))
                (< (expt 2 h) p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list ws asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list (- 1 (expt 2 h)) z0)
                             (list (expt 2 h) m)
                             (list (- (expt 2 h)) z2))
                    :b (list (list 1 1))
                    :c (pow2sum-vector ws 0))
                   asg p)
                  (equal (mod (+ (lookup-equal z0 asg)
                                 (* (expt 2 h)
                                    (- (lookup-equal m asg)
                                       (+ (lookup-equal z0 asg)
                                          (lookup-equal z2 asg)))))
                              p)
                         (mod (lebits=>nat (lookup-equal-list ws asg)) p))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0))
        int-mulpow-lc-dot-product
        int-mulpow-dot-product-of-one)
  :enable r1cs::r1cs-constraint-holdsp
  :disable r1cs::dot-product)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-karatsuba-multiply-spec-components
  (implies (integer-widthp n)
           (equal (int-karatsuba-multiply-spec x y signedp n)
                  (list (int-wrap (int-mul-wrapped-sum x y n) signedp n)
                        (int->lebits (floor (int-mul-wrapped-sum x y n)
                                            (expt 2 n))
                                     (1+ (floor n 2)))
                        (* (int-mulpow-hi x n) (int-mulpow-hi y n)))))
  :enable (int-karatsuba-multiply-spec int-mul-wrapped-sum
           int-mulpow-babbage-sum int-mulpow-lo int-mulpow-hi
           int-spec-unsigned posp-when-integer-widthp))

(defruled int-mulpow-bit-list-is-int->lebits
  (implies (and (bit-listp b)
                (equal (len b) k)
                (natp k)
                (equal (lebits=>nat b) v))
           (equal (int->lebits v k) b))
  :do-not-induct t
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits b))
  :enable (int->lebits acl2::bit-list-fix-when-bit-listp acl2::mod-when-<)
  :disable acl2::nat=>lebits-of-lebits=>nat)

(defruled int-mulpow-lo-hi-bound
  (implies (integer-widthp n)
           (and (< (int-mulpow-lo x n) (expt 2 (floor n 2)))
                (< (int-mulpow-hi x n) (expt 2 (floor n 2)))))
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64) (equal n 128))
  :enable (int-mulpow-lo int-mulpow-hi integer-widthp acl2::<-of-floor-arg1))

(defruled int-mulpow-middle-product-bound
  (implies (and (integer-widthp n)
                (natp a) (natp b) (natp c) (natp d)
                (< a (expt 2 (floor n 2))) (< b (expt 2 (floor n 2)))
                (< c (expt 2 (floor n 2))) (< d (expt 2 (floor n 2))))
           (< (* (+ a b) (+ c d)) (base-prime)))
  :do-not-induct t
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64) (equal n 128))
  :use ((:instance int-mulpow-times-mono (x (+ a b)) (y (+ c d))
                   (a (* 2 (expt 2 (floor n 2)))) (b (* 2 (expt 2 (floor n 2))))))
  :enable (integer-widthp (:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruled int-mulpow-karatsuba-width-facts
  (implies (integer-widthp n)
           (and (< (expt 2 (+ n (floor n 2) 1)) (base-prime))
                (< 1 (expt 2 (floor n 2)))
                (< (expt 2 (floor n 2)) (base-prime))
                (posp (floor n 2))
                (< (+ n (floor n 2) 1) 253)
                (evenp n)
                (posp n)
                (equal (* 2 (floor n 2)) n)
                (equal (+ (floor n 2) (floor n 2)) n)
                (< (+ (floor n 2) (floor n 2)) 253)
                (< n 253)))
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64) (equal n 128))
  :enable (integer-widthp (:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruled int-mulpow-karatsuba-z0
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (symbolp z0)
                (r1cs::valuation-bindsp asg z0))
           (equal (r1cs::r1cs-constraints-holdp
                   (bits-mul-field-gadget (take (floor n 2) xs)
                                          (take (floor n 2) ys) z0 p)
                   asg p)
                  (equal (lookup-equal z0 asg)
                         (* (int-mulpow-lo x n) (int-mulpow-lo y n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-karatsuba-width-facts)
        (:instance bits-mul-field-gadget-to-equal-of-mul
                   (xs (take (floor n 2) xs)) (ys (take (floor n 2) ys))
                   (z z0)))
  :enable (lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           int-mulpow-valuation-binds-allp-of-nthcdr
           int-mulpow-lo-is-take
           int-mulpow-hi-is-nthcdr
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           integer-length-of-base-prime)
  :disable integer-widthp)

(defruled int-mulpow-karatsuba-z2
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (symbolp z2)
                (r1cs::valuation-bindsp asg z2))
           (equal (r1cs::r1cs-constraints-holdp
                   (bits-mul-field-gadget (nthcdr (floor n 2) xs)
                                          (nthcdr (floor n 2) ys) z2 p)
                   asg p)
                  (equal (lookup-equal z2 asg)
                         (* (int-mulpow-hi x n) (int-mulpow-hi y n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-karatsuba-width-facts)
        (:instance bits-mul-field-gadget-to-equal-of-mul
                   (xs (nthcdr (floor n 2) xs)) (ys (nthcdr (floor n 2) ys))
                   (z z2)))
  :enable (lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           int-mulpow-valuation-binds-allp-of-nthcdr
           int-mulpow-lo-is-take
           int-mulpow-hi-is-nthcdr
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           integer-length-of-base-prime)
  :disable integer-widthp)

(defruled int-mulpow-karatsuba-m
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (symbolp m)
                (r1cs::valuation-bindsp asg m))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (append (pow2sum-vector (nthcdr (floor n 2) xs) 0)
                               (pow2sum-vector (take (floor n 2) xs) 0))
                    :b (append (pow2sum-vector (nthcdr (floor n 2) ys) 0)
                               (pow2sum-vector (take (floor n 2) ys) 0))
                    :c (list (list 1 m)))
                   asg p)
                  (equal (lookup-equal m asg)
                         (* (+ (int-mulpow-hi x n) (int-mulpow-lo x n))
                            (+ (int-mulpow-hi y n) (int-mulpow-lo y n))))))
  :do-not-induct t
  :use ((:instance int-mulpow-karatsuba-width-facts)
        (:instance int-mulpow-lo-hi-bound)
        (:instance int-mulpow-lo-hi-bound (x y))
        (:instance int-mulpow-middle-product-bound
                   (a (int-mulpow-hi x n)) (b (int-mulpow-lo x n))
                   (c (int-mulpow-hi y n)) (d (int-mulpow-lo y n)))
        (:instance int-mulpow-middle-constraint
                   (xs1 (nthcdr (floor n 2) xs)) (xs0 (take (floor n 2) xs))
                   (ys1 (nthcdr (floor n 2) ys)) (ys0 (take (floor n 2) ys))))
  :enable (lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           int-mulpow-valuation-binds-allp-of-nthcdr
           int-mulpow-lo-is-take
           int-mulpow-hi-is-nthcdr
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           integer-length-of-base-prime acl2::mod-when-<)
  :disable (integer-widthp r1cs::r1cs-constraint-holdsp))

(defruled int-karatsuba-multiply-gadget-facts
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp ws)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len ws) (+ n (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-karatsuba-multiply-gadget xs ys z0 z2 m ws p) asg p))
           (and (equal (lookup-equal z0 asg)
                       (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                (equal (lookup-equal z2 asg)
                       (* (int-mulpow-hi x n) (int-mulpow-hi y n)))
                (bit-listp (lookup-equal-list ws asg))
                (equal (lebits=>nat (lookup-equal-list ws asg))
                       (int-mul-wrapped-sum x y n))))
  :do-not-induct t
  :use ((:instance int-mulpow-karatsuba-width-facts)
        (:instance int-mul-wrapped-sum-bound)
        (:instance int-mulpow-lo-hi-bound)
        (:instance int-mulpow-lo-hi-bound (x y))
        (:instance int-mulpow-middle-product-bound
                   (a (int-mulpow-hi x n)) (b (int-mulpow-lo x n))
                   (c (int-mulpow-hi y n)) (d (int-mulpow-lo y n)))
        (:instance acl2::lebits=>nat-upper-bound
                   (acl2::digits (lookup-equal-list ws asg))))
  :in-theory (e/d (int-karatsuba-multiply-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   int-mulpow-karatsuba-z0
                   int-mulpow-karatsuba-z2
                   int-mulpow-karatsuba-m
                   int-mulpow-last-constraint
                   boolean-check-gadget-list-to-bit-listp
                   int-mulpow-valuation-binds-allp-of-nthcdr
                   lookup-equal-list-of-take
                   lookup-equal-list-of-nthcdr
                   int-mulpow-lo-is-take
                   int-mulpow-hi-is-nthcdr
                   bit-listp-of-int->lebits-explicit
                   len-of-int->lebits
                   integer-length-of-base-prime
                   int-mul-wrapped-sum
                   int-mulpow-babbage-sum
                   acl2::mod-when-<)
                  (integer-widthp
                   int-mulpow-lo int-mulpow-hi
                   bits-mul-field-gadget
                   boolean-check-gadget-list
                   r1cs::r1cs-constraint-holdsp)))

(defruled int-mulpow-int->lebits-of-mod
  (implies (natp n)
           (equal (int->lebits (mod (ifix v) (expt 2 n)) n)
                  (int->lebits v n)))
  :enable int->lebits)

(defruled int-karatsuba-multiply-gadget-sound
  :short "Every width including 128, both signednesses."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp ws)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len ws) (+ n (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-karatsuba-multiply-gadget xs ys z0 z2 m ws p) asg p))
           (b* ((spec (int-karatsuba-multiply-spec x y signedp n)))
             (and (equal (lookup-equal-list (take n ws) asg)
                         (int->lebits (first spec) n))
                  (equal (lookup-equal-list (nthcdr n ws) asg)
                         (second spec))
                  (equal (lookup-equal z2 asg)
                         (third spec)))))
  :do-not-induct t
  :use ((:instance int-karatsuba-multiply-gadget-facts)
        (:instance int-mulpow-karatsuba-width-facts)
        (:instance int-mulpow-lebits=>nat-take-nthcdr
                   (b (lookup-equal-list ws asg)) (h n))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (take n (lookup-equal-list ws asg)))
                   (k n)
                   (v (mod (int-mul-wrapped-sum x y n) (expt 2 n))))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (nthcdr n (lookup-equal-list ws asg)))
                   (k (+ (floor n 2) 1))
                   (v (floor (int-mul-wrapped-sum x y n) (expt 2 n))))
        (:instance int-mulpow-int->lebits-of-mod
                   (v (int-mul-wrapped-sum x y n))))
  :in-theory (e/d (int-karatsuba-multiply-spec-components
                   int->lebits-of-int-wrap
                   lookup-equal-list-of-take
                   lookup-equal-list-of-nthcdr)
                  (integer-widthp int-mul-wrapped-sum int->lebits)))

(defruled int-karatsuba-multiply-gadget-complete
  :short "Every width including 128, both signednesses."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbol-listp ws)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len ws) (+ n (floor n 2) 1))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal z0 asg)
                       (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                (equal (lookup-equal z2 asg)
                       (* (int-mulpow-hi x n) (int-mulpow-hi y n)))
                (equal (lookup-equal m asg)
                       (* (+ (int-mulpow-hi x n) (int-mulpow-lo x n))
                          (+ (int-mulpow-hi y n) (int-mulpow-lo y n))))
                (equal (lookup-equal-list ws asg)
                       (int->lebits (int-mul-wrapped-sum x y n)
                                    (+ n (floor n 2) 1))))
           (r1cs::r1cs-constraints-holdp
            (int-karatsuba-multiply-gadget xs ys z0 z2 m ws p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-karatsuba-width-facts)
        (:instance int-mul-wrapped-sum-bound))
  :in-theory (e/d (int-karatsuba-multiply-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   int-mulpow-karatsuba-z0
                   int-mulpow-karatsuba-z2
                   int-mulpow-karatsuba-m
                   int-mulpow-last-constraint
                   boolean-check-gadget-list-to-bit-listp
                   bit-listp-of-int->lebits-explicit
                   lebits=>nat-of-int->lebits
                   int-mul-wrapped-sum
                   int-mulpow-babbage-sum
                   acl2::mod-when-<)
                  (integer-widthp
                   int-mulpow-lo int-mulpow-hi
                   bits-mul-field-gadget
                   boolean-check-gadget-list
                   r1cs::r1cs-constraint-holdsp)))
