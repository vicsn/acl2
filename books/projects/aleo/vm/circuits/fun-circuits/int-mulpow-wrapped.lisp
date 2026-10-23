; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MulWrapped for every integer width (8, 16, 32, 64, 128) and both
; signednesses.
;
; snarkVM's mul_wrapped is the same circuit for every width and
; signedness: three field products of the half-width bit sums, then
; to_lower_bits_le of z0 + 2^(n/2) z1 on n + n/2 + 1 bits, truncated to n.
; That is int-mul-wrapped-gadget (r1cs/unsigned-small-mul-wrapped).  For
; n = 128 the decomposition has 193 bits, below the 253-bit field, so the
; library soundness theorem applies.  Wrapped multiplication only depends
; on the bit patterns, so the output bits are int->lebits of the funspec
; for both signednesses.

(in-package "ALEOVM")

(include-book "int-mul")

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

(defruled int-mulpow-width-mul-wrapped-fits
  (implies (integer-widthp n)
           (and (evenp n)
                (< 0 n)
                (< (+ n (+ 1 (floor n 2))) 253)))
  :enable integer-widthp)

(defruled int-mulpow-bits-are-int->lebits
  (implies (and (bit-listp zs)
                (equal (len zs) n)
                (natp n)
                (equal (lebits=>nat zs)
                       (mod (* (mod (ifix x) (expt 2 n))
                               (mod (ifix y) (expt 2 n)))
                            (expt 2 n))))
           (equal (int->lebits (* (ifix x) (ifix y)) n) zs))
  :do-not-induct t
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits zs))
  :enable (int->lebits
           acl2::bit-list-fix-when-bit-listp
           acl2::mod-of-*-of-mod
           acl2::mod-of-*-of-mod-2)
  :disable acl2::nat=>lebits-of-lebits=>nat)

(defruled int-mul-wrapped-gadget-sound
  :short "Every width including 128, both signednesses."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len zs-high) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh
                                         zs zs-high p)
                 asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-mul-wrapped-spec x y signedp n) n)))
  :do-not-induct t
  :use ((:instance unsigned-small-mul-wrapped-gadget-soundness
                   (p (base-prime)))
        (:instance int-mulpow-width-mul-wrapped-fits)
        (:instance int-mulpow-bits-are-int->lebits
                   (zs (lookup-equal-list zs asg))))
  :enable (int-mul-wrapped-gadget
           int-mul-wrapped-spec
           int->lebits-of-int-wrap
           integer-length-of-base-prime
           posp-when-integer-widthp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness.  The canonical witnesses are the three half-width
; products and the n + n/2 + 1 bits of z0 + 2^(n/2) z1, whose low n bits
; are the wrapped product.

(defruled int-mulpow-times-mono
  (implies (and (natp x) (natp y) (natp a) (natp b)
                (<= x a) (<= y b))
           (<= (* x y) (* a b)))
  :hints (("Goal" :nonlinearp t)))

(define int-mulpow-babbage-sum ((x0 natp) (x1 natp) (y0 natp) (y1 natp)
                                (h natp))
  :returns (s natp :hyp :guard)
  (+ (* x0 y0) (* (expt 2 h) (+ (* x1 y0) (* x0 y1)))))

(defruled int-mulpow-babbage-sum-bound
  (implies (and (member-equal h '(4 8 16 32 64))
                (natp x0) (natp x1) (natp y0) (natp y1)
                (< x0 (expt 2 h)) (< x1 (expt 2 h))
                (< y0 (expt 2 h)) (< y1 (expt 2 h)))
           (< (int-mulpow-babbage-sum x0 x1 y0 y1 h)
              (expt 2 (+ 1 (* 3 h)))))
  :do-not-induct t
  :use ((:instance int-mulpow-times-mono (x x0) (y y0)
                   (a (1- (expt 2 h))) (b (1- (expt 2 h))))
        (:instance int-mulpow-times-mono (x x1) (y y0)
                   (a (1- (expt 2 h))) (b (1- (expt 2 h))))
        (:instance int-mulpow-times-mono (x x0) (y y1)
                   (a (1- (expt 2 h))) (b (1- (expt 2 h)))))
  :enable int-mulpow-babbage-sum)

(defruled int-mulpow-lebits=>nat-of-nat=>lebits-below
  (implies (and (natp k) (natp v) (< v (expt 2 k)))
           (equal (lebits=>nat (acl2::nat=>lebits k v)) v))
  :enable (acl2::lebits=>nat-of-nat=>lebits acl2::mod-when-<))

(defruled int-mulpow-floor-bound
  (implies (and (natp s) (posp n) (natp h)
                (< s (expt 2 (+ n h 1))))
           (< (floor s (expt 2 n)) (expt 2 (+ h 1))))
  :enable (acl2::expt-of-+ acl2::<-of-floor-arg1))

(defruled int-mulpow-mul-wrapped-last-constraint
  (implies (and (primep p)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp ws)
                (natp h)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list ws asg))
                (equal (+ (lookup-equal lowlow asg)
                          (* (expt 2 h) (lookup-equal highlow asg))
                          (* (expt 2 h) (lookup-equal lowhigh asg)))
                       (lebits=>nat (lookup-equal-list ws asg))))
           (r1cs::r1cs-constraint-holdsp
            (r1cs::make-r1cs-constraint
             :a (list (list 1 lowlow)
                      (list (expt 2 h) highlow)
                      (list (expt 2 h) lowhigh))
             :b (list (list 1 1))
             :c (pow2sum-vector ws 0))
            asg p))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0)))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add pfield::mul
           acl2::mod-of-+-of-mod-arg1
           acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-*-of-mod
           acl2::mod-of-*-of-mod-2))


(defruled int-mulpow-valuation-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (nthcdr i xs)))
  :enable (r1cs::valuation-binds-allp nthcdr))

(defruled int-mulpow-bits-mul-field-holds
  (implies (and (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbolp z)
                (< (+ (len xs) (len ys)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal z asg)
                       (* (lebits=>nat (lookup-equal-list xs asg))
                          (lebits=>nat (lookup-equal-list ys asg)))))
           (r1cs::r1cs-constraints-holdp
            (bits-mul-field-gadget xs ys z p) asg p))
  :use bits-mul-field-gadget-to-equal-of-mul)


(defruled int-mulpow-mod-plus-floor
  (implies (and (natp s) (posp k))
           (equal (+ (mod s k) (* k (floor s k))) s))
  :enable mod)

(defruled int-mulpow-mul-wrapped-last-holds
  (implies (and (primep p)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (natp h) (natp n) (natp s)
                (< s (expt 2 (+ n h 1)))
                (equal (len zs) n)
                (equal (len zs-high) (1+ h))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (equal (lookup-equal-list zs asg)
                       (acl2::nat=>lebits n (mod s (expt 2 n))))
                (equal (lookup-equal-list zs-high asg)
                       (acl2::nat=>lebits (1+ h) (floor s (expt 2 n))))
                (equal (+ (lookup-equal lowlow asg)
                          (* (expt 2 h) (lookup-equal highlow asg))
                          (* (expt 2 h) (lookup-equal lowhigh asg)))
                       s))
           (r1cs::r1cs-constraint-holdsp
            (r1cs::make-r1cs-constraint
             :a (list (list 1 lowlow)
                      (list (expt 2 h) highlow)
                      (list (expt 2 h) lowhigh))
             :b (list (list 1 1))
             :c (pow2sum-vector (append zs zs-high) 0))
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-mul-wrapped-last-constraint
                   (ws (append zs zs-high)))
        (:instance int-mulpow-floor-bound)
        (:instance int-mulpow-mod-plus-floor (k (expt 2 n))))
  :enable (lookup-equal-list-of-append
           acl2::lebits=>nat-of-append
           int-mulpow-lebits=>nat-of-nat=>lebits-below))

(defruled int-mulpow-mul-wrapped-body-holds
  (b* ((xb (lookup-equal-list xs asg))
       (yb (lookup-equal-list ys asg))
       (x0 (lebits=>nat (take h xb)))
       (x1 (lebits=>nat (nthcdr h xb)))
       (y0 (lebits=>nat (take h yb)))
       (y1 (lebits=>nat (nthcdr h yb)))
       (s (int-mulpow-babbage-sum x0 x1 y0 y1 h)))
    (implies (and (primep p)
                  (symbol-listp xs) (symbol-listp ys)
                  (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                  (symbol-listp zs) (symbol-listp zs-high)
                  (posp h)
                  (equal (len xs) (* 2 h))
                  (equal (len ys) (* 2 h))
                  (< (+ (* 2 h) h 1) (integer-length p))
                  (< s (expt 2 (+ (* 2 h) h 1)))
                  (equal (len zs) (* 2 h))
                  (equal (len zs-high) (1+ h))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg xs)
                  (r1cs::valuation-binds-allp asg ys)
                  (r1cs::valuation-bindsp asg lowlow)
                  (r1cs::valuation-bindsp asg highlow)
                  (r1cs::valuation-bindsp asg lowhigh)
                  (r1cs::valuation-binds-allp asg zs)
                  (r1cs::valuation-binds-allp asg zs-high)
                  (bit-listp xb)
                  (bit-listp yb)
                  (equal (lookup-equal lowlow asg) (* x0 y0))
                  (equal (lookup-equal highlow asg) (* x1 y0))
                  (equal (lookup-equal lowhigh asg) (* x0 y1))
                  (equal (lookup-equal-list zs asg)
                         (acl2::nat=>lebits (* 2 h) (mod s (expt 2 (* 2 h)))))
                  (equal (lookup-equal-list zs-high asg)
                         (acl2::nat=>lebits (1+ h) (floor s (expt 2 (* 2 h))))))
             (r1cs::r1cs-constraints-holdp
              (append (bits-mul-field-gadget (take h xs) (take h ys) lowlow p)
                      (bits-mul-field-gadget (nthcdr h xs) (take h ys) highlow p)
                      (bits-mul-field-gadget (take h xs) (nthcdr h ys) lowhigh p)
                      (boolean-check-gadget-list zs p)
                      (boolean-check-gadget-list zs-high p)
                      (list
                       (r1cs::make-r1cs-constraint
                        :a (list (list 1 lowlow)
                                 (list (expt 2 h) highlow)
                                 (list (expt 2 h) lowhigh))
                        :b (list (list 1 1))
                        :c (pow2sum-vector (append zs zs-high) 0))))
              asg p)))
  :do-not-induct t
  :use ((:instance int-mulpow-mul-wrapped-last-holds
                   (n (* 2 h))
                   (s (int-mulpow-babbage-sum
                       (lebits=>nat (take h (lookup-equal-list xs asg)))
                       (lebits=>nat (nthcdr h (lookup-equal-list xs asg)))
                       (lebits=>nat (take h (lookup-equal-list ys asg)))
                       (lebits=>nat (nthcdr h (lookup-equal-list ys asg)))
                       h)))
        (:instance int-mulpow-bits-mul-field-holds
                   (xs (take h xs)) (ys (take h ys)) (z lowlow))
        (:instance int-mulpow-bits-mul-field-holds
                   (xs (nthcdr h xs)) (ys (take h ys)) (z highlow))
        (:instance int-mulpow-bits-mul-field-holds
                   (xs (take h xs)) (ys (nthcdr h ys)) (z lowhigh)))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp-of-append
                   boolean-check-gadget-list-to-bit-listp
                   int-mulpow-valuation-binds-allp-of-nthcdr
                   lookup-equal-list-of-take
                   lookup-equal-list-of-nthcdr
                   int-mulpow-babbage-sum)
                  (r1cs::r1cs-constraint-holdsp
                   bits-mul-field-gadget
                   boolean-check-gadget-list)))

(defruledl int-mulpow-floor-of-low-plus-scaled
  (implies (and (natp a) (natp c) (posp k) (< a k))
           (equal (floor (+ a (* k c)) k) c))
  :do-not-induct t
  :use ((:instance int-mulpow-mod-plus-floor (s (+ a (* k c)))))
  :enable acl2::mod-when-<)

(defruled int-mulpow-lebits=>nat-take-nthcdr
  (implies (and (bit-listp b) (natp h) (<= h (len b)))
           (and (equal (lebits=>nat (take h b))
                       (mod (lebits=>nat b) (expt 2 h)))
                (equal (lebits=>nat (nthcdr h b))
                       (floor (lebits=>nat b) (expt 2 h)))))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (take h b)) (acl2::hidigits (nthcdr h b)))
        (:instance int-mulpow-floor-of-low-plus-scaled
                   (a (lebits=>nat (take h b)))
                   (c (lebits=>nat (nthcdr h b)))
                   (k (expt 2 h))))
  :enable (acl2::mod-when-<))

(define int-mulpow-lo ((x integerp) (n posp))
  :returns (lo natp)
  (mod (mod (ifix x) (expt 2 (acl2::pos-fix n))) (expt 2 (floor (acl2::pos-fix n) 2))))

(define int-mulpow-hi ((x integerp) (n posp))
  :returns (hi natp :rule-classes :type-prescription)
  (floor (mod (ifix x) (expt 2 (acl2::pos-fix n))) (expt 2 (floor (acl2::pos-fix n) 2))))

(define int-mul-wrapped-sum ((x integerp) (y integerp) (n posp))
  :returns (s natp)
  :short "@($z_0 + 2^{n/2} z_1$), the value decomposed into the
          @($n + n/2 + 1$) witness bits."
  (int-mulpow-babbage-sum (int-mulpow-lo x n) (int-mulpow-hi x n)
                          (int-mulpow-lo y n) (int-mulpow-hi y n)
                          (floor (acl2::pos-fix n) 2)))

(defruledl int-mulpow-babbage-mod
  (implies (and (integerp lx) (integerp ly) (integerp hx) (integerp hy)
                (posp k))
           (equal (mod (* (+ lx (* k hx)) (+ ly (* k hy))) (* k k))
                  (mod (+ (* lx ly) (* k (+ (* hx ly) (* lx hy)))) (* k k))))
  :do-not-induct t
  :use ((:instance acl2::mod-of-+-of-*-same-arg2-arg1
                   (acl2::x1 (+ (* lx ly) (* k (+ (* hx ly) (* lx hy)))))
                   (acl2::x2 (* hx hy))
                   (acl2::y (* k k)))))

(defruledl int-mulpow-babbage-mod-split
  (implies (and (natp ux) (natp uy) (posp k))
           (equal (mod (int-mulpow-babbage-sum (mod ux k) (floor ux k)
                                               (mod uy k) (floor uy k) h)
                       (* k k))
                  (if (equal k (expt 2 h))
                      (mod (* ux uy) (* k k))
                    (mod (int-mulpow-babbage-sum (mod ux k) (floor ux k)
                                                 (mod uy k) (floor uy k) h)
                         (* k k)))))
  :do-not-induct t
  :use ((:instance int-mulpow-mod-plus-floor (s ux))
        (:instance int-mulpow-mod-plus-floor (s uy))
        (:instance int-mulpow-babbage-mod
                   (lx (mod ux k)) (hx (floor ux k))
                   (ly (mod uy k)) (hy (floor uy k))))
  :enable int-mulpow-babbage-sum
  :disable (acl2::+-of-mod-and-*-of-floor-same))

(defruledl int-mulpow-twice-half
  (implies (and (integerp n) (evenp n))
           (equal (+ (floor n 2) (floor n 2)) n))
  :enable evenp)

(defruled int-mulpow-mod-of-wrapped-sum
  (implies (and (posp n) (evenp n))
           (equal (mod (int-mul-wrapped-sum x y n) (expt 2 n))
                  (mod (* (ifix x) (ifix y)) (expt 2 n))))
  :do-not-induct t
  :use ((:instance int-mulpow-babbage-mod-split
                   (ux (mod (ifix x) (expt 2 n)))
                   (uy (mod (ifix y) (expt 2 n)))
                   (h (floor n 2))
                   (k (expt 2 (floor n 2))))
        (:instance int-mulpow-twice-half)
        (:instance acl2::expt-of-+ (acl2::r 2)
                   (acl2::i1 (floor n 2)) (acl2::i2 (floor n 2))))
  :enable (int-mul-wrapped-sum int-mulpow-lo int-mulpow-hi evenp
           acl2::mod-of-*-of-mod acl2::mod-of-*-of-mod-2)
  :disable (acl2::expt-of-+))

(defruled int-mulpow-twice-half-times
  (implies (and (integerp n) (evenp n))
           (equal (* 2 (floor n 2)) n))
  :enable evenp)

(defruled int-mulpow-lo-is-take
  (implies (and (posp n) (evenp n))
           (equal (lebits=>nat (take (floor n 2) (int->lebits x n)))
                  (int-mulpow-lo x n)))
  :do-not-induct t
  :use (:instance int-mulpow-lebits=>nat-take-nthcdr
                  (b (int->lebits x n)) (h (floor n 2)))
  :enable (int-mulpow-lo lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit len-of-int->lebits))

(defruled int-mulpow-hi-is-nthcdr
  (implies (and (posp n) (evenp n))
           (equal (lebits=>nat (nthcdr (floor n 2) (int->lebits x n)))
                  (int-mulpow-hi x n)))
  :do-not-induct t
  :use (:instance int-mulpow-lebits=>nat-take-nthcdr
                  (b (int->lebits x n)) (h (floor n 2)))
  :enable (int-mulpow-hi lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit len-of-int->lebits))

(defruled int-mulpow-fold-wrapped-sum
  (implies (posp n)
           (equal (int-mulpow-babbage-sum (int-mulpow-lo x n) (int-mulpow-hi x n)
                                          (int-mulpow-lo y n) (int-mulpow-hi y n)
                                          (floor n 2))
                  (int-mul-wrapped-sum x y n)))
  :enable int-mul-wrapped-sum)

(defruled int-mulpow-int->lebits-of-product
  (implies (and (posp n) (evenp n))
           (equal (int->lebits (* (ifix x) (ifix y)) n)
                  (acl2::nat=>lebits n (mod (int-mul-wrapped-sum x y n)
                                            (expt 2 n)))))
  :enable (int-mulpow-mod-of-wrapped-sum int->lebits))

(defruled int->lebits-of-int-mul-wrapped-spec
  (implies (and (posp n) (evenp n))
           (equal (int->lebits (int-mul-wrapped-spec x y signedp n) n)
                  (acl2::nat=>lebits n (mod (int-mul-wrapped-sum x y n)
                                            (expt 2 n)))))
  :use int-mulpow-int->lebits-of-product
  :enable (int-mul-wrapped-spec int->lebits-of-int-wrap)
  :disable (int-wrap int->lebits ifix))

(defruled int-mul-wrapped-sum-bound
  (implies (integer-widthp n)
           (< (int-mul-wrapped-sum x y n)
              (expt 2 (+ n (floor n 2) 1))))
  :do-not-induct t
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64) (equal n 128))
  :use ((:instance int-mulpow-babbage-sum-bound
                   (h (floor n 2))
                   (x0 (int-mulpow-lo x n)) (x1 (int-mulpow-hi x n))
                   (y0 (int-mulpow-lo y n)) (y1 (int-mulpow-hi y n))))
  :enable (int-mul-wrapped-sum int-mulpow-lo int-mulpow-hi integer-widthp
           acl2::<-of-floor-arg1)
  :disable int-mulpow-babbage-sum)

(defruled int-mul-wrapped-gadget-complete
  :short "Every width including 128, both signednesses."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len zs-high) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal lowlow asg)
                       (* (int-mulpow-lo x n) (int-mulpow-lo y n)))
                (equal (lookup-equal highlow asg)
                       (* (int-mulpow-hi x n) (int-mulpow-lo y n)))
                (equal (lookup-equal lowhigh asg)
                       (* (int-mulpow-lo x n) (int-mulpow-hi y n)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-wrapped-spec x y signedp n) n))
                (equal (lookup-equal-list zs-high asg)
                       (acl2::nat=>lebits (1+ (floor n 2))
                                          (floor (int-mul-wrapped-sum x y n)
                                                 (expt 2 n)))))
           (r1cs::r1cs-constraints-holdp
            (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh zs zs-high p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-width-mul-wrapped-fits)
        (:instance int-mulpow-twice-half-times)
        (:instance int-mulpow-mul-wrapped-body-holds
                   (p (base-prime)) (h (floor n 2)))
        (:instance int-mul-wrapped-sum-bound))
  :in-theory (e/d (int-mul-wrapped-gadget
                   unsigned-small-mul-wrapped-gadget
                   int-mulpow-twice-half-times
                   int-mulpow-lo-is-take
                   int-mulpow-hi-is-nthcdr
                   int-mulpow-fold-wrapped-sum
                   int->lebits-of-int-mul-wrapped-spec
                   integer-length-of-base-prime
                   posp-when-integer-widthp
                   bit-listp-of-int->lebits-explicit)
                  (integer-widthp
                   int-mul-wrapped-sum
                   int-mulpow-babbage-sum)))
