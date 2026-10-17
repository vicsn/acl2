; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unsigned PowChecked::pow_checked (also Pow::pow) at 128 bits, variable base
; and variable exponent, any exponent width
; (snarkVM circuit/types/integers/src/pow_checked.rs, mul_with_flags in
; mul_checked.rs).
;
; At 128 bits mul_with_flags uses karatsuba_multiply(a, b), which returns the
; 128 product bits ps, the 65 carry bits fc and z2 = X1 * Y1, and the flag
; is_not_equal(from_bits_le(fc) + z2, 0).  int-mul-with-flags-128-gadget-sound
; proves the weaker guarantee that pow_checked relies on (flag is a bit, flag
; = 0 implies the product is in range and ps are its bits);
; int-mul-with-flags-128-gadget-complete proves that the honest witness
; (flag = 0 exactly when a * b < 2^128) satisfies the constraints.
;
; The first iteration is constant-folded: 1 * 1 is a constant, and
; karatsuba_multiply(1, self) has z0, m linear in the bits of self and z2 the
; constant 0, so what remains is the 193 boolean witnesses ps ++ fc, the
; linear constraint self * 1 = from_bits_le(ps ++ fc), and the is_not_equal
; of from_bits_le(fc).  The ternary against the constant 1 is as in
; pow_wrapped.

(in-package "ALEOVM")

(include-book "int-mulpow-pow-checked")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lookup-equal-list"))
(local (include-book "../library-extensions/r1cses"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defund int-mul-with-flags-128-gadget (as bs ps fz0 fz2 fm fc mult isneq one p)
  (declare (xargs :verify-guards nil))
  (append (int-karatsuba-multiply-gadget as bs fz0 fz2 fm (append ps fc) p)
          (int-mulpow-pc-neq-gadget (cons (list 1 fz2) (pow2sum-vector fc 0))
                                    mult isneq one p)))

(defruled int-mulpow-pc128-delta-value
  (implies (and (primep p)
                (symbolp z) (symbol-listp fc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-binds-allp asg fc)
                (bit-listp (lookup-equal-list fc asg)))
           (equal (r1cs::dot-product
                   (cons (list 1 z) (pow2sum-vector fc 0)) asg p)
                  (mod (+ (lookup-equal z asg)
                          (lebits=>nat (lookup-equal-list fc asg)))
                       p)))
  :do-not-induct t
  :expand ((r1cs::dot-product (cons (list 1 z) (pow2sum-vector fc 0)) asg p))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs fc) (i 0)))
  :enable (pfield::add pfield::mul acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-+-of-mod-arg1))

(defruled int-mulpow-pc128-sum-zero
  (implies (and (natp u) (natp v) (< (+ u v) p))
           (equal (equal (mod (+ u v) p) 0)
                  (and (equal u 0) (equal v 0))))
  :enable acl2::mod-when-<)

(defruled int-mulpow-pc128-unsigned-facts
  (implies (int-valuep a nil 128)
           (and (equal (int-spec-unsigned a 128) a)
                (equal (mod a (expt 2 128)) a)
                (natp a)
                (< a (expt 2 128))))
  :enable (int-valuep int-min int-max int-spec-unsigned acl2::mod-when-<))

(defruled int-mulpow-pc128-hi-bound
  (implies (int-valuep a nil 128)
           (and (natp (int-mulpow-hi a 128))
                (< (int-mulpow-hi a 128) (expt 2 64))))
  :enable (int-mulpow-hi int-valuep int-min int-max acl2::mod-when-<
           acl2::<-of-floor-arg1))

(defruled int-mul-with-flags-128-gadget-sound
  :short "The weaker guarantee at 128 bits: the flag is a bit, and flag = 0
          implies that the product is in range and its bits are correct."
  (implies (and (equal p (base-prime))
                (equal n 128)
                (symbol-listp as) (equal (len as) n)
                (symbol-listp bs) (equal (len bs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
                (symbolp fz0) (symbolp fz2) (symbolp fm)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg fz0)
                (r1cs::valuation-bindsp asg fz2)
                (r1cs::valuation-bindsp asg fm)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil n) (int-valuep b nil n)
                (equal (lookup-equal-list as asg) (int->lebits a n))
                (equal (lookup-equal-list bs asg) (int->lebits b n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-128-gadget as bs ps fz0 fz2 fm fc
                                                mult isneq one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (and (int-valuep (* a b) nil n)
                              (equal (lookup-equal-list ps asg)
                                     (int->lebits (* a b) n))))))
  :do-not-induct t
  :use ((:instance int-karatsuba-multiply-gadget-facts
                   (xs as) (ys bs) (z0 fz0) (z2 fz2) (m fm) (ws (append ps fc))
                   (x a) (y b))
        (:instance int-mulpow-product-split (x a) (y b))
        (:instance int-mulpow-pc128-unsigned-facts)
        (:instance int-mulpow-pc128-unsigned-facts (a b))
        (:instance int-mulpow-pc128-hi-bound)
        (:instance int-mulpow-pc128-hi-bound (a b))
        (:instance int-mulpow-pc-neq-sound
                   (delta (cons (list 1 fz2) (pow2sum-vector fc 0))))
        (:instance int-mulpow-pc128-delta-value (z fz2))
        (:instance int-mulpow-pc128-sum-zero
                   (u (lookup-equal fz2 asg))
                   (v (lebits=>nat (lookup-equal-list fc asg))))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list fc asg)))
        (:instance int-mulpow-times-mono
                   (x (int-mulpow-hi a 128)) (y (int-mulpow-hi b 128))
                   (a (expt 2 64)) (b (expt 2 64)))
        (:instance int-mulpow-pw-first-ps
                   (x (* a b)) (a (lookup-equal-list ps asg)) (b nil)))
  :in-theory (e/d (int-mul-with-flags-128-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-hi int-spec-unsigned
                   int-mul-wrapped-sum int-karatsuba-multiply-gadget)))


(defun int-mulpow-pc128-d (a b)
  (declare (xargs :verify-guards nil))
  (+ (* (int-mulpow-hi a 128) (int-mulpow-hi b 128))
     (floor (int-mul-wrapped-sum a b 128) (expt 2 128))))

(defun int-mulpow-pc128-honest-mult (a b)
  (declare (xargs :verify-guards nil))
  (if (equal (int-mulpow-pc128-d a b) 0)
      1
    (pfield::inv (mod (int-mulpow-pc128-d a b) (base-prime)) (base-prime))))

(defruledl int-mulpow-pc128-split-lemma
  (implies (and (natp s) (natp z) (natp f) (natp r) (< r k) (posp k)
                (equal s (+ r (* k f))))
           (equal (< (+ s (* k z)) k)
                  (equal (+ f z) 0)))
  :cases ((equal (+ f z) 0))
  :use ((:instance int-mulpow-times-mono (x 1) (y k) (a (+ f z)) (b k))))

(defruled int-mulpow-pc128-d-zero-iff
  (implies (and (int-valuep a nil 128) (int-valuep b nil 128))
           (equal (equal (int-mulpow-pc128-d a b) 0)
                  (int-valuep (* a b) nil 128)))
  :do-not-induct t
  :use ((:instance int-mulpow-product-split (x a) (y b) (n 128))
        (:instance int-mulpow-pc128-unsigned-facts)
        (:instance int-mulpow-pc128-unsigned-facts (a b))
        (:instance int-mulpow-pc128-hi-bound)
        (:instance int-mulpow-pc128-hi-bound (a b))
        (:instance int-mulpow-mod-plus-floor
                   (s (int-mul-wrapped-sum a b 128)) (k (expt 2 128)))
        (:instance int-mulpow-pc128-split-lemma
                   (s (int-mul-wrapped-sum a b 128))
                   (z (* (int-mulpow-hi a 128) (int-mulpow-hi b 128)))
                   (f (floor (int-mul-wrapped-sum a b 128) (expt 2 128)))
                   (r (mod (int-mul-wrapped-sum a b 128) (expt 2 128)))
                   (k (expt 2 128))))
  :in-theory (e/d (int-valuep int-min int-max)
                  (int-mulpow-hi int-spec-unsigned int-mul-wrapped-sum)))

(defrulel int-mulpow-pc128-natsum-zero
  (implies (and (natp x) (natp y) (equal (+ x y) 0))
           (and (equal x 0) (equal y 0)))
  :rule-classes nil)

(defruledl int-mulpow-pc128-parts-natp
  (implies (and (int-valuep a nil 128) (int-valuep b nil 128))
           (and (natp (* (int-mulpow-hi a 128) (int-mulpow-hi b 128)))
                (natp (floor (int-mul-wrapped-sum a b 128) (expt 2 128)))))
  :in-theory (enable int-mulpow-hi int-mul-wrapped-sum int-mulpow-lo
                     int-valuep int-min int-max))

(defruled int-mulpow-pc128-in-range-parts
  (implies (and (int-valuep a nil 128) (int-valuep b nil 128)
                (int-valuep (* a b) nil 128))
           (and (equal (* (int-mulpow-hi a 128) (int-mulpow-hi b 128)) 0)
                (equal (floor (int-mul-wrapped-sum a b 128) (expt 2 128)) 0)))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-d-zero-iff)
        (:instance int-mulpow-pc128-hi-bound)
        (:instance int-mulpow-pc128-hi-bound (a b))
        (:instance int-mul-wrapped-sum-bound (x a) (y b) (n 128))
        (:instance int-mulpow-pc128-unsigned-facts)
        (:instance int-mulpow-pc128-parts-natp)
        (:instance int-mulpow-pc128-natsum-zero
                   (x (* (int-mulpow-hi a 128) (int-mulpow-hi b 128)))
                   (y (floor (int-mul-wrapped-sum a b 128) (expt 2 128)))))
  :in-theory (disable int-mulpow-hi int-spec-unsigned int-mul-wrapped-sum
                      int-valuep))

(defruled int-mul-with-flags-128-gadget-complete
  (implies (and (equal p (base-prime))
                (equal n 128)
                (symbol-listp as) (equal (len as) n)
                (symbol-listp bs) (equal (len bs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
                (symbolp fz0) (symbolp fz2) (symbolp fm)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg fz0)
                (r1cs::valuation-bindsp asg fz2)
                (r1cs::valuation-bindsp asg fm)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil n) (int-valuep b nil n)
                (equal (lookup-equal-list as asg) (int->lebits a n))
                (equal (lookup-equal-list bs asg) (int->lebits b n))
                (equal (lookup-equal fz0 asg)
                       (* (int-mulpow-lo a n) (int-mulpow-lo b n)))
                (equal (lookup-equal fz2 asg)
                       (* (int-mulpow-hi a n) (int-mulpow-hi b n)))
                (equal (lookup-equal fm asg)
                       (* (+ (int-mulpow-hi a n) (int-mulpow-lo a n))
                          (+ (int-mulpow-hi b n) (int-mulpow-lo b n))))
                (equal (lookup-equal-list ps asg)
                       (int->lebits (int-mul-wrapped-sum a b n) n))
                (equal (lookup-equal-list fc asg)
                       (int->lebits (floor (int-mul-wrapped-sum a b n)
                                           (expt 2 n))
                                    (1+ (floor n 2))))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* a b) n))
                (equal (lookup-equal mult asg)
                       (int-mulpow-pc128-honest-mult a b)))
           (r1cs::r1cs-constraints-holdp
            (int-mul-with-flags-128-gadget as bs ps fz0 fz2 fm fc
                                           mult isneq one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-karatsuba-multiply-gadget-complete
                   (xs as) (ys bs) (z0 fz0) (z2 fz2) (m fm) (ws (append ps fc))
                   (x a) (y b) (signedp nil))
        (:instance int-mulpow-append-int->lebits
                   (s (int-mul-wrapped-sum a b 128)) (n 128) (k 65))
        (:instance int-mul-wrapped-sum-bound (x a) (y b) (n 128))
        (:instance int-mulpow-pc128-hi-bound)
        (:instance int-mulpow-pc128-hi-bound (a b))
        (:instance int-mulpow-pc128-d-zero-iff)
        (:instance int-mulpow-pc128-in-range-parts)
        (:instance int-mulpow-pc-neq-complete
                   (delta (cons (list 1 fz2) (pow2sum-vector fc 0))))
        (:instance int-mulpow-pc128-delta-value (z fz2))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list fc asg)))
        (:instance int-mulpow-floor-bound
                   (s (int-mul-wrapped-sum a b 128)) (n 128) (h 64))
        (:instance int-mulpow-times-mono
                   (x (int-mulpow-hi a 128)) (y (int-mulpow-hi b 128))
                   (a (expt 2 64)) (b (expt 2 64))))
  :in-theory (e/d (int-mul-with-flags-128-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-append
                   bit-listp-of-int->lebits-explicit
                   lebits=>nat-of-int->lebits
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-hi int-mulpow-lo int-spec-unsigned
                   int-mul-wrapped-sum int-karatsuba-multiply-gadget
                   int-valuep)))


(defund int-mulpow-pc128-first-flags-gadget (xs ps fc mult isneq one p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list (append ps fc) p)
          (list (r1cs::make-r1cs-constraint
                 :a (pow2sum-vector xs 0)
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append ps fc) 0)))
          (int-mulpow-pc-neq-gadget (pow2sum-vector fc 0) mult isneq one p)))

(defruled int-mulpow-pc128-first-constraint
  (implies (and (primep p)
                (symbol-listp xs) (symbol-listp ws)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ws asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (pow2sum-vector xs 0)
                    :b (list (list 1 1))
                    :c (pow2sum-vector ws 0))
                   asg p)
                  (equal (mod (lebits=>nat (lookup-equal-list xs asg)) p)
                         (mod (lebits=>nat (lookup-equal-list ws asg)) p))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat (i 0))
        int-mulpow-dot-product-of-one)
  :enable (r1cs::r1cs-constraint-holdsp pfield::mul)
  :disable r1cs::dot-product)

(defruled int-mulpow-pc128-fc-value
  (implies (and (primep p)
                (symbol-listp fc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg fc)
                (bit-listp (lookup-equal-list fc asg)))
           (equal (r1cs::dot-product (pow2sum-vector fc 0) asg p)
                  (mod (lebits=>nat (lookup-equal-list fc asg)) p)))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs fc) (i 0))))

(defrule int-mulpow-pc128-first-split
  (implies (and (natp x) (< x k) (natp u) (< u k) (natp v) (posp k)
                (equal x (+ u (* k v))))
           (and (equal v 0) (equal u x)))
  :rule-classes nil
  :cases ((equal v 0))
  :use ((:instance int-mulpow-times-mono (x 1) (y k) (a v) (b k))))

(defruled int-mulpow-pc128-first-flags-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc128-first-flags-gadget xs ps fc mult isneq one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (equal (lookup-equal-list ps asg) (int->lebits x 128))))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs (append ps fc)))
        (:instance int-mulpow-pc128-first-constraint (ws (append ps fc)))
        (:instance int-mulpow-pc-neq-sound (delta (pow2sum-vector fc 0)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list fc asg)))
        (:instance int-mulpow-pc128-first-split
                   (k (expt 2 128))
                   (u (lebits=>nat (lookup-equal-list ps asg)))
                   (v (lebits=>nat (lookup-equal-list fc asg))))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (lookup-equal-list ps asg)) (k 128) (v x)))
  :in-theory (e/d (int-mulpow-pc128-first-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-pc-neq-gadget)))

(defruled int-mulpow-pc128-first-flags-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list ps asg) (int->lebits x 128))
                (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc128-first-flags-gadget xs ps fc mult isneq one p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs (append ps fc)))
        (:instance int-mulpow-pc128-first-constraint (ws (append ps fc)))
        (:instance int-mulpow-pc-neq-complete (delta (pow2sum-vector fc 0)))
        (:instance int-mulpow-pc128-fc-value))
  :in-theory (e/d (int-mulpow-pc128-first-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-pc-neq-gadget)))


(defund int-mulpow-pc128-first-gadget (e xs ps fc mult isneq out rs one p)
  (declare (xargs :verify-guards nil))
  (append (int-mulpow-pc128-first-flags-gadget xs ps fc mult isneq one p)
          (int-mulpow-pc-overflow-gadget isneq e out)
          (boolean-or-notleft-gadget e (car ps) (car rs) one p)
          (int-mulpow-pw-and-list e (cdr ps) (cdr rs))))

(defruled int-mulpow-pc128-first-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc128-first-gadget e xs ps fc mult isneq out rs
                                                one p)
                 asg p))
           (and (int-valuep (expt x (lookup-equal e asg)) nil 128)
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) 128))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-first-flags-sound)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance int-mulpow-pw-first-rs-sound)
        (:instance int-mulpow-pw-int->lebits-of-1 (n 128)))
  :in-theory (e/d (int-mulpow-pc128-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

(defruled int-mulpow-pc128-first-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list ps asg) (int->lebits x 128))
                (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) 128)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc128-first-gadget e xs ps fc mult isneq out rs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-first-flags-complete)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance int-mulpow-pw-first-rs-complete)
        (:instance int-mulpow-pw-int->lebits-of-1 (n 128)))
  :in-theory (e/d (int-mulpow-pc128-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   int-mulpow-pc-integerp-when-int-valuep
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

; A 128-bit loop iteration record is the list of wires
;   (z0 z2 m sqs carry ps fz0 fz2 fm fc rs mult isneq out)
; of the checked squaring, the Karatsuba mul_with_flags, the overflow
; assertion, and the selected result (kept at index 10).

(defund int-mulpow-pc128-rec-okp (rec asg)
  (declare (xargs :verify-guards nil))
  (and (true-listp rec)
       (equal (len rec) 14)
       (symbolp (nth 0 rec)) (symbolp (nth 1 rec)) (symbolp (nth 2 rec))
       (symbol-listp (nth 3 rec)) (symbol-listp (nth 4 rec))
       (symbol-listp (nth 5 rec))
       (symbolp (nth 6 rec)) (symbolp (nth 7 rec)) (symbolp (nth 8 rec))
       (symbol-listp (nth 9 rec)) (symbol-listp (nth 10 rec))
       (symbolp (nth 11 rec)) (symbolp (nth 12 rec)) (symbolp (nth 13 rec))
       (equal (len (nth 3 rec)) 128)
       (equal (len (nth 4 rec)) 65)
       (equal (len (nth 5 rec)) 128)
       (equal (len (nth 9 rec)) 65)
       (equal (len (nth 10 rec)) 128)
       (r1cs::valuation-bindsp asg (nth 0 rec))
       (r1cs::valuation-bindsp asg (nth 1 rec))
       (r1cs::valuation-bindsp asg (nth 2 rec))
       (r1cs::valuation-binds-allp asg (nth 3 rec))
       (r1cs::valuation-binds-allp asg (nth 4 rec))
       (r1cs::valuation-binds-allp asg (nth 5 rec))
       (r1cs::valuation-bindsp asg (nth 6 rec))
       (r1cs::valuation-bindsp asg (nth 7 rec))
       (r1cs::valuation-bindsp asg (nth 8 rec))
       (r1cs::valuation-binds-allp asg (nth 9 rec))
       (r1cs::valuation-binds-allp asg (nth 10 rec))
       (r1cs::valuation-bindsp asg (nth 11 rec))
       (r1cs::valuation-bindsp asg (nth 12 rec))
       (r1cs::valuation-bindsp asg (nth 13 rec))))

(defruled int-mulpow-pc128-rec-okp-out
  (implies (int-mulpow-pc128-rec-okp rec asg)
           (and (symbol-listp (nth 10 rec))
                (equal (len (nth 10 rec)) 128)
                (r1cs::valuation-binds-allp asg (nth 10 rec))))
  :enable int-mulpow-pc128-rec-okp)

(defund int-mulpow-pc128-step-gadget (e xs rs rec one p)
  (declare (xargs :verify-guards nil))
  (append (int-mul-checked-unsigned-any-gadget rs rs (nth 0 rec) (nth 1 rec)
                                               (nth 2 rec) (nth 3 rec)
                                               (nth 4 rec) p)
          (int-mul-with-flags-128-gadget (nth 3 rec) xs (nth 5 rec)
                                         (nth 6 rec) (nth 7 rec) (nth 8 rec)
                                         (nth 9 rec) (nth 11 rec) (nth 12 rec)
                                         one p)
          (int-mulpow-pc-overflow-gadget (nth 12 rec) e (nth 13 rec))
          (integer-ternary-gadget e (nth 5 rec) (nth 3 rec) (nth 10 rec) p)))

(defruled int-mulpow-pc128-step-sound-wires
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp carry) (equal (len carry) 65)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp rs2) (equal (len rs2) 128)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbolp fz0) (symbolp fz2) (symbolp fm)
                (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg rs2)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg fz0)
                (r1cs::valuation-bindsp asg fz2)
                (r1cs::valuation-bindsp asg fm)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128)
                (int-valuep r nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits r 128))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-any-gadget rs rs z0 z2 m sqs carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-128-gadget sqs xs ps fz0 fz2 fm fc
                                                mult isneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-overflow-gadget isneq e out) asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget e ps sqs rs2 p) asg p))
           (and (int-valuep (* r r) nil 128)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* r r x) nil 128))
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* r r x) 128)
                         (int->lebits (* r r) 128)))))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-sound
                   (xs rs) (ys rs) (zs sqs) (x r) (y r) (n 128))
        (:instance int-mul-with-flags-128-gadget-sound
                   (as sqs) (bs xs) (a (* r r)) (b x) (n 128))
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs2)))
  :in-theory (e/d (int-mul-checked-spec bitp
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-128-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defruled int-mulpow-pc128-step-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128) (natp v)
                (int-valuep (expt x v) nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) 128))
                (int-mulpow-pc128-rec-okp rec asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc128-step-gadget e xs rs rec one p) asg p))
           (and (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) nil 128)
                (equal (lookup-equal-list (nth 10 rec) asg)
                       (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg)))
                                    128))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-step-sound-wires
                   (z0 (nth 0 rec)) (z2 (nth 1 rec)) (m (nth 2 rec))
                   (sqs (nth 3 rec)) (carry (nth 4 rec))
                   (ps (nth 5 rec)) (fz0 (nth 6 rec)) (fz2 (nth 7 rec))
                   (fm (nth 8 rec)) (fc (nth 9 rec)) (rs2 (nth 10 rec))
                   (mult (nth 11 rec)) (isneq (nth 12 rec)) (out (nth 13 rec))
                   (r (expt x v)))
        (:instance int-mulpow-pw-expt-step (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-pc128-step-gadget
                   int-mulpow-pc128-rec-okp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pc-integerp-when-int-valuep
                   bitp)
                  (int->lebits int-valuep expt
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-128-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc128-recs-okp (bs recs asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pc128-rec-okp (car recs) asg)
         (int-mulpow-pc128-recs-okp (cdr bs) (cdr recs) asg))))

(defund int-mulpow-pc128-loop-gadget (bs xs rs recs one p)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      nil
    (append (int-mulpow-pc128-step-gadget (car bs) xs rs (car recs) one p)
            (int-mulpow-pc128-loop-gadget (cdr bs) xs (nth 10 (car recs))
                                          (cdr recs) one p))))

(defruled int-mulpow-pc128-loop-sound
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (int-valuep x nil 128) (natp v)
                (int-valuep (expt x v) nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) 128))
                (int-mulpow-pc128-recs-okp bs recs asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc128-loop-gadget bs xs rs recs one p) asg p))
           (and (int-valuep
                 (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                 nil 128)
                (equal (lookup-equal-list (int-mulpow-pw-loop-out bs rs recs) asg)
                       (int->lebits
                        (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                        128))))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-pc128-loop-gadget
                            int-mulpow-pw-loop-out
                            int-mulpow-pc128-recs-okp
                            int-mulpow-msb-val
                            int-mulpow-pc128-rec-okp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pc128-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defund int-pow-checked-unsigned-128-gadget (xs es ps fc mult isneq out r0 recs
                                                one p)
  (declare (xargs :verify-guards nil))
  (b* ((bs (rev es)))
    (append (int-mulpow-pc128-first-gadget (car bs) xs ps fc mult isneq out r0
                                           one p)
            (int-mulpow-pc128-loop-gadget (cdr bs) xs r0 recs one p))))

(defruled int-pow-checked-unsigned-128-gadget-sound
  :short "Unsigned pow_checked (Pow) at 128 bits, variable base and exponent,
          any exponent width."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp r0) (equal (len r0) 128)
                (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pc128-recs-okp (cdr (rev es)) recs asg)
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (bit-listp (lookup-equal-list es asg))
                (r1cs::r1cs-constraints-holdp
                 (int-pow-checked-unsigned-128-gadget xs es ps fc mult isneq out
                                                      r0 recs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-pow-checked-spec x e nil 128) (spec-error)))
                  (equal (lookup-equal-list (int-pow-checked-gadget-out es r0 recs)
                                            asg)
                         (int->lebits (int-pow-checked-spec x e nil 128) 128)))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-first-sound
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pc128-loop-sound
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg)))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-unsigned-128-gadget
                   int-pow-checked-gadget-out
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep)))


(defruled int-mulpow-pc128-sum-when-in-range
  (implies (and (int-valuep a nil 128) (int-valuep b nil 128)
                (int-valuep (* a b) nil 128))
           (equal (int-mul-wrapped-sum a b 128) (* a b)))
  :do-not-induct t
  :use ((:instance int-mulpow-product-split (x a) (y b) (n 128))
        (:instance int-mulpow-pc128-in-range-parts)
        (:instance int-mulpow-pc128-unsigned-facts)
        (:instance int-mulpow-pc128-unsigned-facts (a b)))
  :in-theory (disable int-mulpow-hi int-spec-unsigned int-mul-wrapped-sum
                      int-valuep int-mulpow-pc128-d))

(defruled int-mulpow-pc128-step-complete-wires
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp carry) (equal (len carry) 65)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp rs2) (equal (len rs2) 128)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbolp fz0) (symbolp fz2) (symbolp fm)
                (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg rs2)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg fz0)
                (r1cs::valuation-bindsp asg fz2)
                (r1cs::valuation-bindsp asg fm)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128)
                (int-valuep r nil 128)
                (int-valuep (* r r) nil 128)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* r r x) nil 128))
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits r 128))
                (equal (lookup-equal-list sqs asg) (int->lebits (* r r) 128))
                (equal (lookup-equal z0 asg)
                       (* (int-mulpow-lo r 128) (int-mulpow-lo r 128)))
                (equal (lookup-equal z2 asg)
                       (* (int-mulpow-hi r 128) (int-mulpow-hi r 128)))
                (equal (lookup-equal m asg)
                       (* (+ (int-mulpow-hi r 128) (int-mulpow-lo r 128))
                          (+ (int-mulpow-hi r 128) (int-mulpow-lo r 128))))
                (equal (lookup-equal-list carry asg)
                       (second (int-karatsuba-multiply-spec r r nil 128)))
                (equal (lookup-equal fz0 asg)
                       (* (int-mulpow-lo (* r r) 128) (int-mulpow-lo x 128)))
                (equal (lookup-equal fz2 asg)
                       (* (int-mulpow-hi (* r r) 128) (int-mulpow-hi x 128)))
                (equal (lookup-equal fm asg)
                       (* (+ (int-mulpow-hi (* r r) 128)
                             (int-mulpow-lo (* r r) 128))
                          (+ (int-mulpow-hi x 128) (int-mulpow-lo x 128))))
                (equal (lookup-equal-list ps asg)
                       (int->lebits (int-mul-wrapped-sum (* r r) x 128) 128))
                (equal (lookup-equal-list fc asg)
                       (int->lebits (floor (int-mul-wrapped-sum (* r r) x 128)
                                           (expt 2 128))
                                    65))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* r r x) 128))
                (equal (lookup-equal mult asg)
                       (int-mulpow-pc128-honest-mult (* r r) x))
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* r r x) 128)
                         (int->lebits (* r r) 128))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-any-gadget rs rs z0 z2 m sqs carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-128-gadget sqs xs ps fz0 fz2 fm fc
                                                mult isneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-overflow-gadget isneq e out) asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget e ps sqs rs2 p) asg p)))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-complete
                   (xs rs) (ys rs) (zs sqs) (x r) (y r) (n 128))
        (:instance int-mul-with-flags-128-gadget-complete
                   (as sqs) (bs xs) (a (* r r)) (b x) (n 128))
        (:instance int-mulpow-pc128-sum-when-in-range (a (* r r)) (b x))
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs2)))
  :in-theory (e/d (int-mul-checked-spec bitp
                   int-mulpow-pc-honest-isneq
                   bit-listp-of-int->lebits-explicit
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep int-mulpow-pc128-honest-mult
                   int-mulpow-hi int-mulpow-lo int-mul-wrapped-sum
                   int-karatsuba-multiply-spec
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-128-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc128-rec-honestp (rec x v b asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (expt x v))
       (a (* r r)))
    (and (equal (lookup-equal (nth 0 rec) asg)
                (* (int-mulpow-lo r 128) (int-mulpow-lo r 128)))
         (equal (lookup-equal (nth 1 rec) asg)
                (* (int-mulpow-hi r 128) (int-mulpow-hi r 128)))
         (equal (lookup-equal (nth 2 rec) asg)
                (* (+ (int-mulpow-hi r 128) (int-mulpow-lo r 128))
                   (+ (int-mulpow-hi r 128) (int-mulpow-lo r 128))))
         (equal (lookup-equal-list (nth 3 rec) asg) (int->lebits a 128))
         (equal (lookup-equal-list (nth 4 rec) asg)
                (second (int-karatsuba-multiply-spec r r nil 128)))
         (equal (lookup-equal-list (nth 5 rec) asg)
                (int->lebits (int-mul-wrapped-sum a x 128) 128))
         (equal (lookup-equal (nth 6 rec) asg)
                (* (int-mulpow-lo a 128) (int-mulpow-lo x 128)))
         (equal (lookup-equal (nth 7 rec) asg)
                (* (int-mulpow-hi a 128) (int-mulpow-hi x 128)))
         (equal (lookup-equal (nth 8 rec) asg)
                (* (+ (int-mulpow-hi a 128) (int-mulpow-lo a 128))
                   (+ (int-mulpow-hi x 128) (int-mulpow-lo x 128))))
         (equal (lookup-equal-list (nth 9 rec) asg)
                (int->lebits (floor (int-mul-wrapped-sum a x 128)
                                    (expt 2 128))
                             65))
         (equal (lookup-equal-list (nth 10 rec) asg)
                (int->lebits (expt x (+ (* 2 v) b)) 128))
         (equal (lookup-equal (nth 11 rec) asg)
                (int-mulpow-pc128-honest-mult a x))
         (equal (lookup-equal (nth 12 rec) asg)
                (int-mulpow-pc-honest-isneq (* a x) 128))
         (equal (lookup-equal (nth 13 rec) asg) 0))))

(defruled int-mulpow-pc128-step-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128) (natp v)
                (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) 128))
                (int-mulpow-pc128-rec-okp rec asg)
                (int-mulpow-pc128-rec-honestp rec x v (lookup-equal e asg) asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc128-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-step-complete-wires
                   (z0 (nth 0 rec)) (z2 (nth 1 rec)) (m (nth 2 rec))
                   (sqs (nth 3 rec)) (carry (nth 4 rec))
                   (ps (nth 5 rec)) (fz0 (nth 6 rec)) (fz2 (nth 7 rec))
                   (fm (nth 8 rec)) (fc (nth 9 rec)) (rs2 (nth 10 rec))
                   (mult (nth 11 rec)) (isneq (nth 12 rec)) (out (nth 13 rec))
                   (r (expt x v)))
        (:instance int-mulpow-pc-range-step (b (lookup-equal e asg)) (n 128))
        (:instance int-mulpow-pc-rs2-form (b (lookup-equal e asg)) (n 128)))
  :in-theory (e/d (int-mulpow-pc128-step-gadget
                   int-mulpow-pc128-rec-okp
                   int-mulpow-pc128-rec-honestp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pc-integerp-when-int-valuep
                   bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-pc-honest-isneq int-mulpow-pc128-honest-mult
                   int-mulpow-hi int-mulpow-lo int-mul-wrapped-sum
                   int-karatsuba-multiply-spec
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-128-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc128-recs-honestp (bs recs x v asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pc128-rec-honestp (car recs) x v (lookup-equal (car bs) asg)
                                       asg)
         (int-mulpow-pc128-recs-honestp (cdr bs) (cdr recs) x
                                        (+ (* 2 v) (lookup-equal (car bs) asg))
                                        asg))))

(defruled int-mulpow-pc128-rec-honestp-out
  (implies (int-mulpow-pc128-rec-honestp rec x v b asg)
           (equal (lookup-equal-list (nth 10 rec) asg)
                  (int->lebits (expt x (+ (* 2 v) b)) 128)))
  :enable int-mulpow-pc128-rec-honestp)

(defruled int-mulpow-pc128-step-complete-bounded
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil 128) (natp v) (natp ee)
                (<= (+ (* 2 v) (lookup-equal e asg)) ee)
                (int-valuep (expt x ee) nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) 128))
                (int-mulpow-pc128-rec-okp rec asg)
                (int-mulpow-pc128-rec-honestp rec x v (lookup-equal e asg) asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc128-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-step-complete)
        (:instance int-mulpow-pc-range-mono
                   (a (+ (* 2 v) (lookup-equal e asg))) (b ee) (n 128)))
  :in-theory (e/d (int-mulpow-pc-natp-when-unsigned bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-pc128-step-gadget int-mulpow-pc128-rec-okp
                   int-mulpow-pc128-rec-honestp)))

(defruled int-mulpow-pc128-loop-complete
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (int-valuep x nil 128) (natp v) (natp ee)
                (<= (int-mulpow-msb-val (lookup-equal-list bs asg) v) ee)
                (int-valuep (expt x ee) nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) 128))
                (int-mulpow-pc128-recs-okp bs recs asg)
                (int-mulpow-pc128-recs-honestp bs recs x v asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc128-loop-gadget bs xs rs recs one p) asg p))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-pc128-loop-gadget
                            int-mulpow-pc128-recs-okp
                            int-mulpow-pc128-recs-honestp
                            int-mulpow-msb-val
                            int-mulpow-pc128-rec-okp-out
                            int-mulpow-pc128-rec-honestp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pc128-step-complete-bounded
                                  (e (car bs)) (rec (car recs)))
                       (:instance int-mulpow-msb-val-ge
                                  (bs (cdr (lookup-equal-list bs asg)))
                                  (v (+ (* 2 v) (lookup-equal (car bs) asg)))))))))

(defruled int-pow-checked-unsigned-128-gadget-complete
  :short "Unsigned pow_checked (Pow) at 128 bits, variable base and exponent,
          any exponent width."
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (equal (len xs) 128)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbol-listp r0) (equal (len r0) 128)
                (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pc128-recs-okp (cdr (rev es)) recs asg)
                (int-valuep x nil 128)
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (bit-listp (lookup-equal-list es asg))
                (not (equal (int-pow-checked-spec
                             x (lebits=>nat (lookup-equal-list es asg)) nil 128)
                            (spec-error)))
                (equal (lookup-equal-list ps asg) (int->lebits x 128))
                (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list r0 asg)
                       (int->lebits (expt x (lookup-equal (car (rev es)) asg))
                                    128))
                (int-mulpow-pc128-recs-honestp (cdr (rev es)) recs x
                                               (lookup-equal (car (rev es)) asg)
                                               asg))
           (r1cs::r1cs-constraints-holdp
            (int-pow-checked-unsigned-128-gadget xs es ps fc mult isneq out r0
                                                 recs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc128-first-complete
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pc128-loop-complete
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg))
                   (ee (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-unsigned-128-gadget
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep)))
