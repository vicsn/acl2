; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unsigned PowChecked::pow_checked (also Pow::pow) with variable base and
; variable exponent, widths 8 to 64, any exponent width
; (snarkVM circuit/types/integers/src/pow_checked.rs):
;
;   result = 1 (constant)
;   for bit in exponent.bits_le.rev():
;     result = result.mul_checked(result)
;     (product, overflow) = mul_with_flags(result, self)
;     assert_eq(overflow & bit, 0)
;     result = ternary(bit, product, result)
;
; For 2n < 252, mul_with_flags witnesses the n product bits (boolean
; checked), computes the field product w of the operands, and returns
; is_not_equal(w, product): delta * mult = is_neq and delta * (1 - is_neq)
; = 0, with is_neq not boolean checked (the two constraints force it to be
; 0 or 1).  int-mul-with-flags-gadget-sound proves only the weaker guarantee
; that pow_checked relies on: the flag is a bit, and flag = 0 implies the
; product is in range and its bits are correct.
;
; The first iteration is constant-folded by snarkVM: 1 * 1 is a constant,
; and mul_with_flags(1, self) has computed product the linear combination of
; the bits of self, so only the witnessed bits and the is_not_equal remain.
; The ternary against the constant 1 is !e | p_0 for bit 0 and e & p_i for
; the other bits, as in pow_wrapped.
;
; The 128-bit case (Karatsuba flag), the signed case (abs_wrapped, sign
; logic, conditional negation) and constant operands are not covered here.

(in-package "ALEOVM")

(include-book "int-mulpow-pow-wrapped")
(include-book "int-mulpow-checked")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lookup-equal-list"))
(local (include-book "../library-extensions/r1cses"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund int-mulpow-pc-neq-gadget (delta mult isneq one p)
  (declare (xargs :verify-guards nil))
  (list (r1cs::make-r1cs-constraint
         :a delta
         :b (list (list 1 mult))
         :c (list (list 1 isneq)))
        (r1cs::make-r1cs-constraint
         :a delta
         :b (list (list 1 one) (list (1- p) isneq))
         :c nil)))

(defruled int-mulpow-pc-neq-sound
  (implies (and (primep p)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-neq-gadget delta mult isneq one p) asg p))
           (equal (lookup-equal isneq asg)
                  (if (equal (r1cs::dot-product delta asg p) 0) 0 1)))
  :do-not-induct t
  :expand ((r1cs::dot-product (list (list 1 mult)) asg p)
           (r1cs::dot-product (list (list 1 isneq)) asg p)
           (r1cs::dot-product (list (list 1 one) (list (1- p) isneq)) asg p)
           (r1cs::dot-product (list (list (1- p) isneq)) asg p)
           (r1cs::dot-product nil asg p))
  :enable (int-mulpow-pc-neq-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp))

(defruled int-mulpow-pc-neq-complete
  (implies (and (primep p)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal isneq asg)
                       (if (equal (r1cs::dot-product delta asg p) 0) 0 1))
                (equal (lookup-equal mult asg)
                       (if (equal (r1cs::dot-product delta asg p) 0)
                           1
                         (pfield::inv (r1cs::dot-product delta asg p) p))))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-neq-gadget delta mult isneq one p) asg p))
  :do-not-induct t
  :expand ((r1cs::dot-product (list (list 1 mult)) asg p)
           (r1cs::dot-product (list (list 1 isneq)) asg p)
           (r1cs::dot-product (list (list 1 one) (list (1- p) isneq)) asg p)
           (r1cs::dot-product (list (list (1- p) isneq)) asg p)
           (r1cs::dot-product nil asg p))
  :enable (int-mulpow-pc-neq-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp))

(defruled int-mulpow-pc-delta-zero-iff
  (implies (and (primep p)
                (natp u) (< u p)
                (natp v) (< v p))
           (equal (equal (mod (+ u (- v)) p) 0)
                  (equal u v)))
  :cases ((<= v u))
  :use ((:instance acl2::mod-when-< (x (+ u (- v))) (y p))
        (:instance acl2::mod-when-< (x (+ p u (- v))) (y p))
        (:instance acl2::mod-of-+-same-arg1 (x (+ u (- v))) (y p)))
  :in-theory (disable acl2::mod-of-+-same-arg1 acl2::mod-when-<))

(defruled int-mulpow-pc-delta-w
  (implies (and (primep p)
                (symbolp w) (symbol-listp ps)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg ps)
                (bit-listp (lookup-equal-list ps asg))
                (< (lebits=>nat (lookup-equal-list ps asg)) p))
           (equal (equal (r1cs::dot-product
                          (cons (list 1 w) (pow2sum-neg-vector ps 0)) asg p)
                         0)
                  (equal (lookup-equal w asg)
                         (lebits=>nat (lookup-equal-list ps asg)))))
  :do-not-induct t
  :expand ((r1cs::dot-product (cons (list 1 w) (pow2sum-neg-vector ps 0)) asg p))
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs ps) (i 0))
        (:instance int-mulpow-pc-delta-zero-iff
                   (u (lookup-equal w asg))
                   (v (lebits=>nat (lookup-equal-list ps asg)))))
  :enable (pfield::add pfield::mul acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-+-of-mod-arg1))

(defruled int-mulpow-pc-delta-xs
  (implies (and (primep p)
                (symbol-listp xs) (symbol-listp ps)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ps asg))
                (< (lebits=>nat (lookup-equal-list xs asg)) p)
                (< (lebits=>nat (lookup-equal-list ps asg)) p))
           (equal (equal (r1cs::dot-product
                          (append (pow2sum-vector xs 0) (pow2sum-neg-vector ps 0))
                          asg p)
                         0)
                  (equal (lebits=>nat (lookup-equal-list xs asg))
                         (lebits=>nat (lookup-equal-list ps asg)))))
  :do-not-induct t
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs ps) (i 0))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat (i 0))
        (:instance int-mulpow-pc-delta-zero-iff
                   (u (lebits=>nat (lookup-equal-list xs asg)))
                   (v (lebits=>nat (lookup-equal-list ps asg)))))
  :enable (r1cs::dot-product-of-append
           pfield::add acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-+-of-mod-arg1 acl2::mod-when-<))

;; mul_with_flags for 2n < 252, variable operands: witnessed product bits,
;; field product w, and is_not_equal(w, product).
(defund int-mul-with-flags-gadget (as bs ps w mult isneq one p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list ps p)
          (bits-mul-field-gadget as bs w p)
          (int-mulpow-pc-neq-gadget (cons (list 1 w) (pow2sum-neg-vector ps 0))
                                    mult isneq one p)))

(defruled int-mulpow-pc-width-small
  (implies (and (integer-widthp n) (not (equal n 128)))
           (and (posp n) (< (* 2 n) 252)))
  :enable integer-widthp)

(defruled int-mul-with-flags-gadget-sound
  :short "The weaker guarantee: the flag is a bit, and flag = 0 implies
          that the product is in range and the product bits are correct."
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp as) (equal (len as) n)
                (symbol-listp bs) (equal (len bs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbolp w) (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil n) (int-valuep b nil n)
                (equal (lookup-equal-list as asg) (int->lebits a n))
                (equal (lookup-equal-list bs asg) (int->lebits b n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-gadget as bs ps w mult isneq one p) asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (and (int-valuep (* a b) nil n)
                              (equal (lookup-equal-list ps asg)
                                     (int->lebits (* a b) n))))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-width-small)
        (:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance bits-mul-field-gadget-to-equal-of-mul
                   (xs as) (ys bs) (z w))
        (:instance int-mulpow-pc-neq-sound
                   (delta (cons (list 1 w) (pow2sum-neg-vector ps 0))))
        (:instance int-mulpow-pc-delta-w)
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-pw-first-ps
                   (x (* a b)) (a (lookup-equal-list ps asg)) (b nil)))
  :in-theory (e/d (int-mul-with-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   integer-length-of-base-prime
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits)))

(defund int-mulpow-pc-assert-zero (z)
  (declare (xargs :verify-guards nil))
  (r1cs::make-r1cs-constraint :a (list (list 1 z))
                              :b (list (list 1 1))
                              :c nil))

(defruled int-mulpow-pc-assert-zero-iff
  (implies (and (primep p) (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraint-holdsp (int-mulpow-pc-assert-zero z) asg p)
                  (equal (lookup-equal z asg) 0)))
  :expand ((r1cs::dot-product (list (list 1 z)) asg p)
           (r1cs::dot-product (list (list 1 1)) asg p)
           (r1cs::dot-product nil asg p))
  :enable (int-mulpow-pc-assert-zero r1cs::r1cs-constraint-holdsp))

;; The overflow assertion assert_eq(flag & bit, 0).
(defund int-mulpow-pc-overflow-gadget (isneq e out)
  (declare (xargs :verify-guards nil))
  (append (boolean-and-gadget isneq e out)
          (list (int-mulpow-pc-assert-zero out))))

(defruled int-mulpow-pc-overflow-iff
  (implies (and (primep p) (symbolp isneq) (symbolp e) (symbolp out)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal isneq asg))
                (bitp (lookup-equal e asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-pc-overflow-gadget isneq e out) asg p)
                  (and (equal (lookup-equal out asg) 0)
                       (not (and (equal (lookup-equal isneq asg) 1)
                                 (equal (lookup-equal e asg) 1))))))
  :use (:instance boolean-and-gadget-to-bitand (x isneq) (y e) (z out))
  :enable (int-mulpow-pc-overflow-gadget
           r1cs::r1cs-constraints-holdp-of-append
           int-mulpow-pw-holdp-of-singleton
           int-mulpow-pc-assert-zero-iff
           bitand bitp))

(defund int-mulpow-pc-first-flags-gadget (xs ps mult isneq one p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list ps p)
          (int-mulpow-pc-neq-gadget
           (append (pow2sum-vector xs 0) (pow2sum-neg-vector ps 0))
           mult isneq one p)))

(defruled int-mulpow-pc-first-flags-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-first-flags-gadget xs ps mult isneq one p) asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (equal (lookup-equal-list ps asg)
                                (int->lebits x n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-width-mul-wrapped-fits)
        (:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance int-mulpow-pc-neq-sound
                   (delta (append (pow2sum-vector xs 0) (pow2sum-neg-vector ps 0))))
        (:instance int-mulpow-pc-delta-xs)
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list ps asg)))
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list xs asg)))
        (:instance lebits=>nat-of-int->lebits)
        (:instance int-mulpow-pw-first-ps
                   (a (lookup-equal-list ps asg)) (b nil)))
  :in-theory (e/d (int-mulpow-pc-first-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   integer-length-of-base-prime
                   posp-when-integer-widthp)
                  (int->lebits lebits=>nat-of-int->lebits)))

(defund int-mulpow-pc-first-gadget (e xs ps mult isneq out rs one p)
  (declare (xargs :verify-guards nil))
  (append (int-mulpow-pc-first-flags-gadget xs ps mult isneq one p)
          (int-mulpow-pc-overflow-gadget isneq e out)
          (boolean-or-notleft-gadget e (car ps) (car rs) one p)
          (int-mulpow-pw-and-list e (cdr ps) (cdr rs))))

(defruled int-mulpow-pc-first-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-first-gadget e xs ps mult isneq out rs one p)
                 asg p))
           (and (int-valuep (expt x (lookup-equal e asg)) nil n)
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) n))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-first-flags-sound)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance int-mulpow-pw-first-rs-sound)
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pc-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

; A pow_checked loop iteration record is the list of wires
;   (z0 z2 m sqs carry ps w mult isneq out rs)
; of the checked squaring, mul_with_flags, the overflow assertion, and the
; selected result.

(defund int-mulpow-pc-rec-okp (rec n asg)
  (declare (xargs :verify-guards nil))
  (and (true-listp rec)
       (equal (len rec) 11)
       (symbolp (nth 0 rec)) (symbolp (nth 1 rec)) (symbolp (nth 2 rec))
       (symbol-listp (nth 3 rec)) (symbol-listp (nth 4 rec))
       (symbol-listp (nth 5 rec))
       (symbolp (nth 6 rec)) (symbolp (nth 7 rec)) (symbolp (nth 8 rec))
       (symbolp (nth 9 rec))
       (symbol-listp (nth 10 rec))
       (equal (len (nth 3 rec)) n)
       (equal (len (nth 4 rec)) (1+ (floor n 2)))
       (equal (len (nth 5 rec)) n)
       (equal (len (nth 10 rec)) n)
       (r1cs::valuation-bindsp asg (nth 0 rec))
       (r1cs::valuation-bindsp asg (nth 1 rec))
       (r1cs::valuation-bindsp asg (nth 2 rec))
       (r1cs::valuation-binds-allp asg (nth 3 rec))
       (r1cs::valuation-binds-allp asg (nth 4 rec))
       (r1cs::valuation-binds-allp asg (nth 5 rec))
       (r1cs::valuation-bindsp asg (nth 6 rec))
       (r1cs::valuation-bindsp asg (nth 7 rec))
       (r1cs::valuation-bindsp asg (nth 8 rec))
       (r1cs::valuation-bindsp asg (nth 9 rec))
       (r1cs::valuation-binds-allp asg (nth 10 rec))))

(defruled int-mulpow-pc-rec-okp-out
  (implies (int-mulpow-pc-rec-okp rec n asg)
           (and (symbol-listp (nth 10 rec))
                (equal (len (nth 10 rec)) n)
                (r1cs::valuation-binds-allp asg (nth 10 rec))))
  :enable int-mulpow-pc-rec-okp)

(defund int-mulpow-pc-step-gadget (e xs rs rec one p)
  (declare (xargs :verify-guards nil))
  (append (int-mul-checked-unsigned-any-gadget rs rs (nth 0 rec) (nth 1 rec)
                                               (nth 2 rec) (nth 3 rec)
                                               (nth 4 rec) p)
          (int-mul-with-flags-gadget (nth 3 rec) xs (nth 5 rec) (nth 6 rec)
                                     (nth 7 rec) (nth 8 rec) one p)
          (int-mulpow-pc-overflow-gadget (nth 8 rec) e (nth 9 rec))
          (integer-ternary-gadget e (nth 5 rec) (nth 3 rec) (nth 10 rec) p)))

(defruled int-mulpow-pc-integerp-when-int-valuep
  (implies (int-valuep x signedp n) (integerp x))
  :rule-classes :forward-chaining
  :enable int-valuep)

(defruled int-mulpow-pc-step-sound-wires
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp sqs) (equal (len sqs) n)
                (symbol-listp carry) (equal (len carry) (1+ (floor n 2)))
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp rs2) (equal (len rs2) n)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbolp w) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs2)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n)
                (int-valuep r nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits r n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-any-gadget rs rs z0 z2 m sqs carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-gadget sqs xs ps w mult isneq one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-overflow-gadget isneq e out) asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget e ps sqs rs2 p) asg p))
           (and (int-valuep (* r r) nil n)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* r r x) nil n))
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* r r x) n)
                         (int->lebits (* r r) n)))))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-sound
                   (xs rs) (ys rs) (zs sqs) (x r) (y r))
        (:instance int-mul-with-flags-gadget-sound
                   (as sqs) (bs xs) (a (* r r)) (b x))
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs2)))
  :in-theory (e/d (int-mul-checked-spec bitp
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defruled int-mulpow-pc-step-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n) (natp v)
                (int-valuep (expt x v) nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pc-rec-okp rec n asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-step-gadget e xs rs rec one p) asg p))
           (and (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) nil n)
                (equal (lookup-equal-list (nth 10 rec) asg)
                       (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg)))
                                    n))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-step-sound-wires
                   (z0 (nth 0 rec)) (z2 (nth 1 rec)) (m (nth 2 rec))
                   (sqs (nth 3 rec)) (carry (nth 4 rec))
                   (ps (nth 5 rec)) (w (nth 6 rec)) (mult (nth 7 rec))
                   (isneq (nth 8 rec)) (out (nth 9 rec)) (rs2 (nth 10 rec))
                   (r (expt x v)))
        (:instance int-mulpow-pw-expt-step (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-pc-step-gadget
                   int-mulpow-pc-rec-okp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pc-integerp-when-int-valuep
                   bitp)
                  (int->lebits int-valuep expt
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc-recs-okp (bs recs n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pc-rec-okp (car recs) n asg)
         (int-mulpow-pc-recs-okp (cdr bs) (cdr recs) n asg))))

(defund int-mulpow-pc-loop-gadget (bs xs rs recs one p)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      nil
    (append (int-mulpow-pc-step-gadget (car bs) xs rs (car recs) one p)
            (int-mulpow-pc-loop-gadget (cdr bs) xs (nth 10 (car recs))
                                       (cdr recs) one p))))

(defruled int-mulpow-pc-loop-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (int-valuep x nil n) (natp v)
                (int-valuep (expt x v) nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pc-recs-okp bs recs n asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-loop-gadget bs xs rs recs one p) asg p))
           (and (int-valuep
                 (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                 nil n)
                (equal (lookup-equal-list (int-mulpow-pw-loop-out bs rs recs) asg)
                       (int->lebits
                        (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                        n))))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-pc-loop-gadget
                            int-mulpow-pw-loop-out
                            int-mulpow-pc-recs-okp
                            int-mulpow-msb-val
                            int-mulpow-pc-rec-okp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pc-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defund int-pow-checked-unsigned-gadget (xs es ps mult isneq out r0 recs one p)
  (declare (xargs :verify-guards nil))
  (b* ((bs (rev es)))
    (append (int-mulpow-pc-first-gadget (car bs) xs ps mult isneq out r0 one p)
            (int-mulpow-pc-loop-gadget (cdr bs) xs r0 recs one p))))

(defund int-pow-checked-gadget-out (es r0 recs)
  (declare (xargs :verify-guards nil))
  (int-mulpow-pw-loop-out (cdr (rev es)) r0 recs))

(defruled int-pow-checked-unsigned-gadget-sound
  :short "Unsigned pow_checked (Pow), variable base and exponent,
          widths 8 to 64, any exponent width."
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp r0) (equal (len r0) n)
                (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pc-recs-okp (cdr (rev es)) recs n asg)
                (int-valuep x nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (bit-listp (lookup-equal-list es asg))
                (r1cs::r1cs-constraints-holdp
                 (int-pow-checked-unsigned-gadget xs es ps mult isneq out r0
                                                  recs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-pow-checked-spec x e nil n) (spec-error)))
                  (equal (lookup-equal-list (int-pow-checked-gadget-out es r0 recs)
                                            asg)
                         (int->lebits (int-pow-checked-spec x e nil n) n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-first-sound
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pc-loop-sound
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg)))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-unsigned-gadget
                   int-pow-checked-gadget-out
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep)))

(defruled int-mulpow-pc-range-mono
  (implies (and (natp x) (natp a) (natp b) (<= a b) (posp n)
                (int-valuep (expt x b) nil n))
           (int-valuep (expt x a) nil n))
  :cases ((equal x 0))
  :use ((:instance acl2::<=-of-expt-and-expt-same-base-linear
                   (r x) (i1 a) (i2 b)))
  :enable (int-valuep int-min int-max))

(defruled int-mulpow-msb-val-ge
  (implies (and (bit-listp bs) (natp v))
           (<= v (int-mulpow-msb-val bs v)))
  :induct (int-mulpow-msb-val bs v)
  :enable int-mulpow-msb-val)

(defruled int-mulpow-pc-delta-w-value
  (implies (and (primep p)
                (symbolp w) (symbol-listp ps)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg ps)
                (bit-listp (lookup-equal-list ps asg)))
           (equal (r1cs::dot-product
                   (cons (list 1 w) (pow2sum-neg-vector ps 0)) asg p)
                  (mod (+ (lookup-equal w asg)
                          (- (lebits=>nat (lookup-equal-list ps asg))))
                       p)))
  :do-not-induct t
  :expand ((r1cs::dot-product (cons (list 1 w) (pow2sum-neg-vector ps 0)) asg p))
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs ps) (i 0)))
  :enable (pfield::add pfield::mul acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-+-of-mod-arg1))

(defun int-mulpow-pc-honest-mult (z n)
  (declare (xargs :verify-guards nil))
  (if (int-valuep z nil n)
      1
    (pfield::inv (mod (- z (mod z (expt 2 n))) (base-prime)) (base-prime))))

(defun int-mulpow-pc-honest-isneq (z n)
  (declare (xargs :verify-guards nil))
  (if (int-valuep z nil n) 0 1))

(defruled int-mulpow-pc-product-bound
  (implies (and (int-valuep a nil n) (int-valuep b nil n)
                (integer-widthp n) (not (equal n 128)))
           (and (<= 0 (* a b))
                (< (* a b) (base-prime))))
  :do-not-induct t
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
  :use ((:instance int-mulpow-times-mono
                   (x a) (y b) (a (1- (expt 2 n))) (b (1- (expt 2 n)))))
  :enable (int-valuep int-min int-max integer-widthp))

(defruled int-mul-with-flags-gadget-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp as) (equal (len as) n)
                (symbol-listp bs) (equal (len bs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbolp w) (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil n) (int-valuep b nil n)
                (equal (lookup-equal-list as asg) (int->lebits a n))
                (equal (lookup-equal-list bs asg) (int->lebits b n))
                (equal (lookup-equal-list ps asg) (int->lebits (* a b) n))
                (equal (lookup-equal w asg) (* a b))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* a b) n))
                (equal (lookup-equal mult asg)
                       (int-mulpow-pc-honest-mult (* a b) n)))
           (r1cs::r1cs-constraints-holdp
            (int-mul-with-flags-gadget as bs ps w mult isneq one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-width-small)
        (:instance int-mulpow-pc-product-bound)
        (:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance bits-mul-field-gadget-to-equal-of-mul
                   (xs as) (ys bs) (z w))
        (:instance int-mulpow-pc-neq-complete
                   (delta (cons (list 1 w) (pow2sum-neg-vector ps 0))))
        (:instance int-mulpow-pc-delta-w-value)
        (:instance int-mulpow-pc-delta-zero-iff
                   (u (* a b)) (v (mod (* a b) (expt 2 n)))))
  :in-theory (e/d (int-mul-with-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits)))

(defruled int-mulpow-pc-first-flags-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-first-flags-gadget xs ps mult isneq one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-width-mul-wrapped-fits)
        (:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance int-mulpow-pc-neq-complete
                   (delta (append (pow2sum-vector xs 0) (pow2sum-neg-vector ps 0))))
        (:instance int-mulpow-pc-delta-xs)
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list ps asg))))
  :in-theory (e/d (int-mulpow-pc-first-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   integer-length-of-base-prime
                   posp-when-integer-widthp)
                  (int->lebits)))

(defruled int-mulpow-pc-first-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) n)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-first-gadget e xs ps mult isneq out rs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-first-flags-complete)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance int-mulpow-pw-first-rs-complete)
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pc-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

(defruled int-mulpow-pc-step-complete-wires
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp sqs) (equal (len sqs) n)
                (symbol-listp carry) (equal (len carry) (1+ (floor n 2)))
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp rs2) (equal (len rs2) n)
                (symbolp z0) (symbolp z2) (symbolp m)
                (symbolp w) (symbolp mult) (symbolp isneq) (symbolp out)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs2)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n)
                (int-valuep r nil n)
                (int-valuep (* r r) nil n)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* r r x) nil n))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits r n))
                (equal (lookup-equal-list sqs asg) (int->lebits (* r r) n))
                (equal (lookup-equal-list ps asg) (int->lebits (* r r x) n))
                (equal (lookup-equal w asg) (* r r x))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* r r x) n))
                (equal (lookup-equal mult asg)
                       (int-mulpow-pc-honest-mult (* r r x) n))
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* r r x) n)
                         (int->lebits (* r r) n))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-any-gadget rs rs z0 z2 m sqs carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-gadget sqs xs ps w mult isneq one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-overflow-gadget isneq e out) asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget e ps sqs rs2 p) asg p)))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-complete
                   (xs rs) (ys rs) (zs sqs) (x r) (y r))
        (:instance int-mul-with-flags-gadget-complete
                   (as sqs) (bs xs) (a (* r r)) (b x))
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs2)))
  :in-theory (e/d (int-mul-checked-spec bitp
                   int-mulpow-pc-honest-isneq
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep int-mulpow-pc-honest-mult
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc-rec-honestp (rec x v b n asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (expt x v)))
    (and (equal (lookup-equal-list (nth 3 rec) asg) (int->lebits (* r r) n))
         (equal (lookup-equal-list (nth 5 rec) asg) (int->lebits (* r r x) n))
         (equal (lookup-equal (nth 6 rec) asg) (* r r x))
         (equal (lookup-equal (nth 7 rec) asg)
                (int-mulpow-pc-honest-mult (* r r x) n))
         (equal (lookup-equal (nth 8 rec) asg)
                (int-mulpow-pc-honest-isneq (* r r x) n))
         (equal (lookup-equal (nth 9 rec) asg) 0)
         (equal (lookup-equal-list (nth 10 rec) asg)
                (int->lebits (expt x (+ (* 2 v) b)) n)))))

(defruled int-mulpow-pc-natp-when-unsigned
  (implies (int-valuep x nil n) (natp x))
  :rule-classes :forward-chaining
  :enable (int-valuep int-min))

(defruled int-mulpow-pc-range-step
  (implies (and (int-valuep x nil n) (natp v) (bitp b) (posp n)
                (int-valuep (expt x (+ (* 2 v) b)) nil n))
           (and (int-valuep (expt x v) nil n)
                (int-valuep (* (expt x v) (expt x v)) nil n)
                (implies (equal b 1)
                         (int-valuep (* (expt x v) (expt x v) x) nil n))))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-expt-step)
        (:instance int-mulpow-pw-expt-step (b 0))
        (:instance int-mulpow-pc-range-mono (a v) (b (+ (* 2 v) b)))
        (:instance int-mulpow-pc-range-mono (a (* 2 v)) (b (+ (* 2 v) b))))
  :in-theory (e/d (int-mulpow-pc-integerp-when-int-valuep
                   int-mulpow-pc-natp-when-unsigned bitp)
                  (int-valuep expt))
  :otf-flg t)

(defruled int-mulpow-pc-rs2-form
  (implies (and (integerp x) (natp v) (bitp b))
           (equal (int->lebits (expt x (+ (* 2 v) b)) n)
                  (if (equal b 1)
                      (int->lebits (* (expt x v) (expt x v) x) n)
                    (int->lebits (* (expt x v) (expt x v)) n))))
  :use int-mulpow-pw-expt-step
  :in-theory (e/d (bitp) (int->lebits expt)))

(defruled int-mulpow-pc-step-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n) (natp v)
                (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pc-rec-okp rec n asg)
                (int-mulpow-pc-rec-honestp rec x v (lookup-equal e asg) n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-step-complete-wires
                   (z0 (nth 0 rec)) (z2 (nth 1 rec)) (m (nth 2 rec))
                   (sqs (nth 3 rec)) (carry (nth 4 rec))
                   (ps (nth 5 rec)) (w (nth 6 rec)) (mult (nth 7 rec))
                   (isneq (nth 8 rec)) (out (nth 9 rec)) (rs2 (nth 10 rec))
                   (r (expt x v)))
        (:instance int-mulpow-pc-range-step (b (lookup-equal e asg)))
        (:instance int-mulpow-pc-rs2-form (b (lookup-equal e asg)))
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pc-step-gadget
                   int-mulpow-pc-rec-okp
                   int-mulpow-pc-rec-honestp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pc-integerp-when-int-valuep
                   bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-pc-honest-isneq int-mulpow-pc-honest-mult
                   int-mul-checked-unsigned-any-gadget
                   int-mul-with-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defund int-mulpow-pc-recs-honestp (bs recs x v n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pc-rec-honestp (car recs) x v (lookup-equal (car bs) asg)
                                    n asg)
         (int-mulpow-pc-recs-honestp (cdr bs) (cdr recs) x
                                     (+ (* 2 v) (lookup-equal (car bs) asg))
                                     n asg))))

(defruled int-mulpow-pc-rec-honestp-out
  (implies (int-mulpow-pc-rec-honestp rec x v b n asg)
           (equal (lookup-equal-list (nth 10 rec) asg)
                  (int->lebits (expt x (+ (* 2 v) b)) n)))
  :enable int-mulpow-pc-rec-honestp)

(defruled int-mulpow-pc-step-complete-bounded
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (int-valuep x nil n) (natp v) (natp ee)
                (<= (+ (* 2 v) (lookup-equal e asg)) ee)
                (int-valuep (expt x ee) nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pc-rec-okp rec n asg)
                (int-mulpow-pc-rec-honestp rec x v (lookup-equal e asg) n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-step-complete)
        (:instance int-mulpow-pc-range-mono
                   (a (+ (* 2 v) (lookup-equal e asg))) (b ee))
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pc-natp-when-unsigned bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-pc-step-gadget int-mulpow-pc-rec-okp
                   int-mulpow-pc-rec-honestp)))

(defruled int-mulpow-pc-loop-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (int-valuep x nil n) (natp v) (natp ee)
                (<= (int-mulpow-msb-val (lookup-equal-list bs asg) v) ee)
                (int-valuep (expt x ee) nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pc-recs-okp bs recs n asg)
                (int-mulpow-pc-recs-honestp bs recs x v n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pc-loop-gadget bs xs rs recs one p) asg p))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-pc-loop-gadget
                            int-mulpow-pc-recs-okp
                            int-mulpow-pc-recs-honestp
                            int-mulpow-msb-val
                            int-mulpow-pc-rec-okp-out
                            int-mulpow-pc-rec-honestp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pc-step-complete-bounded
                                  (e (car bs)) (rec (car recs)))
                       (:instance int-mulpow-msb-val-ge
                                  (bs (cdr (lookup-equal-list bs asg)))
                                  (v (+ (* 2 v) (lookup-equal (car bs) asg)))))))))

(defruled int-pow-checked-unsigned-gadget-complete
  :short "Unsigned pow_checked (Pow), variable base and exponent,
          widths 8 to 64, any exponent width."
  (implies (and (equal p (base-prime))
                (integer-widthp n) (not (equal n 128))
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp r0) (equal (len r0) n)
                (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pc-recs-okp (cdr (rev es)) recs n asg)
                (int-valuep x nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (bit-listp (lookup-equal-list es asg))
                (not (equal (int-pow-checked-spec
                             x (lebits=>nat (lookup-equal-list es asg)) nil n)
                            (spec-error)))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list r0 asg)
                       (int->lebits (expt x (lookup-equal (car (rev es)) asg)) n))
                (int-mulpow-pc-recs-honestp (cdr (rev es)) recs x
                                            (lookup-equal (car (rev es)) asg)
                                            n asg))
           (r1cs::r1cs-constraints-holdp
            (int-pow-checked-unsigned-gadget xs es ps mult isneq out r0
                                             recs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pc-first-complete
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pc-loop-complete
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg))
                   (ee (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-unsigned-gadget
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep)))
