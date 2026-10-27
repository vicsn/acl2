;; AleoVM Library
;;
;; Copyright (C) 2026 Provable Inc.
;;
;; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed PowChecked::pow_checked (also Pow::pow), every width 8 to 128,
; variable base and variable exponent, any exponent width
; (snarkVM circuit/types/integers/src/pow_checked.rs).
;
; Each loop iteration is
;   result = result.mul_checked(result)            (signed mul_checked)
;   (product, flag) = mul_with_flags(|result|, |self|)  (abs_wrapped both)
;   s = msb(result) xor msb(self)                   (not operands_same_sign)
;   overflow = flag | (!s & msb(product))
;            | (s & !(!msb(product) | (msb(product) & !lower_nonzero)))
;   assert(overflow & bit = 0)
;   result_times_self = s ? (!product).add_wrapped(1) : product
;   result = ternary(bit, result_times_self, result)
; int-mulpow-sp-times-gadget models everything after the squaring and
; int-mulpow-sp-step-gadget adds the squaring and the ternary; a step record
; (46 wires, output at index 10) is checked by int-mulpow-sp-rec-okp.  The
; first iteration is constant-folded (result = 1): abs(1) is the constant 1,
; mul_with_flags(1, |self|) is the first-iteration flags gadget of the
; unsigned proofs, operands_same_sign = !msb(self), and the ternary against
; the constant 1 is as in pow_wrapped.
;
; The is_equal of the two sign bits is modelled by an xor wire s (the gadget
; uses its negation linearly), and (!product).add_wrapped(1) by n+1 boolean
; wires constrained by one linear equation, 2^n - product = sum of 2^i bits.
;
; int-pow-checked-signed-gadget-sound: the constraints imply the result is in
; range and the output bits are x^e.  int-pow-checked-signed-gadget-complete:
; when x^e is in range the honest witnesses satisfy the constraints; the
; intermediate powers are then in range by int-mulpow-sp-range-mono.

(in-package "ALEOVM")

(include-book "int-mulpow-pow-checked-128")
(include-book "int-mulpow-signed-checked")
(include-book "int-mulpow-checked")
(include-book "int-mulpow-karatsuba")
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "../r1cs/integer-ternary")
(include-book "../r1cs/boolean-or-notleft")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum-vectors")
(include-book "kestrel/arithmetic-light/expt" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/arithmetic-light/times" :dir :system)
(include-book "kestrel/arithmetic-light/plus" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "../library-extensions/digits")
(include-book "../library-extensions/lists")
(include-book "../library-extensions/bit-lists")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../library-extensions/r1cses")
(include-book "std/typed-lists/symbol-listp" :dir :system)
(include-book "kestrel/arithmetic-light/floor" :dir :system)
(include-book "kestrel/arithmetic-light/minus" :dir :system)
(include-book "std/lists/butlast" :dir :system)

(defruled int-mulpow-sp-bitp-msb
  (implies (posp n)
           (bitp (car (last (int->lebits v n)))))
  :use ((:instance bitp-of-car-of-last-when-bit-listp (bits (int->lebits v n)))
        (:instance len-of-int->lebits (x v)))
  :disable len-of-int->lebits
  :enable (bit-listp-of-int->lebits-explicit))

(defrule int-mulpow-sp-msb-arith
  (implies (and (posp n) (integerp v)
                (<= (- (expt 2 (1- n))) v) (< v (expt 2 (1- n)))
                (bitp h) (natp lo) (< lo (expt 2 (1- n)))
                (equal (mod v (expt 2 n)) (+ lo (* (expt 2 (1- n)) h))))
           (equal h (if (< v 0) 1 0)))
  :rule-classes nil
  :cases ((< v 0))
  :hints (("Subgoal 2" :in-theory (enable acl2::mod-when-<))
          ("Subgoal 1" :use ((:instance acl2::mod-when-< (x (+ v (expt 2 n)))
                                        (y (expt 2 n))))
           :in-theory (enable acl2::mod-of-+-same-arg1)))
  :use ((:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))
  :enable bitp)

(defruled int-mulpow-sp-msb-of-int->lebits
  (implies (and (posp n) (int-valuep v t n))
           (equal (car (last (int->lebits v n)))
                  (if (< v 0) 1 0)))
  :do-not-induct t
  :use ((:instance int-mulpow-int->lebits-of-mod)
        (:instance int-mulpow-sp-bitp-msb)
        (:instance int-mulpow-top-bit-facts (v (mod v (expt 2 n))))
        (:instance int-mulpow-sp-msb-arith
                   (h (car (last (int->lebits v n))))
                   (lo (lebits=>nat (butlast (int->lebits v n) 1)))))
  :in-theory (e/d (int-valuep int-min int-max)
                  (int->lebits butlast bitp)))

; (!ps).add_wrapped(1): the field value sum 2^i (1 - p_i) + 1 = 2^n - P,
; then to_lower_bits_le(n + 1), dropping the carry bit z.

(defund int-mulpow-sp-negadd-gadget (ps zs z p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list (append zs (list z)) p)
          (list (r1cs::make-r1cs-constraint
                 :a (cons (list (expt 2 (len ps)) 1)
                          (pow2sum-neg-vector ps 0))
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append zs (list z)) 0)))))

(defruled int-mulpow-sp-negadd-a-value
  (implies (and (primep p) (natp k)
                (symbol-listp ps)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (bit-listp (lookup-equal-list ps asg)))
           (equal (r1cs::dot-product
                   (cons (list k 1) (pow2sum-neg-vector ps 0)) asg p)
                  (mod (- k (lebits=>nat (lookup-equal-list ps asg))) p)))
  :do-not-induct t
  :expand ((r1cs::dot-product (cons (list k 1) (pow2sum-neg-vector ps 0))
                              asg p))
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs ps) (i 0)))
  :enable (pfield::add pfield::mul acl2::mod-of-+-of-mod-arg2
           acl2::mod-of-+-of-mod-arg1))

(defrule int-mulpow-sp-negadd-arith
  (implies (and (posp k) (natp a) (< a k) (bitp z) (natp pv) (< pv k)
                (equal (+ a (* k z)) (- k pv)))
           (equal a (mod (- pv) k)))
  :rule-classes nil
  :cases ((equal pv 0))
  :hints (("Subgoal 1" :cases ((equal z 0)))
          ("Subgoal 2" :cases ((equal z 0))))
  :use ((:instance acl2::mod-when-< (x (- k pv)) (y k)))
  :enable (bitp acl2::mod-of-+-same-arg1))

(defruled int-mulpow-sp-negadd-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp zs) (equal (len zs) n)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (natp pv) (< pv (expt 2 n))
                (equal (lookup-equal-list ps asg) (int->lebits pv n))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-negadd-gadget ps zs z p) asg p))
           (equal (lookup-equal-list zs asg) (int->lebits (- pv) n)))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp
                   (xs (append zs (list z))))
        (:instance int-mulpow-sp-negadd-a-value (k (expt 2 n)))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat
                   (xs (append zs (list z))) (i 0))
        int-mulpow-dot-product-of-one
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list zs asg)))
        (:instance int-mulpow-sp-negadd-arith
                   (k (expt 2 n))
                   (a (lebits=>nat (lookup-equal-list zs asg)))
                   (z (lookup-equal z asg)))
        (:instance int-mulpow-int->lebits-of-mod (v (- pv)))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (lookup-equal-list zs asg)) (k n)
                   (v (mod (- pv) (expt 2 n))))
        (:instance int-width-add-fits)
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime))
                   (bs (append (lookup-equal-list zs asg)
                               (list (lookup-equal z asg))))))
  :in-theory (e/d (int-mulpow-sp-negadd-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   r1cs::r1cs-constraint-holdsp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   acl2::lebits=>nat-of-cons
                   lookup-equal-list
                   lebits=>nat-of-int->lebits
                   integer-length-of-base-prime
                   posp-when-integer-widthp
                   pfield::mul
                   acl2::mod-when-<)
                  (int->lebits r1cs::dot-product)))

(defrule int-mulpow-sp-negadd-carry-arith
  (implies (and (posp k) (natp pv) (< pv k))
           (equal (+ (mod (- pv) k) (* k (if (equal pv 0) 1 0)))
                  (- k pv)))
  :rule-classes nil
  :cases ((equal pv 0))
  :use ((:instance acl2::mod-when-< (x (- k pv)) (y k)))
  :enable acl2::mod-of-+-same-arg1)

(defruled int-mulpow-sp-negadd-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp zs) (equal (len zs) n)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (natp pv) (< pv (expt 2 n))
                (equal (lookup-equal-list ps asg) (int->lebits pv n))
                (equal (lookup-equal-list zs asg) (int->lebits (- pv) n))
                (equal (lookup-equal z asg) (if (equal pv 0) 1 0)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-negadd-gadget ps zs z p) asg p))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp
                   (xs (append zs (list z))))
        (:instance int-mulpow-sp-negadd-a-value (k (expt 2 n)))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat
                   (xs (append zs (list z))) (i 0))
        int-mulpow-dot-product-of-one
        (:instance int-mulpow-sp-negadd-carry-arith (k (expt 2 n)))
        (:instance int-width-add-fits)
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime))
                   (bs (append (lookup-equal-list zs asg)
                               (list (lookup-equal z asg))))))
  :in-theory (e/d (int-mulpow-sp-negadd-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   r1cs::r1cs-constraint-holdsp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   acl2::lebits=>nat-of-cons
                   lookup-equal-list
                   bit-listp-of-int->lebits-explicit
                   lebits=>nat-of-int->lebits
                   integer-length-of-base-prime
                   posp-when-integer-widthp
                   pfield::mul
                   acl2::mod-when-<)
                  (int->lebits r1cs::dot-product)))

(defund int-mul-with-flags-any-gadget (as bs ps fz0 fz2 fm fc mult isneq one p)
  (declare (xargs :verify-guards nil))
  (if (equal (len as) 128)
      (int-mul-with-flags-128-gadget as bs ps fz0 fz2 fm fc mult isneq one p)
    (int-mul-with-flags-gadget as bs ps fz0 mult isneq one p)))

(defmacro int-mulpow-sp-flags-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
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
        (equal (lookup-equal-list bs asg) (int->lebits b n))))

(defruled int-mul-with-flags-any-gadget-sound
  (implies (and (int-mulpow-sp-flags-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-any-gadget as bs ps fz0 fz2 fm fc
                                                mult isneq one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (and (int-valuep (* a b) nil n)
                              (equal (lookup-equal-list ps asg)
                                     (int->lebits (* a b) n))))))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 2" :use ((:instance int-mul-with-flags-gadget-sound
                                        (w fz0))))
          ("Subgoal 1" :use ((:instance int-mul-with-flags-128-gadget-sound))))
  :in-theory (e/d (int-mul-with-flags-any-gadget)
                  (int->lebits int-valuep int-mul-with-flags-gadget
                   int-mul-with-flags-128-gadget)))

(defruled int-mulpow-sp-lebits-of-sum
  (implies (and (int-valuep a nil 128) (int-valuep b nil 128))
           (equal (int->lebits (int-mul-wrapped-sum a b 128) 128)
                  (int->lebits (* a b) 128)))
  :do-not-induct t
  :use ((:instance int-mulpow-product-split (x a) (y b) (n 128))
        (:instance int-mulpow-pc128-unsigned-facts)
        (:instance int-mulpow-pc128-unsigned-facts (a b))
        (:instance int-mulpow-int->lebits-of-mod (n 128) (v (* a b)))
        (:instance int-mulpow-int->lebits-of-mod (n 128)
                   (v (int-mul-wrapped-sum a b 128))))
  :in-theory (e/d (int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep int-mulpow-hi int-spec-unsigned
                   int-mul-wrapped-sum)))

(defun int-mulpow-sp-flags-honestp (a b ps fz0 fz2 fm fc mult isneq n asg)
  (declare (xargs :verify-guards nil))
  (and (equal (lookup-equal-list ps asg) (int->lebits (* a b) n))
       (equal (lookup-equal isneq asg) (int-mulpow-pc-honest-isneq (* a b) n))
       (if (equal n 128)
           (and (equal (lookup-equal fz0 asg)
                       (* (int-mulpow-lo a n) (int-mulpow-lo b n)))
                (equal (lookup-equal fz2 asg)
                       (* (int-mulpow-hi a n) (int-mulpow-hi b n)))
                (equal (lookup-equal fm asg)
                       (* (+ (int-mulpow-hi a n) (int-mulpow-lo a n))
                          (+ (int-mulpow-hi b n) (int-mulpow-lo b n))))
                (equal (lookup-equal-list fc asg)
                       (int->lebits (floor (int-mul-wrapped-sum a b n)
                                           (expt 2 n))
                                    (1+ (floor n 2))))
                (equal (lookup-equal mult asg)
                       (int-mulpow-pc128-honest-mult a b)))
         (and (equal (lookup-equal fz0 asg) (* a b))
              (equal (lookup-equal mult asg)
                     (int-mulpow-pc-honest-mult (* a b) n))))))

(defruled int-mul-with-flags-any-gadget-complete
  (implies (and (int-mulpow-sp-flags-wire-hyps)
                (int-mulpow-sp-flags-honestp a b ps fz0 fz2 fm fc mult isneq
                                             n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mul-with-flags-any-gadget as bs ps fz0 fz2 fm fc
                                           mult isneq one p)
            asg p))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 2" :use ((:instance int-mul-with-flags-gadget-complete
                                        (w fz0))))
          ("Subgoal 1" :use ((:instance int-mul-with-flags-128-gadget-complete)
                             (:instance int-mulpow-sp-lebits-of-sum))))
  :in-theory (e/d (int-mul-with-flags-any-gadget)
                  (int->lebits int-valuep int-mul-with-flags-gadget
                   int-mul-with-flags-128-gadget
                   int-mulpow-pc-honest-mult int-mulpow-pc128-honest-mult
                   int-mulpow-pc-honest-isneq
                   int-mulpow-hi int-mulpow-lo int-mul-wrapped-sum)))

(defund int-mulpow-sp-first-flags-gadget (xs ps fc mult isneq one p)
  (declare (xargs :verify-guards nil))
  (if (equal (len xs) 128)
      (int-mulpow-pc128-first-flags-gadget xs ps fc mult isneq one p)
    (int-mulpow-pc-first-flags-gadget xs ps mult isneq one p)))

(defmacro int-mulpow-sp-first-flags-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
        (symbol-listp xs) (equal (len xs) n)
        (symbol-listp ps) (equal (len ps) n)
        (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
        (symbolp mult) (symbolp isneq) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (int-valuep x nil n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))))

(defruled int-mulpow-sp-first-flags-sound
  (implies (and (int-mulpow-sp-first-flags-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-flags-gadget xs ps fc mult isneq one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (equal (lookup-equal-list ps asg)
                                (int->lebits x n)))))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 2" :use ((:instance int-mulpow-pc-first-flags-sound)))
          ("Subgoal 1" :use ((:instance int-mulpow-pc128-first-flags-sound))))
  :in-theory (e/d (int-mulpow-sp-first-flags-gadget
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep int-mulpow-pc-first-flags-gadget
                   int-mulpow-pc128-first-flags-gadget)))

(defruled int-mulpow-sp-first-flags-complete
  (implies (and (int-mulpow-sp-first-flags-wire-hyps)
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (implies (equal n 128)
                         (equal (lookup-equal-list fc asg) (int->lebits 0 65)))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-first-flags-gadget xs ps fc mult isneq one p)
            asg p))
  :do-not-induct t
  :cases ((equal n 128))
  :hints (("Subgoal 2" :use ((:instance int-mulpow-pc-first-flags-complete)))
          ("Subgoal 1" :use ((:instance int-mulpow-pc128-first-flags-complete))))
  :in-theory (e/d (int-mulpow-sp-first-flags-gadget
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits int-valuep int-mulpow-pc-first-flags-gadget
                   int-mulpow-pc128-first-flags-gadget)))

(defruled int-mulpow-sp-lookup-equal-list-of-butlast
  (equal (lookup-equal-list (butlast l 1) asg)
         (butlast (lookup-equal-list l asg) 1))
  :induct (len l)
  :enable (lookup-equal-list butlast))

(defruled int-mulpow-sp-lookup-equal-list-of-cdr
  (equal (lookup-equal-list (cdr l) asg)
         (cdr (lookup-equal-list l asg)))
  :enable lookup-equal-list)

(defruled int-mulpow-sp-binds-allp-of-butlast
  (implies (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (butlast l 1)))
  :induct (len l)
  :enable (r1cs::valuation-binds-allp butlast))

(defruled int-mulpow-sp-binds-allp-of-cdr
  (implies (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (cdr l)))
  :enable r1cs::valuation-binds-allp)

(defruled int-mulpow-sp-symbol-listp-of-butlast
  (implies (symbol-listp l)
           (symbol-listp (butlast l 1)))
  :induct (len l)
  :enable butlast)

(defruled int-mulpow-sp-bindsp-of-car
  (implies (and (r1cs::valuation-binds-allp asg l) (consp l))
           (r1cs::valuation-bindsp asg (car l)))
  :enable r1cs::valuation-binds-allp)

(defruled int-mulpow-sp-lookup-equal-of-car-of-last
  (implies (consp l)
           (equal (lookup-equal (car (last l)) asg)
                  (car (last (lookup-equal-list l asg)))))
  :induct (len l)
  :enable lookup-equal-list)

(defruled int-mulpow-sp-car-last-facts
  (implies (and (symbol-listp l) (consp l) (r1cs::valuation-binds-allp asg l))
           (and (symbolp (car (last l)))
                (r1cs::valuation-bindsp asg (car (last l)))))
  :induct (len l)
  :enable r1cs::valuation-binds-allp)

(defruled int-mulpow-sp-consp-when-len
  (implies (and (equal n (len l)) (posp n))
           (consp l)))


(defruled int-mulpow-sp-bit-listp-of-butlast
  (implies (bit-listp l)
           (bit-listp (butlast l 1)))
  :induct (len l)
  :enable butlast)

(defruled int-mulpow-sp-bitp-of-car
  (implies (and (bit-listp l) (consp l))
           (bitp (car l))))

(defruled int-mulpow-sp-len-of-cdr
  (implies (consp l)
           (equal (len (cdr l)) (+ -1 (len l)))))

(defruled int-mulpow-sp-low-bits-or-iff
  (implies (and (primep p)
                (symbol-listp ps) (symbol-listp lws)
                (natp n) (< 2 n)
                (equal (len ps) n)
                (equal (len lws) (- n 2))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg lws)
                (bit-listp (lookup-equal-list ps asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                              (cdr (butlast ps 1)) lws p)
                   asg p)
                  (equal (lookup-equal-list lws asg)
                         (int-mulpow-or-scan
                          (car (butlast (lookup-equal-list ps asg) 1))
                          (cdr (butlast (lookup-equal-list ps asg) 1))))))
  :do-not-induct t
  :use ((:instance int-mulpow-or-fold-iff
                   (acc (car (butlast ps 1)))
                   (bits (cdr (butlast ps 1)))
                   (ws lws))
        (:instance len-of-butlast (x ps) (n 1))
        (:instance int-mulpow-sp-len-of-cdr (l (butlast ps 1)))
        (:instance int-mulpow-sp-bindsp-of-car (l (butlast ps 1)))
        (:instance lookup-equal-of-car (keys (butlast ps 1)) (alist asg))
        (:instance int-mulpow-sp-bit-listp-of-butlast
                   (l (lookup-equal-list ps asg)))
        (:instance len-of-butlast (x (lookup-equal-list ps asg)) (n 1))
        (:instance int-mulpow-sp-bitp-of-car
                   (l (butlast (lookup-equal-list ps asg) 1))))
  :enable (int-mulpow-sp-lookup-equal-list-of-butlast
           int-mulpow-sp-lookup-equal-list-of-cdr
           int-mulpow-sp-binds-allp-of-butlast
           int-mulpow-sp-binds-allp-of-cdr
           int-mulpow-sp-symbol-listp-of-butlast)
  :disable (butlast int-mulpow-or-fold-gadget int-mulpow-or-scan))

(defruled int-mulpow-sp-low-bits-or-last
  (implies (and (natp n) (< 2 n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (len lws) (- n 2))
                (equal (lookup-equal-list lws asg)
                       (int-mulpow-or-scan (car (butlast bits 1))
                                           (cdr (butlast bits 1)))))
           (equal (lookup-equal (car (last lws)) asg)
                  (if (equal (lebits=>nat (butlast bits 1)) 0) 0 1)))
  :do-not-induct t
  :use ((:instance int-mulpow-or-scan-last
                   (a (car (butlast bits 1)))
                   (bs (cdr (butlast bits 1))))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l lws))
        (:instance len-of-butlast (x bits) (n 1))
        (:instance int-mulpow-sp-len-of-cdr (l (butlast bits 1)))
        (:instance int-mulpow-sp-bit-listp-of-butlast (l bits)))
  :disable (butlast int-mulpow-or-scan))

(defmacro int-mulpow-sp-chain-hyps ()
  '(and (primep p)
        (symbolp s) (symbolp isneq) (symbolp e) (symbolp hw) (symbolp lw)
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg e)
        (r1cs::valuation-bindsp asg hw)
        (r1cs::valuation-bindsp asg lw)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal s asg))
        (bitp (lookup-equal isneq asg))
        (bitp (lookup-equal e asg))
        (bitp (lookup-equal hw asg))
        (bitp (lookup-equal lw asg))))

(defmacro int-mulpow-sp-chain-holds ()
  '(and (r1cs::r1cs-constraints-holdp
         (boolean-and-notleft-gadget s hw po one p) asg p)
        (r1cs::r1cs-constraints-holdp
         (boolean-and-notright-gadget hw lw tt one p) asg p)
        (r1cs::r1cs-constraints-holdp
         (boolean-or-notleft-gadget hw tt u one p) asg p)
        (r1cs::r1cs-constraints-holdp
         (boolean-and-notright-gadget s u v one p) asg p)
        (r1cs::r1cs-constraints-holdp
         (boolean-or-gadget isneq po o1 p) asg p)
        (r1cs::r1cs-constraints-holdp
         (boolean-or-gadget o1 v o2 p) asg p)
        (r1cs::r1cs-constraints-holdp
         (int-mulpow-pc-overflow-gadget o2 e out) asg p)))

(defrule int-mulpow-sp-chain-arith
  (implies (and (bitp s) (bitp i) (bitp e) (bitp h) (bitp l)
                (equal po (if (and (equal s 0) (equal h 1)) 1 0))
                (equal tt (if (and (equal h 1) (equal l 0)) 1 0))
                (equal u (if (or (equal h 0) (equal tt 1)) 1 0))
                (equal v (if (and (equal s 1) (equal u 0)) 1 0))
                (equal o1 (bitor i po))
                (equal o2 (bitor o1 v))
                (not (and (equal o2 1) (equal e 1)))
                (equal e 1))
           (and (equal i 0)
                (implies (equal s 0) (equal h 0))
                (or (equal h 0) (equal l 0))))
  :rule-classes nil
  :enable (bitp bitor))

(defruled int-mulpow-sp-chain-values
  (implies (and (int-mulpow-sp-chain-hyps)
                (int-mulpow-sp-chain-holds))
           (b* ((s$ (lookup-equal s asg))
                (h$ (lookup-equal hw asg))
                (l$ (lookup-equal lw asg))
                (po$ (lookup-equal po asg))
                (tt$ (lookup-equal tt asg))
                (u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (o1$ (lookup-equal o1 asg)))
             (and (equal po$ (if (and (equal s$ 0) (equal h$ 1)) 1 0))
                  (equal tt$ (if (and (equal h$ 1) (equal l$ 0)) 1 0))
                  (equal u$ (if (or (equal h$ 0) (equal tt$ 1)) 1 0))
                  (equal v$ (if (and (equal s$ 1) (equal u$ 0)) 1 0))
                  (equal o1$ (bitor (lookup-equal isneq asg) po$))
                  (equal (lookup-equal o2 asg) (bitor o1$ v$))
                  (equal (lookup-equal out asg) 0)
                  (not (and (equal (lookup-equal o2 asg) 1)
                            (equal (lookup-equal e asg) 1))))))
  :do-not-induct t
  :use ((:instance boolean-and-notleft-gadget-to-booland-boolnot
                   (x s) (y hw) (z po))
        (:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x hw) (y lw) (z tt))
        (:instance boolean-or-notleft-gadget-to-boolor-boolnot
                   (x hw) (y tt) (z u))
        (:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x s) (y u) (z v))
        (:instance boolean-or-gadget-to-bitor (x isneq) (y po) (z o1))
        (:instance boolean-or-gadget-to-bitor (x o1) (y v) (z o2))
        (:instance int-mulpow-pc-overflow-iff (isneq o2)))
  :in-theory (disable bitp bitor))

(defruled int-mulpow-sp-chain-sound
  (implies (and (int-mulpow-sp-chain-hyps)
                (int-mulpow-sp-chain-holds)
                (equal (lookup-equal e asg) 1))
           (b* ((s$ (lookup-equal s asg))
                (h$ (lookup-equal hw asg))
                (l$ (lookup-equal lw asg)))
             (and (equal (lookup-equal isneq asg) 0)
                  (implies (equal s$ 0) (equal h$ 0))
                  (or (equal h$ 0) (equal l$ 0)))))
  :do-not-induct t
  :use (int-mulpow-sp-chain-values
        (:instance int-mulpow-sp-chain-arith
                   (s (lookup-equal s asg)) (i (lookup-equal isneq asg))
                   (e (lookup-equal e asg)) (h (lookup-equal hw asg))
                   (l (lookup-equal lw asg))
                   (po (lookup-equal po asg)) (tt (lookup-equal tt asg))
                   (u (lookup-equal u asg)) (v (lookup-equal v asg))
                   (o1 (lookup-equal o1 asg)) (o2 (lookup-equal o2 asg))))
  :in-theory nil)

(defund int-mulpow-sp-andnot (a b)
  (declare (xargs :guard t))
  (if (and (equal a 0) (equal b 1)) 1 0))

(defund int-mulpow-sp-ornot (a b)
  (declare (xargs :guard t))
  (if (or (equal a 0) (equal b 1)) 1 0))

(defruled int-mulpow-sp-bitp-andnot
  (bitp (int-mulpow-sp-andnot a b))
  :enable int-mulpow-sp-andnot)

(defruled int-mulpow-sp-bitp-ornot
  (bitp (int-mulpow-sp-ornot a b))
  :enable int-mulpow-sp-ornot)

(defruled int-mulpow-sp-bitp-bitor
  (bitp (bitor a b))
  :enable bitor)

(defmacro int-mulpow-sp-gate-hyps ()
  '(and (symbolp x) (symbolp y) (symbolp z) (symbolp one) (primep p)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg x)
        (r1cs::valuation-bindsp asg y)
        (r1cs::valuation-bindsp asg z)
        (r1cs::valuation-bindsp asg one)
        (bitp (lookup-equal x asg)) (bitp (lookup-equal y asg))
        (equal (lookup-equal one asg) 1)))

(defruled int-mulpow-sp-and-notleft-iff
  (implies (int-mulpow-sp-gate-hyps)
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-and-notleft-gadget x y z one p) asg p)
                  (equal (lookup-equal z asg)
                         (int-mulpow-sp-andnot (lookup-equal x asg)
                                               (lookup-equal y asg)))))
  :use boolean-and-notleft-gadget-to-booland-boolnot
  :enable int-mulpow-sp-andnot)

(defruled int-mulpow-sp-and-notright-iff
  (implies (int-mulpow-sp-gate-hyps)
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-and-notright-gadget x y z one p) asg p)
                  (equal (lookup-equal z asg)
                         (int-mulpow-sp-andnot (lookup-equal y asg)
                                               (lookup-equal x asg)))))
  :use boolean-and-notright-gadget-to-booland-boolnot
  :enable int-mulpow-sp-andnot)

(defruled int-mulpow-sp-or-notleft-iff
  (implies (int-mulpow-sp-gate-hyps)
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-or-notleft-gadget x y z one p) asg p)
                  (equal (lookup-equal z asg)
                         (int-mulpow-sp-ornot (lookup-equal x asg)
                                              (lookup-equal y asg)))))
  :use boolean-or-notleft-gadget-to-boolor-boolnot
  :enable int-mulpow-sp-ornot)

(defruled int-mulpow-sp-chain-complete
  (implies (and (int-mulpow-sp-chain-hyps)
                (b* ((s$ (lookup-equal s asg))
                     (h$ (lookup-equal hw asg))
                     (l$ (lookup-equal lw asg))
                     (po$ (lookup-equal po asg))
                     (tt$ (lookup-equal tt asg))
                     (u$ (lookup-equal u asg))
                     (v$ (lookup-equal v asg))
                     (o1$ (lookup-equal o1 asg)))
                  (and (equal po$ (int-mulpow-sp-andnot s$ h$))
                       (equal tt$ (int-mulpow-sp-andnot l$ h$))
                       (equal u$ (int-mulpow-sp-ornot h$ tt$))
                       (equal v$ (int-mulpow-sp-andnot u$ s$))
                       (equal o1$ (bitor (lookup-equal isneq asg) po$))
                       (equal (lookup-equal o2 asg) (bitor o1$ v$))
                       (equal (lookup-equal out asg) 0)
                       (not (and (equal (lookup-equal o2 asg) 1)
                                 (equal (lookup-equal e asg) 1))))))
           (int-mulpow-sp-chain-holds))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-and-notleft-iff (x s) (y hw) (z po))
        (:instance int-mulpow-sp-and-notright-iff (x hw) (y lw) (z tt))
        (:instance int-mulpow-sp-or-notleft-iff (x hw) (y tt) (z u))
        (:instance int-mulpow-sp-and-notright-iff (x s) (y u) (z v))
        (:instance boolean-or-gadget-to-bitor (x isneq) (y po) (z o1))
        (:instance boolean-or-gadget-to-bitor (x o1) (y v) (z o2))
        (:instance int-mulpow-pc-overflow-iff (isneq o2))
        (:instance int-mulpow-sp-bitp-andnot (a (lookup-equal s asg))
                   (b (lookup-equal hw asg)))
        (:instance int-mulpow-sp-bitp-andnot (a (lookup-equal lw asg))
                   (b (lookup-equal hw asg)))
        (:instance int-mulpow-sp-bitp-ornot (a (lookup-equal hw asg))
                   (b (lookup-equal tt asg)))
        (:instance int-mulpow-sp-bitp-andnot (a (lookup-equal u asg))
                   (b (lookup-equal s asg)))
        (:instance int-mulpow-sp-bitp-bitor (a (lookup-equal isneq asg))
                   (b (lookup-equal po asg)))
        (:instance int-mulpow-sp-bitp-bitor (a (lookup-equal o1 asg))
                   (b (lookup-equal v asg))))
  :in-theory (theory 'minimal-theory))

(defund int-mulpow-sp-tail-gadget (s isneq e ps lws po tt u v o1 o2 out
                                     nps nz zs one p)
  (declare (xargs :verify-guards nil))
  (b* ((h (car (last ps)))
       (low (butlast ps 1)))
    (append (boolean-and-notleft-gadget s h po one p)
            (int-mulpow-or-fold-gadget (car low) (cdr low) lws p)
            (boolean-and-notright-gadget h (car (last lws)) tt one p)
            (boolean-or-notleft-gadget h tt u one p)
            (boolean-and-notright-gadget s u v one p)
            (boolean-or-gadget isneq po o1 p)
            (boolean-or-gadget o1 v o2 p)
            (int-mulpow-pc-overflow-gadget o2 e out)
            (int-mulpow-sp-negadd-gadget ps nps nz p)
            (int-mulpow-negsel-gadget s ps nps zs one p))))

(defmacro int-mulpow-sp-tail-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
        (symbolp s) (symbolp isneq) (symbolp e)
        (symbol-listp ps) (equal (len ps) n)
        (symbol-listp lws) (equal (len lws) (- n 2))
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out)
        (symbol-listp nps) (equal (len nps) n)
        (symbolp nz)
        (symbol-listp zs) (equal (len zs) n)
        (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg e)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal s asg))
        (bitp (lookup-equal isneq asg))
        (bitp (lookup-equal e asg))
        (natp pv) (< pv (expt 2 n))
        (equal (lookup-equal-list ps asg) (int->lebits pv n))))

(defruled int-mulpow-sp-width-facts
  (implies (integer-widthp n)
           (and (posp n) (< 2 n) (natp (- n 2))))
  :enable integer-widthp)

(defruled int-mulpow-sp-ps-facts
  (implies (and (posp n) (natp pv) (< pv (expt 2 n)))
           (b* ((bits (int->lebits pv n)))
             (and (bit-listp bits)
                  (equal (len bits) n)
                  (consp bits)
                  (bitp (car (last bits))))))
  :use ((:instance int-mulpow-sp-bitp-msb (v pv))
        (:instance len-of-int->lebits (x pv)))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit)
                  (len-of-int->lebits int->lebits)))

(defruled int-mulpow-sp-tail-parts
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p))
           (b* ((h (car (last ps)))
                (low (butlast ps 1)))
             (and (r1cs::r1cs-constraints-holdp
                   (boolean-and-notleft-gadget s h po one p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-mulpow-or-fold-gadget (car low) (cdr low) lws p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-and-notright-gadget h (car (last lws)) tt one p)
                   asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-or-notleft-gadget h tt u one p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-and-notright-gadget s u v one p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget isneq po o1 p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget o1 v o2 p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-mulpow-pc-overflow-gadget o2 e out) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-mulpow-sp-negadd-gadget ps nps nz p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-mulpow-negsel-gadget s ps nps zs one p) asg p))))
  :do-not-induct t
  :in-theory '(int-mulpow-sp-tail-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(deftheory int-mulpow-sp-min-theory
  (union-theories '(posp-when-integer-widthp
                    primes::primep-of-bls12-377-scalar-field-prime-constant
                    (:e base-prime) (:e bitp)
                    (:compound-recognizer acl2::bitp-compound-recognizer)
                    (:compound-recognizer acl2::natp-compound-recognizer)
                    (:compound-recognizer acl2::posp-compound-recognizer))
                  (theory 'minimal-theory)))

(defruled int-mulpow-sp-tail-hl
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p))
           (b* ((bits (int->lebits pv n)))
             (and (equal (lookup-equal (car (last ps)) asg) (car (last bits)))
                  (bitp (car (last bits)))
                  (equal (lookup-equal (car (last lws)) asg)
                         (if (equal (lebits=>nat (butlast bits 1)) 0) 0 1)))))
  :do-not-induct t
  :use (int-mulpow-sp-tail-parts
        int-mulpow-sp-width-facts
        int-mulpow-sp-ps-facts
        (:instance int-mulpow-sp-low-bits-or-iff)
        (:instance int-mulpow-sp-low-bits-or-last (bits (int->lebits pv n)))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l ps))
        (:instance int-mulpow-sp-consp-when-len (l ps)))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-tail-e1
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (b* ((bits (int->lebits pv n))
                (h (car (last bits)))
                (lo (lebits=>nat (butlast bits 1))))
             (and (equal (lookup-equal isneq asg) 0)
                  (implies (equal (lookup-equal s asg) 0) (equal h 0))
                  (or (equal h 0) (equal lo 0)))))
  :do-not-induct t
  :use (int-mulpow-sp-tail-parts
        int-mulpow-sp-tail-hl
        int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-car-last-facts (l ps))
        (:instance int-mulpow-sp-car-last-facts (l lws))
        (:instance int-mulpow-sp-consp-when-len (l ps))
        (:instance int-mulpow-sp-consp-when-len (l lws) (n (- n 2)))
        (:instance int-mulpow-sp-chain-sound
                   (hw (car (last ps))) (lw (car (last lws)))))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-tail-bounds
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (and (<= pv (expt 2 (1- n)))
                (implies (equal (lookup-equal s asg) 0)
                         (< pv (expt 2 (1- n))))))
  :do-not-induct t
  :use (int-mulpow-sp-tail-e1
        int-mulpow-sp-width-facts
        (:instance int-mulpow-top-bit-facts (v pv))
        (:instance int-mulpow-top-bit-arith
                   (v pv)
                   (h (car (last (int->lebits pv n))))
                   (lo (lebits=>nat (butlast (int->lebits pv n) 1)))))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-tail-zs
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (if (equal (lookup-equal s asg) 0) pv (- pv))
                               n)))
  :do-not-induct t
  :use (int-mulpow-sp-tail-parts
        (:instance int-mulpow-sp-negadd-sound (zs nps) (z nz))
        (:instance int-mulpow-negsel-gadget-iff
                   (c s) (xs ps) (ys nps) (x pv) (y (- pv))))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-tail-sound
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p))
           (and (implies (equal (lookup-equal e asg) 1)
                         (and (equal (lookup-equal isneq asg) 0)
                              (<= pv (expt 2 (1- n)))
                              (implies (equal (lookup-equal s asg) 0)
                                       (< pv (expt 2 (1- n))))))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (if (equal (lookup-equal s asg) 0) pv (- pv))
                                    n))))
  :do-not-induct t
  :use (int-mulpow-sp-tail-e1 int-mulpow-sp-tail-bounds int-mulpow-sp-tail-zs)
  :in-theory nil)

(defund int-mulpow-sp-tail-honest-chainp (pv s isneq lws po tt u v o1 o2 out
                                              n asg)
  (declare (xargs :verify-guards nil))
  (b* ((bits (int->lebits pv n))
       (h (car (last bits)))
       (l (if (equal (lebits=>nat (butlast bits 1)) 0) 0 1))
       (s$ (lookup-equal s asg))
       (po$ (int-mulpow-sp-andnot s$ h))
       (tt$ (int-mulpow-sp-andnot l h))
       (u$ (int-mulpow-sp-ornot h tt$))
       (v$ (int-mulpow-sp-andnot u$ s$))
       (o1$ (bitor (lookup-equal isneq asg) po$)))
    (and (equal (lookup-equal-list lws asg)
                (int-mulpow-or-scan (car (butlast bits 1))
                                    (cdr (butlast bits 1))))
         (equal (lookup-equal po asg) po$)
         (equal (lookup-equal tt asg) tt$)
         (equal (lookup-equal u asg) u$)
         (equal (lookup-equal v asg) v$)
         (equal (lookup-equal o1 asg) o1$)
         (equal (lookup-equal o2 asg) (bitor o1$ v$))
         (equal (lookup-equal out asg) 0))))

(defund int-mulpow-sp-tail-honest-ep (pv e s isneq n asg)
  (declare (xargs :verify-guards nil))
  (implies (equal (lookup-equal e asg) 1)
           (and (equal (lookup-equal isneq asg) 0)
                (<= pv (expt 2 (1- n)))
                (implies (equal (lookup-equal s asg) 0)
                         (< pv (expt 2 (1- n)))))))

(defund int-mulpow-sp-tail-honest-negp (pv s nps nz zs n asg)
  (declare (xargs :verify-guards nil))
  (and (equal (lookup-equal-list nps asg) (int->lebits (- pv) n))
       (equal (lookup-equal nz asg) (if (equal pv 0) 1 0))
       (equal (lookup-equal-list zs asg)
              (int->lebits (if (equal (lookup-equal s asg) 0) pv (- pv)) n))))

(defun int-mulpow-sp-tail-honestp (pv e s isneq lws po tt u v o1 o2 out nps nz zs
                                      n asg)
  (declare (xargs :verify-guards nil))
  (and (int-mulpow-sp-tail-honest-chainp pv s isneq lws po tt u v o1 o2 out n asg)
       (int-mulpow-sp-tail-honest-ep pv e s isneq n asg)
       (int-mulpow-sp-tail-honest-negp pv s nps nz zs n asg)))

(defrule int-mulpow-sp-o2-arith
  (implies (and (posp n) (bitp s) (bitp h) (natp lo) (< lo (expt 2 (1- n)))
                (natp pv) (equal pv (+ lo (* (expt 2 (1- n)) h)))
                (<= pv (expt 2 (1- n)))
                (implies (equal s 0) (< pv (expt 2 (1- n)))))
           (b* ((l (if (equal lo 0) 0 1))
                (po (int-mulpow-sp-andnot s h))
                (tt (int-mulpow-sp-andnot l h))
                (u (int-mulpow-sp-ornot h tt))
                (v (int-mulpow-sp-andnot u s)))
             (and (equal po 0) (equal v 0))))
  :rule-classes nil
  :cases ((equal h 0) (equal h 1))
  :enable (bitp int-mulpow-sp-andnot int-mulpow-sp-ornot))

(defruled int-mulpow-sp-tail-o2
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (int-mulpow-sp-tail-honestp pv e s isneq lws po tt u v o1 o2 out
                                            nps nz zs n asg)
                (equal (lookup-equal e asg) 1))
           (equal (lookup-equal o2 asg) 0))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        int-mulpow-sp-ps-facts
        (:instance int-mulpow-top-bit-facts (v pv))
        (:instance int-mulpow-sp-o2-arith
                   (s (lookup-equal s asg))
                   (h (car (last (int->lebits pv n))))
                   (lo (lebits=>nat (butlast (int->lebits pv n) 1)))))
  :in-theory (union-theories '(int-mulpow-sp-tail-honestp
                               int-mulpow-sp-tail-honest-chainp
                               int-mulpow-sp-tail-honest-ep
                               bitor (:e bitor))
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-tail-o2-implies
  (implies (and (int-mulpow-sp-tail-wire-hyps)
                (int-mulpow-sp-tail-honestp pv e s isneq lws po tt u v o1 o2 out
                                            nps nz zs n asg))
           (not (and (equal (lookup-equal o2 asg) 1)
                     (equal (lookup-equal e asg) 1))))
  :use int-mulpow-sp-tail-o2
  :in-theory nil)

(defmacro int-mulpow-sp-tail-c-hyps ()
  '(and (int-mulpow-sp-tail-wire-hyps)
        (int-mulpow-sp-tail-honestp pv e s isneq lws po tt u v o1 o2 out
                                    nps nz zs n asg)))

(defruled int-mulpow-sp-tail-c-lws
  (implies (int-mulpow-sp-tail-c-hyps)
           (b* ((bits (int->lebits pv n)))
             (and (r1cs::r1cs-constraints-holdp
                   (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                              (cdr (butlast ps 1)) lws p)
                   asg p)
                  (equal (lookup-equal (car (last ps)) asg) (car (last bits)))
                  (bitp (car (last bits)))
                  (equal (lookup-equal (car (last lws)) asg)
                         (if (equal (lebits=>nat (butlast bits 1)) 0) 0 1)))))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        int-mulpow-sp-ps-facts
        (:instance int-mulpow-sp-low-bits-or-iff)
        (:instance int-mulpow-sp-low-bits-or-last (bits (int->lebits pv n)))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l ps))
        (:instance int-mulpow-sp-consp-when-len (l ps)))
  :in-theory (union-theories '(int-mulpow-sp-tail-honestp
                               int-mulpow-sp-tail-honest-chainp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-tail-c-chain
  (implies (int-mulpow-sp-tail-c-hyps)
           (b* ((hw (car (last ps)))
                (lw (car (last lws))))
             (int-mulpow-sp-chain-holds)))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        int-mulpow-sp-tail-c-lws
        int-mulpow-sp-tail-o2-implies
        (:instance int-mulpow-sp-car-last-facts (l ps))
        (:instance int-mulpow-sp-car-last-facts (l lws))
        (:instance int-mulpow-sp-consp-when-len (l ps))
        (:instance int-mulpow-sp-consp-when-len (l lws) (n (- n 2)))
        (:instance int-mulpow-sp-chain-complete
                   (hw (car (last ps))) (lw (car (last lws)))))
  :in-theory (union-theories '(int-mulpow-sp-tail-honestp
                               int-mulpow-sp-tail-honest-chainp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-tail-c-neg
  (implies (int-mulpow-sp-tail-c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-negadd-gadget ps nps nz p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-negsel-gadget s ps nps zs one p) asg p)))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-negadd-complete (zs nps) (z nz))
        (:instance int-mulpow-negsel-gadget-iff
                   (c s) (xs ps) (ys nps) (x pv) (y (- pv))))
  :in-theory (union-theories '(int-mulpow-sp-tail-honestp
                               int-mulpow-sp-tail-honest-negp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-tail-complete
  (implies (int-mulpow-sp-tail-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                       nps nz zs one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-tail-c-lws int-mulpow-sp-tail-c-chain
        int-mulpow-sp-tail-c-neg)
  :in-theory '(int-mulpow-sp-tail-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled int-mulpow-sp-abs-valuep
  (implies (and (posp n) (int-valuep x t n))
           (and (natp (abs x))
                (<= (abs x) (expt 2 (1- n)))
                (< (abs x) (expt 2 n))
                (int-valuep (abs x) nil n)
                (equal (mod (abs x) (expt 2 n)) (abs x))))
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruled int-mulpow-sp-sc-final-arith
  (implies (and (integerp x) (integerp y) (posp n)
                (equal sv (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (<= (* (abs x) (abs y)) (expt 2 (1- n)))
                (implies (equal sv 0)
                         (< (* (abs x) (abs y)) (expt 2 (1- n)))))
           (and (int-valuep (* x y) t n)
                (equal (if (equal sv 0)
                           (* (abs x) (abs y))
                         (- (* (abs x) (abs y))))
                       (* x y))))
  :cases ((and (< x 0) (< y 0))
          (and (< x 0) (<= 0 y))
          (and (<= 0 x) (< y 0)))
  :hints (("Goal" :in-theory (enable int-valuep int-min int-max bitxor))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defruled int-mulpow-sp-sc-complete-arith
  (implies (and (integerp x) (integerp y) (posp n)
                (int-valuep (* x y) t n))
           (and (<= (* (abs x) (abs y)) (expt 2 (1- n)))
                (implies (equal (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)) 0)
                         (< (* (abs x) (abs y)) (expt 2 (1- n))))
                (equal (if (equal (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)) 0)
                           (* (abs x) (abs y))
                         (- (* (abs x) (abs y))))
                       (* x y))))
  :cases ((and (< x 0) (< y 0))
          (and (< x 0) (<= 0 y))
          (and (<= 0 x) (< y 0)))
  :hints (("Goal" :in-theory (enable int-valuep int-min int-max bitxor))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defruled int-mulpow-sp-sc-abs-wrapped-bits
  (implies (posp n)
           (equal (int->lebits (int-abs-wrapped-spec x t n) n)
                  (int->lebits (abs (ifix x)) n)))
  :enable (int-abs-wrapped-spec int->lebits-of-int-wrap))

(defund int-mulpow-sp-times-gadget (ls xs al ml cl ax mx cx ps fz0 fz2 fm fc
                                       mult isneq s lws po tt u v o1 o2 out
                                       nps nz zs e one p)
  (declare (xargs :verify-guards nil))
  (append (int-abs-wrapped-signed-gadget ls al ml cl one p)
          (int-abs-wrapped-signed-gadget xs ax mx cx one p)
          (int-mul-with-flags-any-gadget al ax ps fz0 fz2 fm fc mult isneq one p)
          (boolean-xor-gadget (car (last ls)) (car (last xs)) s p)
          (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                     nps nz zs one p)))

(defmacro int-mulpow-sp-times-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
        (symbol-listp ls) (equal (len ls) n)
        (symbol-listp xs) (equal (len xs) n)
        (symbol-listp al) (equal (len al) n)
        (symbol-listp ml) (equal (len ml) n)
        (symbolp cl)
        (symbol-listp ax) (equal (len ax) n)
        (symbol-listp mx) (equal (len mx) n)
        (symbolp cx)
        (symbol-listp ps) (equal (len ps) n)
        (symbolp fz0) (symbolp fz2) (symbolp fm)
        (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
        (symbolp mult) (symbolp isneq) (symbolp s)
        (symbol-listp lws) (equal (len lws) (- n 2))
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out)
        (symbol-listp nps) (equal (len nps) n)
        (symbolp nz)
        (symbol-listp zs) (equal (len zs) n)
        (symbolp e) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg ls)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg al)
        (r1cs::valuation-binds-allp asg ml)
        (r1cs::valuation-bindsp asg cl)
        (r1cs::valuation-binds-allp asg ax)
        (r1cs::valuation-binds-allp asg mx)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-bindsp asg fz0)
        (r1cs::valuation-bindsp asg fz2)
        (r1cs::valuation-bindsp asg fm)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-bindsp asg e)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal e asg))
        (int-valuep l t n) (int-valuep x t n)
        (equal (lookup-equal-list ls asg) (int->lebits l n))
        (equal (lookup-equal-list xs asg) (int->lebits x n))))

(defruled int-mulpow-sp-times-parts
  (implies (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm fc
                                        mult isneq s lws po tt u v o1 o2 out
                                        nps nz zs e one p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget ls al ml cl one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs ax mx cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-with-flags-any-gadget al ax ps fz0 fz2 fm fc
                                                mult isneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last ls)) (car (last xs)) s p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                            nps nz zs one p)
                 asg p)))
  :in-theory '(int-mulpow-sp-times-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled int-mulpow-sp-s-value
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last ls)) (car (last xs)) s p) asg p))
           (equal (lookup-equal s asg)
                  (bitxor (if (< l 0) 1 0) (if (< x 0) 1 0))))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-msb-of-int->lebits (v l))
        (:instance int-mulpow-sp-msb-of-int->lebits (v x))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l ls))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l xs))
        (:instance int-mulpow-sp-car-last-facts (l ls))
        (:instance int-mulpow-sp-car-last-facts (l xs))
        (:instance int-mulpow-sp-consp-when-len (l ls))
        (:instance int-mulpow-sp-consp-when-len (l xs))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last ls))) (y (car (last xs))) (z s)))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-times-abs
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p))
           (and (equal (lookup-equal-list al asg) (int->lebits (abs l) n))
                (equal (lookup-equal-list ax asg) (int->lebits (abs x) n))
                (int-valuep (abs l) nil n)
                (int-valuep (abs x) nil n)))
  :do-not-induct t
  :use (int-mulpow-sp-times-parts
        (:instance int-mulpow-abs-bits (xs ls) (axs al) (mxs ml) (cx cl) (x l))
        (:instance int-mulpow-abs-bits (axs ax) (mxs mx))
        (:instance int-mulpow-sp-abs-valuep (x l))
        (:instance int-mulpow-sp-abs-valuep))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-times-flags
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (and (int-valuep (* (abs l) (abs x)) nil n)
                              (equal (lookup-equal-list ps asg)
                                     (int->lebits (* (abs l) (abs x)) n))))))
  :do-not-induct t
  :use (int-mulpow-sp-times-parts
        int-mulpow-sp-times-abs
        (:instance int-mul-with-flags-any-gadget-sound
                   (as al) (bs ax) (a (abs l)) (b (abs x))))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-ps-from-bits
  (implies (and (bit-listp bs) (equal (len bs) n) (natp n))
           (and (natp (lebits=>nat bs))
                (< (lebits=>nat bs) (expt 2 n))
                (equal (int->lebits (lebits=>nat bs) n) bs)))
  :use ((:instance int-mulpow-bit-list-is-int->lebits
                   (b bs) (k n) (v (lebits=>nat bs)))
        (:instance int-mulpow-pw-lebits-bound)))

(defruled int-mulpow-sp-times-s-bitp
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p))
           (bitp (lookup-equal s asg)))
  :do-not-induct t
  :use (int-mulpow-sp-times-parts int-mulpow-sp-s-value)
  :in-theory (enable bitxor bitp))

(defruled int-mulpow-sp-times-tail0
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (b* ((pv (lebits=>nat (lookup-equal-list ps asg))))
             (and (equal (lookup-equal isneq asg) 0)
                  (<= pv (expt 2 (1- n)))
                  (implies (equal (lookup-equal s asg) 0)
                           (< pv (expt 2 (1- n))))
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (if (equal (lookup-equal s asg) 0)
                                          pv (- pv))
                                      n)))))
  :do-not-induct t
  :use (int-mulpow-sp-times-parts
        int-mulpow-sp-times-flags
        int-mulpow-sp-times-s-bitp
        (:instance int-mulpow-sp-ps-from-bits (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-sp-tail-sound
                   (pv (lebits=>nat (lookup-equal-list ps asg)))))
  :in-theory (union-theories '(len-of-lookup-equal-list) (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-mod-when-unsigned
  (implies (and (posp n) (int-valuep v nil n))
           (equal (mod (ifix v) (expt 2 n)) v))
  :enable (int-valuep int-min int-max))

(defruled int-mulpow-sp-times-tail
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (b* ((pv (* (abs l) (abs x))))
             (and (equal (lookup-equal isneq asg) 0)
                  (<= pv (expt 2 (1- n)))
                  (implies (equal (lookup-equal s asg) 0)
                           (< pv (expt 2 (1- n))))
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (if (equal (lookup-equal s asg) 0)
                                          pv (- pv))
                                      n)))))
  :do-not-induct t
  :use (int-mulpow-sp-times-tail0
        int-mulpow-sp-times-flags
        (:instance lebits=>nat-of-int->lebits (x (* (abs l) (abs x)))))
  :in-theory (union-theories '(int-mulpow-pc-natp-when-unsigned int-mulpow-sp-mod-when-unsigned int-mulpow-sp-width-facts)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-integerp-when-int-valuep
  (implies (int-valuep v signedp n) (integerp v))
  :enable int-valuep)

(defruled int-mulpow-sp-times-sound
  (implies (and (int-mulpow-sp-times-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm
                                             fc mult isneq s lws po tt u v o1 o2
                                             out nps nz zs e one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (and (equal (lookup-equal isneq asg) 0)
                (int-valuep (* l x) t n)
                (equal (lookup-equal-list zs asg) (int->lebits (* l x) n))))
  :do-not-induct t
  :use (int-mulpow-sp-times-tail
        int-mulpow-sp-times-parts
        int-mulpow-sp-s-value
        (:instance int-mulpow-sp-sc-final-arith
                   (y x) (x l) (sv (lookup-equal s asg))))
  :in-theory (union-theories '(int-mulpow-sp-width-facts int-mulpow-sp-integerp-when-int-valuep)
                             (theory 'int-mulpow-sp-min-theory)))

(defun int-mulpow-sp-times-honestp (l x al ml cl ax mx cx ps fz0 fz2 fm fc mult
                                      isneq s lws po tt u v o1 o2 out nps nz zs
                                      e n asg)
  (declare (xargs :verify-guards nil))
  (and (equal (lookup-equal-list al asg) (int->lebits (int-abs-wrapped-spec l t n) n))
       (equal (lookup-equal-list ml asg) (int->lebits (- (ifix l)) n))
       (equal (lookup-equal cl asg) (int-sub-carry 0 l n))
       (equal (lookup-equal-list ax asg) (int->lebits (int-abs-wrapped-spec x t n) n))
       (equal (lookup-equal-list mx asg) (int->lebits (- (ifix x)) n))
       (equal (lookup-equal cx asg) (int-sub-carry 0 x n))
       (int-mulpow-sp-flags-honestp (abs l) (abs x) ps fz0 fz2 fm fc mult isneq
                                    n asg)
       (equal (lookup-equal s asg) (bitxor (if (< l 0) 1 0) (if (< x 0) 1 0)))
       (int-mulpow-sp-tail-honestp (mod (* (abs l) (abs x)) (expt 2 n)) e s isneq lws po tt u v
                                   o1 o2 out nps nz zs n asg)))

(defmacro int-mulpow-sp-times-c-hyps ()
  '(and (int-mulpow-sp-times-wire-hyps)
        (int-mulpow-sp-times-honestp l x al ml cl ax mx cx ps fz0 fz2 fm fc mult
                                     isneq s lws po tt u v o1 o2 out nps nz zs
                                     e n asg)))

(defruled int-mulpow-sp-times-c-abs
  (implies (int-mulpow-sp-times-c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget ls al ml cl one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs ax mx cx one p) asg p)
                (equal (lookup-equal-list al asg) (int->lebits (abs l) n))
                (equal (lookup-equal-list ax asg) (int->lebits (abs x) n))))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-consp-when-len (l ls))
        (:instance int-mulpow-sp-consp-when-len (l xs))
        (:instance int-abs-wrapped-signed-gadget-complete
                   (xs ls) (ys al) (minus-xs ml) (carry cl) (x l))
        (:instance int-abs-wrapped-signed-gadget-complete
                   (ys ax) (minus-xs mx) (carry cx))
        (:instance int-mulpow-sp-sc-abs-wrapped-bits (x l))
        (:instance int-mulpow-sp-sc-abs-wrapped-bits)
        (:instance int-mulpow-sp-integerp-when-int-valuep (v l) (signedp t))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (union-theories '(int-mulpow-sp-times-honestp ifix)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-times-c-flags
  (implies (int-mulpow-sp-times-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mul-with-flags-any-gadget al ax ps fz0 fz2 fm fc mult isneq one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-times-c-abs
        (:instance int-mulpow-sp-abs-valuep (x l))
        (:instance int-mulpow-sp-abs-valuep)
        (:instance int-mul-with-flags-any-gadget-complete
                   (as al) (bs ax) (a (abs l)) (b (abs x))))
  :in-theory (union-theories '(int-mulpow-sp-times-honestp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-times-c-xor
  (implies (int-mulpow-sp-times-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last ls)) (car (last xs)) s p) asg p))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-msb-of-int->lebits (v l))
        (:instance int-mulpow-sp-msb-of-int->lebits (v x))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l ls))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l xs))
        (:instance int-mulpow-sp-car-last-facts (l ls))
        (:instance int-mulpow-sp-car-last-facts (l xs))
        (:instance int-mulpow-sp-consp-when-len (l ls))
        (:instance int-mulpow-sp-consp-when-len (l xs))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last ls))) (y (car (last xs))) (z s)))
  :in-theory (union-theories '(int-mulpow-sp-times-honestp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-mod-range
  (implies (and (integerp v) (posp n))
           (and (natp (mod v (expt 2 n)))
                (< (mod v (expt 2 n)) (expt 2 n)))))

(defruled int-mulpow-sp-natp-prod
  (implies (and (natp a) (natp b)) (natp (* a b))))

(defruled int-mulpow-sp-times-c-bits
  (implies (int-mulpow-sp-times-honestp l x al ml cl ax mx cx ps fz0 fz2 fm fc
                                        mult isneq s lws po tt u v o1 o2 out nps
                                        nz zs e n asg)
           (and (bitp (lookup-equal s asg))
                (bitp (lookup-equal isneq asg))
                (equal (lookup-equal-list ps asg)
                       (int->lebits (* (abs l) (abs x)) n))))
  :in-theory '(int-mulpow-sp-times-honestp int-mulpow-sp-flags-honestp
               int-mulpow-pc-honest-isneq bitxor bitp (:e bitp) (:e bitxor)))

(defruled int-mulpow-sp-times-c-tail
  (implies (int-mulpow-sp-times-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-tail-gadget s isneq e ps lws po tt u v o1 o2 out
                                       nps nz zs one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-abs-valuep (x l))
        (:instance int-mulpow-sp-abs-valuep)
        int-mulpow-sp-times-c-bits
        (:instance int-mulpow-sp-natp-prod (a (abs l)) (b (abs x)))
        (:instance int-mulpow-sp-mod-range (v (* (abs l) (abs x))))
        (:instance int-mulpow-int->lebits-of-mod (v (* (abs l) (abs x))))
        (:instance int-mulpow-sp-tail-complete
                   (pv (mod (* (abs l) (abs x)) (expt 2 n)))))
  :in-theory (union-theories '(int-mulpow-sp-times-honestp
                               ifix)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-times-complete
  (implies (int-mulpow-sp-times-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-times-gadget ls xs al ml cl ax mx cx ps fz0 fz2 fm fc
                                        mult isneq s lws po tt u v o1 o2 out
                                        nps nz zs e one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-times-c-abs int-mulpow-sp-times-c-flags
        int-mulpow-sp-times-c-xor int-mulpow-sp-times-c-tail)
  :in-theory '(int-mulpow-sp-times-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled int-mulpow-sp-times-honest-ep
  (implies (and (integer-widthp n)
                (int-valuep l t n) (int-valuep x t n)
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* (abs l) (abs x)) n))
                (equal (lookup-equal s asg)
                       (bitxor (if (< l 0) 1 0) (if (< x 0) 1 0)))
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* l x) t n)))
           (int-mulpow-sp-tail-honest-ep (mod (* (abs l) (abs x)) (expt 2 n))
                                         e s isneq n asg))
  :do-not-induct t
  :cases ((equal (lookup-equal e asg) 1))
  :hints (("Subgoal 1"
           :use (int-mulpow-sp-width-facts
                 (:instance int-mulpow-sp-integerp-when-int-valuep (v l) (signedp t))
                 (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t))
                 (:instance int-mulpow-sp-sc-complete-arith (x l) (y x))
                 (:instance int-mulpow-sp-abs-valuep (x l))
                 (:instance int-mulpow-sp-abs-valuep)
                 (:instance int-mulpow-sp-natp-prod (a (abs l)) (b (abs x)))
                 (:instance int-mulpow-sp-half-lt (v (* (abs l) (abs x)))))
           :in-theory (union-theories '(int-mulpow-sp-tail-honest-ep
                                        int-mulpow-pc-honest-isneq)
                                      (theory 'int-mulpow-sp-min-theory))))
  :in-theory '(int-mulpow-sp-tail-honest-ep)
  :prep-lemmas
  ((defrule int-mulpow-sp-half-lt
     (implies (and (natp v) (posp n) (<= v (expt 2 (1- n))))
              (and (int-valuep v nil n)
                   (equal (mod v (expt 2 n)) v)))
     :rule-classes nil
     :enable (int-valuep int-min int-max)
     :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))))

(defund int-mulpow-sp-step-wires-gadget
  (e xs rs qa qm qc qb qn qd qz0 qz2 qmm qps qcarry qs qlws qpo qtt qu qv qnps
     qnc sqs al ml cl ax mx cx ps fz0 fz2 fm fc mult isneq s lws po tt u v o1 o2
     out nps nz zs rs2 one p)
  (declare (xargs :verify-guards nil))
  (append (int-mul-checked-signed-gadget rs rs qa qm qc qb qn qd qz0 qz2 qmm qps
                                         qcarry qs qlws qpo qtt qu qv qnps qnc
                                         sqs one p)
          (int-mulpow-sp-times-gadget sqs xs al ml cl ax mx cx ps fz0 fz2 fm fc
                                      mult isneq s lws po tt u v o1 o2 out
                                      nps nz zs e one p)
          (integer-ternary-gadget e zs sqs rs2 p)))

(defmacro int-mulpow-sp-sq-wire-hyps ()
  '(and (symbol-listp qa) (symbol-listp qm) (symbolp qc)
        (symbol-listp qb) (symbol-listp qn) (symbolp qd)
        (symbolp qz0) (symbolp qz2) (symbolp qmm)
        (symbol-listp qps) (symbol-listp qcarry)
        (symbolp qs) (symbol-listp qlws)
        (symbolp qpo) (symbolp qtt) (symbolp qu) (symbolp qv)
        (symbol-listp qnps) (symbolp qnc)
        (symbol-listp rs) (equal (len rs) n)
        (symbol-listp sqs)
        (int-mulpow-sc-lens n rs qa qm qb qn qps qcarry qlws qnps sqs)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-binds-allp asg qa)
        (r1cs::valuation-binds-allp asg qm)
        (r1cs::valuation-bindsp asg qc)
        (r1cs::valuation-binds-allp asg qb)
        (r1cs::valuation-binds-allp asg qn)
        (r1cs::valuation-bindsp asg qd)
        (r1cs::valuation-bindsp asg qz0)
        (r1cs::valuation-bindsp asg qz2)
        (r1cs::valuation-bindsp asg qmm)
        (r1cs::valuation-binds-allp asg qps)
        (r1cs::valuation-binds-allp asg qcarry)
        (r1cs::valuation-bindsp asg qs)
        (r1cs::valuation-binds-allp asg qlws)
        (r1cs::valuation-bindsp asg qpo)
        (r1cs::valuation-bindsp asg qtt)
        (r1cs::valuation-bindsp asg qu)
        (r1cs::valuation-bindsp asg qv)
        (r1cs::valuation-binds-allp asg qnps)
        (r1cs::valuation-bindsp asg qnc)
        (r1cs::valuation-binds-allp asg sqs)
        (symbol-listp rs2) (equal (len rs2) n)
        (r1cs::valuation-binds-allp asg rs2)
        (int-valuep r t n)
        (equal (lookup-equal-list rs asg) (int->lebits r n))))

(defruled int-mulpow-sp-step-sq
  (implies (and (int-mulpow-sp-sq-wire-hyps)
                (equal p (base-prime)) (integer-widthp n)
                (symbolp one) (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-signed-gadget rs rs qa qm qc qb qn qd qz0 qz2
                                                qmm qps qcarry qs qlws qpo qtt qu
                                                qv qnps qnc sqs one p)
                 asg p))
           (and (int-valuep (* r r) t n)
                (equal (lookup-equal-list sqs asg) (int->lebits (* r r) n))))
  :do-not-induct t
  :use ((:instance int-mul-checked-signed-gadget-sound
                   (xs rs) (ys rs) (axs qa) (mxs qm) (cx qc) (ays qb) (mys qn)
                   (cy qd) (z0 qz0) (z2 qz2) (m qmm) (ps qps) (carry qcarry)
                   (s qs) (lws qlws) (po qpo) (tt qtt) (u qu) (v qv) (nps qnps)
                   (nc qnc) (zs sqs) (x r) (y r))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v r) (signedp t)))
  :in-theory (union-theories '(int-mul-checked-spec ifix
                               primes::primep-of-bls12-377-scalar-field-prime-constant)
                             (theory 'int-mulpow-sp-min-theory)))

(defmacro int-mulpow-sp-step-wire-hyps ()
  '(and (int-mulpow-sp-sq-wire-hyps)
        (equal p (base-prime))
        (integer-widthp n)
        (symbol-listp xs) (equal (len xs) n)
        (symbol-listp al) (equal (len al) n)
        (symbol-listp ml) (equal (len ml) n)
        (symbolp cl)
        (symbol-listp ax) (equal (len ax) n)
        (symbol-listp mx) (equal (len mx) n)
        (symbolp cx)
        (symbol-listp ps) (equal (len ps) n)
        (symbolp fz0) (symbolp fz2) (symbolp fm)
        (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
        (symbolp mult) (symbolp isneq) (symbolp s)
        (symbol-listp lws) (equal (len lws) (- n 2))
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out)
        (symbol-listp nps) (equal (len nps) n)
        (symbolp nz)
        (symbol-listp zs) (equal (len zs) n)
        (symbolp e) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg al)
        (r1cs::valuation-binds-allp asg ml)
        (r1cs::valuation-bindsp asg cl)
        (r1cs::valuation-binds-allp asg ax)
        (r1cs::valuation-binds-allp asg mx)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-bindsp asg fz0)
        (r1cs::valuation-bindsp asg fz2)
        (r1cs::valuation-bindsp asg fm)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-bindsp asg e)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal e asg))
        (int-valuep x t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))))

(defruled int-mulpow-sp-step-wires-parts
  (implies (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-step-wires-gadget
             e xs rs qa qm qc qb qn qd qz0 qz2 qmm qps qcarry qs qlws qpo qtt qu
             qv qnps qnc sqs al ml cl ax mx cx ps fz0 fz2 fm fc mult isneq s lws
             po tt u v o1 o2 out nps nz zs rs2 one p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-signed-gadget rs rs qa qm qc qb qn qd qz0 qz2
                                                qmm qps qcarry qs qlws qpo qtt qu
                                                qv qnps qnc sqs one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-times-gadget sqs xs al ml cl ax mx cx ps fz0 fz2
                                             fm fc mult isneq s lws po tt u v o1
                                             o2 out nps nz zs e one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget e zs sqs rs2 p) asg p)))
  :in-theory '(int-mulpow-sp-step-wires-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled int-mulpow-sp-step-wires-sound
  (implies (and (int-mulpow-sp-step-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-step-wires-gadget
                  e xs rs qa qm qc qb qn qd qz0 qz2 qmm qps qcarry qs qlws qpo qtt
                  qu qv qnps qnc sqs al ml cl ax mx cx ps fz0 fz2 fm fc mult isneq
                  s lws po tt u v o1 o2 out nps nz zs rs2 one p)
                 asg p))
           (and (int-valuep (* r r) t n)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* r r x) t n))
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* r r x) n)
                         (int->lebits (* r r) n)))))
  :do-not-induct t
  :use (int-mulpow-sp-step-wires-parts
        int-mulpow-sp-step-sq
        (:instance int-mulpow-sp-sc-lens-sqs)
        (:instance int-mulpow-sp-times-sound (ls sqs) (l (* r r)))
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys zs) (zs sqs) (ws rs2)))
  :in-theory (union-theories '(primes::primep-of-bls12-377-scalar-field-prime-constant
                               acl2::associativity-of-*)
                             (theory 'int-mulpow-sp-min-theory))
  :prep-lemmas
  ((defrule int-mulpow-sp-sc-lens-sqs
     (implies (int-mulpow-sc-lens n rs qa qm qb qn qps qcarry qlws qnps sqs)
              (equal (len sqs) n))
     :rule-classes nil
     :enable int-mulpow-sc-lens)))

(defun int-mulpow-sp-sq-honestp (r qa qm qc qb qn qd qz0 qz2 qmm qps qcarry qs
                                   qlws qpo qtt qu qv qnps qnc sqs n asg)
  (declare (xargs :verify-guards nil))
  (and (equal (lookup-equal-list qa asg) (int->lebits (abs r) n))
       (equal (lookup-equal-list qm asg) (int->lebits (- r) n))
       (equal (lookup-equal qc asg) (int-sub-carry 0 r n))
       (equal (lookup-equal-list qb asg) (int->lebits (abs r) n))
       (equal (lookup-equal-list qn asg) (int->lebits (- r) n))
       (equal (lookup-equal qd asg) (int-sub-carry 0 r n))
       (implies (equal n 128)
                (and (equal (lookup-equal qz0 asg)
                            (* (int-mulpow-lo (abs r) n)
                               (int-mulpow-lo (abs r) n)))
                     (equal (lookup-equal qz2 asg)
                            (* (int-mulpow-hi (abs r) n)
                               (int-mulpow-hi (abs r) n)))
                     (equal (lookup-equal qmm asg)
                            (* (+ (int-mulpow-hi (abs r) n)
                                  (int-mulpow-lo (abs r) n))
                               (+ (int-mulpow-hi (abs r) n)
                                  (int-mulpow-lo (abs r) n))))
                     (equal (lookup-equal-list qcarry asg)
                            (second (int-karatsuba-multiply-spec
                                     (abs r) (abs r) nil n)))))
       (equal (lookup-equal-list qps asg)
              (int->lebits (* (abs r) (abs r)) n))
       (equal (lookup-equal qs asg)
              (bitxor (if (< r 0) 1 0) (if (< r 0) 1 0)))
       (equal (lookup-equal-list qlws asg)
              (int-mulpow-or-scan
               (car (butlast (int->lebits (* (abs r) (abs r)) n) 1))
               (cdr (butlast (int->lebits (* (abs r) (abs r)) n) 1))))
       (equal (lookup-equal qpo asg) 0)
       (equal (lookup-equal qtt asg)
              (if (equal (* (abs r) (abs r)) (expt 2 (1- n))) 1 0))
       (equal (lookup-equal qu asg) 1)
       (equal (lookup-equal qv asg) 0)
       (equal (lookup-equal-list qnps asg)
              (int->lebits (- (* (abs r) (abs r))) n))
       (equal (lookup-equal qnc asg)
              (if (equal (* (abs r) (abs r)) 0) 1 0))
       (equal (lookup-equal-list sqs asg) (int->lebits (* r r) n))))

(defrule int-mulpow-sp-sq-not-error
  (implies (and (int-valuep r t n) (int-valuep (* r r) t n))
           (not (equal (int-mul-checked-spec r r t n) (spec-error))))
  :rule-classes nil
  :enable (int-mul-checked-spec int-mulpow-sp-integerp-when-int-valuep))

(defrule int-mulpow-sp-expt-half-pos
  (implies (integer-widthp n) (not (equal (expt 2 (1- n)) 0)))
  :rule-classes nil
  :enable integer-widthp)

(defrule int-mulpow-sp-step-c-sq-hyps
  (implies (and (int-mulpow-sp-sq-wire-hyps)
                (equal p (base-prime)) (integer-widthp n)
                (symbolp one) (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep (* r r) t n)
                (int-mulpow-sp-sq-honestp r qa qm qc qb qn qd qz0 qz2 qmm qps
                                          qcarry qs qlws qpo qtt qu qv qnps qnc
                                          sqs n asg))
           (let ((xs rs) (ys rs) (axs qa) (mxs qm) (cx qc) (ays qb) (mys qn)
                   (cy qd) (z0 qz0) (z2 qz2) (m qmm) (ps qps) (carry qcarry)
                   (s qs) (lws qlws) (po qpo) (tt qtt) (u qu) (v qv) (nps qnps)
                   (nc qnc) (zs sqs) (x r) (y r))
             (int-mulpow-sc-complete-hyps)))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-integerp-when-int-valuep (v r) (signedp t))
        (:instance int-mulpow-sp-sq-not-error)
        (:instance int-mulpow-sp-expt-half-pos)
        (:instance primes::primep-of-bls12-377-scalar-field-prime-constant))
  :rule-classes nil
  :in-theory (union-theories '(int-mulpow-sp-sq-honestp (:e base-prime)) (theory 'minimal-theory)))

(defruled int-mulpow-sp-step-c-sq
  (implies (and (int-mulpow-sp-sq-wire-hyps)
                (equal p (base-prime)) (integer-widthp n)
                (symbolp one) (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep (* r r) t n)
                (int-mulpow-sp-sq-honestp r qa qm qc qb qn qd qz0 qz2 qmm qps
                                          qcarry qs qlws qpo qtt qu qv qnps qnc
                                          sqs n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mul-checked-signed-gadget rs rs qa qm qc qb qn qd qz0 qz2
                                           qmm qps qcarry qs qlws qpo qtt qu
                                           qv qnps qnc sqs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mul-checked-signed-gadget-complete
                   (xs rs) (ys rs) (axs qa) (mxs qm) (cx qc) (ays qb) (mys qn)
                   (cy qd) (z0 qz0) (z2 qz2) (m qmm) (ps qps) (carry qcarry)
                   (s qs) (lws qlws) (po qpo) (tt qtt) (u qu) (v qv) (nps qnps)
                   (nc qnc) (zs sqs) (x r) (y r))
        int-mulpow-sp-step-c-sq-hyps)
  :in-theory nil)

(defruled int-mulpow-sp-step-wires-complete
  (implies (and (int-mulpow-sp-step-wire-hyps)
                (int-valuep (* r r) t n)
                (int-mulpow-sp-sq-honestp r qa qm qc qb qn qd qz0 qz2 qmm qps
                                          qcarry qs qlws qpo qtt qu qv qnps qnc
                                          sqs n asg)
                (int-mulpow-sp-times-honestp (* r r) x al ml cl ax mx cx ps fz0
                                             fz2 fm fc mult isneq s lws po tt u
                                             v o1 o2 out nps nz zs e n asg)
                (equal (lookup-equal-list rs2 asg)
                       (if (equal (lookup-equal e asg) 1)
                           (lookup-equal-list zs asg)
                         (lookup-equal-list sqs asg))))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-step-wires-gadget
             e xs rs qa qm qc qb qn qd qz0 qz2 qmm qps qcarry qs qlws qpo qtt
             qu qv qnps qnc sqs al ml cl ax mx cx ps fz0 fz2 fm fc mult isneq
             s lws po tt u v o1 o2 out nps nz zs rs2 one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-step-c-sq
        (:instance int-mulpow-sp-sc-lens-sqs2)
        (:instance int-mulpow-sp-sq-out)
        (:instance int-mulpow-sp-times-complete (ls sqs) (l (* r r)))
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys zs) (zs sqs) (ws rs2)))
  :in-theory (union-theories '(int-mulpow-sp-step-wires-gadget
                               r1cs::r1cs-constraints-holdp-of-append
                               primes::primep-of-bls12-377-scalar-field-prime-constant)
                             (theory 'int-mulpow-sp-min-theory))
  :prep-lemmas
  ((defrule int-mulpow-sp-sc-lens-sqs2
     (implies (int-mulpow-sc-lens n rs qa qm qb qn qps qcarry qlws qnps sqs)
              (equal (len sqs) n))
     :rule-classes nil
     :enable int-mulpow-sc-lens)
   (defrule int-mulpow-sp-sq-out
     (implies (int-mulpow-sp-sq-honestp r qa qm qc qb qn qd qz0 qz2 qmm qps
                                        qcarry qs qlws qpo qtt qu qv qnps qnc
                                        sqs n asg)
              (equal (lookup-equal-list sqs asg) (int->lebits (* r r) n)))
     :rule-classes nil
     :in-theory '(int-mulpow-sp-sq-honestp))))

(defruled int-mulpow-sp-abs-expt
  (implies (and (integerp x) (natp a))
           (equal (abs (expt x a)) (expt (abs x) a)))
  :induct (int-mulpow-sp-nat-ind a)
  :hints (("Goal" :in-theory (union-theories '(int-mulpow-sp-nat-ind zp natp
                                               int-mulpow-sp-abs-times
                                               acl2::commutativity-of-+
                                               fix zip
                                               (:type-prescription expt)
                                               (:e expt) (:e abs))
                                             (theory 'minimal-theory))
                  :expand ((expt x a) (expt (abs x) a)))
          (and stable-under-simplificationp
               '(:in-theory (enable abs))))
  :prep-lemmas
  ((defrule int-mulpow-sp-abs-times
     (implies (and (rationalp x) (rationalp y))
              (equal (abs (* x y)) (* (abs x) (abs y)))))
   (defun int-mulpow-sp-nat-ind (a)
     (if (zp a) a (int-mulpow-sp-nat-ind (1- a))))))

(defrule int-mulpow-sp-expt-mono-nil
  (implies (and (rationalp y) (<= 1 y) (integerp i) (integerp j) (<= i j))
           (<= (expt y i) (expt y j)))
  :rule-classes nil
  :use (:instance acl2::<=-of-expt-and-expt-same-base-linear
                  (acl2::r y) (acl2::i1 i) (acl2::i2 j)))

(defrule int-mulpow-sp-2e
  (implies (and (rationalp e) (<= 0 e) (rationalp y) (<= 2 y))
           (<= (* 2 e) (* y e)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defruled int-mulpow-sp-expt-gap
  (implies (and (natp y) (<= 2 y) (natp a) (natp b) (< a b))
           (<= (* 2 (expt y a)) (expt y b)))
  :use ((:instance int-mulpow-sp-expt-mono-nil (i (1+ a)) (j b))
        (:instance acl2::expt-of-+ (acl2::r y) (acl2::i1 a) (acl2::i2 1))
        (:instance int-mulpow-sp-2e (e (expt y a))))
  :in-theory (disable expt acl2::<=-of-expt-and-expt-same-base-linear
                      acl2::<-of-expt-and-expt-same-base
                      acl2::<-of-expt-and-expt-same-base-linear
                      acl2::expt-of-+))

(defrule int-mulpow-sp-expt-le-1
  (implies (and (natp y) (<= y 1) (natp a)) (<= (expt y a) 1))
  :rule-classes nil
  :cases ((equal y 0) (equal y 1)))

(defrule int-mulpow-sp-abs-cases
  (implies (integerp e)
           (and (natp (abs e))
                (<= (- (abs e)) e)
                (<= e (abs e))
                (or (equal (abs e) e) (equal (abs e) (- e)))))
  :rule-classes nil)

(defruled int-mulpow-sp-range-small
  (implies (and (integerp x) (<= (abs x) 1) (natp a) (integer-widthp n))
           (int-valuep (expt x a) t n))
  :use ((:instance int-mulpow-sp-abs-expt)
        (:instance int-mulpow-sp-expt-le-1 (y (abs x)))
        (:instance int-mulpow-sp-abs-cases (e x))
        (:instance int-mulpow-sp-abs-cases (e (expt x a))))
  :in-theory (e/d (int-valuep int-min int-max integer-widthp)
                  (expt abs)))

(defruled int-mulpow-sp-range-big
  (implies (and (integerp x) (< 1 (abs x)) (natp a) (natp b) (< a b)
                (integer-widthp n)
                (int-valuep (expt x b) t n))
           (int-valuep (expt x a) t n))
  :use ((:instance int-mulpow-sp-abs-expt)
        (:instance int-mulpow-sp-abs-expt (a b))
        (:instance int-mulpow-sp-expt-gap (y (abs x)))
        (:instance int-mulpow-sp-abs-cases (e x))
        (:instance int-mulpow-sp-abs-cases (e (expt x a)))
        (:instance int-mulpow-sp-abs-cases (e (expt x b)))
        (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (- n 2))
                   (acl2::i2 1))
        (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (- n 1))
                   (acl2::i2 1)))
  :in-theory (e/d (int-valuep int-min int-max integer-widthp)
                  (expt abs acl2::expt-of-+)))

(defruled int-mulpow-sp-range-mono
  (implies (and (integerp x) (natp a) (natp b) (<= a b) (integer-widthp n)
                (int-valuep (expt x b) t n))
           (int-valuep (expt x a) t n))
  :cases ((equal a b))
  :use (int-mulpow-sp-range-small int-mulpow-sp-range-big)
  :in-theory (disable expt int-valuep))

(defund int-mulpow-sp-rec-okp (rec n asg)
  (declare (xargs :verify-guards nil))
  (and (true-listp rec)
       (equal (len rec) 46)
       (symbol-listp (nth 0 rec))
       (equal (len (nth 0 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 0 rec))
       (symbol-listp (nth 1 rec))
       (equal (len (nth 1 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 1 rec))
       (symbolp (nth 2 rec))
       (r1cs::valuation-bindsp asg (nth 2 rec))
       (symbol-listp (nth 3 rec))
       (equal (len (nth 3 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 3 rec))
       (symbol-listp (nth 4 rec))
       (equal (len (nth 4 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 4 rec))
       (symbolp (nth 5 rec))
       (r1cs::valuation-bindsp asg (nth 5 rec))
       (symbolp (nth 6 rec))
       (r1cs::valuation-bindsp asg (nth 6 rec))
       (symbolp (nth 7 rec))
       (r1cs::valuation-bindsp asg (nth 7 rec))
       (symbolp (nth 8 rec))
       (r1cs::valuation-bindsp asg (nth 8 rec))
       (symbol-listp (nth 9 rec))
       (equal (len (nth 9 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 9 rec))
       (symbol-listp (nth 10 rec))
       (equal (len (nth 10 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 10 rec))
       (symbol-listp (nth 11 rec))
       (equal (len (nth 11 rec)) (1+ (floor n 2)))
       (r1cs::valuation-binds-allp asg (nth 11 rec))
       (symbolp (nth 12 rec))
       (r1cs::valuation-bindsp asg (nth 12 rec))
       (symbol-listp (nth 13 rec))
       (equal (len (nth 13 rec)) (- n 2))
       (r1cs::valuation-binds-allp asg (nth 13 rec))
       (symbolp (nth 14 rec))
       (r1cs::valuation-bindsp asg (nth 14 rec))
       (symbolp (nth 15 rec))
       (r1cs::valuation-bindsp asg (nth 15 rec))
       (symbolp (nth 16 rec))
       (r1cs::valuation-bindsp asg (nth 16 rec))
       (symbolp (nth 17 rec))
       (r1cs::valuation-bindsp asg (nth 17 rec))
       (symbol-listp (nth 18 rec))
       (equal (len (nth 18 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 18 rec))
       (symbolp (nth 19 rec))
       (r1cs::valuation-bindsp asg (nth 19 rec))
       (symbol-listp (nth 20 rec))
       (equal (len (nth 20 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 20 rec))
       (symbol-listp (nth 21 rec))
       (equal (len (nth 21 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 21 rec))
       (symbol-listp (nth 22 rec))
       (equal (len (nth 22 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 22 rec))
       (symbolp (nth 23 rec))
       (r1cs::valuation-bindsp asg (nth 23 rec))
       (symbol-listp (nth 24 rec))
       (equal (len (nth 24 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 24 rec))
       (symbol-listp (nth 25 rec))
       (equal (len (nth 25 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 25 rec))
       (symbolp (nth 26 rec))
       (r1cs::valuation-bindsp asg (nth 26 rec))
       (symbol-listp (nth 27 rec))
       (equal (len (nth 27 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 27 rec))
       (symbolp (nth 28 rec))
       (r1cs::valuation-bindsp asg (nth 28 rec))
       (symbolp (nth 29 rec))
       (r1cs::valuation-bindsp asg (nth 29 rec))
       (symbolp (nth 30 rec))
       (r1cs::valuation-bindsp asg (nth 30 rec))
       (symbol-listp (nth 31 rec))
       (equal (len (nth 31 rec)) (1+ (floor n 2)))
       (r1cs::valuation-binds-allp asg (nth 31 rec))
       (symbolp (nth 32 rec))
       (r1cs::valuation-bindsp asg (nth 32 rec))
       (symbolp (nth 33 rec))
       (r1cs::valuation-bindsp asg (nth 33 rec))
       (symbolp (nth 34 rec))
       (r1cs::valuation-bindsp asg (nth 34 rec))
       (symbol-listp (nth 35 rec))
       (equal (len (nth 35 rec)) (- n 2))
       (r1cs::valuation-binds-allp asg (nth 35 rec))
       (symbolp (nth 36 rec))
       (r1cs::valuation-bindsp asg (nth 36 rec))
       (symbolp (nth 37 rec))
       (r1cs::valuation-bindsp asg (nth 37 rec))
       (symbolp (nth 38 rec))
       (r1cs::valuation-bindsp asg (nth 38 rec))
       (symbolp (nth 39 rec))
       (r1cs::valuation-bindsp asg (nth 39 rec))
       (symbolp (nth 40 rec))
       (r1cs::valuation-bindsp asg (nth 40 rec))
       (symbolp (nth 41 rec))
       (r1cs::valuation-bindsp asg (nth 41 rec))
       (symbolp (nth 42 rec))
       (r1cs::valuation-bindsp asg (nth 42 rec))
       (symbol-listp (nth 43 rec))
       (equal (len (nth 43 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 43 rec))
       (symbolp (nth 44 rec))
       (r1cs::valuation-bindsp asg (nth 44 rec))
       (symbol-listp (nth 45 rec))
       (equal (len (nth 45 rec)) n)
       (r1cs::valuation-binds-allp asg (nth 45 rec))))

(defruled int-mulpow-sp-rec-okp-out
  (implies (int-mulpow-sp-rec-okp rec n asg)
           (and (symbol-listp (nth 10 rec))
                (equal (len (nth 10 rec)) n)
                (r1cs::valuation-binds-allp asg (nth 10 rec))))
  :enable int-mulpow-sp-rec-okp)

(defund int-mulpow-sp-step-gadget (e xs rs rec one p)
  (declare (xargs :verify-guards nil))
  (int-mulpow-sp-step-wires-gadget e xs rs (nth 0 rec) (nth 1 rec) (nth 2 rec) (nth 3 rec) (nth 4 rec) (nth 5 rec) (nth 6 rec) (nth 7 rec) (nth 8 rec) (nth 9 rec) (nth 11 rec) (nth 12 rec) (nth 13 rec) (nth 14 rec) (nth 15 rec) (nth 16 rec) (nth 17 rec) (nth 18 rec) (nth 19 rec) (nth 20 rec) (nth 21 rec) (nth 22 rec) (nth 23 rec) (nth 24 rec) (nth 25 rec) (nth 26 rec) (nth 27 rec) (nth 28 rec) (nth 29 rec) (nth 30 rec) (nth 31 rec) (nth 32 rec) (nth 33 rec) (nth 34 rec) (nth 35 rec) (nth 36 rec) (nth 37 rec) (nth 38 rec) (nth 39 rec) (nth 40 rec) (nth 41 rec) (nth 42 rec) (nth 43 rec) (nth 44 rec) (nth 45 rec) (nth 10 rec) one p))

(defmacro int-mulpow-sp-step-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
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
        (int-valuep x t n) (natp v)
        (int-valuep (expt x v) t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
        (int-mulpow-sp-rec-okp rec n asg)))

(defruled int-mulpow-sp-step-sound
  (implies (and (int-mulpow-sp-step-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-step-gadget e xs rs rec one p) asg p))
           (and (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) t n)
                (equal (lookup-equal-list (nth 10 rec) asg)
                       (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg)))
                                    n))))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-step-wires-sound
                   (qa (nth 0 rec))
                   (qm (nth 1 rec))
                   (qc (nth 2 rec))
                   (qb (nth 3 rec))
                   (qn (nth 4 rec))
                   (qd (nth 5 rec))
                   (qz0 (nth 6 rec))
                   (qz2 (nth 7 rec))
                   (qmm (nth 8 rec))
                   (qps (nth 9 rec))
                   (rs2 (nth 10 rec))
                   (qcarry (nth 11 rec))
                   (qs (nth 12 rec))
                   (qlws (nth 13 rec))
                   (qpo (nth 14 rec))
                   (qtt (nth 15 rec))
                   (qu (nth 16 rec))
                   (qv (nth 17 rec))
                   (qnps (nth 18 rec))
                   (qnc (nth 19 rec))
                   (sqs (nth 20 rec))
                   (al (nth 21 rec))
                   (ml (nth 22 rec))
                   (cl (nth 23 rec))
                   (ax (nth 24 rec))
                   (mx (nth 25 rec))
                   (cx (nth 26 rec))
                   (ps (nth 27 rec))
                   (fz0 (nth 28 rec))
                   (fz2 (nth 29 rec))
                   (fm (nth 30 rec))
                   (fc (nth 31 rec))
                   (mult (nth 32 rec))
                   (isneq (nth 33 rec))
                   (s (nth 34 rec))
                   (lws (nth 35 rec))
                   (po (nth 36 rec))
                   (tt (nth 37 rec))
                   (u (nth 38 rec))
                   (v (nth 39 rec))
                   (o1 (nth 40 rec))
                   (o2 (nth 41 rec))
                   (out (nth 42 rec))
                   (nps (nth 43 rec))
                   (nz (nth 44 rec))
                   (zs (nth 45 rec))
                   (r (expt x v)))
        (:instance int-mulpow-pw-expt-step (b (lookup-equal e asg)))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t))
        (:instance int-mulpow-sp-lens-from-okp))
  :in-theory (union-theories '(int-mulpow-sp-step-gadget int-mulpow-sp-rec-okp acl2::associativity-of-*)
                             (theory 'int-mulpow-sp-min-theory))
  :prep-lemmas
  ((defrule int-mulpow-sp-lens-from-okp
     (implies (and (int-mulpow-sp-rec-okp rec n asg) (equal (len rs) n))
              (int-mulpow-sc-lens n rs (nth 0 rec) (nth 1 rec) (nth 3 rec) (nth 4 rec) (nth 9 rec) (nth 11 rec) (nth 13 rec) (nth 18 rec) (nth 20 rec)))
     :rule-classes nil
     :enable (int-mulpow-sp-rec-okp int-mulpow-sc-lens))))

(defund int-mulpow-sp-first-gadget (e xs ax mx cx ps fc mult isneq lws po tt u v
                                      o1 o2 out nps nz zs rs one p)
  (declare (xargs :verify-guards nil))
  (append (int-abs-wrapped-signed-gadget xs ax mx cx one p)
          (int-mulpow-sp-first-flags-gadget ax ps fc mult isneq one p)
          (int-mulpow-sp-tail-gadget (car (last xs)) isneq e ps lws po tt u v
                                     o1 o2 out nps nz zs one p)
          (boolean-or-notleft-gadget e (car zs) (car rs) one p)
          (int-mulpow-pw-and-list e (cdr zs) (cdr rs))))

(defmacro int-mulpow-sp-first-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
        (symbol-listp xs) (equal (len xs) n)
        (symbol-listp ax) (equal (len ax) n)
        (symbol-listp mx) (equal (len mx) n)
        (symbolp cx)
        (symbol-listp ps) (equal (len ps) n)
        (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
        (symbolp mult) (symbolp isneq)
        (symbol-listp lws) (equal (len lws) (- n 2))
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out)
        (symbol-listp nps) (equal (len nps) n)
        (symbolp nz)
        (symbol-listp zs) (equal (len zs) n)
        (symbol-listp rs) (equal (len rs) n)
        (symbolp e) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ax)
        (r1cs::valuation-binds-allp asg mx)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg e)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal e asg))
        (int-valuep x t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))))

(defruled int-mulpow-sp-first-parts
  (implies (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po tt
                                        u v o1 o2 out nps nz zs rs one p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs ax mx cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-flags-gadget ax ps fc mult isneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-tail-gadget (car (last xs)) isneq e ps lws po tt
                                            u v o1 o2 out nps nz zs one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget e (car zs) (car rs) one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-and-list e (cdr zs) (cdr rs)) asg p)))
  :in-theory '(int-mulpow-sp-first-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled int-mulpow-sp-first-msb
  (implies (int-mulpow-sp-first-wire-hyps)
           (and (symbolp (car (last xs)))
                (r1cs::valuation-bindsp asg (car (last xs)))
                (equal (lookup-equal (car (last xs)) asg) (if (< x 0) 1 0))
                (bitp (lookup-equal (car (last xs)) asg))))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-msb-of-int->lebits (v x))
        (:instance int-mulpow-sp-lookup-equal-of-car-of-last (l xs))
        (:instance int-mulpow-sp-car-last-facts (l xs))
        (:instance int-mulpow-sp-consp-when-len (l xs)))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-first-abs
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs ax mx cx one p) asg p))
           (and (equal (lookup-equal-list ax asg) (int->lebits (abs x) n))
                (int-valuep (abs x) nil n)))
  :do-not-induct t
  :use ((:instance int-mulpow-abs-bits (axs ax) (mxs mx))
        (:instance int-mulpow-sp-abs-valuep))
  :in-theory (union-theories '(primes::primep-of-bls12-377-scalar-field-prime-constant)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-flags
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po
                                             tt u v o1 o2 out nps nz zs rs one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (equal (lookup-equal-list ps asg)
                                (int->lebits (abs x) n)))
                (int-valuep (abs x) nil n)))
  :do-not-induct t
  :use (int-mulpow-sp-first-parts
        int-mulpow-sp-first-abs
        (:instance int-mulpow-sp-first-flags-sound (xs ax) (x (abs x))))
  :in-theory (theory 'int-mulpow-sp-min-theory))

(defruled int-mulpow-sp-first-tail0
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po
                                             tt u v o1 o2 out nps nz zs rs one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (b* ((pv (lebits=>nat (lookup-equal-list ps asg)))
                (s (lookup-equal (car (last xs)) asg)))
             (and (equal (lookup-equal isneq asg) 0)
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (if (equal s 0) pv (- pv)) n)))))
  :do-not-induct t
  :use (int-mulpow-sp-first-parts
        int-mulpow-sp-first-flags
        int-mulpow-sp-first-msb
        (:instance int-mulpow-sp-ps-from-bits (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-sp-tail-sound
                   (s (car (last xs)))
                   (pv (lebits=>nat (lookup-equal-list ps asg)))))
  :in-theory (union-theories '(len-of-lookup-equal-list)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-zs-bits
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po
                                             tt u v o1 o2 out nps nz zs rs one p)
                 asg p))
           (bit-listp (lookup-equal-list zs asg)))
  :do-not-induct t
  :use (int-mulpow-sp-first-parts
        int-mulpow-sp-first-flags
        int-mulpow-sp-first-msb
        (:instance int-mulpow-sp-ps-from-bits (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-sp-tail-sound
                   (s (car (last xs)))
                   (pv (lebits=>nat (lookup-equal-list ps asg)))))
  :in-theory (union-theories '(len-of-lookup-equal-list
                               bit-listp-of-int->lebits-explicit)
                             (theory 'int-mulpow-sp-min-theory)))

(defrule int-mulpow-sp-first-sign-arith
  (implies (integerp x)
           (equal (if (equal (if (< x 0) 1 0) 0) (abs x) (- (abs x))) x))
  :rule-classes nil)

(defruled int-mulpow-sp-first-zs
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po
                                             tt u v o1 o2 out nps nz zs rs one p)
                 asg p)
                (equal (lookup-equal e asg) 1))
           (equal (lookup-equal-list zs asg) (int->lebits x n)))
  :do-not-induct t
  :use (int-mulpow-sp-first-tail0
        int-mulpow-sp-first-flags
        int-mulpow-sp-first-msb
        int-mulpow-sp-first-sign-arith
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t))
        (:instance lebits=>nat-of-int->lebits (x (abs x)))
        (:instance int-mulpow-sp-mod-when-unsigned (v (abs x))))
  :in-theory (union-theories '(int-mulpow-sp-width-facts ifix
                               int-mulpow-pc-natp-when-unsigned)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-sound
  (implies (and (int-mulpow-sp-first-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po
                                             tt u v o1 o2 out nps nz zs rs one p)
                 asg p))
           (and (int-valuep (expt x (lookup-equal e asg)) t n)
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) n))))
  :do-not-induct t
  :cases ((equal (lookup-equal e asg) 1))
  :use (int-mulpow-sp-first-parts
        int-mulpow-sp-first-zs
        int-mulpow-sp-first-zs-bits
        int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-consp-when-len (l zs))
        (:instance int-mulpow-sp-consp-when-len (l rs))
        (:instance int-mulpow-pw-first-rs-sound (ps zs))
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance int-mulpow-sp-one-valuep)
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit bitp
                   int-mulpow-sp-len-of-cdr
                   primes::primep-of-bls12-377-scalar-field-prime-constant)
                  (int->lebits int-valuep r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1 int-mulpow-sp-first-gadget
                   boolean-or-notleft-gadget int-mulpow-pw-and-list))
  :prep-lemmas
  ((defrule int-mulpow-sp-one-valuep
     (implies (integer-widthp n) (int-valuep 1 t n))
     :rule-classes nil
     :enable (int-valuep int-min int-max integer-widthp))))

(defund int-mulpow-sp-recs-okp (bs recs n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-sp-rec-okp (car recs) n asg)
         (int-mulpow-sp-recs-okp (cdr bs) (cdr recs) n asg))))

(defund int-mulpow-sp-loop-gadget (bs xs rs recs one p)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      nil
    (append (int-mulpow-sp-step-gadget (car bs) xs rs (car recs) one p)
            (int-mulpow-sp-loop-gadget (cdr bs) xs (nth 10 (car recs))
                                       (cdr recs) one p))))

(defruled int-mulpow-sp-loop-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
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
                (int-valuep x t n) (natp v)
                (int-valuep (expt x v) t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-sp-recs-okp bs recs n asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-sp-loop-gadget bs xs rs recs one p) asg p))
           (and (int-valuep
                 (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                 t n)
                (equal (lookup-equal-list (int-mulpow-pw-loop-out bs rs recs) asg)
                       (int->lebits
                        (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                        n))))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-sp-loop-gadget
                            int-mulpow-pw-loop-out
                            int-mulpow-sp-recs-okp
                            int-mulpow-msb-val
                            int-mulpow-sp-rec-okp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-sp-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defund int-pow-checked-signed-gadget (xs es ax mx cx ps fc mult isneq lws po tt
                                          u v o1 o2 out nps nz zs r0 recs one p)
  (declare (xargs :verify-guards nil))
  (b* ((bs (rev es)))
    (append (int-mulpow-sp-first-gadget (car bs) xs ax mx cx ps fc mult isneq lws
                                        po tt u v o1 o2 out nps nz zs r0 one p)
            (int-mulpow-sp-loop-gadget (cdr bs) xs r0 recs one p))))

(defmacro int-mulpow-sp-top-wire-hyps ()
  '(and (equal p (base-prime))
        (integer-widthp n)
        (symbol-listp xs) (equal (len xs) n)
        (symbol-listp es) (consp es)
        (symbol-listp ax) (equal (len ax) n)
        (symbol-listp mx) (equal (len mx) n)
        (symbolp cx)
        (symbol-listp ps) (equal (len ps) n)
        (symbol-listp fc) (equal (len fc) (1+ (floor n 2)))
        (symbolp mult) (symbolp isneq)
        (symbol-listp lws) (equal (len lws) (- n 2))
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbolp o1) (symbolp o2) (symbolp out)
        (symbol-listp nps) (equal (len nps) n)
        (symbolp nz)
        (symbol-listp zs) (equal (len zs) n)
        (symbol-listp r0) (equal (len r0) n)
        (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg es)
        (r1cs::valuation-binds-allp asg ax)
        (r1cs::valuation-binds-allp asg mx)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-bindsp asg o1)
        (r1cs::valuation-bindsp asg o2)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-binds-allp asg r0)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (int-mulpow-sp-recs-okp (cdr (rev es)) recs n asg)
        (int-valuep x t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (bit-listp (lookup-equal-list es asg))))

(defruled int-pow-checked-signed-gadget-sound
  :short "Signed pow_checked (Pow), variable base and exponent, every width
          8 to 128, any exponent width."
  (implies (and (int-mulpow-sp-top-wire-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-pow-checked-signed-gadget xs es ax mx cx ps fc mult isneq
                                                lws po tt u v o1 o2 out nps nz zs
                                                r0 recs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-pow-checked-spec x e t n) (spec-error)))
                  (equal (lookup-equal-list (int-pow-checked-gadget-out es r0 recs)
                                            asg)
                         (int->lebits (int-pow-checked-spec x e t n) n)))))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-first-sound
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-sp-loop-sound
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg)))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-signed-gadget
                   int-pow-checked-gadget-out
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep)))

(defun int-mulpow-sp-first-honestp (x xs e ax mx cx ps fc mult isneq lws po tt u v
                                      o1 o2 out nps nz zs rs n asg)
  (declare (xargs :verify-guards nil))
  (and (equal (lookup-equal-list ax asg) (int->lebits (int-abs-wrapped-spec x t n) n))
       (equal (lookup-equal-list mx asg) (int->lebits (- (ifix x)) n))
       (equal (lookup-equal cx asg) (int-sub-carry 0 x n))
       (equal (lookup-equal-list ps asg) (int->lebits (abs x) n))
       (implies (equal n 128)
                (equal (lookup-equal-list fc asg) (int->lebits 0 65)))
       (equal (lookup-equal isneq asg) 0)
       (equal (lookup-equal mult asg) 1)
       (int-mulpow-sp-tail-honest-chainp (abs x) (car (last xs)) isneq lws po tt
                                         u v o1 o2 out n asg)
       (int-mulpow-sp-tail-honest-negp (abs x) (car (last xs)) nps nz zs n asg)
       (equal (lookup-equal-list rs asg)
              (int->lebits (expt x (lookup-equal e asg)) n))))

(defmacro int-mulpow-sp-first-c-hyps ()
  '(and (int-mulpow-sp-first-wire-hyps)
        (int-mulpow-sp-first-honestp x xs e ax mx cx ps fc mult isneq lws po tt u v
                                     o1 o2 out nps nz zs rs n asg)))

(defruled int-mulpow-sp-first-c-abs
  (implies (int-mulpow-sp-first-c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs ax mx cx one p) asg p)
                (equal (lookup-equal-list ax asg) (int->lebits (abs x) n))))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-consp-when-len (l xs))
        (:instance int-abs-wrapped-signed-gadget-complete
                   (ys ax) (minus-xs mx) (carry cx))
        (:instance int-mulpow-sp-sc-abs-wrapped-bits)
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (union-theories '(int-mulpow-sp-first-honestp ifix)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-c-flags
  (implies (int-mulpow-sp-first-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-first-flags-gadget ax ps fc mult isneq one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-first-c-abs
        (:instance int-mulpow-sp-abs-valuep)
        (:instance int-mulpow-sp-first-flags-complete (xs ax) (x (abs x))))
  :in-theory (union-theories '(int-mulpow-sp-first-honestp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-c-ep
  (implies (and (integer-widthp n) (int-valuep x t n)
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal s asg) (if (< x 0) 1 0)))
           (int-mulpow-sp-tail-honest-ep (abs x) e s isneq n asg))
  :enable (int-mulpow-sp-tail-honest-ep int-valuep int-min int-max integer-widthp)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruled int-mulpow-sp-first-c-tail
  (implies (int-mulpow-sp-first-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-tail-gadget (car (last xs)) isneq e ps lws po tt u v
                                       o1 o2 out nps nz zs one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sp-width-facts
        int-mulpow-sp-first-msb
        (:instance int-mulpow-sp-abs-valuep)
        (:instance int-mulpow-sp-first-c-ep (s (car (last xs))))
        (:instance int-mulpow-sp-tail-complete (s (car (last xs))) (pv (abs x))))
  :in-theory (union-theories '(int-mulpow-sp-first-honestp
                               int-mulpow-sp-tail-honestp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-c-zs
  (implies (int-mulpow-sp-first-c-hyps)
           (equal (lookup-equal-list zs asg) (int->lebits x n)))
  :do-not-induct t
  :use (int-mulpow-sp-first-msb
        int-mulpow-sp-first-sign-arith
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (union-theories '(int-mulpow-sp-first-honestp
                               int-mulpow-sp-tail-honest-negp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-c-rs
  (implies (and (int-mulpow-sp-first-c-hyps))
           (equal (lookup-equal-list rs asg)
                  (if (equal (lookup-equal e asg) 1)
                      (int->lebits x n)
                    (int->lebits 1 n))))
  :do-not-induct t
  :cases ((equal (lookup-equal e asg) 1) (equal (lookup-equal e asg) 0))
  :use ((:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (union-theories '(int-mulpow-sp-first-honestp (:e expt) expt
                               zip fix bitp acl2::unicity-of-1 acl2::commutativity-of-*)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-first-complete
  (implies (int-mulpow-sp-first-c-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-first-gadget e xs ax mx cx ps fc mult isneq lws po tt
                                        u v o1 o2 out nps nz zs rs one p)
            asg p))
  :do-not-induct t
  :cases ((equal (lookup-equal e asg) 1))
  :use (int-mulpow-sp-first-c-abs
        int-mulpow-sp-first-c-flags
        int-mulpow-sp-first-c-tail
        int-mulpow-sp-first-c-zs
        int-mulpow-sp-first-c-rs
        int-mulpow-sp-width-facts
        (:instance int-mulpow-sp-consp-when-len (l zs))
        (:instance int-mulpow-sp-consp-when-len (l rs))
        (:instance int-mulpow-pw-first-rs-complete (ps zs))
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit bitp
                   int-mulpow-sp-len-of-cdr
                   int-mulpow-sp-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   primes::primep-of-bls12-377-scalar-field-prime-constant)
                  (int->lebits int-valuep r1cs::r1cs-constraints-holdp
                   int-mulpow-sp-first-honestp
                   int-mulpow-pw-int->lebits-of-1
                   boolean-or-notleft-gadget int-mulpow-pw-and-list)))

(defun int-mulpow-sp-times-witnessp (l x al ml cl ax mx cx ps fz0 fz2 fm fc mult
                                       isneq s lws po tt u v o1 o2 out nps nz zs
                                       n asg)
  (declare (xargs :verify-guards nil))
  (b* ((pv (mod (* (abs l) (abs x)) (expt 2 n))))
    (and (equal (lookup-equal-list al asg) (int->lebits (int-abs-wrapped-spec l t n) n))
         (equal (lookup-equal-list ml asg) (int->lebits (- (ifix l)) n))
         (equal (lookup-equal cl asg) (int-sub-carry 0 l n))
         (equal (lookup-equal-list ax asg) (int->lebits (int-abs-wrapped-spec x t n) n))
         (equal (lookup-equal-list mx asg) (int->lebits (- (ifix x)) n))
         (equal (lookup-equal cx asg) (int-sub-carry 0 x n))
         (int-mulpow-sp-flags-honestp (abs l) (abs x) ps fz0 fz2 fm fc mult isneq
                                      n asg)
         (equal (lookup-equal s asg) (bitxor (if (< l 0) 1 0) (if (< x 0) 1 0)))
         (int-mulpow-sp-tail-honest-chainp pv s isneq lws po tt u v o1 o2 out
                                           n asg)
         (int-mulpow-sp-tail-honest-negp pv s nps nz zs n asg))))

(defruled int-mulpow-sp-times-witness-honest
  (implies (and (int-mulpow-sp-times-witnessp l x al ml cl ax mx cx ps fz0 fz2 fm
                                              fc mult isneq s lws po tt u v o1 o2
                                              out nps nz zs n asg)
                (integer-widthp n)
                (int-valuep l t n) (int-valuep x t n)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* l x) t n)))
           (int-mulpow-sp-times-honestp l x al ml cl ax mx cx ps fz0 fz2 fm fc
                                        mult isneq s lws po tt u v o1 o2 out nps
                                        nz zs e n asg))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-times-honest-ep))
  :in-theory '(int-mulpow-sp-times-witnessp int-mulpow-sp-times-honestp
               int-mulpow-sp-tail-honestp int-mulpow-sp-flags-honestp))

(defrule int-mulpow-sp-half-lt2
  (implies (and (natp v) (posp n) (<= v (expt 2 (1- n))))
           (and (int-valuep v nil n)
                (equal (mod v (expt 2 n)) v)))
  :rule-classes nil
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruled int-mulpow-sp-times-witness-zs
  (implies (and (int-mulpow-sp-times-witnessp l x al ml cl ax mx cx ps fz0 fz2 fm
                                              fc mult isneq s lws po tt u v o1 o2
                                              out nps nz zs n asg)
                (integer-widthp n)
                (int-valuep l t n) (int-valuep x t n)
                (int-valuep (* l x) t n))
           (equal (lookup-equal-list zs asg) (int->lebits (* l x) n)))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-integerp-when-int-valuep (v l) (signedp t))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t))
        (:instance int-mulpow-sp-sc-complete-arith (x l) (y x))
        (:instance int-mulpow-sp-abs-valuep (x l))
        (:instance int-mulpow-sp-abs-valuep)
        (:instance int-mulpow-sp-natp-prod (a (abs l)) (b (abs x)))
        (:instance int-mulpow-sp-half-lt2 (v (* (abs l) (abs x))))
        int-mulpow-sp-width-facts)
  :in-theory (union-theories '(int-mulpow-sp-times-witnessp
                               int-mulpow-sp-tail-honest-negp)
                             (theory 'int-mulpow-sp-min-theory)))

(defund int-mulpow-sp-rec-honestp (rec e x v n asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (expt x v)))
    (and (int-mulpow-sp-sq-honestp r (nth 0 rec) (nth 1 rec) (nth 2 rec) (nth 3 rec) (nth 4 rec) (nth 5 rec) (nth 6 rec) (nth 7 rec) (nth 8 rec) (nth 9 rec) (nth 11 rec) (nth 12 rec) (nth 13 rec) (nth 14 rec) (nth 15 rec) (nth 16 rec) (nth 17 rec) (nth 18 rec) (nth 19 rec) (nth 20 rec) n asg)
         (int-mulpow-sp-times-witnessp (* r r) x (nth 21 rec) (nth 22 rec) (nth 23 rec) (nth 24 rec) (nth 25 rec) (nth 26 rec) (nth 27 rec) (nth 28 rec) (nth 29 rec) (nth 30 rec) (nth 31 rec) (nth 32 rec) (nth 33 rec) (nth 34 rec) (nth 35 rec) (nth 36 rec) (nth 37 rec) (nth 38 rec) (nth 39 rec) (nth 40 rec) (nth 41 rec) (nth 42 rec) (nth 43 rec) (nth 44 rec) (nth 45 rec) n asg)
         (equal (lookup-equal-list (nth 10 rec) asg)
                (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg))) n)))))

(defruled int-mulpow-sp-rec-honestp-out
  (implies (int-mulpow-sp-rec-honestp rec e x v n asg)
           (equal (lookup-equal-list (nth 10 rec) asg)
                  (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg))) n)))
  :enable int-mulpow-sp-rec-honestp)

(defruled int-mulpow-sp-expt-2v
  (implies (and (integerp x) (natp v))
           (equal (expt x (* 2 v)) (* (expt x v) (expt x v))))
  :use (:instance int-mulpow-pw-expt-step (b 0)))

(defruled int-mulpow-sp-sq-honest-out
  (implies (int-mulpow-sp-sq-honestp r qa qm qc qb qn qd qz0 qz2 qmm qps
                                     qcarry qs qlws qpo qtt qu qv qnps qnc
                                     sqs n asg)
           (equal (lookup-equal-list sqs asg) (int->lebits (* r r) n)))
  :in-theory '(int-mulpow-sp-sq-honestp))

(defruled int-mulpow-sp-step-c-rs2
  (implies (and (int-mulpow-sp-step-hyps)
                (int-mulpow-sp-rec-honestp rec e x v n asg)
                (int-valuep (expt x (* 2 v)) t n)
                (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) t n))
           (and (int-valuep (* (expt x v) (expt x v)) t n)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* (* (expt x v) (expt x v)) x) t n))
                (equal (lookup-equal-list (nth 10 rec) asg)
                       (if (equal (lookup-equal e asg) 1)
                           (lookup-equal-list (nth 45 rec) asg)
                         (lookup-equal-list (nth 20 rec) asg)))))
  :do-not-induct t
  :cases ((equal (lookup-equal e asg) 1))
  :use ((:instance int-mulpow-pw-expt-step (b (lookup-equal e asg)))
        (:instance int-mulpow-sp-expt-2v)
        (:instance int-mulpow-sp-sq-honest-out (r (expt x v))
                   (qa (nth 0 rec))
                   (qm (nth 1 rec))
                   (qc (nth 2 rec))
                   (qb (nth 3 rec))
                   (qn (nth 4 rec))
                   (qd (nth 5 rec))
                   (qz0 (nth 6 rec))
                   (qz2 (nth 7 rec))
                   (qmm (nth 8 rec))
                   (qps (nth 9 rec))
                   (qcarry (nth 11 rec))
                   (qs (nth 12 rec))
                   (qlws (nth 13 rec))
                   (qpo (nth 14 rec))
                   (qtt (nth 15 rec))
                   (qu (nth 16 rec))
                   (qv (nth 17 rec))
                   (qnps (nth 18 rec))
                   (qnc (nth 19 rec))
                   (sqs (nth 20 rec)))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t))
        (:instance int-mulpow-sp-times-witness-zs
                   (l (* (expt x v) (expt x v)))
                   (al (nth 21 rec))
                   (ml (nth 22 rec))
                   (cl (nth 23 rec))
                   (ax (nth 24 rec))
                   (mx (nth 25 rec))
                   (cx (nth 26 rec))
                   (ps (nth 27 rec))
                   (fz0 (nth 28 rec))
                   (fz2 (nth 29 rec))
                   (fm (nth 30 rec))
                   (fc (nth 31 rec))
                   (mult (nth 32 rec))
                   (isneq (nth 33 rec))
                   (s (nth 34 rec))
                   (lws (nth 35 rec))
                   (po (nth 36 rec))
                   (tt (nth 37 rec))
                   (u (nth 38 rec))
                   (v (nth 39 rec))
                   (o1 (nth 40 rec))
                   (o2 (nth 41 rec))
                   (out (nth 42 rec))
                   (nps (nth 43 rec))
                   (nz (nth 44 rec))
                   (zs (nth 45 rec))))
  :in-theory (union-theories '(int-mulpow-sp-rec-honestp
                               (:e bitp) bitp)
                             (theory 'int-mulpow-sp-min-theory)))

(defruled int-mulpow-sp-step-complete
  (implies (and (int-mulpow-sp-step-hyps)
                (int-mulpow-sp-rec-honestp rec e x v n asg)
                (int-valuep (expt x (* 2 v)) t n)
                (int-valuep (expt x (+ (* 2 v) (lookup-equal e asg))) t n))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use (int-mulpow-sp-step-c-rs2
        (:instance int-mulpow-sp-step-wires-complete
                   (qa (nth 0 rec))
                   (qm (nth 1 rec))
                   (qc (nth 2 rec))
                   (qb (nth 3 rec))
                   (qn (nth 4 rec))
                   (qd (nth 5 rec))
                   (qz0 (nth 6 rec))
                   (qz2 (nth 7 rec))
                   (qmm (nth 8 rec))
                   (qps (nth 9 rec))
                   (rs2 (nth 10 rec))
                   (qcarry (nth 11 rec))
                   (qs (nth 12 rec))
                   (qlws (nth 13 rec))
                   (qpo (nth 14 rec))
                   (qtt (nth 15 rec))
                   (qu (nth 16 rec))
                   (qv (nth 17 rec))
                   (qnps (nth 18 rec))
                   (qnc (nth 19 rec))
                   (sqs (nth 20 rec))
                   (al (nth 21 rec))
                   (ml (nth 22 rec))
                   (cl (nth 23 rec))
                   (ax (nth 24 rec))
                   (mx (nth 25 rec))
                   (cx (nth 26 rec))
                   (ps (nth 27 rec))
                   (fz0 (nth 28 rec))
                   (fz2 (nth 29 rec))
                   (fm (nth 30 rec))
                   (fc (nth 31 rec))
                   (mult (nth 32 rec))
                   (isneq (nth 33 rec))
                   (s (nth 34 rec))
                   (lws (nth 35 rec))
                   (po (nth 36 rec))
                   (tt (nth 37 rec))
                   (u (nth 38 rec))
                   (v (nth 39 rec))
                   (o1 (nth 40 rec))
                   (o2 (nth 41 rec))
                   (out (nth 42 rec))
                   (nps (nth 43 rec))
                   (nz (nth 44 rec))
                   (zs (nth 45 rec))
                   (r (expt x v)))
        (:instance int-mulpow-sp-times-witness-honest
                   (l (* (expt x v) (expt x v)))
                   (al (nth 21 rec))
                   (ml (nth 22 rec))
                   (cl (nth 23 rec))
                   (ax (nth 24 rec))
                   (mx (nth 25 rec))
                   (cx (nth 26 rec))
                   (ps (nth 27 rec))
                   (fz0 (nth 28 rec))
                   (fz2 (nth 29 rec))
                   (fm (nth 30 rec))
                   (fc (nth 31 rec))
                   (mult (nth 32 rec))
                   (isneq (nth 33 rec))
                   (s (nth 34 rec))
                   (lws (nth 35 rec))
                   (po (nth 36 rec))
                   (tt (nth 37 rec))
                   (u (nth 38 rec))
                   (v (nth 39 rec))
                   (o1 (nth 40 rec))
                   (o2 (nth 41 rec))
                   (out (nth 42 rec))
                   (nps (nth 43 rec))
                   (nz (nth 44 rec))
                   (zs (nth 45 rec)))
        (:instance int-mulpow-sp-lens-from-okp2))
  :in-theory (union-theories '(int-mulpow-sp-step-gadget int-mulpow-sp-rec-okp
                               int-mulpow-sp-rec-honestp)
                             (theory 'int-mulpow-sp-min-theory))
  :prep-lemmas
  ((defrule int-mulpow-sp-lens-from-okp2
     (implies (and (int-mulpow-sp-rec-okp rec n asg) (equal (len rs) n))
              (int-mulpow-sc-lens n rs (nth 0 rec) (nth 1 rec) (nth 3 rec) (nth 4 rec) (nth 9 rec) (nth 11 rec) (nth 13 rec) (nth 18 rec) (nth 20 rec)))
     :rule-classes nil
     :enable (int-mulpow-sp-rec-okp int-mulpow-sc-lens))))

(defund int-mulpow-sp-recs-honestp (bs recs x v n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-sp-rec-honestp (car recs) (car bs) x v n asg)
         (int-mulpow-sp-recs-honestp (cdr bs) (cdr recs) x
                                     (+ (* 2 v) (lookup-equal (car bs) asg))
                                     n asg))))

(defruled int-mulpow-sp-step-complete-bounded
  (implies (and (int-mulpow-sp-step-hyps)
                (int-mulpow-sp-rec-honestp rec e x v n asg)
                (natp ee)
                (<= (+ (* 2 v) (lookup-equal e asg)) ee)
                (int-valuep (expt x ee) t n))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-step-gadget e xs rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-step-complete)
        (:instance int-mulpow-sp-range-mono
                   (a (+ (* 2 v) (lookup-equal e asg))) (b ee))
        (:instance int-mulpow-sp-range-mono (a (* 2 v)) (b ee))
        (:instance int-mulpow-sp-integerp-when-int-valuep (v x) (signedp t)))
  :in-theory (e/d (bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-sp-step-gadget int-mulpow-sp-rec-okp
                   int-mulpow-sp-rec-honestp)))

(defruled int-mulpow-sp-loop-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
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
                (int-valuep x t n) (natp v) (natp ee)
                (<= (int-mulpow-msb-val (lookup-equal-list bs asg) v) ee)
                (int-valuep (expt x ee) t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-sp-recs-okp bs recs n asg)
                (int-mulpow-sp-recs-honestp bs recs x v n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-sp-loop-gadget bs xs rs recs one p) asg p))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-sp-loop-gadget
                            int-mulpow-sp-recs-okp
                            int-mulpow-sp-recs-honestp
                            int-mulpow-msb-val
                            int-mulpow-sp-rec-okp-out
                            int-mulpow-sp-rec-honestp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-sp-step-complete-bounded
                                  (e (car bs)) (rec (car recs)))
                       (:instance int-mulpow-sp-range-mono
                                  (a (+ (* 2 v) (lookup-equal (car bs) asg)))
                                  (b ee))
                       (:instance int-mulpow-sp-range-mono (a v) (b ee))
                       (:instance int-mulpow-msb-val-ge
                                  (bs (lookup-equal-list bs asg)))
                       (:instance int-mulpow-sp-integerp-when-int-valuep
                                  (v x) (signedp t))
                       (:instance int-mulpow-msb-val-ge
                                  (bs (cdr (lookup-equal-list bs asg)))
                                  (v (+ (* 2 v) (lookup-equal (car bs) asg)))))))))

(defruled int-mulpow-sp-first-honest-rs
  (implies (int-mulpow-sp-first-honestp x xs e ax mx cx ps fc mult isneq lws po
                                        tt u v o1 o2 out nps nz zs rs n asg)
           (equal (lookup-equal-list rs asg)
                  (int->lebits (expt x (lookup-equal e asg)) n)))
  :in-theory '(int-mulpow-sp-first-honestp))

(defruled int-pow-checked-signed-gadget-complete
  :short "Signed pow_checked (Pow), variable base and exponent, every width
          8 to 128, any exponent width."
  (implies (and (int-mulpow-sp-top-wire-hyps)
                (not (equal (int-pow-checked-spec
                             x (lebits=>nat (lookup-equal-list es asg)) t n)
                            (spec-error)))
                (int-mulpow-sp-first-honestp x xs (car (rev es)) ax mx cx ps fc
                                             mult isneq lws po tt u v o1 o2 out
                                             nps nz zs r0 n asg)
                (int-mulpow-sp-recs-honestp (cdr (rev es)) recs x
                                            (lookup-equal (car (rev es)) asg)
                                            n asg))
           (r1cs::r1cs-constraints-holdp
            (int-pow-checked-signed-gadget xs es ax mx cx ps fc mult isneq lws po
                                           tt u v o1 o2 out nps nz zs r0 recs
                                           one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-sp-first-complete
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-sp-loop-complete
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg))
                   (ee (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-sp-first-honest-rs
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-checked-signed-gadget
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep int-mulpow-sp-first-honestp)))
