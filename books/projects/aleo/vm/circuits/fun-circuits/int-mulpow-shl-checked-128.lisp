; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ShlChecked::shl_checked (also Shl, ShlAssign) at 128 bits, both
; signednesses, any magnitude width (snarkVM
; circuit/types/integers/src/shl_checked.rs).
;
; u128: self.mul_checked(two.pow_checked(rhs)) with the constant two.
; i128: two.cast_as_dual().pow_checked(rhs) (the same unsigned circuit),
; reinterpreted as signed_factor; signed_factor.is_equal(MIN), which is the
; field is_not_equal of from_bits_le(factor) - 2^127 followed by a negation;
; lhs = ternary(is_min, 0.sub_wrapped(self), self), where each bit is
; Boolean::ternary with the linear-combination condition 1 - is_neq; and
; lhs.mul_checked(signed_factor) (int-mul-checked-signed-gadget).
;
; Constant-base two.pow_checked at u128, exponent bits b1 b2 ... (msb first):
;   iteration 1 is constant-folded except for the ternary against the
;     constants 2 and 1, whose bits are the linear combinations 1 - b1 and
;     b1, so nothing is emitted;
;   iteration 2 squares that linear-combination integer: Karatsuba with
;     x1 = y1 = 0 constant, so z2 = 0 is a constant and only
;     (1 + b1)^2 = z0, (1 + b1)^2 = m, the 193 boolean bits, the
;     recombination ((1 - 2^64) z0 + 2^64 m) * 1 = sum, and the carry
;     check remain (int-mulpow-two128-sq2-gadget);
;   from iteration 2 on, mul_with_flags(square, 2) has the constant 2 as
;     second operand, so Karatsuba folds to the linear constraint
;     2 * from_bits_le(square) = from_bits_le(ps ++ fc) with 193 boolean bits
;     and the flag is_not_equal(from_bits_le(fc), 0)
;     (int-mulpow-two128-flags-gadget), followed by the overflow assertion
;     and the integer ternary (int-mulpow-two128-tail-gadget);
;   from iteration 3 on, the squaring is the variable 128-bit mul_checked.

(in-package "ALEOVM")

(include-book "int-mulpow-pow-checked-128")
(include-book "int-mulpow-signed-checked")
(include-book "int-divshift-sub-wrapped-const")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/butlast" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lookup-equal-list"))
(local (include-book "../library-extensions/r1cses"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund int-mulpow-two128-flags-gadget (sqs ps fc mult isneq one p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list (append ps fc) p)
          (list (r1cs::make-r1cs-constraint
                 :a (pow2sum-vector sqs 1)
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append ps fc) 0)))
          (int-mulpow-pc-neq-gadget (pow2sum-vector fc 0) mult isneq one p)))

(defruled int-mulpow-two128-constraint
  (implies (and (primep p)
                (symbol-listp xs) (symbol-listp ws)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ws asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (pow2sum-vector xs 1)
                    :b (list (list 1 1))
                    :c (pow2sum-vector ws 0))
                   asg p)
                  (equal (mod (* 2 (lebits=>nat (lookup-equal-list xs asg))) p)
                         (mod (lebits=>nat (lookup-equal-list ws asg)) p))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat (i 1))
        int-mulpow-dot-product-of-one)
  :enable (r1cs::r1cs-constraint-holdsp pfield::mul)
  :disable r1cs::dot-product)

(defrule int-mulpow-two128-small
  (implies (and (natp a) (< a (expt 2 128)))
           (and (< (* 2 a) (base-prime))
                (natp (* 2 a))))
  :rule-classes nil
  :enable (base-prime))

(defrule int-mulpow-two128-split-vals
  (implies (and (natp u) (< u (expt 2 128)) (natp v) (< v (expt 2 65))
                (natp a) (< a (expt 2 128))
                (equal (mod (* 2 a) (base-prime))
                       (mod (+ u (* (expt 2 128) v)) (base-prime))))
           (equal (+ u (* (expt 2 128) v)) (* 2 a)))
  :rule-classes nil
  :use ((:instance acl2::mod-when-< (x (* 2 a)) (y (base-prime)))
        (:instance acl2::mod-when-< (x (+ u (* (expt 2 128) v)))
                   (y (base-prime))))
  :enable (base-prime))

(defruled int-mulpow-two128-flags-sound
  (implies (and (equal p (base-prime))
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil 128)
                (equal (lookup-equal-list sqs asg) (int->lebits a 128))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-flags-gadget sqs ps fc mult isneq one p)
                 asg p))
           (and (bitp (lookup-equal isneq asg))
                (bit-listp (lookup-equal-list ps asg))
                (implies (equal (lookup-equal isneq asg) 0)
                         (and (int-valuep (* 2 a) nil 128)
                              (equal (lookup-equal-list ps asg)
                                     (int->lebits (* 2 a) 128))))))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs (append ps fc)))
        (:instance int-mulpow-two128-constraint (xs sqs) (ws (append ps fc)))
        (:instance int-mulpow-pc-neq-sound (delta (pow2sum-vector fc 0)))
        (:instance int-mulpow-pc128-fc-value)
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list ps asg)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list fc asg)))
        (:instance int-mulpow-two128-split-vals
                   (u (lebits=>nat (lookup-equal-list ps asg)))
                   (v (lebits=>nat (lookup-equal-list fc asg))))
        (:instance acl2::mod-when-<
                   (x (lebits=>nat (lookup-equal-list fc asg))) (y (base-prime)))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (lookup-equal-list ps asg)) (k 128) (v (* 2 a))))
  :in-theory (e/d (int-mulpow-two128-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-pc-neq-gadget)))

(defruled int-mulpow-two128-floor-bit
  (implies (and (natp a) (< a (expt 2 128)))
           (and (natp (floor (* 2 a) (expt 2 128)))
                (< (floor (* 2 a) (expt 2 128)) 2)
                (equal (equal (floor (* 2 a) (expt 2 128)) 0)
                       (< (* 2 a) (expt 2 128)))))
  :enable (acl2::<-of-floor-arg1 acl2::floor-when-<))

(defruled int-mulpow-two128-flags-complete
  (implies (and (equal p (base-prime))
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp ps) (equal (len ps) 128)
                (symbol-listp fc) (equal (len fc) 65)
                (symbolp mult) (symbolp isneq) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg fc)
                (r1cs::valuation-bindsp asg mult)
                (r1cs::valuation-bindsp asg isneq)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil 128)
                (equal (lookup-equal-list sqs asg) (int->lebits a 128))
                (equal (lookup-equal-list ps asg) (int->lebits (* 2 a) 128))
                (equal (lookup-equal-list fc asg)
                       (int->lebits (floor (* 2 a) (expt 2 128)) 65))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* 2 a) 128))
                (equal (lookup-equal mult asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-flags-gadget sqs ps fc mult isneq one p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs (append ps fc)))
        (:instance int-mulpow-two128-constraint (xs sqs) (ws (append ps fc)))
        (:instance int-mulpow-pc-neq-complete (delta (pow2sum-vector fc 0)))
        (:instance int-mulpow-pc128-fc-value)
        (:instance int-mulpow-two128-floor-bit)
        (:instance int-mulpow-append-int->lebits (s (* 2 a)) (n 128) (k 65))
        (:instance int-mulpow-two128-small))
  :in-theory (e/d (int-mulpow-two128-flags-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   int-mulpow-pc-honest-isneq
                   int-valuep int-min int-max
                   acl2::mod-when-<)
                  (int->lebits int-mulpow-pc-neq-gadget)))


(defund int-mulpow-two128-sq2-gadget (b1 z0 m sqs carry p)
  (declare (xargs :verify-guards nil))
  (append (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 1) (list 1 b1))
                 :b (list (list 1 1) (list 1 b1))
                 :c (list (list 1 z0)))
                (r1cs::make-r1cs-constraint
                 :a (list (list 1 1) (list 1 b1))
                 :b (list (list 1 1) (list 1 b1))
                 :c (list (list 1 m))))
          (boolean-check-gadget-list (append sqs carry) p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list (- 1 (expt 2 64)) z0)
                          (list (expt 2 64) m))
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append sqs carry) 0))
                (r1cs::make-r1cs-constraint
                 :a (int-mulpow-ones-vector carry)
                 :b (list (list 1 1))
                 :c nil))))

(defruled int-mulpow-two128-sq-constraint
  (implies (and (primep p)
                (symbolp b1) (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal b1 asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list 1 1) (list 1 b1))
                    :b (list (list 1 1) (list 1 b1))
                    :c (list (list 1 z)))
                   asg p)
                  (equal (lookup-equal z asg)
                         (mod (expt 2 (* 2 (lookup-equal b1 asg))) p))))
  :do-not-induct t
  :cases ((equal (lookup-equal b1 asg) 0))
  :expand ((:free (x y) (r1cs::dot-product (cons x y) asg p))
           (r1cs::dot-product nil asg p))
  :enable (r1cs::r1cs-constraint-holdsp pfield::mul pfield::add bitp
           acl2::mod-when-<))

(defrule int-mulpow-two128-lin-arith1
  (equal (+ (* (expt 2 64) y) (* (mod (- 1 (expt 2 64)) (base-prime)) y))
         (+ y (* (base-prime) y)))
  :rule-classes nil
  :in-theory (enable (:e base-prime)))

(defrule int-mulpow-two128-lin-arith
  (implies (and (natp y) (< y (base-prime)))
           (equal (mod (+ (* (expt 2 64) y)
                          (* (mod (- 1 (expt 2 64)) (base-prime)) y))
                       (base-prime))
                  y))
  :rule-classes nil
  :use (int-mulpow-two128-lin-arith1
        (:instance acl2::mod-of-+-of-*-same-arg2-arg1 (acl2::x1 y) (acl2::x2 y)
                   (acl2::y (base-prime))))
  :in-theory (disable (:e base-prime) base-prime))

(defruled int-mulpow-two128-lin-dot
  (implies (and (equal p (base-prime))
                (symbolp z0) (symbolp m)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg m)
                (equal (lookup-equal m asg) (lookup-equal z0 asg)))
           (equal (r1cs::dot-product (list (list (- 1 (expt 2 64)) z0)
                                           (list (expt 2 64) m))
                                     asg p)
                  (lookup-equal z0 asg)))
  :do-not-induct t
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var z0) (r1cs::valuation asg)
                   (r1cs::prime p))
        (:instance int-mulpow-two128-lin-arith (y (lookup-equal z0 asg))))
  :enable (r1cs::dot-product pfield::add pfield::mul (:e base-prime)
           acl2::mod-when-< pfield::fep))

(defruled int-mulpow-two128-lin-constraint
  (implies (and (equal p (base-prime))
                (symbolp z0) (symbolp m) (symbol-listp ws)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list ws asg))
                (equal (lookup-equal m asg) (lookup-equal z0 asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list (- 1 (expt 2 64)) z0)
                             (list (expt 2 64) m))
                    :b (list (list 1 1))
                    :c (pow2sum-vector ws 0))
                   asg p)
                  (equal (lookup-equal z0 asg)
                         (mod (lebits=>nat (lookup-equal-list ws asg)) p))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0))
        int-mulpow-two128-lin-dot
        int-mulpow-dot-product-of-one)
  :enable (r1cs::r1cs-constraint-holdsp pfield::mul pfield::add
           (:e base-prime) acl2::mod-when-<))

(defruled int-mulpow-two128-sq2-sound
  (implies (and (equal p (base-prime))
                (symbolp b1) (symbolp z0) (symbolp m)
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp carry) (equal (len carry) 65)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (bitp (lookup-equal b1 asg))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-sq2-gadget b1 z0 m sqs carry p) asg p))
           (and (bit-listp (lookup-equal-list sqs asg))
                (equal (lookup-equal-list sqs asg)
                       (int->lebits (expt 2 (* 2 (lookup-equal b1 asg))) 128))))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp
                   (xs (append sqs carry)))
        (:instance int-mulpow-two128-sq-constraint (z z0))
        (:instance int-mulpow-two128-sq-constraint (z m))
        (:instance int-mulpow-two128-lin-constraint (ws (append sqs carry)))
        (:instance int-mulpow-carry-constraint)
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list sqs asg)))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list carry asg)))
        (:instance acl2::mod-when-<
                   (x (lebits=>nat (lookup-equal-list sqs asg)))
                   (y (base-prime)))
        (:instance int-mulpow-bit-list-is-int->lebits
                   (b (lookup-equal-list sqs asg)) (k 128)
                   (v (expt 2 (* 2 (lookup-equal b1 asg))))))
  :in-theory (e/d (int-mulpow-two128-sq2-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   bitp (:e base-prime)
                   acl2::mod-when-<)
                  (int->lebits r1cs::r1cs-constraint-holdsp)))

(defruled int-mulpow-two128-sq2-complete
  (implies (and (equal p (base-prime))
                (symbolp b1) (symbolp z0) (symbolp m)
                (symbol-listp sqs) (equal (len sqs) 128)
                (symbol-listp carry) (equal (len carry) 65)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg carry)
                (bitp (lookup-equal b1 asg))
                (equal (lookup-equal z0 asg)
                       (expt 2 (* 2 (lookup-equal b1 asg))))
                (equal (lookup-equal m asg)
                       (expt 2 (* 2 (lookup-equal b1 asg))))
                (equal (lookup-equal-list sqs asg)
                       (int->lebits (expt 2 (* 2 (lookup-equal b1 asg))) 128))
                (equal (lookup-equal-list carry asg) (int->lebits 0 65)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-sq2-gadget b1 z0 m sqs carry p) asg p))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp
                   (xs (append sqs carry)))
        (:instance int-mulpow-two128-sq-constraint (z z0))
        (:instance int-mulpow-two128-sq-constraint (z m))
        (:instance int-mulpow-two128-lin-constraint (ws (append sqs carry)))
        (:instance int-mulpow-carry-constraint))
  :in-theory (e/d (int-mulpow-two128-sq2-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraints-holdp
                   lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   lebits=>nat-of-int->lebits
                   bit-listp-of-int->lebits-explicit
                   bitp (:e base-prime)
                   acl2::mod-when-<)
                  (r1cs::r1cs-constraint-holdsp)))


(defund int-mulpow-two128-tail-gadget (e sqs ps fc mult isneq out rs one p)
  (declare (xargs :verify-guards nil))
  (append (int-mulpow-two128-flags-gadget sqs ps fc mult isneq one p)
          (int-mulpow-pc-overflow-gadget isneq e out)
          (integer-ternary-gadget e ps sqs rs p)))

(defmacro int-mulpow-two128-tail-hyps ()
  '(and (equal p (base-prime))
        (symbol-listp sqs) (equal (len sqs) 128)
        (symbol-listp ps) (equal (len ps) 128)
        (symbol-listp fc) (equal (len fc) 65)
        (symbol-listp rs) (equal (len rs) 128)
        (symbolp e) (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg sqs)
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
        (int-valuep a nil 128)
        (equal (lookup-equal-list sqs asg) (int->lebits a 128))))

(defruled int-mulpow-two128-tail-sound
  (implies (and (int-mulpow-two128-tail-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-tail-gadget e sqs ps fc mult isneq out rs
                                                one p)
                 asg p))
           (and (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* 2 a) nil 128))
                (equal (lookup-equal-list rs asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* 2 a) 128)
                         (int->lebits a 128)))))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-flags-sound)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs)))
  :in-theory (e/d (int-mulpow-two128-tail-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   bitp)
                  (int->lebits int-valuep
                   int-mulpow-two128-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))

(defruled int-mulpow-two128-tail-complete
  (implies (and (int-mulpow-two128-tail-hyps)
                (implies (equal (lookup-equal e asg) 1)
                         (int-valuep (* 2 a) nil 128))
                (equal (lookup-equal-list ps asg) (int->lebits (* 2 a) 128))
                (equal (lookup-equal-list fc asg)
                       (int->lebits (floor (* 2 a) (expt 2 128)) 65))
                (equal (lookup-equal isneq asg)
                       (int-mulpow-pc-honest-isneq (* 2 a) 128))
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs asg)
                       (if (equal (lookup-equal e asg) 1)
                           (int->lebits (* 2 a) 128)
                         (int->lebits a 128))))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-tail-gadget e sqs ps fc mult isneq out rs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-flags-complete)
        (:instance int-mulpow-pc-overflow-iff)
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys ps) (zs sqs) (ws rs)))
  :in-theory (e/d (int-mulpow-two128-tail-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   int-mulpow-pc-honest-isneq
                   bitp)
                  (int->lebits int-valuep
                   int-mulpow-two128-flags-gadget
                   int-mulpow-pc-overflow-gadget
                   integer-ternary-gadget)))


(defund int-mulpow-two128-second-gadget (b1 b2 z0 m sqs carry ps fc mult isneq
                                            out rs one p)
  (declare (xargs :verify-guards nil))
  (append (int-mulpow-two128-sq2-gadget b1 z0 m sqs carry p)
          (int-mulpow-two128-tail-gadget b2 sqs ps fc mult isneq out rs one p)))

(defmacro int-mulpow-two128-second-hyps ()
  '(and (equal p (base-prime))
        (symbolp b1) (symbolp b2) (symbolp z0) (symbolp m)
        (symbol-listp sqs) (equal (len sqs) 128)
        (symbol-listp carry) (equal (len carry) 65)
        (symbol-listp ps) (equal (len ps) 128)
        (symbol-listp fc) (equal (len fc) 65)
        (symbol-listp rs) (equal (len rs) 128)
        (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg b1)
        (r1cs::valuation-bindsp asg b2)
        (r1cs::valuation-bindsp asg z0)
        (r1cs::valuation-bindsp asg m)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg carry)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bitp (lookup-equal b1 asg))
        (bitp (lookup-equal b2 asg))))

(defrule int-mulpow-two128-second-arith
  (implies (and (bitp b1) (bitp b2))
           (and (int-valuep (expt 2 (* 2 b1)) nil 128)
                (int-valuep (* 2 (expt 2 (* 2 b1))) nil 128)
                (equal (expt 2 (+ (* 2 b1) b2))
                       (if (equal b2 1)
                           (* 2 (expt 2 (* 2 b1)))
                         (expt 2 (* 2 b1))))
                (equal (floor (* 2 (expt 2 (* 2 b1))) (expt 2 128)) 0)
                (equal (int-mulpow-pc-honest-isneq (* 2 (expt 2 (* 2 b1))) 128)
                       0)))
  :rule-classes nil
  :cases ((and (equal b1 0) (equal b2 0))
          (and (equal b1 0) (equal b2 1))
          (and (equal b1 1) (equal b2 0)))
  :in-theory (enable bitp int-valuep int-min int-max))

(defruled int-mulpow-two128-second-sound
  (implies (and (int-mulpow-two128-second-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-second-gadget b1 b2 z0 m sqs carry ps fc
                                                  mult isneq out rs one p)
                 asg p))
           (b* ((v (+ (* 2 (lookup-equal b1 asg)) (lookup-equal b2 asg))))
             (and (int-valuep (expt 2 v) nil 128)
                  (equal (lookup-equal-list rs asg)
                         (int->lebits (expt 2 v) 128)))))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-sq2-sound)
        (:instance int-mulpow-two128-tail-sound
                   (e b2) (a (expt 2 (* 2 (lookup-equal b1 asg)))))
        (:instance int-mulpow-two128-second-arith
                   (b1 (lookup-equal b1 asg)) (b2 (lookup-equal b2 asg))))
  :in-theory (e/d (int-mulpow-two128-second-gadget
                   r1cs::r1cs-constraints-holdp-of-append)
                  (int->lebits int-valuep expt
                   int-mulpow-two128-sq2-gadget
                   int-mulpow-two128-tail-gadget)))

(defruled int-mulpow-two128-second-complete
  (implies (and (int-mulpow-two128-second-hyps)
                (equal (lookup-equal z0 asg)
                       (expt 2 (* 2 (lookup-equal b1 asg))))
                (equal (lookup-equal m asg)
                       (expt 2 (* 2 (lookup-equal b1 asg))))
                (equal (lookup-equal-list sqs asg)
                       (int->lebits (expt 2 (* 2 (lookup-equal b1 asg))) 128))
                (equal (lookup-equal-list carry asg) (int->lebits 0 65))
                (equal (lookup-equal-list ps asg)
                       (int->lebits (* 2 (expt 2 (* 2 (lookup-equal b1 asg))))
                                    128))
                (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                (equal (lookup-equal isneq asg) 0)
                (equal (lookup-equal mult asg) 1)
                (equal (lookup-equal out asg) 0)
                (equal (lookup-equal-list rs asg)
                       (int->lebits
                        (expt 2 (+ (* 2 (lookup-equal b1 asg))
                                   (lookup-equal b2 asg)))
                        128)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-second-gadget b1 b2 z0 m sqs carry ps fc
                                             mult isneq out rs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-sq2-complete)
        (:instance int-mulpow-two128-tail-complete
                   (e b2) (a (expt 2 (* 2 (lookup-equal b1 asg)))))
        (:instance int-mulpow-two128-second-arith
                   (b1 (lookup-equal b1 asg)) (b2 (lookup-equal b2 asg))))
  :in-theory (e/d (int-mulpow-two128-second-gadget
                   r1cs::r1cs-constraints-holdp-of-append)
                  (int->lebits int-valuep expt int-mulpow-pc-honest-isneq
                   int-mulpow-two128-sq2-gadget
                   int-mulpow-two128-tail-gadget)))

; Iterations from the third on: the record is the list of wires
;   (z0 z2 m sqs carry ps fc mult isneq out rs)
; of the checked squaring, the doubling with flags, the overflow assertion,
; and the selected result (kept at index 10).

(defund int-mulpow-two128-rec-okp (rec asg)
  (declare (xargs :verify-guards nil))
  (and (true-listp rec)
       (equal (len rec) 11)
       (symbolp (nth 0 rec)) (symbolp (nth 1 rec)) (symbolp (nth 2 rec))
       (symbol-listp (nth 3 rec)) (symbol-listp (nth 4 rec))
       (symbol-listp (nth 5 rec)) (symbol-listp (nth 6 rec))
       (symbolp (nth 7 rec)) (symbolp (nth 8 rec)) (symbolp (nth 9 rec))
       (symbol-listp (nth 10 rec))
       (equal (len (nth 3 rec)) 128)
       (equal (len (nth 4 rec)) 65)
       (equal (len (nth 5 rec)) 128)
       (equal (len (nth 6 rec)) 65)
       (equal (len (nth 10 rec)) 128)
       (r1cs::valuation-bindsp asg (nth 0 rec))
       (r1cs::valuation-bindsp asg (nth 1 rec))
       (r1cs::valuation-bindsp asg (nth 2 rec))
       (r1cs::valuation-binds-allp asg (nth 3 rec))
       (r1cs::valuation-binds-allp asg (nth 4 rec))
       (r1cs::valuation-binds-allp asg (nth 5 rec))
       (r1cs::valuation-binds-allp asg (nth 6 rec))
       (r1cs::valuation-bindsp asg (nth 7 rec))
       (r1cs::valuation-bindsp asg (nth 8 rec))
       (r1cs::valuation-bindsp asg (nth 9 rec))
       (r1cs::valuation-binds-allp asg (nth 10 rec))))

(defruled int-mulpow-two128-rec-okp-out
  (implies (int-mulpow-two128-rec-okp rec asg)
           (and (symbol-listp (nth 10 rec))
                (equal (len (nth 10 rec)) 128)
                (r1cs::valuation-binds-allp asg (nth 10 rec))))
  :enable int-mulpow-two128-rec-okp)

(defund int-mulpow-two128-step-gadget (e rs rec one p)
  (declare (xargs :verify-guards nil))
  (append (int-mul-checked-unsigned-any-gadget rs rs (nth 0 rec) (nth 1 rec)
                                               (nth 2 rec) (nth 3 rec)
                                               (nth 4 rec) p)
          (int-mulpow-two128-tail-gadget e (nth 3 rec) (nth 5 rec) (nth 6 rec)
                                         (nth 7 rec) (nth 8 rec) (nth 9 rec)
                                         (nth 10 rec) one p)))

(defruled int-mulpow-two128-step-sound
  (implies (and (equal p (base-prime))
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (natp v)
                (int-valuep (expt 2 v) nil 128)
                (equal (lookup-equal-list rs asg) (int->lebits (expt 2 v) 128))
                (int-mulpow-two128-rec-okp rec asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-step-gadget e rs rec one p) asg p))
           (and (int-valuep (expt 2 (+ (* 2 v) (lookup-equal e asg))) nil 128)
                (equal (lookup-equal-list (nth 10 rec) asg)
                       (int->lebits (expt 2 (+ (* 2 v) (lookup-equal e asg)))
                                    128))))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-sound
                   (xs rs) (ys rs) (z0 (nth 0 rec)) (z2 (nth 1 rec))
                   (m (nth 2 rec)) (zs (nth 3 rec)) (carry (nth 4 rec))
                   (x (expt 2 v)) (y (expt 2 v)) (n 128))
        (:instance int-mulpow-two128-tail-sound
                   (sqs (nth 3 rec)) (ps (nth 5 rec)) (fc (nth 6 rec))
                   (mult (nth 7 rec)) (isneq (nth 8 rec)) (out (nth 9 rec))
                   (rs (nth 10 rec)) (a (* (expt 2 v) (expt 2 v))))
        (:instance int-mulpow-pw-expt-step (x 2) (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-two128-step-gadget
                   int-mulpow-two128-rec-okp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mul-checked-spec
                   int-mulpow-pc-integerp-when-int-valuep
                   (:e integer-widthp)
                   bitp)
                  (int->lebits int-valuep expt
                   int-mul-checked-unsigned-any-gadget
                   int-mulpow-two128-tail-gadget)))

(defund int-mulpow-two128-rec-honestp (rec v b asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (expt 2 v))
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
         (equal (lookup-equal-list (nth 5 rec) asg) (int->lebits (* 2 a) 128))
         (equal (lookup-equal-list (nth 6 rec) asg)
                (int->lebits (floor (* 2 a) (expt 2 128)) 65))
         (equal (lookup-equal (nth 7 rec) asg) 1)
         (equal (lookup-equal (nth 8 rec) asg)
                (int-mulpow-pc-honest-isneq (* 2 a) 128))
         (equal (lookup-equal (nth 9 rec) asg) 0)
         (equal (lookup-equal-list (nth 10 rec) asg)
                (int->lebits (expt 2 (+ (* 2 v) b)) 128)))))

(defruled int-mulpow-two128-rec-honestp-out
  (implies (int-mulpow-two128-rec-honestp rec v b asg)
           (equal (lookup-equal-list (nth 10 rec) asg)
                  (int->lebits (expt 2 (+ (* 2 v) b)) 128)))
  :enable int-mulpow-two128-rec-honestp)

(defruled int-mulpow-two128-step-complete
  (implies (and (equal p (base-prime))
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (natp v)
                (int-valuep (expt 2 (+ (* 2 v) (lookup-equal e asg))) nil 128)
                (equal (lookup-equal-list rs asg) (int->lebits (expt 2 v) 128))
                (int-mulpow-two128-rec-okp rec asg)
                (int-mulpow-two128-rec-honestp rec v (lookup-equal e asg) asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-step-gadget e rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mul-checked-unsigned-any-gadget-complete
                   (xs rs) (ys rs) (z0 (nth 0 rec)) (z2 (nth 1 rec))
                   (m (nth 2 rec)) (zs (nth 3 rec)) (carry (nth 4 rec))
                   (x (expt 2 v)) (y (expt 2 v)) (n 128))
        (:instance int-mulpow-two128-tail-complete
                   (sqs (nth 3 rec)) (ps (nth 5 rec)) (fc (nth 6 rec))
                   (mult (nth 7 rec)) (isneq (nth 8 rec)) (out (nth 9 rec))
                   (rs (nth 10 rec)) (a (* (expt 2 v) (expt 2 v))))
        (:instance int-mulpow-pc-range-step (x 2) (b (lookup-equal e asg))
                   (n 128))
        (:instance int-mulpow-pw-expt-step (x 2) (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-two128-step-gadget
                   int-mulpow-two128-rec-okp
                   int-mulpow-two128-rec-honestp
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mul-checked-spec
                   int-mulpow-pc-integerp-when-int-valuep
                   (:e integer-widthp)
                   bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-pc-honest-isneq
                   int-mulpow-hi int-mulpow-lo int-karatsuba-multiply-spec
                   int-mul-checked-unsigned-any-gadget
                   int-mulpow-two128-tail-gadget)))


(defund int-mulpow-two128-recs-okp (bs recs asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-two128-rec-okp (car recs) asg)
         (int-mulpow-two128-recs-okp (cdr bs) (cdr recs) asg))))

(defund int-mulpow-two128-loop-gadget (bs rs recs one p)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      nil
    (append (int-mulpow-two128-step-gadget (car bs) rs (car recs) one p)
            (int-mulpow-two128-loop-gadget (cdr bs) (nth 10 (car recs))
                                           (cdr recs) one p))))

(defruled int-mulpow-two128-loop-sound
  (implies (and (equal p (base-prime))
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (natp v)
                (int-valuep (expt 2 v) nil 128)
                (equal (lookup-equal-list rs asg) (int->lebits (expt 2 v) 128))
                (int-mulpow-two128-recs-okp bs recs asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-two128-loop-gadget bs rs recs one p) asg p))
           (and (int-valuep
                 (expt 2 (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                 nil 128)
                (equal (lookup-equal-list (int-mulpow-pw-loop-out bs rs recs) asg)
                       (int->lebits
                        (expt 2 (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                        128))))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-two128-loop-gadget
                            int-mulpow-pw-loop-out
                            int-mulpow-two128-recs-okp
                            int-mulpow-msb-val
                            int-mulpow-two128-rec-okp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-two128-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defund int-mulpow-two128-recs-honestp (bs recs v asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-two128-rec-honestp (car recs) v (lookup-equal (car bs) asg)
                                        asg)
         (int-mulpow-two128-recs-honestp (cdr bs) (cdr recs)
                                         (+ (* 2 v) (lookup-equal (car bs) asg))
                                         asg))))

(defruled int-mulpow-two128-step-complete-bounded
  (implies (and (equal p (base-prime))
                (symbol-listp rs) (equal (len rs) 128)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (natp v) (natp ee)
                (<= (+ (* 2 v) (lookup-equal e asg)) ee)
                (int-valuep (expt 2 ee) nil 128)
                (equal (lookup-equal-list rs asg) (int->lebits (expt 2 v) 128))
                (int-mulpow-two128-rec-okp rec asg)
                (int-mulpow-two128-rec-honestp rec v (lookup-equal e asg) asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-step-gadget e rs rec one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-step-complete)
        (:instance int-mulpow-pc-range-mono
                   (x 2) (a (+ (* 2 v) (lookup-equal e asg))) (b ee) (n 128)))
  :in-theory (e/d (bitp)
                  (int->lebits int-valuep expt
                   int-mulpow-two128-step-gadget int-mulpow-two128-rec-okp
                   int-mulpow-two128-rec-honestp)))

(defruled int-mulpow-two128-loop-complete
  (implies (and (equal p (base-prime))
                (symbol-listp rs) (equal (len rs) 128)
                (symbol-listp bs) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list bs asg))
                (natp v) (natp ee)
                (<= (int-mulpow-msb-val (lookup-equal-list bs asg) v) ee)
                (int-valuep (expt 2 ee) nil 128)
                (equal (lookup-equal-list rs asg) (int->lebits (expt 2 v) 128))
                (int-mulpow-two128-recs-okp bs recs asg)
                (int-mulpow-two128-recs-honestp bs recs v asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-two128-loop-gadget bs rs recs one p) asg p))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-two128-loop-gadget
                            int-mulpow-two128-recs-okp
                            int-mulpow-two128-recs-honestp
                            int-mulpow-msb-val
                            int-mulpow-two128-rec-okp-out
                            int-mulpow-two128-rec-honestp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt int-valuep)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-two128-step-complete-bounded
                                  (e (car bs)) (rec (car recs)))
                       (:instance int-mulpow-msb-val-ge
                                  (bs (cdr (lookup-equal-list bs asg)))
                                  (v (+ (* 2 v) (lookup-equal (car bs) asg)))))))))

(defruled int-mulpow-two128-two-facts
  (implies (and (symbol-listp l) (consp (cdr l))
                (r1cs::valuation-binds-allp asg l)
                (bit-listp (lookup-equal-list l asg)))
           (and (symbolp (car l))
                (symbolp (cadr l))
                (symbol-listp (cddr l))
                (r1cs::valuation-bindsp asg (car l))
                (r1cs::valuation-bindsp asg (cadr l))
                (r1cs::valuation-binds-allp asg (cddr l))
                (bitp (lookup-equal (car l) asg))
                (bitp (lookup-equal (cadr l) asg))
                (bit-listp (lookup-equal-list (cddr l) asg))
                (equal (int-mulpow-msb-val
                        (lookup-equal-list (cddr l) asg)
                        (+ (* 2 (lookup-equal (car l) asg))
                           (lookup-equal (cadr l) asg)))
                       (int-mulpow-msb-val (cdr (lookup-equal-list l asg))
                                           (car (lookup-equal-list l asg))))))
  :do-not-induct t
  :expand ((lookup-equal-list l asg)
           (lookup-equal-list (cdr l) asg)
           (int-mulpow-msb-val (cdr (lookup-equal-list l asg))
                               (car (lookup-equal-list l asg)))
           (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (cdr l))
           (:free (a b v) (int-mulpow-msb-val (cons a b) v)))
  :in-theory (enable bitp))

(defruled int-mulpow-two128-rev2-facts
  (implies (and (symbol-listp es) (consp (cdr es))
                (r1cs::valuation-binds-allp asg es)
                (bit-listp (lookup-equal-list es asg)))
           (and (symbolp (car (rev es)))
                (symbolp (cadr (rev es)))
                (symbol-listp (cddr (rev es)))
                (r1cs::valuation-bindsp asg (car (rev es)))
                (r1cs::valuation-bindsp asg (cadr (rev es)))
                (r1cs::valuation-binds-allp asg (cddr (rev es)))
                (bitp (lookup-equal (car (rev es)) asg))
                (bitp (lookup-equal (cadr (rev es)) asg))
                (bit-listp (lookup-equal-list (cddr (rev es)) asg))
                (equal (int-mulpow-msb-val
                        (lookup-equal-list (cddr (rev es)) asg)
                        (+ (* 2 (lookup-equal (car (rev es)) asg))
                           (lookup-equal (cadr (rev es)) asg)))
                       (lebits=>nat (lookup-equal-list es asg)))))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-two-facts (l (rev es)))
        (:instance int-mulpow-pw-binds-allp-of-rev (l es))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg))))
  :in-theory (e/d (lookup-equal-list-of-rev)
                  (rev int-mulpow-msb-val)))

(defund int-pow-two-checked-128-gadget (es z0 m sqs carry ps fc mult isneq out
                                           r0 recs one p)
  (declare (xargs :verify-guards nil))
  (b* ((bs (rev es)))
    (append (int-mulpow-two128-second-gadget (car bs) (cadr bs) z0 m sqs carry
                                             ps fc mult isneq out r0 one p)
            (int-mulpow-two128-loop-gadget (cddr bs) r0 recs one p))))

(defund int-pow-two-checked-128-gadget-out (es r0 recs)
  (declare (xargs :verify-guards nil))
  (int-mulpow-pw-loop-out (cddr (rev es)) r0 recs))

(defmacro int-pow-two-checked-128-hyps ()
  '(and (equal p (base-prime))
        (symbol-listp es) (consp (cdr es))
        (symbolp z0) (symbolp m)
        (symbol-listp sqs) (equal (len sqs) 128)
        (symbol-listp carry) (equal (len carry) 65)
        (symbol-listp ps) (equal (len ps) 128)
        (symbol-listp fc) (equal (len fc) 65)
        (symbol-listp r0) (equal (len r0) 128)
        (symbolp mult) (symbolp isneq) (symbolp out) (symbolp one)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg es)
        (r1cs::valuation-bindsp asg z0)
        (r1cs::valuation-bindsp asg m)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg carry)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg fc)
        (r1cs::valuation-binds-allp asg r0)
        (r1cs::valuation-bindsp asg mult)
        (r1cs::valuation-bindsp asg isneq)
        (r1cs::valuation-bindsp asg out)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (bit-listp (lookup-equal-list es asg))
        (int-mulpow-two128-recs-okp (cddr (rev es)) recs asg)))

(defruled int-pow-two-checked-128-gadget-sound
  :short "Unsigned two.pow_checked(e) at 128 bits, where two is the constant
          2: the circuit of shl_checked before the final mul_checked."
  (implies (and (int-pow-two-checked-128-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult
                                                 isneq out r0 recs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-pow-checked-spec 2 e nil 128) (spec-error)))
                  (equal (lookup-equal-list
                          (int-pow-two-checked-128-gadget-out es r0 recs) asg)
                         (int->lebits (int-pow-checked-spec 2 e nil 128)
                                      128)))))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-rev2-facts)
        (:instance int-mulpow-two128-second-sound
                   (b1 (car (rev es))) (b2 (cadr (rev es))) (rs r0))
        (:instance int-mulpow-two128-loop-sound
                   (bs (cddr (rev es))) (rs r0)
                   (v (+ (* 2 (lookup-equal (car (rev es)) asg))
                         (lookup-equal (cadr (rev es)) asg)))))
  :in-theory (e/d (int-pow-two-checked-128-gadget
                   int-pow-two-checked-128-gadget-out
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   bitp)
                  (int->lebits expt int-valuep rev)))

(defruled int-pow-two-checked-128-gadget-complete
  (implies (and (int-pow-two-checked-128-hyps)
                (not (equal (int-pow-checked-spec
                             2 (lebits=>nat (lookup-equal-list es asg)) nil 128)
                            (spec-error)))
                (b* ((b1 (lookup-equal (car (rev es)) asg))
                     (b2 (lookup-equal (cadr (rev es)) asg)))
                  (and (equal (lookup-equal z0 asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal m asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal-list sqs asg)
                              (int->lebits (expt 2 (* 2 b1)) 128))
                       (equal (lookup-equal-list carry asg) (int->lebits 0 65))
                       (equal (lookup-equal-list ps asg)
                              (int->lebits (* 2 (expt 2 (* 2 b1))) 128))
                       (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                       (equal (lookup-equal isneq asg) 0)
                       (equal (lookup-equal mult asg) 1)
                       (equal (lookup-equal out asg) 0)
                       (equal (lookup-equal-list r0 asg)
                              (int->lebits (expt 2 (+ (* 2 b1) b2)) 128))
                       (int-mulpow-two128-recs-honestp (cddr (rev es)) recs
                                                       (+ (* 2 b1) b2) asg))))
           (r1cs::r1cs-constraints-holdp
            (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult isneq
                                            out r0 recs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-two128-rev2-facts)
        (:instance int-mulpow-two128-second-complete
                   (b1 (car (rev es))) (b2 (cadr (rev es))) (rs r0))
        (:instance int-mulpow-two128-loop-complete
                   (bs (cddr (rev es))) (rs r0)
                   (v (+ (* 2 (lookup-equal (car (rev es)) asg))
                         (lookup-equal (cadr (rev es)) asg)))
                   (ee (lebits=>nat (lookup-equal-list es asg)))))
  :in-theory (e/d (int-pow-two-checked-128-gadget
                   int-pow-checked-spec
                   r1cs::r1cs-constraints-holdp-of-append
                   bitp)
                  (int->lebits expt int-valuep rev)))


(defund int-shl-checked-unsigned-128-gadget (xs es z0 m sqs carry ps fc mult
                                                isneq out r0 recs
                                                mz0 mz2 mm zs mcarry one p)
  (declare (xargs :verify-guards nil))
  (append (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult isneq
                                          out r0 recs one p)
          (int-mul-checked-unsigned-any-gadget
           xs (int-pow-two-checked-128-gadget-out es r0 recs)
           mz0 mz2 mm zs mcarry p)))

(defruled int-mulpow-two128-out-facts
  (implies (and (int-mulpow-two128-recs-okp bs recs asg)
                (symbol-listp r0) (equal (len r0) 128)
                (r1cs::valuation-binds-allp asg r0))
           (and (symbol-listp (int-mulpow-pw-loop-out bs r0 recs))
                (equal (len (int-mulpow-pw-loop-out bs r0 recs)) 128)
                (r1cs::valuation-binds-allp
                 asg (int-mulpow-pw-loop-out bs r0 recs))))
  :induct (int-mulpow-pw-loop-out bs r0 recs)
  :in-theory (enable int-mulpow-pw-loop-out int-mulpow-two128-recs-okp
                     int-mulpow-two128-rec-okp-out))

(defruled int-mulpow-two128-exponent-bound
  (implies (and (natp e) (int-valuep (expt 2 e) nil 128))
           (< e 128))
  :use ((:instance acl2::<=-of-expt-and-expt-same-base-linear
                   (r 2) (i1 128) (i2 e)))
  :in-theory (enable int-valuep int-min int-max))

(defruled int-mulpow-two128-shl-spec
  (implies (and (natp e) (int-valuep x nil 128))
           (equal (int-shl-checked-spec x e nil 128)
                  (if (int-valuep (expt 2 e) nil 128)
                      (int-mul-checked-spec x (expt 2 e) nil 128)
                    (spec-error))))
  :do-not-induct t
  :cases ((< e 128))
  :use (int-mulpow-two128-exponent-bound
        (:instance acl2::<=-of-expt-and-expt-same-base-linear
                   (r 2) (i1 e) (i2 127)))
  :in-theory (enable int-shl-checked-spec int-mul-checked-spec
                     int-valuep int-min int-max))

(defmacro int-shl-checked-unsigned-128-hyps ()
  '(and (int-pow-two-checked-128-hyps)
        (symbol-listp xs) (equal (len xs) 128)
        (symbolp mz0) (symbolp mz2) (symbolp mm)
        (symbol-listp zs) (equal (len zs) 128)
        (symbol-listp mcarry) (equal (len mcarry) 65)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-bindsp asg mz0)
        (r1cs::valuation-bindsp asg mz2)
        (r1cs::valuation-bindsp asg mm)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-binds-allp asg mcarry)
        (int-valuep x nil 128)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))))

(defruled int-shl-checked-unsigned-128-gadget-sound
  :short "Unsigned shl_checked (also Shl, ShlAssign) at 128 bits:
          self.mul_checked(two.pow_checked(rhs)), any magnitude width."
  (implies (and (int-shl-checked-unsigned-128-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-unsigned-128-gadget xs es z0 m sqs carry ps fc
                                                      mult isneq out r0 recs
                                                      mz0 mz2 mm zs mcarry
                                                      one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-shl-checked-spec x e nil 128) (spec-error)))
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (int-shl-checked-spec x e nil 128)
                                      128)))))
  :do-not-induct t
  :use ((:instance int-pow-two-checked-128-gadget-sound)
        (:instance int-mulpow-two128-out-facts (bs (cddr (rev es))))
        (:instance int-mul-checked-unsigned-any-gadget-sound
                   (ys (int-pow-two-checked-128-gadget-out es r0 recs))
                   (z0 mz0) (z2 mz2) (m mm) (carry mcarry)
                   (y (expt 2 (lebits=>nat (lookup-equal-list es asg))))
                   (n 128))
        (:instance int-mulpow-two128-shl-spec
                   (e (lebits=>nat (lookup-equal-list es asg)))))
  :in-theory (e/d (int-shl-checked-unsigned-128-gadget
                   int-pow-two-checked-128-gadget-out
                   r1cs::r1cs-constraints-holdp-of-append
                   int-pow-checked-spec
                   (:e integer-widthp))
                  (int->lebits expt int-valuep rev
                   int-mul-checked-unsigned-any-gadget
                   int-pow-two-checked-128-gadget)))

(defruled int-shl-checked-unsigned-128-gadget-complete
  (implies (and (int-shl-checked-unsigned-128-hyps)
                (b* ((e (lebits=>nat (lookup-equal-list es asg)))
                     (f (expt 2 e))
                     (b1 (lookup-equal (car (rev es)) asg))
                     (b2 (lookup-equal (cadr (rev es)) asg)))
                  (and (not (equal (int-shl-checked-spec x e nil 128)
                                   (spec-error)))
                       (equal (lookup-equal z0 asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal m asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal-list sqs asg)
                              (int->lebits (expt 2 (* 2 b1)) 128))
                       (equal (lookup-equal-list carry asg) (int->lebits 0 65))
                       (equal (lookup-equal-list ps asg)
                              (int->lebits (* 2 (expt 2 (* 2 b1))) 128))
                       (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                       (equal (lookup-equal isneq asg) 0)
                       (equal (lookup-equal mult asg) 1)
                       (equal (lookup-equal out asg) 0)
                       (equal (lookup-equal-list r0 asg)
                              (int->lebits (expt 2 (+ (* 2 b1) b2)) 128))
                       (int-mulpow-two128-recs-honestp (cddr (rev es)) recs
                                                       (+ (* 2 b1) b2) asg)
                       (equal (lookup-equal-list zs asg)
                              (int->lebits (* x f) 128))
                       (equal (lookup-equal mz0 asg)
                              (* (int-mulpow-lo x 128) (int-mulpow-lo f 128)))
                       (equal (lookup-equal mz2 asg)
                              (* (int-mulpow-hi x 128) (int-mulpow-hi f 128)))
                       (equal (lookup-equal mm asg)
                              (* (+ (int-mulpow-hi x 128) (int-mulpow-lo x 128))
                                 (+ (int-mulpow-hi f 128) (int-mulpow-lo f 128))))
                       (equal (lookup-equal-list mcarry asg)
                              (second (int-karatsuba-multiply-spec
                                       x f nil 128))))))
           (r1cs::r1cs-constraints-holdp
            (int-shl-checked-unsigned-128-gadget xs es z0 m sqs carry ps fc
                                                 mult isneq out r0 recs
                                                 mz0 mz2 mm zs mcarry one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-pow-two-checked-128-gadget-complete)
        (:instance int-pow-two-checked-128-gadget-sound)
        (:instance int-mulpow-two128-out-facts (bs (cddr (rev es))))
        (:instance int-mul-checked-unsigned-any-gadget-complete
                   (ys (int-pow-two-checked-128-gadget-out es r0 recs))
                   (z0 mz0) (z2 mz2) (m mm) (carry mcarry)
                   (y (expt 2 (lebits=>nat (lookup-equal-list es asg))))
                   (n 128))
        (:instance int-mulpow-two128-shl-spec
                   (e (lebits=>nat (lookup-equal-list es asg)))))
  :in-theory (e/d (int-shl-checked-unsigned-128-gadget
                   int-pow-two-checked-128-gadget-out
                   r1cs::r1cs-constraints-holdp-of-append
                   int-pow-checked-spec int-mul-checked-spec
                   int-mulpow-pc-integerp-when-int-valuep
                   (:e integer-widthp))
                  (int->lebits expt int-valuep rev
                   int-mulpow-lo int-mulpow-hi int-karatsuba-multiply-spec
                   int-mul-checked-unsigned-any-gadget
                   int-pow-two-checked-128-gadget)))


; Boolean::ternary(!c, y, z) for variable bits, where !c is the linear
; combination 1 - c: (1 - c) * (y - z) = w - z.

(defund int-mulpow-notcond-if-gadget (c y z w one p)
  (declare (xargs :verify-guards nil))
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 one) (list (1- p) c))
         :b (list (list (1- p) z) (list 1 y))
         :c (list (list (1- p) z) (list 1 w)))))

(defruled int-mulpow-notcond-if-gadget-to-if
  (implies (and (primep p)
                (symbolp c) (symbolp y) (symbolp z) (symbolp w) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal c asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-notcond-if-gadget c y z w one p) asg p)
                  (equal (lookup-equal w asg)
                         (if (equal (lookup-equal c asg) 0)
                             (lookup-equal y asg)
                           (lookup-equal z asg)))))
  :do-not-induct t
  :cases ((equal (lookup-equal c asg) 0))
  :enable (int-mulpow-notcond-if-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           bitp))

(defund int-mulpow-notcond-ternary-gadget (c ys zs ws one p)
  (declare (xargs :verify-guards nil))
  (if (endp ys)
      nil
    (append (int-mulpow-notcond-if-gadget c (car ys) (car zs) (car ws) one p)
            (int-mulpow-notcond-ternary-gadget c (cdr ys) (cdr zs) (cdr ws)
                                               one p))))

(defun int-mulpow-notcond-ind (ys zs ws)
  (if (or (atom ys) (atom zs) (atom ws))
      nil
    (int-mulpow-notcond-ind (cdr ys) (cdr zs) (cdr ws))))

(defruled int-mulpow-notcond-ternary-gadget-to-if
  (implies (and (primep p)
                (symbolp c) (symbol-listp ys) (symbol-listp zs)
                (symbol-listp ws) (symbolp one)
                (equal (len zs) (len ys))
                (equal (len ws) (len ys))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal c asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-notcond-ternary-gadget c ys zs ws one p) asg p)
                  (equal (lookup-equal-list ws asg)
                         (if (equal (lookup-equal c asg) 0)
                             (lookup-equal-list ys asg)
                           (lookup-equal-list zs asg)))))
  :induct (int-mulpow-notcond-ind ys zs ws)
  :enable (int-mulpow-notcond-ternary-gadget
           int-mulpow-notcond-if-gadget-to-if
           r1cs::r1cs-constraints-holdp-of-append
           lookup-equal-list))

; Integer::is_equal against the constant MIN = 2^127 (as bits): the field
; is_not_equal of from_bits_le(fs) - 2^127.

(defund int-mulpow-shl-min-delta (fs)
  (declare (xargs :verify-guards nil))
  (cons (list (- (expt 2 127)) 1) (pow2sum-vector fs 0)))

(defruled int-mulpow-shl-min-delta-value
  (implies (and (equal p (base-prime))
                (symbol-listp fs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg fs)
                (bit-listp (lookup-equal-list fs asg))
                (equal (len fs) 128))
           (equal (equal (r1cs::dot-product (int-mulpow-shl-min-delta fs) asg p)
                         0)
                  (equal (lebits=>nat (lookup-equal-list fs asg))
                         (expt 2 127))))
  :do-not-induct t
  :expand ((:free (x y q) (r1cs::dot-product (cons x y) asg q)))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs fs) (i 0))
        (:instance int-mulpow-pw-lebits-bound (bs (lookup-equal-list fs asg)))
        (:instance int-mulpow-shl-min-delta-arith
                   (v (lebits=>nat (lookup-equal-list fs asg)))))
  :enable (int-mulpow-shl-min-delta pfield::add pfield::mul
           acl2::mod-of-+-of-mod-arg2 acl2::mod-of-+-of-mod-arg1)
  :disable (r1cs::dot-product)
  :prep-lemmas
  ((defrule int-mulpow-shl-min-delta-arith
     (implies (and (natp v) (< v (expt 2 128)))
              (equal (equal (mod (+ (- (expt 2 127)) v) (base-prime)) 0)
                     (equal v (expt 2 127))))
     :rule-classes nil
     :cases ((<= (expt 2 127) v))
     :use ((:instance acl2::mod-when-< (x (+ (- (expt 2 127)) v))
                      (y (base-prime)))
           (:instance acl2::mod-of-+-same-arg1 (x (+ (- (expt 2 127)) v))
                      (y (base-prime))))
     :in-theory (enable (:e base-prime)))))

(defun int-mulpow-shl-factor (e)
  (declare (xargs :verify-guards nil))
  (if (equal e 127) (- (expt 2 127)) (expt 2 e)))

(defun int-mulpow-shl-lhs (x e)
  (declare (xargs :verify-guards nil))
  (if (equal e 127) (int-sub-wrapped-spec 0 x t 128) x))

(defruled int-mulpow-shl-factor-facts
  (implies (and (natp e) (< e 128))
           (and (int-valuep (int-mulpow-shl-factor e) t 128)
                (equal (int->lebits (int-mulpow-shl-factor e) 128)
                       (int->lebits (expt 2 e) 128))
                (equal (equal (expt 2 e) (expt 2 127)) (equal e 127))))
  :do-not-induct t
  :cases ((< e 127))
  :use ((:instance acl2::<=-of-expt-and-expt-same-base-linear
                   (r 2) (i1 e) (i2 126))
        (:instance acl2::<-of-expt-and-expt-same-base (r 2) (i e) (j 127)))
  :in-theory (enable int-valuep int-min int-max int->lebits))

(defruled int-mulpow-shl-lhs-valuep
  (implies (int-valuep x t 128)
           (int-valuep (int-mulpow-shl-lhs x e) t 128))
  :enable (int-sub-wrapped-spec int-wrap int-valuep int-min int-max))

(defruled int-mulpow-shl-neg-value
  (implies (int-valuep x t 128)
           (equal (int-sub-wrapped-spec 0 x t 128)
                  (if (equal x (- (expt 2 127))) x (- x))))
  :do-not-induct t
  :cases ((< x 0) (equal x 0))
  :use ((:instance acl2::mod-when-< (x (- x)) (y (expt 2 128)))
        (:instance acl2::mod-of-+-same-arg1 (x (- x)) (y (expt 2 128))))
  :enable (int-sub-wrapped-spec int-wrap int-valuep int-min int-max
           acl2::mod-when-<))

(defruled int-mulpow-shl-signed-spec
  (implies (and (int-valuep x t 128) (natp e) (< e 128))
           (equal (int-shl-checked-spec x e t 128)
                  (int-mul-checked-spec (int-mulpow-shl-lhs x e)
                                        (int-mulpow-shl-factor e) t 128)))
  :do-not-induct t
  :cases ((not (equal e 127))
          (equal x (- (expt 2 127))))
  :use int-mulpow-shl-neg-value
  :enable (int-shl-checked-spec int-mul-checked-spec
           int-valuep int-min int-max))


(defund int-shl-checked-signed-128-gadget
  (xs es z0 m sqs carry ps fc mult isneq out r0 recs
   emult eneq nxs nc lhs
   axs mxs cx ays mys cy mz0 mz2 mm mps mcarry s lws po tt u v nps nc2 zs
   one p)
  (declare (xargs :verify-guards nil))
  (b* ((fs (int-pow-two-checked-128-gadget-out es r0 recs)))
    (append (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult isneq
                                            out r0 recs one p)
            (int-mulpow-pc-neq-gadget (int-mulpow-shl-min-delta fs)
                                      emult eneq one p)
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits 0 128) xs nxs nc one p)
            (int-mulpow-notcond-ternary-gadget eneq nxs xs lhs one p)
            (int-mul-checked-signed-gadget
             lhs fs axs mxs cx ays mys cy mz0 mz2 mm mps mcarry
             s lws po tt u v nps nc2 zs one p))))

(defmacro int-shl-checked-signed-128-hyps ()
  '(and (int-pow-two-checked-128-hyps)
        (symbol-listp xs) (equal (len xs) 128)
        (symbolp emult) (symbolp eneq)
        (symbol-listp nxs) (equal (len nxs) 128) (symbolp nc)
        (symbol-listp lhs) (equal (len lhs) 128)
        (symbol-listp axs) (symbol-listp mxs) (symbolp cx)
        (symbol-listp ays) (symbol-listp mys) (symbolp cy)
        (symbolp mz0) (symbolp mz2) (symbolp mm)
        (symbol-listp mps) (symbol-listp mcarry)
        (symbolp s) (symbol-listp lws)
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbol-listp nps) (symbolp nc2)
        (symbol-listp zs)
        (equal (len axs) 128) (equal (len mxs) 128)
        (equal (len ays) 128) (equal (len mys) 128)
        (equal (len mps) 128) (equal (len mcarry) 65)
        (equal (len lws) 126) (equal (len nps) 128) (equal (len zs) 128)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-bindsp asg emult)
        (r1cs::valuation-bindsp asg eneq)
        (r1cs::valuation-binds-allp asg nxs)
        (r1cs::valuation-bindsp asg nc)
        (r1cs::valuation-binds-allp asg lhs)
        (r1cs::valuation-binds-allp asg axs)
        (r1cs::valuation-binds-allp asg mxs)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ays)
        (r1cs::valuation-binds-allp asg mys)
        (r1cs::valuation-bindsp asg cy)
        (r1cs::valuation-bindsp asg mz0)
        (r1cs::valuation-bindsp asg mz2)
        (r1cs::valuation-bindsp asg mm)
        (r1cs::valuation-binds-allp asg mps)
        (r1cs::valuation-binds-allp asg mcarry)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nc2)
        (r1cs::valuation-binds-allp asg zs)
        (int-valuep x t 128)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))))

(defruled int-mulpow-shl-fs-value
  (implies (and (natp e) (< e 128))
           (equal (lebits=>nat (int->lebits (expt 2 e) 128)) (expt 2 e)))
  :use ((:instance acl2::<-of-expt-and-expt-same-base (r 2) (i e) (j 128)))
  :enable (lebits=>nat-of-int->lebits acl2::mod-when-<))

(defruled int-pow-two-checked-128-gadget-out-facts
  (implies (and (int-mulpow-two128-recs-okp (cddr (rev es)) recs asg)
                (symbol-listp r0) (equal (len r0) 128)
                (r1cs::valuation-binds-allp asg r0))
           (and (symbol-listp (int-pow-two-checked-128-gadget-out es r0 recs))
                (equal (len (int-pow-two-checked-128-gadget-out es r0 recs))
                       128)
                (r1cs::valuation-binds-allp
                 asg (int-pow-two-checked-128-gadget-out es r0 recs))))
  :use (:instance int-mulpow-two128-out-facts (bs (cddr (rev es))))
  :enable int-pow-two-checked-128-gadget-out)

(defruled int-shl-checked-signed-128-front-sound
  (implies (and (int-shl-checked-signed-128-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult
                                                 isneq out r0 recs one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-neq-gadget
                  (int-mulpow-shl-min-delta
                   (int-pow-two-checked-128-gadget-out es r0 recs))
                  emult eneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 128) xs nxs nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-notcond-ternary-gadget eneq nxs xs lhs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg)))
                (fs (int-pow-two-checked-128-gadget-out es r0 recs)))
             (and (natp e) (< e 128)
                  (symbol-listp fs) (equal (len fs) 128)
                  (r1cs::valuation-binds-allp asg fs)
                  (equal (lookup-equal-list fs asg)
                         (int->lebits (int-mulpow-shl-factor e) 128))
                  (equal (lookup-equal-list lhs asg)
                         (int->lebits (int-mulpow-shl-lhs x e) 128)))))
  :do-not-induct t
  :use ((:instance int-pow-two-checked-128-gadget-sound)
        int-pow-two-checked-128-gadget-out-facts
        (:instance int-mulpow-two128-exponent-bound
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-factor-facts
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-fs-value
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-pc-neq-sound
                   (delta (int-mulpow-shl-min-delta
                           (int-pow-two-checked-128-gadget-out es r0 recs)))
                   (mult emult) (isneq eneq))
        (:instance int-mulpow-shl-min-delta-value
                   (fs (int-pow-two-checked-128-gadget-out es r0 recs)))
        (:instance int-divshift-sub-wrapped-const-var-sound
                   (signedp t) (n 128) (x 0) (y x) (ys xs) (zs nxs) (z nc))
        (:instance int-mulpow-notcond-ternary-gadget-to-if
                   (c eneq) (ys nxs) (zs xs) (ws lhs)))
  :in-theory (e/d (int-pow-checked-spec
                   int-mulpow-shl-lhs
                   bit-listp-of-int->lebits-explicit
                   (:e integer-widthp)
                   (:e int-valuep)
                   bitp)
                  (int->lebits expt int-valuep rev int-sub-wrapped-spec
                   int-mulpow-shl-factor
                   int-pow-two-checked-128-gadget-out
                   int-pow-two-checked-128-gadget
                   int-mulpow-pc-neq-gadget
                   unsigned-small-sub-wrapped-const-var-gadget
                   int-mulpow-notcond-ternary-gadget)))

(defruled int-shl-checked-signed-128-gadget-sound
  :short "Signed shl_checked (also Shl, ShlAssign) at 128 bits: the unsigned
          two.pow_checked(rhs), the is_equal against MIN, the negation and
          ternary, and the signed mul_checked; any magnitude width."
  (implies (and (int-shl-checked-signed-128-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-signed-128-gadget
                  xs es z0 m sqs carry ps fc mult isneq out r0 recs
                  emult eneq nxs nc lhs
                  axs mxs cx ays mys cy mz0 mz2 mm mps mcarry s lws po tt u v
                  nps nc2 zs one p)
                 asg p))
           (b* ((e (lebits=>nat (lookup-equal-list es asg))))
             (and (not (equal (int-shl-checked-spec x e t 128) (spec-error)))
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (int-shl-checked-spec x e t 128) 128)))))
  :do-not-induct t
  :use ((:instance int-shl-checked-signed-128-front-sound)
        (:instance int-mulpow-shl-factor-facts
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-lhs-valuep
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-signed-spec
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mul-checked-signed-gadget-sound
                   (xs lhs) (ys (int-pow-two-checked-128-gadget-out es r0 recs))
                   (z0 mz0) (z2 mz2) (m mm) (ps mps) (carry mcarry) (nc nc2)
                   (x (int-mulpow-shl-lhs x (lebits=>nat
                                             (lookup-equal-list es asg))))
                   (y (int-mulpow-shl-factor (lebits=>nat
                                              (lookup-equal-list es asg))))
                   (n 128)))
  :in-theory (e/d (int-shl-checked-signed-128-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-sc-lens
                   (:e integer-widthp))
                  (int->lebits expt int-valuep rev
                   int-mulpow-shl-factor int-mulpow-shl-lhs
                   int-shl-checked-spec int-mul-checked-spec
                   int-pow-two-checked-128-gadget-out
                   int-pow-two-checked-128-gadget
                   int-mulpow-pc-neq-gadget
                   unsigned-small-sub-wrapped-const-var-gadget
                   int-mulpow-notcond-ternary-gadget
                   int-mul-checked-signed-gadget)))


(defrule int-mulpow-shl-mod-sum
  (implies (and (integerp a) (integerp v) (posp q))
           (equal (mod (+ (mod a q) (mod v q)) q) (mod (+ a v) q)))
  :rule-classes nil)

(defruled int-mulpow-shl-min-delta-dot
  (implies (and (equal p (base-prime))
                (symbol-listp fs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg fs)
                (bit-listp (lookup-equal-list fs asg)))
           (equal (r1cs::dot-product (int-mulpow-shl-min-delta fs) asg p)
                  (mod (- (lebits=>nat (lookup-equal-list fs asg))
                          (expt 2 127))
                       p)))
  :do-not-induct t
  :expand ((:free (x y q) (r1cs::dot-product (cons x y) asg q)))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (xs fs) (i 0))
        (:instance int-mulpow-shl-mod-sum (a (- (expt 2 127)))
                   (v (lebits=>nat (lookup-equal-list fs asg))) (q p)))
  :enable (int-mulpow-shl-min-delta pfield::add pfield::mul)
  :disable (r1cs::dot-product))

(defun int-mulpow-shl-honest-emult (e)
  (declare (xargs :verify-guards nil))
  (if (equal e 127)
      1
    (pfield::inv (mod (- (expt 2 e) (expt 2 127)) (base-prime)) (base-prime))))

(defmacro int-shl-checked-signed-128-front-honest-hyps ()
  '(b* ((e (lebits=>nat (lookup-equal-list es asg)))
                     (b1 (lookup-equal (car (rev es)) asg))
                     (b2 (lookup-equal (cadr (rev es)) asg))
                     (lv (int-mulpow-shl-lhs x e))
                     )
                  (and (not (equal (int-shl-checked-spec x e t 128)
                                   (spec-error)))
                       (equal (lookup-equal z0 asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal m asg) (expt 2 (* 2 b1)))
                       (equal (lookup-equal-list sqs asg)
                              (int->lebits (expt 2 (* 2 b1)) 128))
                       (equal (lookup-equal-list carry asg) (int->lebits 0 65))
                       (equal (lookup-equal-list ps asg)
                              (int->lebits (* 2 (expt 2 (* 2 b1))) 128))
                       (equal (lookup-equal-list fc asg) (int->lebits 0 65))
                       (equal (lookup-equal isneq asg) 0)
                       (equal (lookup-equal mult asg) 1)
                       (equal (lookup-equal out asg) 0)
                       (equal (lookup-equal-list r0 asg)
                              (int->lebits (expt 2 (+ (* 2 b1) b2)) 128))
                       (int-mulpow-two128-recs-honestp (cddr (rev es)) recs
                                                       (+ (* 2 b1) b2) asg)
                       (equal (lookup-equal eneq asg) (if (equal e 127) 0 1))
                       (equal (lookup-equal emult asg)
                              (int-mulpow-shl-honest-emult e))
                       (equal (lookup-equal-list nxs asg)
                              (int->lebits (int-sub-wrapped-spec 0 x t 128) 128))
                       (equal (lookup-equal nc asg)
                              (if (< 0 (mod x (expt 2 128))) 0 1))
                       (equal (lookup-equal-list lhs asg) (int->lebits lv 128)))))

(defmacro int-shl-checked-signed-128-mul-honest-hyps ()
  '(b* ((e (lebits=>nat (lookup-equal-list es asg)))
       (lv (int-mulpow-shl-lhs x e))
       (fv (int-mulpow-shl-factor e)))
    (and
                       (equal (lookup-equal-list axs asg)
                              (int->lebits (abs lv) 128))
                       (equal (lookup-equal-list mxs asg)
                              (int->lebits (- lv) 128))
                       (equal (lookup-equal cx asg) (int-sub-carry 0 lv 128))
                       (equal (lookup-equal-list ays asg)
                              (int->lebits (abs fv) 128))
                       (equal (lookup-equal-list mys asg)
                              (int->lebits (- fv) 128))
                       (equal (lookup-equal cy asg) (int-sub-carry 0 fv 128))
                       (equal (lookup-equal mz0 asg)
                              (* (int-mulpow-lo (abs lv) 128)
                                 (int-mulpow-lo (abs fv) 128)))
                       (equal (lookup-equal mz2 asg)
                              (* (int-mulpow-hi (abs lv) 128)
                                 (int-mulpow-hi (abs fv) 128)))
                       (equal (lookup-equal mm asg)
                              (* (+ (int-mulpow-hi (abs lv) 128)
                                    (int-mulpow-lo (abs lv) 128))
                                 (+ (int-mulpow-hi (abs fv) 128)
                                    (int-mulpow-lo (abs fv) 128))))
                       (equal (lookup-equal-list mcarry asg)
                              (second (int-karatsuba-multiply-spec
                                       (abs lv) (abs fv) nil 128)))
                       (equal (lookup-equal-list mps asg)
                              (int->lebits (* (abs lv) (abs fv)) 128))
                       (equal (lookup-equal s asg)
                              (bitxor (if (< lv 0) 1 0) (if (< fv 0) 1 0)))
                       (equal (lookup-equal-list lws asg)
                              (int-mulpow-or-scan
                               (car (butlast (int->lebits (* (abs lv) (abs fv))
                                                          128)
                                             1))
                               (cdr (butlast (int->lebits (* (abs lv) (abs fv))
                                                          128)
                                             1))))
                       (equal (lookup-equal po asg) 0)
                       (equal (lookup-equal tt asg)
                              (if (equal (* (abs lv) (abs fv)) (expt 2 127))
                                  1
                                0))
                       (equal (lookup-equal u asg) 1)
                       (equal (lookup-equal v asg) 0)
                       (equal (lookup-equal-list nps asg)
                              (int->lebits (- (* (abs lv) (abs fv))) 128))
                       (equal (lookup-equal nc2 asg)
                              (if (equal (* (abs lv) (abs fv)) 0) 1 0))
                       (equal (lookup-equal-list zs asg)
                              (int->lebits (* lv fv) 128)))))

(defruled int-mulpow-shl-spec-error-when-large
  (implies (and (natp e) (<= 128 e))
           (equal (int-shl-checked-spec x e signedp 128) (spec-error)))
  :enable int-shl-checked-spec)

(defruled int-mulpow-two128-expt-valuep
  (implies (and (natp e) (< e 128))
           (int-valuep (expt 2 e) nil 128))
  :use ((:instance acl2::<-of-expt-and-expt-same-base (r 2) (i e) (j 128)))
  :enable (int-valuep int-min int-max))

(defruled int-shl-checked-signed-128-pow-complete
  (implies (and (int-shl-checked-signed-128-hyps)
                (int-shl-checked-signed-128-front-honest-hyps))
           (and (r1cs::r1cs-constraints-holdp
                 (int-pow-two-checked-128-gadget es z0 m sqs carry ps fc mult
                                                 isneq out r0 recs one p)
                 asg p)
                (natp (lebits=>nat (lookup-equal-list es asg))) (< (lebits=>nat (lookup-equal-list es asg)) 128)
                (symbol-listp (int-pow-two-checked-128-gadget-out es r0 recs)) (equal (len (int-pow-two-checked-128-gadget-out es r0 recs)) 128)
                (r1cs::valuation-binds-allp asg (int-pow-two-checked-128-gadget-out es r0 recs))
                (equal (lookup-equal-list (int-pow-two-checked-128-gadget-out es r0 recs) asg)
                       (int->lebits (expt 2 (lebits=>nat (lookup-equal-list es asg))) 128))))
  :do-not-induct t
  :use ((:instance int-pow-two-checked-128-gadget-complete)
        (:instance int-pow-two-checked-128-gadget-sound)
        int-pow-two-checked-128-gadget-out-facts
        (:instance int-mulpow-two128-exponent-bound (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-spec-error-when-large (signedp t)
                   (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-two128-expt-valuep
                   (e (lebits=>nat (lookup-equal-list es asg)))))
  :in-theory (e/d (int-pow-checked-spec int-mul-checked-spec
                   int-mulpow-pc-integerp-when-int-valuep)
                  (int->lebits expt int-valuep rev int-sub-wrapped-spec
                   int-mulpow-shl-factor int-mulpow-shl-lhs
                   int-shl-checked-spec int-mul-checked-spec
                   int-mulpow-lo int-mulpow-hi int-karatsuba-multiply-spec
                   int-sub-carry int-mulpow-or-scan bitxor abs
                   int-mulpow-shl-honest-emult
                   int-mulpow-two128-recs-honestp
                   int-pow-two-checked-128-gadget-out
                   int-pow-two-checked-128-gadget
                   int-mulpow-pc-neq-gadget
                   unsigned-small-sub-wrapped-const-var-gadget
                   int-mulpow-notcond-ternary-gadget
                   int-mul-checked-signed-gadget)))

(defruled int-shl-checked-signed-128-mid-complete
  (implies (and (int-shl-checked-signed-128-hyps)
                (int-shl-checked-signed-128-front-honest-hyps)
                (natp (lebits=>nat (lookup-equal-list es asg))) (< (lebits=>nat (lookup-equal-list es asg)) 128)
                (symbol-listp (int-pow-two-checked-128-gadget-out es r0 recs)) (equal (len (int-pow-two-checked-128-gadget-out es r0 recs)) 128)
                (r1cs::valuation-binds-allp asg (int-pow-two-checked-128-gadget-out es r0 recs))
                (equal (lookup-equal-list (int-pow-two-checked-128-gadget-out es r0 recs) asg)
                       (int->lebits (expt 2 (lebits=>nat (lookup-equal-list es asg))) 128)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pc-neq-gadget (int-mulpow-shl-min-delta (int-pow-two-checked-128-gadget-out es r0 recs))
                                           emult eneq one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 128) xs nxs nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-notcond-ternary-gadget eneq nxs xs lhs one p)
                 asg p)))
  :do-not-induct t
  :use ((:instance int-mulpow-shl-factor-facts (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-fs-value (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-pc-neq-complete
                   (delta (int-mulpow-shl-min-delta (int-pow-two-checked-128-gadget-out es r0 recs)))
                   (mult emult) (isneq eneq))
        (:instance int-mulpow-shl-min-delta-dot (fs (int-pow-two-checked-128-gadget-out es r0 recs)))
        (:instance int-mulpow-shl-min-delta-value (fs (int-pow-two-checked-128-gadget-out es r0 recs)))
        (:instance int-divshift-sub-wrapped-const-var-complete
                   (signedp t) (n 128) (x 0) (y x) (ys xs) (zs nxs) (z nc))
        (:instance int-mulpow-notcond-ternary-gadget-to-if
                   (c eneq) (ys nxs) (zs xs) (ws lhs)))
  :in-theory (e/d (int-mulpow-shl-honest-emult
                   int-mulpow-shl-lhs
                   bit-listp-of-int->lebits-explicit
                   (:e integer-widthp)
                   (:e int-valuep)
                   bitp)
                  (int->lebits expt int-valuep rev int-sub-wrapped-spec
                   int-mulpow-shl-factor
                   int-shl-checked-spec int-mul-checked-spec
                   int-mulpow-lo int-mulpow-hi int-karatsuba-multiply-spec
                   int-sub-carry int-mulpow-or-scan bitxor abs
                   
                   int-mulpow-two128-recs-honestp
                   int-pow-two-checked-128-gadget-out
                   int-pow-two-checked-128-gadget
                   int-mulpow-pc-neq-gadget
                   unsigned-small-sub-wrapped-const-var-gadget
                   int-mulpow-notcond-ternary-gadget
                   int-mul-checked-signed-gadget)))

(defruled int-shl-checked-signed-128-mul-complete
  (implies (and (int-shl-checked-signed-128-hyps)
                (int-shl-checked-signed-128-front-honest-hyps)
                (int-shl-checked-signed-128-mul-honest-hyps)
                (natp (lebits=>nat (lookup-equal-list es asg))) (< (lebits=>nat (lookup-equal-list es asg)) 128)
                (symbol-listp (int-pow-two-checked-128-gadget-out es r0 recs)) (equal (len (int-pow-two-checked-128-gadget-out es r0 recs)) 128)
                (r1cs::valuation-binds-allp asg (int-pow-two-checked-128-gadget-out es r0 recs))
                (equal (lookup-equal-list (int-pow-two-checked-128-gadget-out es r0 recs) asg)
                       (int->lebits (expt 2 (lebits=>nat (lookup-equal-list es asg))) 128)))
           (r1cs::r1cs-constraints-holdp
            (int-mul-checked-signed-gadget
             lhs (int-pow-two-checked-128-gadget-out es r0 recs) axs mxs cx ays mys cy mz0 mz2 mm mps mcarry
             s lws po tt u v nps nc2 zs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-shl-factor-facts (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-lhs-valuep (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mulpow-shl-signed-spec (e (lebits=>nat (lookup-equal-list es asg))))
        (:instance int-mul-checked-signed-gadget-complete
                   (xs lhs) (ys (int-pow-two-checked-128-gadget-out es r0 recs))
                   (z0 mz0) (z2 mz2) (m mm) (ps mps) (carry mcarry) (nc nc2)
                   (x (int-mulpow-shl-lhs x (lebits=>nat (lookup-equal-list es asg))))
                   (y (int-mulpow-shl-factor (lebits=>nat (lookup-equal-list es asg))))
                   (n 128)))
  :in-theory (e/d (int-mulpow-sc-lens
                   (:e integer-widthp))
                  (int->lebits expt int-valuep rev int-sub-wrapped-spec
                   int-mulpow-shl-factor int-mulpow-shl-lhs
                   int-shl-checked-spec int-mul-checked-spec
                   int-mulpow-lo int-mulpow-hi int-karatsuba-multiply-spec
                   int-sub-carry int-mulpow-or-scan bitxor abs
                   int-mulpow-shl-honest-emult
                   int-mulpow-two128-recs-honestp
                   int-pow-two-checked-128-gadget-out
                   int-pow-two-checked-128-gadget
                   int-mulpow-pc-neq-gadget
                   unsigned-small-sub-wrapped-const-var-gadget
                   int-mulpow-notcond-ternary-gadget
                   int-mul-checked-signed-gadget)))

(defruled int-shl-checked-signed-128-gadget-complete
  (implies (and (int-shl-checked-signed-128-hyps)
                (int-shl-checked-signed-128-front-honest-hyps)
                (int-shl-checked-signed-128-mul-honest-hyps))
           (r1cs::r1cs-constraints-holdp
            (int-shl-checked-signed-128-gadget
             xs es z0 m sqs carry ps fc mult isneq out r0 recs
             emult eneq nxs nc lhs
             axs mxs cx ays mys cy mz0 mz2 mm mps mcarry s lws po tt u v
             nps nc2 zs one p)
            asg p))
  :do-not-induct t
  :use (int-shl-checked-signed-128-pow-complete
        int-shl-checked-signed-128-mid-complete
        int-shl-checked-signed-128-mul-complete)
  :in-theory (union-theories
              '(int-shl-checked-signed-128-gadget
                r1cs::r1cs-constraints-holdp-of-append)
              (theory 'minimal-theory)))

