; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/types/field crate.
;
; A field element is a natural below (base-prime); booleans are bits.
; Bit lists are little-endian unless the name says -be.
; Write functions (write_bits_le/be) extend an accumulator list of bits.
; See primitives-environment.lisp for the conventions of the primitives-* books.

(in-package "ALEOVM")

(include-book "primitives-boolean")
(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (enable spec-error fieldp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions

; snarkVM circuit/types/field/src/lib.rs: From::from (LinearCombination <-> Field)
(define field-from-funspec ((x fieldp))
  :returns (y fieldp :hyp :guard)
  :short "Conversion between a field circuit and its linear combination:
          the value is unchanged."
  x)

; snarkVM circuit/types/field/src/helpers/from_boolean.rs: FromBoolean::from_boolean
(define field-from-boolean-funspec ((b bitp))
  :returns (x fieldp :hyp :guard)
  :short "The boolean's linear combination, as a field element."
  b
  :prepwork ((local (in-theory (enable bitp pfield::fep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Arithmetic

; snarkVM circuit/types/field/src/mul.rs: Mul::mul, MulAssign::mul_assign
(define field-mul-funspec ((x fieldp) (y fieldp))
  :returns (z fieldp)
  (pfield::mul x y (base-prime)))

; snarkVM circuit/types/field/src/square.rs: Square::square
(define field-square-funspec ((x fieldp))
  :returns (z fieldp)
  (field-mul-funspec x x))

; snarkVM circuit/types/field/src/inverse.rs: Inverse::inverse, Inv::inv
(define field-inverse-funspec ((x fieldp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "Inverse; the constraint @($x \\cdot x^{-1} = 1$) is unsatisfiable for 0."
  (if (equal x 0)
      (spec-error)
    (pfield::inv x (base-prime))))

; snarkVM circuit/types/field/src/div.rs: Div::div, DivAssign::div_assign
(define field-div-funspec ((x fieldp) (y fieldp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "Checked division: halts (constant 0 divisor) or is unsatisfiable
          (variable 0 divisor) when @($y = 0$)."
  (if (equal y 0)
      (spec-error)
    (pfield::div x y (base-prime))))

; snarkVM circuit/types/field/src/div_unchecked.rs: DivUnchecked::div_unchecked
(define field-div-unchecked-funspec ((x fieldp) (y fieldp)
                                     (both-variable booleanp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "Unchecked division."
  :long "The result depends on the modes in the case @($0 / 0$):
         if both operands are non-constant (@('both-variable')),
         the single constraint @($q \\cdot y = x$) holds for any @($q$),
         and snarkVM's witness is @($q = 0$);
         if either operand is constant, @($y^{-1}$) is computed
         with a checked inverse, which fails for @($y = 0$).
         For @($y = 0$ \\neq x$) it is always an error."
  (if (equal y 0)
      (if (and both-variable (equal x 0))
          0
        (spec-error))
    (pfield::div x y (base-prime))))

; snarkVM circuit/types/field/src/pow.rs: Pow::pow
(define field-pow-funspec ((x fieldp) (e fieldp))
  :returns (z fieldp)
  :short "Square-and-multiply over the 253 big-endian bits of the exponent:
          @($x^e$), with @($0^0 = 1$)."
  (pfield::pow x e (base-prime)))

; snarkVM circuit/types/field/src/ternary.rs: Ternary::ternary
(define field-ternary-funspec ((condition bitp) (first fieldp) (second fieldp))
  :returns (z fieldp :hyp (and (fieldp first) (fieldp second)))
  (if (eql condition 1) first second))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Equality and comparison

; snarkVM circuit/types/field/src/equal.rs: Equal::is_not_equal
(define field-is-not-equal-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  (if (equal x y) 0 1))

; snarkVM circuit/types/field/src/equal.rs: Equal::is_equal
(define field-is-equal-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  (boolean-not-funspec (field-is-not-equal-funspec x y)))

; snarkVM circuit/types/field/src/helpers/zero.rs: Zero::is_zero
(define field-is-zero-funspec ((x fieldp))
  :returns (b bitp)
  (field-is-equal-funspec x 0)
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/field/src/helpers/one.rs: One::is_one
(define field-is-one-funspec ((x fieldp))
  :returns (b bitp)
  (field-is-equal-funspec x 1)
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/field/src/compare.rs: Compare::is_less_than
(define field-is-less-than-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  :short "Comparison of the canonical representatives
          (computed from the unique bit decompositions)."
  (if (< (pfield::fep-fix x (base-prime)) (pfield::fep-fix y (base-prime))) 1 0))

; snarkVM circuit/types/field/src/compare.rs: Compare::is_greater_than
(define field-is-greater-than-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  (field-is-less-than-funspec y x))

; snarkVM circuit/types/field/src/compare.rs: Compare::is_greater_than_or_equal
(define field-is-greater-than-or-equal-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  (boolean-not-funspec (field-is-less-than-funspec x y)))

; snarkVM circuit/types/field/src/compare.rs: Compare::is_less_than_or_equal
(define field-is-less-than-or-equal-funspec ((x fieldp) (y fieldp))
  :returns (b bitp)
  (field-is-greater-than-or-equal-funspec y x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Square roots

(define field-modulus-minus-one-div-two ()
  :returns (n natp)
  (floor (1- (base-prime)) 2))

(define field-lesser-square-root ((x fieldp))
  :guard (ecurve::pfield-squarep x (base-prime))
  :returns (r fieldp)
  :short "The square root of a square @('x') that is at most @($(p-1)/2$)."
  (b* ((p (base-prime))
       (r (pfield::fep-fix (ecurve::pfield-square->root x p) p)))
    (if (<= r (field-modulus-minus-one-div-two))
        r
      (pfield::neg r p))))

(local
 (defrule fep-of-field-lesser-square-root
   (pfield::fep (field-lesser-square-root x) primes::*bls12-377-scalar-field-prime*)
   :use fieldp-of-field-lesser-square-root
   :disable fieldp-of-field-lesser-square-root))

; snarkVM circuit/types/field/src/square_root.rs: SquareRoot::square_root
(define field-square-root-funspec ((x fieldp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "The square root at most @($(p-1)/2$) (the lesser one);
          error if @('x') is not a square."
  :long "snarkVM witnesses the lesser root (or 0 for non-squares) and enforces
         @($r \\cdot r = x$) and @($r \\leq (p-1)/2$)."
  (if (ecurve::pfield-squarep x (base-prime))
      (field-lesser-square-root x)
    (spec-error)))

; snarkVM circuit/types/field/src/square_root.rs: Field::even_square_root
(define field-even-square-root-funspec ((x fieldp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "The square root with least significant bit 0 (unique, as p is odd);
          error if @('x') is not a square."
  :long "snarkVM enforces @($r \\cdot r = x$) and that the LSB of
         the canonical bits of @($r$) is 0."
  (b* ((p (base-prime)))
    (if (ecurve::pfield-even-squarep x p)
        (pfield::fep-fix (ecurve::pfield-square->even-root x p) p)
      (spec-error))))

; snarkVM circuit/types/field/src/square_root.rs: Field::square_roots_flagged_nondeterministic
(define field-square-roots-flagged-nondeterministic-funspec ((x fieldp))
  :returns (mv (first-root fieldp)
               (second-root fieldp)
               (error-flag bitp))
  :short "Both square roots and a non-square flag; never an error."
  :long "For a square @('x'), the first root is the lesser one
         (the console witness), the second is its negation, and the flag is 0.
         For a non-square, both roots are 0 and the flag is 1.
         The constraints do not order the two roots;
         the values here are the ones snarkVM computes."
  (b* ((p (base-prime)))
    (if (ecurve::pfield-squarep x p)
        (b* ((r (field-lesser-square-root x)))
          (mv r (pfield::neg r p) 0))
      (mv 0 0 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bit decompositions

(define field-bits-le ((x fieldp))
  :returns (bits bit-listp)
  :short "The 253 little-endian bits of a field element."
  (acl2::nat=>lebits (base-field-size-in-bits) (pfield::fep-fix x (base-prime))))

(defrule len-of-field-bits-le
  (equal (len (field-bits-le x))
         (base-field-size-in-bits))
  :enable field-bits-le)

; snarkVM circuit/types/field/src/helpers/to_bits.rs: Field::to_non_unique_bits_le
(define field-to-non-unique-bits-le-funspec ((x fieldp))
  :returns (bits bit-listp)
  :short "The witnessed bits are the canonical 253 bits; never an error."
  (field-bits-le x))

; snarkVM circuit/types/field/src/helpers/to_bits.rs: ToBits::write_bits_le
(define field-write-bits-le-funspec ((acc bit-listp) (x fieldp))
  :returns (bits bit-listp :hyp (bit-listp acc))
  :short "Append the unique 253 little-endian bits of @('x');
          the range check against @($p - 1$) always holds."
  (append acc (field-bits-le x)))

; snarkVM circuit/types/field/src/helpers/to_bits.rs: ToBits::write_bits_be
(define field-write-bits-be-funspec ((acc bit-listp) (x fieldp))
  :returns (bits bit-listp :hyp (bit-listp acc))
  :short "Append the unique 253 big-endian bits of @('x')."
  (append acc (rev (field-bits-le x))))

; snarkVM circuit/types/field/src/helpers/from_bits.rs: FromBits::from_bits_le
(define field-from-bits-le-funspec ((bits bit-listp))
  :returns (res (or (reserrp res) (fieldp res)))
  :short "Field element from little-endian bits of any length."
  :long "Bits beyond the first 253 must sum to 0; if there are more than 252
         bits, the first 253 must denote a value at most @($p - 1$).
         The result is the value of the first (at most) 253 bits."
  (b* ((p (base-prime))
       (size (base-field-size-in-bits))
       (data-size (1- size))
       (n (len bits))
       ((when (and (> n size)
                   (not (boolean-assert-bits-are-zero-funspec (nthcdr size bits)))))
        (spec-error))
       (low (if (> n size) (take size bits) bits))
       ((when (and (> n data-size)
                   (not (boolean-assert-less-than-or-equal-constant-funspec
                         low (acl2::nat=>lebits size (1- p))))))
        (spec-error)))
    (mod (acl2::lebits=>nat low) p)))

; snarkVM circuit/types/field/src/helpers/from_bits.rs: FromBits::from_bits_be
(define field-from-bits-be-funspec ((bits bit-listp))
  :returns (res (or (reserrp res) (fieldp res))
                :hints (("Goal" :use (:instance return-type-of-field-from-bits-le-funspec
                                      (bits (rev bits))))))
  (field-from-bits-le-funspec (rev bits)))

; snarkVM circuit/types/field/src/helpers/to_lower_bits.rs: ToLowerBits::to_lower_bits_le
(define field-to-lower-bits-le-funspec ((x fieldp) (k natp))
  :returns (res (or (reserrp res) (bit-listp res)))
  :short "The lower @('k') little-endian bits; halts if @($k > 253$),
          unsatisfiable if @($x \\geq 2^k$)."
  (b* ((x (pfield::fep-fix x (base-prime)))
       (k (lnfix k))
       ((when (> k (base-field-size-in-bits))) (spec-error))
       ((unless (< x (expt 2 k))) (spec-error)))
    (acl2::nat=>lebits k x)))

; snarkVM circuit/types/field/src/helpers/to_lower_bits.rs: ToLowerBits::to_lower_bits_be
(define field-to-lower-bits-be-funspec ((x fieldp) (k natp))
  :returns (res (or (reserrp res) (bit-listp res))
                :hints (("Goal" :use return-type-of-field-to-lower-bits-le-funspec)))
  (b* ((res (field-to-lower-bits-le-funspec x k)))
    (if (reserrp res) res (rev res))))

; snarkVM circuit/types/field/src/helpers/to_upper_bits.rs: ToUpperBits::to_upper_bits_be
(define field-to-upper-bits-be-funspec ((x fieldp) (k natp))
  :returns (res (or (reserrp res) (bit-listp res)))
  :short "The upper @('k') of the 253 bits, big-endian; halts if @($k > 253$),
          unsatisfiable unless the lower @($253 - k$) bits are zero."
  (b* ((x (pfield::fep-fix x (base-prime)))
       (k (lnfix k))
       (size (base-field-size-in-bits))
       ((when (> k size)) (spec-error))
       ((unless (equal (mod x (expt 2 (- size k))) 0)) (spec-error)))
    (rev (nthcdr (- size k) (acl2::nat=>lebits size x)))))

; snarkVM circuit/types/field/src/helpers/to_upper_bits.rs: ToUpperBits::to_upper_bits_le
(define field-to-upper-bits-le-funspec ((x fieldp) (k natp))
  :returns (res (or (reserrp res) (bit-listp res))
                :hints (("Goal" :use return-type-of-field-to-upper-bits-be-funspec)))
  (b* ((res (field-to-upper-bits-be-funspec x k)))
    (if (reserrp res) res (rev res))))
