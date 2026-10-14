; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications (FUN-SPEC) of the constraint-generating functions
; of snarkVM's circuit/types/integers crate (Integer<E, I>).
;
; Conventions (in addition to those in base.lisp):
;   - Every spec is parameterized by the signedness (signedp) and
;     the width (n) of the integer type I, and is correct for all ten types
;     I8, I16, I32, I64, I128, U8, U16, U32, U64, U128.
;   - Integer arguments and results are ACL2 integers in the range of the type;
;     shift amounts and exponents (of any unsigned type M = U8, U16, U32)
;     are naturals.
;   - Booleans are bits; field elements and scalars are naturals.
;   - The underlying bit pattern of an integer, as used by to_field,
;     is its two's complement value modulo 2^n (see int-spec-unsigned).
;   - Field-level checks in snarkVM never wrap around the field modulus
;     for these widths (at most 3 * 64 or 1.5 * 128 + 1 bits are used),
;     so they are stated below as checks on integers.
;   - Results are (spec-error) exactly when snarkVM halts or
;     the generated constraints are unsatisfiable.

(in-package "ALEOVM")

(include-book "base")

(local (include-book "arithmetic-5/top" :dir :system))

; The type parameters (signedp, n) are not used by every spec.
(set-ignore-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers

(local
 (defrule int-spec-posp-when-integer-widthp
   (implies (integer-widthp n)
            (posp n))
   :rule-classes :forward-chaining
   :enable integer-widthp))

(local
 (defrule int-spec-integerp-when-int-valuep
   (implies (int-valuep x signedp n)
            (integerp x))
   :rule-classes :forward-chaining
   :enable int-valuep))

(define int-spec-field-data-bits ()
  :returns (k posp)
  :short "snarkVM @('E::BaseField::size_in_data_bits()'),
          which equals @('E::BaseField::size_in_bits() - 1'), i.e. 252."
  (1- (base-field-size-in-bits)))

(define int-spec-unsigned ((x integerp) (n natp))
  :returns (u natp :rule-classes :type-prescription)
  :short "The bit pattern of an integer as a natural below @($2^n$)."
  (mod (ifix x) (expt 2 (nfix n))))

(define int-spec-bool ((b booleanp))
  :returns (bit bitp)
  (if b 1 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injection, conversions, bits

;; snarkVM circuit/types/integers/src/lib.rs: Inject::new
(define int-new-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Injecting a console integer yields the same integer value."
  (declare (ignorable signedp n))
  x)

;; snarkVM circuit/types/integers/src/helpers/from_bits.rs: FromBits::from_bits_le
(define int-from-bits-le-spec ((bits bit-listp)
                               (signedp booleanp)
                               (n integer-widthp))
  :short "Bits beyond the first @('n') must be zero; fewer bits are zero-padded."
  :long "<p>The excess bits are all zero iff the little-endian value
         is below @($2^n$).</p>"
  (b* ((u (acl2::lebits=>nat bits))
       ((when (>= u (expt 2 n))) (spec-error)))
    (int-wrap u signedp n)))

;; snarkVM circuit/types/integers/src/helpers/from_bits.rs: FromBits::from_bits_be
(define int-from-bits-be-spec ((bits bit-listp)
                               (signedp booleanp)
                               (n integer-widthp))
  :short "Reverse the bits and apply @(tsee int-from-bits-le-spec)."
  (b* ((u (acl2::bebits=>nat bits))
       ((when (>= u (expt 2 n))) (spec-error)))
    (int-wrap u signedp n)))

;; snarkVM circuit/types/integers/src/helpers/to_field.rs: ToField::to_field
(define int-to-field-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :returns (f natp :rule-classes :type-prescription)
  (declare (ignorable signedp))
  (int-spec-unsigned x n))

;; snarkVM circuit/types/integers/src/helpers/to_fields.rs: ToFields::to_fields
(define int-to-fields-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  (list (int-to-field-spec x signedp n)))

;; snarkVM circuit/types/integers/src/helpers/to_scalar.rs: Integer::to_scalar
(define int-to-scalar-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :returns (s natp :rule-classes :type-prescription)
  (declare (ignorable signedp))
  (int-spec-unsigned x n))

;; snarkVM circuit/types/integers/src/helpers/from_field.rs: FromField::from_field
(define int-from-field-spec ((f fieldp) (signedp booleanp) (n integer-widthp))
  :short "Fails if the field element is not below @($2^n$);
          otherwise reinterprets its @('n') bits as an integer of the type."
  (b* ((f (nfix f))
       ((when (>= f (expt 2 n))) (spec-error)))
    (int-wrap f signedp n)))

;; snarkVM circuit/types/integers/src/helpers/from_field_lossy.rs: Integer::from_field_lossy
(define int-from-field-lossy-spec ((f fieldp) (signedp booleanp) (n integer-widthp))
  :short "Truncates the field element to its lower @('n') bits."
  (int-wrap (nfix f) signedp n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Equality, comparison, ternary

;; snarkVM circuit/types/integers/src/equal.rs: Equal::is_equal
(define int-is-equal-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (equal x y)))

;; snarkVM circuit/types/integers/src/equal.rs: Equal::is_not_equal
(define int-is-not-equal-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (not (equal x y))))

;; snarkVM circuit/types/integers/src/helpers/zero.rs: Zero::is_zero
(define int-is-zero-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :returns (b bitp)
  (int-spec-bool (equal x 0)))

;; snarkVM circuit/types/integers/src/helpers/one.rs: One::is_one
(define int-is-one-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :returns (b bitp)
  (int-spec-bool (equal x 1)))

;; snarkVM circuit/types/integers/src/compare.rs: Compare::is_less_than
(define int-is-less-than-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (< (ifix x) (ifix y))))

;; snarkVM circuit/types/integers/src/compare.rs: Compare::is_greater_than
(define int-is-greater-than-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (> (ifix x) (ifix y))))

;; snarkVM circuit/types/integers/src/compare.rs: Compare::is_less_than_or_equal
(define int-is-less-than-or-equal-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (<= (ifix x) (ifix y))))

;; snarkVM circuit/types/integers/src/compare.rs: Compare::is_greater_than_or_equal
(define int-is-greater-than-or-equal-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (b bitp)
  (int-spec-bool (>= (ifix x) (ifix y))))

;; snarkVM circuit/types/integers/src/ternary.rs: Ternary::ternary
(define int-ternary-spec ((c bitp) x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  (if (equal c 1) x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bitwise operations (on two's complement bit patterns)

;; snarkVM circuit/types/integers/src/and.rs: BitAnd::bitand, BitAndAssign::bitand_assign
(define int-bitand-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (logand (ifix x) (ifix y)) signedp n))

;; snarkVM circuit/types/integers/src/or.rs: BitOr::bitor, BitOrAssign::bitor_assign
(define int-bitor-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (logior (ifix x) (ifix y)) signedp n))

;; snarkVM circuit/types/integers/src/xor.rs: BitXor::bitxor, BitXorAssign::bitxor_assign
(define int-bitxor-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (logxor (ifix x) (ifix y)) signedp n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Addition, subtraction, negation, absolute value

;; snarkVM circuit/types/integers/src/add_checked.rs: AddChecked::add_checked (also Add::add, AddAssign::add_assign)
(define int-add-checked-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  (b* ((z (+ (ifix x) (ifix y))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/add_wrapped.rs: AddWrapped::add_wrapped
(define int-add-wrapped-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (+ (ifix x) (ifix y)) signedp n))

;; snarkVM circuit/types/integers/src/sub_checked.rs: SubChecked::sub_checked (also Sub::sub, SubAssign::sub_assign)
(define int-sub-checked-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  (b* ((z (- (ifix x) (ifix y))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/sub_wrapped.rs: SubWrapped::sub_wrapped
(define int-sub-wrapped-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (- (ifix x) (ifix y)) signedp n))

;; snarkVM circuit/types/integers/src/neg.rs: Neg::neg
(define int-neg-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Halts for unsigned types; fails on the signed minimum."
  (b* (((unless signedp) (spec-error))
       (z (- (ifix x))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/abs_checked.rs: AbsChecked::abs_checked
(define int-abs-checked-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Identity for unsigned types; fails on the signed minimum."
  (b* ((z (abs (ifix x))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/abs_wrapped.rs: AbsWrapped::abs_wrapped
(define int-abs-wrapped-spec (x (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Identity for unsigned types; the signed minimum maps to itself."
  :returns (z integerp)
  (int-wrap (abs (ifix x)) signedp n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Multiplication

;; snarkVM circuit/types/integers/src/mul_checked.rs: Integer::karatsuba_multiply
(define int-karatsuba-multiply-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Returns @('(list product z1-upper-bits z2)'):
          the product of the bit patterns modulo @($2^n$) as an integer of the type,
          the @('n/2 + 1') bits of @($z_0 + z_1 2^{n/2}$) above bit @('n'),
          and @($z_2 = x_1 y_1$) as a field element."
  :long "<p>Here @($x = x_1 2^{n/2} + x_0$), @($y = y_1 2^{n/2} + y_0$)
         (bit patterns), @($z_0 = x_0 y_0$), @($z_1 = x_1 y_0 + x_0 y_1$).
         The value @($z_0 + z_1 2^{n/2}$) is always below @($2^{3n/2+1}$),
         so the bit decomposition never fails.</p>"
  (b* ((h (nfix (floor n 2)))
       (ux (int-spec-unsigned x n))
       (uy (int-spec-unsigned y n))
       (x0 (mod ux (expt 2 h)))
       (x1 (floor ux (expt 2 h)))
       (y0 (mod uy (expt 2 h)))
       (y1 (floor uy (expt 2 h)))
       (z0 (* x0 y0))
       (z1 (+ (* x1 y0) (* x0 y1)))
       (z2 (* x1 y1))
       (s (+ z0 (* z1 (expt 2 h)))))
    (list (int-wrap s signedp n)
          (int->lebits (floor s (expt 2 n)) (1+ h))
          z2))
  ///
  (defrule bit-listp-of-cadr-of-int-karatsuba-multiply-spec
    (bit-listp (cadr (int-karatsuba-multiply-spec x y signedp n)))))

;; snarkVM circuit/types/integers/src/mul_checked.rs: Integer::mul_and_check
(define int-mul-and-check-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Multiplies the bit patterns of @('x') and @('y');
          fails iff the product is not below @($2^n$)."
  :long "<p>For @($2n < 252$) the product is witnessed and checked in the field;
         otherwise (128 bits) Karatsuba multiplication is used and
         the upper bits of @($z_1$) and @($z_2$) are required to be zero.
         snarkVM halts if neither applies (never, for the ten types).</p>"
  (b* ((ux (int-spec-unsigned x n))
       (uy (int-spec-unsigned y n))
       (k (int-spec-field-data-bits)))
    (cond ((< (* 2 n) k)
           (if (< (* ux uy) (expt 2 n))
               (int-wrap (* ux uy) signedp n)
             (spec-error)))
          ((< (+ n (floor n 2)) k)
           (b* (((list product carry z2)
                 (int-karatsuba-multiply-spec x y signedp n)))
             (if (and (equal (acl2::lebits=>nat carry) 0)
                      (equal z2 0))
                 product
               (spec-error))))
          (t (spec-error)))))

;; snarkVM circuit/types/integers/src/pow_checked.rs: Integer::mul_with_flags
(define int-mul-with-flags-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Returns @('(list product flag)'): the bit patterns' product
          modulo @($2^n$) as an integer of the type, and a bit that is 1
          iff the bit patterns' product is not below @($2^n$)."
  (b* ((ux (int-spec-unsigned x n))
       (uy (int-spec-unsigned y n))
       (k (int-spec-field-data-bits)))
    (cond ((< (* 2 n) k)
           (list (int-wrap (* ux uy) signedp n)
                 (int-spec-bool (>= (* ux uy) (expt 2 n)))))
          ((< (+ n (floor n 2)) k)
           (b* (((list product carry z2)
                 (int-karatsuba-multiply-spec x y signedp n)))
             (list product
                   (int-spec-bool (not (and (equal (acl2::lebits=>nat carry) 0)
                                            (equal z2 0)))))))
          (t (spec-error)))))

;; snarkVM circuit/types/integers/src/mul_checked.rs: MulChecked::mul_checked (also Mul::mul, MulAssign::mul_assign)
(define int-mul-checked-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  (b* ((z (* (ifix x) (ifix y))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/mul_wrapped.rs: MulWrapped::mul_wrapped
(define int-mul-wrapped-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :returns (z integerp)
  (int-wrap (* (ifix x) (ifix y)) signedp n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Division, remainder, modulo

;; snarkVM circuit/types/integers/src/div_wrapped.rs: Integer::unsigned_division_via_witness
(define int-unsigned-division-via-witness-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Returns @('(list quotient remainder)'), or an error
          if the Euclidean and remainder constraints are unsatisfiable."
  :long "<p>snarkVM only calls this on unsigned types, where the result is
         the quotient and remainder of @('x') by @('y'), failing iff @('y') is 0.
         The spec also covers signed types literally: the witnesses are
         Rust's wrapping division and remainder (with divisor 1 if @('y') is 0),
         the Euclidean equation is checked on bit patterns in the field
         (for @($2n < 252$)) or with checked integer operations (otherwise),
         and the remainder must be less than @('y').</p>"
  (b* ((x (ifix x))
       (y (ifix y))
       (d (if (equal y 0) 1 y))
       (q (int-wrap (truncate x d) signedp n))
       (r (int-wrap (rem x d) signedp n))
       (euclid-ok
        (if (< (* 2 n) (int-spec-field-data-bits))
            (equal (mod (int-spec-unsigned x n) (base-prime))
                   (mod (+ (* (int-spec-unsigned q n) (int-spec-unsigned y n))
                           (int-spec-unsigned r n))
                        (base-prime)))
          (b* ((m (* q y)))
            (and (int-valuep m signedp n)
                 (int-valuep (+ m r) signedp n)
                 (equal (+ m r) x)))))
       ((unless (and euclid-ok (< r y))) (spec-error)))
    (list q r)))

;; snarkVM circuit/types/integers/src/div_checked.rs: DivChecked::div_checked (also Div::div, DivAssign::div_assign)
(define int-div-checked-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Division rounding toward zero; fails on division by zero
          and on signed overflow (minimum divided by -1)."
  (b* ((x (ifix x))
       (y (ifix y))
       ((when (equal y 0)) (spec-error))
       (z (truncate x y)))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/div_wrapped.rs: DivWrapped::div_wrapped
(define int-div-wrapped-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Division rounding toward zero, wrapping (minimum divided by -1
          is the minimum); fails on division by zero."
  (b* ((x (ifix x))
       (y (ifix y))
       ((when (equal y 0)) (spec-error)))
    (int-wrap (truncate x y) signedp n)))

;; snarkVM circuit/types/integers/src/rem_checked.rs: RemChecked::rem_checked (also Rem::rem, RemAssign::rem_assign)
(define int-rem-checked-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Remainder of division rounding toward zero (sign of the dividend);
          fails on division by zero and on signed minimum by -1."
  (b* ((x (ifix x))
       (y (ifix y))
       ((when (equal y 0)) (spec-error))
       ((unless (int-valuep (truncate x y) signedp n)) (spec-error)))
    (rem x y)))

;; snarkVM circuit/types/integers/src/rem_wrapped.rs: RemWrapped::rem_wrapped
(define int-rem-wrapped-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Remainder of division rounding toward zero (sign of the dividend);
          signed minimum by -1 gives 0; fails on division by zero."
  (b* ((x (ifix x))
       (y (ifix y))
       ((when (equal y 0)) (spec-error)))
    (rem x y)))

;; snarkVM circuit/types/integers/src/modulo.rs: Modulo::modulo
(define int-modulo-spec (x y (signedp booleanp) (n integer-widthp))
  :guard (and (int-valuep x signedp n) (int-valuep y signedp n))
  :short "Halts for signed types; for unsigned types it is
          @(tsee int-rem-wrapped-spec)."
  (if signedp
      (spec-error)
    (int-rem-wrapped-spec x y signedp n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exponentiation (exponent of any unsigned type U8, U16, U32)

;; snarkVM circuit/types/integers/src/pow_checked.rs: PowChecked::pow_checked (also Pow::pow)
(define int-pow-checked-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Fails iff @($x^e$) is out of range (with @($0^0 = 1$))."
  :long "<p>In the circuit, square-and-multiply also checks every squaring,
         but each intermediate square is @($x^k$) with @($k \\le e$),
         which is in range whenever @($x^e$) is.</p>"
  (b* ((z (expt (ifix x) (lnfix e))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/pow_wrapped.rs: PowWrapped::pow_wrapped
(define int-pow-wrapped-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :returns (z integerp)
  (int-wrap (expt (ifix x) (lnfix e)) signedp n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shifts (shift amount of any unsigned type U8, U16, U32)

;; snarkVM circuit/types/integers/src/shl_checked.rs: ShlChecked::shl_checked (also Shl::shl, ShlAssign::shl_assign)
(define int-shl-checked-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Fails if the shift amount is at least @('n'),
          or if @($x \\cdot 2^e$) is out of range (no bits may be lost,
          and for signed types the sign may not change)."
  (b* ((e (lnfix e))
       ((when (>= e n)) (spec-error))
       (z (* (ifix x) (expt 2 e))))
    (if (int-valuep z signedp n) z (spec-error))))

;; snarkVM circuit/types/integers/src/shl_wrapped.rs: ShlWrapped::shl_wrapped
(define int-shl-wrapped-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Shift left by the amount modulo @('n'), discarding the shifted-out bits."
  :returns (z integerp)
  (int-wrap (* (ifix x) (expt 2 (mod (lnfix e) n))) signedp n))

;; snarkVM circuit/types/integers/src/shr_checked.rs: ShrChecked::shr_checked (also Shr::shr, ShrAssign::shr_assign)
(define int-shr-checked-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Fails if the shift amount is at least @('n'); otherwise shifts right,
          arithmetically for signed types (rounding toward negative infinity)."
  (b* ((e (lnfix e))
       ((when (>= e n)) (spec-error)))
    (floor (ifix x) (expt 2 e))))

;; snarkVM circuit/types/integers/src/shr_wrapped.rs: ShrWrapped::shr_wrapped
(define int-shr-wrapped-spec (x (e natp) (signedp booleanp) (n integer-widthp))
  :guard (int-valuep x signedp n)
  :short "Shift right by the amount modulo @('n'),
          arithmetically for signed types."
  :returns (z integerp)
  (declare (ignorable signedp))
  (floor (ifix x) (expt 2 (mod (lnfix e) n))))
