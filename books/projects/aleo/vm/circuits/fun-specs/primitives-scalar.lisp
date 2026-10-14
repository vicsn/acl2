; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/types/scalar crate.
;
; A scalar is a natural below (scalar-prime); in circuits it is represented
; by a base field element with the same value (scalar-prime < base-prime).
; See primitives-environment.lisp for the conventions of the primitives-* books.

(in-package "ALEOVM")

(include-book "primitives-field")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (enable spec-error scalarp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; snarkVM circuit/types/scalar/src/add.rs: Add::add, AddAssign::add_assign
(define scalar-add-funspec ((a scalarp) (b scalarp))
  :returns (c scalarp)
  :short "Addition modulo the scalar field order; never an error."
  :long "For non-constant operands, the sum is computed in the base field
         (no wrap-around since @($2r < p$)), decomposed into 252 bits,
         and reduced by @($r$) if it is not less than @($r$)."
  (pfield::add a b (scalar-prime)))

; snarkVM circuit/types/scalar/src/ternary.rs: Ternary::ternary
(define scalar-ternary-funspec ((condition bitp) (first scalarp) (second scalarp))
  :returns (c scalarp :hyp (and (scalarp first) (scalarp second)))
  (if (eql condition 1) first second))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Equality and comparison

; snarkVM circuit/types/scalar/src/equal.rs: Equal::is_equal
(define scalar-is-equal-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  (if (equal a b) 1 0))

; snarkVM circuit/types/scalar/src/equal.rs: Equal::is_not_equal
(define scalar-is-not-equal-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  (boolean-not-funspec (scalar-is-equal-funspec a b)))

; snarkVM circuit/types/scalar/src/helpers/zero.rs: Zero::is_zero
(define scalar-is-zero-funspec ((a scalarp))
  :returns (c bitp)
  (scalar-is-equal-funspec a 0)
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/scalar/src/helpers/one.rs: One::is_one
(define scalar-is-one-funspec ((a scalarp))
  :returns (c bitp)
  (scalar-is-equal-funspec a 1)
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/scalar/src/compare.rs: Compare::is_less_than
(define scalar-is-less-than-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  :short "For non-constant operands, the parity of @($2(a - b)$) in the base
          field; this equals @($a < b$) since @($r - 1 \\leq (p-1)/2$)."
  (if (< (pfield::fep-fix a (scalar-prime)) (pfield::fep-fix b (scalar-prime))) 1 0))

; snarkVM circuit/types/scalar/src/compare.rs: Compare::is_greater_than
(define scalar-is-greater-than-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  (scalar-is-less-than-funspec b a))

; snarkVM circuit/types/scalar/src/compare.rs: Compare::is_greater_than_or_equal
(define scalar-is-greater-than-or-equal-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  (boolean-not-funspec (scalar-is-less-than-funspec a b)))

; snarkVM circuit/types/scalar/src/compare.rs: Compare::is_less_than_or_equal
(define scalar-is-less-than-or-equal-funspec ((a scalarp) (b scalarp))
  :returns (c bitp)
  (scalar-is-greater-than-or-equal-funspec b a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bit decompositions and casts

(define scalar-bits-le ((a scalarp))
  :returns (bits bit-listp)
  :short "The 251 little-endian bits of a scalar."
  (acl2::nat=>lebits (scalar-field-size-in-bits) (pfield::fep-fix a (scalar-prime))))

(defrule len-of-scalar-bits-le
  (equal (len (scalar-bits-le a))
         (scalar-field-size-in-bits))
  :enable scalar-bits-le)

; snarkVM circuit/types/scalar/src/helpers/to_bits.rs: ToBits::write_bits_le
(define scalar-write-bits-le-funspec ((acc bit-listp) (a scalarp))
  :returns (bits bit-listp :hyp (bit-listp acc))
  :short "Append the unique 251 little-endian bits of @('a');
          the lower-bits and range checks always hold."
  (append acc (scalar-bits-le a)))

; snarkVM circuit/types/scalar/src/helpers/to_bits.rs: ToBits::write_bits_be
(define scalar-write-bits-be-funspec ((acc bit-listp) (a scalarp))
  :returns (bits bit-listp :hyp (bit-listp acc))
  (append acc (rev (scalar-bits-le a))))

; snarkVM circuit/types/scalar/src/helpers/from_bits.rs: FromBits::from_bits_le
(define scalar-from-bits-le-funspec ((bits bit-listp))
  :returns (res (or (reserrp res) (natp res)))
  :short "Scalar from little-endian bits of any length."
  :long "Bits beyond the first 251 must sum to 0; if there are more than 250
         bits, the first 251 must denote a value at most @($r - 1$).
         The result is the value of the first (at most) 251 bits."
  (b* ((size (scalar-field-size-in-bits))
       (data-size (1- size))
       (n (len bits))
       ((when (and (> n size)
                   (not (boolean-assert-bits-are-zero-funspec (nthcdr size bits)))))
        (spec-error))
       (low (if (> n size) (take size bits) bits))
       ((when (and (> n data-size)
                   (not (boolean-assert-less-than-or-equal-constant-funspec
                         low (acl2::nat=>lebits size (1- (scalar-prime)))))))
        (spec-error)))
    (acl2::lebits=>nat low)))

; snarkVM circuit/types/scalar/src/helpers/from_bits.rs: FromBits::from_bits_be
(define scalar-from-bits-be-funspec ((bits bit-listp))
  :returns (res (or (reserrp res) (natp res))
                :hints (("Goal" :use (:instance return-type-of-scalar-from-bits-le-funspec
                                      (bits (rev bits))))))
  (scalar-from-bits-le-funspec (rev bits)))

; snarkVM circuit/types/scalar/src/helpers/from_field.rs: FromField::from_field
(define scalar-from-field-funspec ((x fieldp))
  :returns (res (or (reserrp res) (natp res))
                :hints (("Goal" :use (:instance return-type-of-scalar-from-bits-le-funspec
                                      (bits (field-bits-le x))))))
  :short "@('Scalar::from_bits_le(field.to_bits_le())'):
          the same value if it is below @($r$), otherwise an error."
  (scalar-from-bits-le-funspec (field-bits-le x)))

; snarkVM circuit/types/scalar/src/helpers/from_field_lossy.rs: Scalar::from_field_lossy
(define scalar-from-field-lossy-funspec ((x fieldp))
  :returns (res (or (reserrp res) (natp res))
                :hints (("Goal" :use (:instance return-type-of-scalar-from-bits-le-funspec
                                      (bits (take (1- (scalar-field-size-in-bits))
                                                  (field-bits-le x)))))))
  :short "The scalar from the lower 250 bits of the field element;
          never an error (the value is @($x \\bmod 2^{250}$))."
  (scalar-from-bits-le-funspec (take (1- (scalar-field-size-in-bits))
                                     (field-bits-le x))))
