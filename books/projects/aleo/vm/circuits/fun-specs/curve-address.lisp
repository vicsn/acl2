; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/types/address crate.
;
; An address circuit wraps a group circuit,
; so an address value is a group value (an Edwards-BLS12 point);
; see curve-group.lisp for the conventions.

(in-package "ALEOVM")

(include-book "curve-group")

(local (in-theory (e/d (spec-error curve-not-reserrp-when-pointp)
                        (bitp (:e base-prime) (:e scalar-prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Construction.

; snarkVM circuit/types/address/src/lib.rs: Inject::new
(define address-new-funspec (p)
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "@('Group::new'): the point is enforced to be in the subgroup."
  (group-new-funspec p))

; snarkVM circuit/types/address/src/helpers/from_field.rs: FromField::from_field
(define address-from-field-funspec ((x fieldp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "@('Group::from_x_coordinate') of the field."
  (group-from-x-coordinate-funspec x))

; snarkVM circuit/types/address/src/helpers/from_field.rs: From<Field>::from
(define address-from-funspec ((x fieldp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (address-from-field-funspec x))

; snarkVM circuit/types/address/src/helpers/from_bits.rs: FromBits::from_bits_le
(define address-from-bits-le-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (group-from-bits-le-funspec bits))

; snarkVM circuit/types/address/src/helpers/from_bits.rs: FromBits::from_bits_be
(define address-from-bits-be-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (group-from-bits-be-funspec bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Projections.

; snarkVM circuit/types/address/src/helpers/to_field.rs: From<Address> for Field::from
(define address-to-field-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (x fieldp :hyp :guard)
  :short "The x-coordinate of the address's point."
  (group-to-x-coordinate-funspec p))

(defrule curve-fep-of-address-to-field-funspec
  (implies (ecurve::edwards-bls12-pointp p)
           (pfield::fep (address-to-field-funspec p) (base-prime)))
  :enable address-to-field-funspec)

; snarkVM circuit/types/address/src/helpers/to_bits.rs: ToBits::write_bits_le
(define address-write-bits-le-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (bits bit-listp)
  (group-write-bits-le-funspec p))

; snarkVM circuit/types/address/src/helpers/to_bits.rs: ToBits::write_bits_be
(define address-write-bits-be-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (bits bit-listp)
  (group-write-bits-be-funspec p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Selection, equality, and comparison.

; snarkVM circuit/types/address/src/ternary.rs: Ternary::ternary
(define address-ternary-funspec ((c bitp) p1 p2)
  (group-ternary-funspec c p1 p2))

; snarkVM circuit/types/address/src/equal.rs: Equal::is_equal
(define address-is-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                  (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  (group-is-equal-funspec p1 p2))

; snarkVM circuit/types/address/src/equal.rs: Equal::is_not_equal
(define address-is-not-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                      (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  (group-is-not-equal-funspec p1 p2))

; snarkVM circuit/types/address/src/compare.rs: Compare::is_less_than
(define address-is-less-than-funspec ((p1 ecurve::edwards-bls12-pointp)
                                      (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "Integer comparison of the x-coordinates."
  (if (< (ecurve::point-finite->x p1) (ecurve::point-finite->x p2)) 1 0))

; snarkVM circuit/types/address/src/compare.rs: Compare::is_greater_than
(define address-is-greater-than-funspec ((p1 ecurve::edwards-bls12-pointp)
                                         (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "@('other.is_less_than(self)')."
  (address-is-less-than-funspec p2 p1))

; snarkVM circuit/types/address/src/compare.rs: Compare::is_greater_than_or_equal
(define address-is-greater-than-or-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                                  (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "@('!self.is_less_than(other)')."
  (- 1 (address-is-less-than-funspec p1 p2))
  :prepwork ((local (in-theory (enable address-is-less-than-funspec)))))

; snarkVM circuit/types/address/src/compare.rs: Compare::is_less_than_or_equal
(define address-is-less-than-or-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                               (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "@('other.is_greater_than_or_equal(self)')."
  (address-is-greater-than-or-equal-funspec p2 p1))
