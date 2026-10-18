; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::write_bits_le / write_bits_be
; (circuit/types/scalar/src/helpers/to_bits.rs).
;
; write_bits_le initialises the cached bits with Field::to_lower_bits_le
; of scalar-field size (251) and Boolean::assert_less_than_or_equal_constant
; against r - 1.  That is the same constraint list as the patched
; Scalar::new: 251 boolean checks, the weighted sum, bits-lte-const,
; and the final assert that the comparison wire is 0.
; write_bits_be reverses that list and emits nothing further.
;
; A satisfying assignment therefore builds a scalar from the bit wires.
; The bits are scalar-bits-le of that scalar.  The accumulator in the
; funspec is the vector the circuit extends; this gadget does not
; constrain the prefix.

(in-package "ALEOVM")

(include-book "scalar-new-r1cs")
(include-book "scalar-from-bits-r1cs")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-write-bits-le-gadget ((s symbolp)
                                     (xs symbol-listp)
                                     (rs symbol-listp)
                                     (p primep))
  :guard (and (equal (len xs) 251)
              (equal (len rs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Scalar::write_bits_le')."
  (scalar-new-gadget s xs rs p))

(defruled scalar-write-bits-canonical
  :short "251 boolean bits whose value is a scalar are @('scalar-bits-le')."
  (implies (and (bit-listp xs)
                (equal (len xs) (scalar-field-size-in-bits))
                (scalarp s)
                (equal (lebits=>nat xs) s))
           (equal (scalar-bits-le s) xs))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits xs))
           :in-theory (e/d (scalar-bits-le
                            scalarp
                            pfield::fep
                            pfield::fep-fix-when-fep
                            scalar-field-size-in-bits
                            acl2::bit-list-fix-when-bit-listp)
                           (acl2::nat=>lebits-of-lebits=>nat)))))

(defruled scalar-write-bits-le-gadget-sound
  :short "Wire soundness of @('Scalar::write_bits_le').  The bit wires
          are @('scalar-bits-le') of the scalar wire, which is a scalar.
          @('acc') is the unconstrained prefix of the funspec."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (bit-listp acc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget s xs rs p) asg p))
           (b* ((s$ (lookup-equal s asg))
                (xs$ (lookup-equal-list xs asg)))
             (and (bit-listp xs$)
                  (equal s$ (lebits=>nat xs$))
                  (scalarp s$)
                  (equal xs$ (scalar-bits-le s$))
                  (equal (append acc xs$)
                         (scalar-write-bits-le-funspec acc s$)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance scalar-new-gadget-sound
                            (s s) (xs xs) (rs rs) (p p) (asg asg))
                 (:instance scalar-write-bits-canonical
                            (xs (lookup-equal-list xs asg))
                            (s (lookup-equal s asg))))
           :in-theory (e/d (scalar-write-bits-le-gadget
                            scalar-write-bits-le-funspec
                            scalar-field-size-in-bits)
                           (scalar-new-gadget-sound
                            scalar-write-bits-canonical)))))

(defruled scalar-write-bits-be-gadget-sound
  :short "Wire soundness of @('Scalar::write_bits_be').  Reversal adds
          no constraint.  The appended bits are the reverse of
          @('scalar-bits-le')."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (bit-listp acc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget s xs rs p) asg p))
           (b* ((s$ (lookup-equal s asg))
                (xs$ (lookup-equal-list xs asg)))
             (and (bit-listp xs$)
                  (scalarp s$)
                  (equal (rev xs$) (rev (scalar-bits-le s$)))
                  (equal (append acc (rev xs$))
                         (scalar-write-bits-be-funspec acc s$)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance scalar-write-bits-le-gadget-sound
                           (s s) (xs xs) (rs rs) (p p) (asg asg) (acc acc))
           :in-theory (e/d (scalar-write-bits-be-funspec)
                           (scalar-write-bits-le-gadget-sound)))))

(defruled scalar-write-bits-le-gadget-complete
  :short "R1CS-COMPLETE of @('Scalar::write_bits_le'): for every scalar, its
          bits and the canonical @('bits-lte-const') fold witness satisfy
          the constraints, and the bit wires are the funspec's output."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (scalarp (lookup-equal s asg))
                (equal (lookup-equal-list xs asg)
                       (scalar-bits-le (lookup-equal s asg)))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (scalar-modulus-minus-one-bits))))
           (and (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget s xs rs p) asg p)
                (equal (append acc (lookup-equal-list xs asg))
                       (scalar-write-bits-le-funspec acc (lookup-equal s asg)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance scalar-new-gadget-complete)
           :in-theory (e/d (scalar-write-bits-le-gadget
                            scalar-write-bits-le-funspec)
                           (scalar-new-gadget-complete)))))

(defruled scalar-write-bits-be-gadget-complete
  :short "R1CS-COMPLETE of @('Scalar::write_bits_be'): the same witnesses as
          @('write_bits_le'); the appended bits are their reverse."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (scalarp (lookup-equal s asg))
                (equal (lookup-equal-list xs asg)
                       (scalar-bits-le (lookup-equal s asg)))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (scalar-modulus-minus-one-bits))))
           (and (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget s xs rs p) asg p)
                (equal (append acc (rev (lookup-equal-list xs asg)))
                       (scalar-write-bits-be-funspec acc (lookup-equal s asg)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance scalar-write-bits-le-gadget-complete)
           :in-theory (e/d (scalar-write-bits-be-funspec)
                           (scalar-write-bits-le-gadget-complete)))))
