; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group and address write_bits are the field bit decomposition of the
; x-coordinate (booleanity, power-of-two sum, and the range check), which
; is the gadget already verified as field-to-bits-gadget.  Big-endian is
; the reversal of those bits and adds no constraint.

(in-package "ALEOVM")

(include-book "../fun-specs/curve-group")
(include-book "../fun-specs/curve-address")
(include-book "../r1cs/field-to-bits")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-write-bits-le-gadget ((x symbolp)
                                        (xs symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-to-bits-gadget x xs rs u p))

(defruled crv-group-write-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-write-bits-le-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (lookup-equal-list xs asg)
                  (group-write-bits-le-funspec p0)))
  :enable (crv-group-write-bits-le-gadget
           group-write-bits-le-funspec
           curve-field-to-bits-le
           acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix)
  :use field-to-bits-soundness)

(define crv-group-write-bits-be-gadget ((x symbolp)
                                        (xs symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as little-endian.  The written list is reversed."
  (crv-group-write-bits-le-gadget x xs rs u p))

(defruled crv-group-write-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-write-bits-be-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (rev (lookup-equal-list xs asg))
                  (group-write-bits-be-funspec p0)))
  :enable (crv-group-write-bits-be-gadget
           group-write-bits-be-funspec
           curve-field-to-bits-be
           curve-field-to-bits-le)
  :use crv-group-write-bits-le-gadget-sound)

(define crv-address-write-bits-le-gadget ((x symbolp)
                                          (xs symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-write-bits-le-gadget x xs rs u p))

(defruled crv-address-write-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-write-bits-le-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (lookup-equal-list xs asg)
                  (address-write-bits-le-funspec p0)))
  :enable (crv-address-write-bits-le-gadget
           address-write-bits-le-funspec
           crv-group-write-bits-le-gadget-sound))

(define crv-address-write-bits-be-gadget ((x symbolp)
                                          (xs symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-write-bits-be-gadget x xs rs u p))

(defruled crv-address-write-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-write-bits-be-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (rev (lookup-equal-list xs asg))
                  (address-write-bits-be-funspec p0)))
  :enable (crv-address-write-bits-be-gadget
           address-write-bits-be-funspec
           crv-group-write-bits-be-gadget-sound))
