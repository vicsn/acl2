; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Address comparisons are the field comparison of the x-coordinates.
;   is_less_than(self, other)              = x(self) < x(other)
;   is_greater_than(self, other)           = is_less_than(other, self)
;   is_greater_than_or_equal(self, other)  = not is_less_than(self, other)
;   is_less_than_or_equal(self, other)     = not is_less_than(other, self)
; Boolean not is the linear combination 1 - r.

(in-package "ALEOVM")

(include-book "../fun-specs/curve-address")
(include-book "../r1cs/field-lt")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-address-is-less-than-gadget ((x1 symbolp)
                                         (xs1 symbol-listp)
                                         (xrs1 symbol-listp)
                                         (x2 symbolp)
                                         (xs2 symbol-listp)
                                         (xrs2 symbol-listp)
                                         (ds symbol-listp)
                                         (rs symbol-listp)
                                         (u symbolp)
                                         (p primep))
  :guard (and (oddp p)
              (equal (len xs1) (integer-length p))
              (equal (len xrs1) (bits-lt-prime-rlen p))
              (equal (len xs2) (integer-length p))
              (equal (len xrs2) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-lt-gadget x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p))

(defruled crv-address-is-less-than-gadget-sound
  (implies (and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
                (symbolp x2) (symbol-listp xs2) (symbol-listp xrs2)
                (symbol-listp ds) (symbol-listp rs)
                (equal (len xs1) (integer-length p))
                (equal (len xrs1) (bits-lt-prime-rlen p))
                (equal (len xs2) (integer-length p))
                (equal (len xrs2) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p) (oddp p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-binds-allp asg xs1)
                (r1cs::valuation-binds-allp asg xrs1)
                (r1cs::valuation-binds-allp asg xs2)
                (r1cs::valuation-binds-allp asg xrs2)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-less-than-gadget
                  x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
                 asg p))
           (b* ((rs$ (lookup-equal-list rs asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (equal (equal (car (last rs$)) 1)
                             (equal (address-is-less-than-funspec p1 p2) 1)))))
  :do-not-induct t
  :enable (crv-address-is-less-than-gadget
           address-is-less-than-funspec
           pfield::fep-fix-when-fep)
  :use field-lt-gadget-soundness)

(define crv-address-is-greater-than-gadget ((x1 symbolp)
                                            (xs1 symbol-listp)
                                            (xrs1 symbol-listp)
                                            (x2 symbolp)
                                            (xs2 symbol-listp)
                                            (xrs2 symbol-listp)
                                            (ds symbol-listp)
                                            (rs symbol-listp)
                                            (u symbolp)
                                            (p primep))
  :guard (and (oddp p)
              (equal (len xs1) (integer-length p))
              (equal (len xrs1) (bits-lt-prime-rlen p))
              (equal (len xs2) (integer-length p))
              (equal (len xrs2) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "is_greater_than is is_less_than with the addresses swapped."
  (crv-address-is-less-than-gadget
   x2 xs2 xrs2 x1 xs1 xrs1 ds rs u p))

(defruled crv-address-is-greater-than-gadget-sound
  (implies (and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
                (symbolp x2) (symbol-listp xs2) (symbol-listp xrs2)
                (symbol-listp ds) (symbol-listp rs)
                (equal (len xs1) (integer-length p))
                (equal (len xrs1) (bits-lt-prime-rlen p))
                (equal (len xs2) (integer-length p))
                (equal (len xrs2) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p) (oddp p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-binds-allp asg xs1)
                (r1cs::valuation-binds-allp asg xrs1)
                (r1cs::valuation-binds-allp asg xs2)
                (r1cs::valuation-binds-allp asg xrs2)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-greater-than-gadget
                  x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
                 asg p))
           (b* ((rs$ (lookup-equal-list rs asg)))
             (implies (equal (lookup-equal u asg) 1)
                      (equal (equal (car (last rs$)) 1)
                             (equal (address-is-greater-than-funspec p1 p2)
                                    1)))))
  :do-not-induct t
  :enable (crv-address-is-greater-than-gadget
           address-is-greater-than-funspec
           address-is-less-than-funspec)
  :use (:instance crv-address-is-less-than-gadget-sound
                  (x1 x2) (xs1 xs2) (xrs1 xrs2)
                  (x2 x1) (xs2 xs1) (xrs2 xrs1)
                  (p1 p2) (p2 p1)))

(define crv-address-is-greater-than-or-equal-gadget
  ((x1 symbolp) (xs1 symbol-listp) (xrs1 symbol-listp)
   (x2 symbolp) (xs2 symbol-listp) (xrs2 symbol-listp)
   (ds symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len xs1) (integer-length p))
              (equal (len xrs1) (bits-lt-prime-rlen p))
              (equal (len xs2) (integer-length p))
              (equal (len xrs2) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same less-than constraints.  The result boolean is @($1 - r$)."
  (crv-address-is-less-than-gadget
   x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p))

(defruled crv-address-is-greater-than-or-equal-gadget-sound
  (implies (and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
                (symbolp x2) (symbol-listp xs2) (symbol-listp xrs2)
                (symbol-listp ds) (symbol-listp rs)
                (equal (len xs1) (integer-length p))
                (equal (len xrs1) (bits-lt-prime-rlen p))
                (equal (len xs2) (integer-length p))
                (equal (len xrs2) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p) (oddp p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-binds-allp asg xs1)
                (r1cs::valuation-binds-allp asg xrs1)
                (r1cs::valuation-binds-allp asg xs2)
                (r1cs::valuation-binds-allp asg xrs2)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (bitp (car (last (lookup-equal-list rs asg))))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-greater-than-or-equal-gadget
                  x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
                 asg p))
           (b* ((r$ (car (last (lookup-equal-list rs asg)))))
             (implies (equal (lookup-equal u asg) 1)
                      (equal (pfield::sub 1 r$ p)
                             (address-is-greater-than-or-equal-funspec p1 p2)))))
  :do-not-induct t
  :enable (crv-address-is-greater-than-or-equal-gadget
           address-is-greater-than-or-equal-funspec
           address-is-less-than-funspec
           bitp)
  :use crv-address-is-less-than-gadget-sound)

(define crv-address-is-less-than-or-equal-gadget
  ((x1 symbolp) (xs1 symbol-listp) (xrs1 symbol-listp)
   (x2 symbolp) (xs2 symbol-listp) (xrs2 symbol-listp)
   (ds symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len xs1) (integer-length p))
              (equal (len xrs1) (bits-lt-prime-rlen p))
              (equal (len xs2) (integer-length p))
              (equal (len xrs2) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "not is_less_than of the swapped addresses."
  (crv-address-is-greater-than-gadget
   x2 xs2 xrs2 x1 xs1 xrs1 ds rs u p))

(defruled crv-address-is-less-than-or-equal-gadget-sound
  (implies (and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
                (symbolp x2) (symbol-listp xs2) (symbol-listp xrs2)
                (symbol-listp ds) (symbol-listp rs)
                (equal (len xs1) (integer-length p))
                (equal (len xrs1) (bits-lt-prime-rlen p))
                (equal (len xs2) (integer-length p))
                (equal (len xrs2) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p) (oddp p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-binds-allp asg xs1)
                (r1cs::valuation-binds-allp asg xrs1)
                (r1cs::valuation-binds-allp asg xs2)
                (r1cs::valuation-binds-allp asg xrs2)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (bitp (car (last (lookup-equal-list rs asg))))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-less-than-or-equal-gadget
                  x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
                 asg p))
           (b* ((r$ (car (last (lookup-equal-list rs asg)))))
             (implies (equal (lookup-equal u asg) 1)
                      (equal (pfield::sub 1 r$ p)
                             (address-is-less-than-or-equal-funspec p1 p2)))))
  :do-not-induct t
  :enable (crv-address-is-less-than-or-equal-gadget
           crv-address-is-greater-than-gadget
           address-is-less-than-or-equal-funspec
           address-is-greater-than-or-equal-funspec)
  :use (:instance crv-address-is-greater-than-or-equal-gadget-sound
                  (x1 x2) (xs1 xs2) (xrs1 xrs2)
                  (x2 x1) (xs2 xs1) (xrs2 xrs1)
                  (p1 p2) (p2 p1)))
