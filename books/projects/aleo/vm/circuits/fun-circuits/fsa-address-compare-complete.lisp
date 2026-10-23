; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE for the four address comparisons.
;
; Each is field-lt-gadget on the x-coordinates (is_greater_than and
; is_less_than_or_equal swap the operands).  The canonical witness is
; the little-endian bits of each x-coordinate, the bits-lte-const fold
; against p - 1 for each, the xor of the bits, and the bits-lt fold;
; fb3-field-is-less-than-gadget-complete shows it satisfies the
; constraints.

(in-package "ALEOVM")

(include-book "crv-compare")
(include-book "fb3-field-compare")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-base-prime-facts
  (and (primep (base-prime))
       (oddp (base-prime)))
  :in-theory '((:e base-prime) (:e primep) (:e oddp)))

(defmacro fsa-lt-complete-hyps ()
  `(and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
        (symbolp x2) (symbol-listp xs2) (symbol-listp xrs2)
        (symbol-listp ds) (symbol-listp rs) (symbolp u)
        (equal (len xs1) (integer-length p))
        (equal (len xrs1) (bits-lt-prime-rlen p))
        (equal (len xs2) (integer-length p))
        (equal (len xrs2) (bits-lt-prime-rlen p))
        (equal (len ds) (integer-length p))
        (equal (len rs) (integer-length p))
        (equal p (base-prime))
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
        (equal (lookup-equal u asg) 1)
        (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
        (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
        (equal (lookup-equal-list xs1 asg)
               (field-bits-le (lookup-equal x1 asg)))
        (equal (lookup-equal-list xs2 asg)
               (field-bits-le (lookup-equal x2 asg)))
        (equal (lookup-equal-list xrs1 asg)
               (fb-bits-lte-const-witness (lookup-equal-list xs1 asg)
                                          (nat=>lebits* (1- p))))
        (equal (lookup-equal-list xrs2 asg)
               (fb-bits-lte-const-witness (lookup-equal-list xs2 asg)
                                          (nat=>lebits* (1- p))))))

(defmacro fsa-lt-witness (a b)
  `(and (equal (lookup-equal-list ds asg)
               (bitxor-list (lookup-equal-list ,a asg)
                            (lookup-equal-list ,b asg)))
        (equal (lookup-equal-list rs asg)
               (fb3-bits-lt-rs (lookup-equal-list ,a asg)
                               (lookup-equal-list ,b asg)
                               p))))

(defruled fsa-address-is-less-than-gadget-complete
  (implies (and (fsa-lt-complete-hyps)
                (fsa-lt-witness xs1 xs2))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-less-than-gadget
             x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
            asg p))
  :do-not-induct t
  :in-theory (e/d (crv-address-is-less-than-gadget
                   fb-field-is-less-than-gadget
                   fieldp)
                  ((:e base-prime)))
  :use ((:instance fb3-field-is-less-than-gadget-complete
                   (x x1) (xs xs1) (xrs xrs1)
                   (y x2) (ys xs2) (yrs xrs2))
        (:instance curve-edwards-bls12-coordinates-are-fields (p p1))
        (:instance curve-edwards-bls12-coordinates-are-fields (p p2))
        fsa-base-prime-facts))

(defruled fsa-address-is-greater-than-gadget-complete
  (implies (and (fsa-lt-complete-hyps)
                (fsa-lt-witness xs2 xs1))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-greater-than-gadget
             x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
            asg p))
  :do-not-induct t
  :enable crv-address-is-greater-than-gadget
  :use (:instance fsa-address-is-less-than-gadget-complete
                  (x1 x2) (xs1 xs2) (xrs1 xrs2)
                  (x2 x1) (xs2 xs1) (xrs2 xrs1)
                  (p1 p2) (p2 p1)))

(defruled fsa-address-is-greater-than-or-equal-gadget-complete
  (implies (and (fsa-lt-complete-hyps)
                (fsa-lt-witness xs1 xs2))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-greater-than-or-equal-gadget
             x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
            asg p))
  :do-not-induct t
  :enable crv-address-is-greater-than-or-equal-gadget
  :use fsa-address-is-less-than-gadget-complete)

(defruled fsa-address-is-less-than-or-equal-gadget-complete
  (implies (and (fsa-lt-complete-hyps)
                (fsa-lt-witness xs2 xs1))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-less-than-or-equal-gadget
             x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
            asg p))
  :do-not-induct t
  :enable crv-address-is-less-than-or-equal-gadget
  :use fsa-address-is-greater-than-gadget-complete)
