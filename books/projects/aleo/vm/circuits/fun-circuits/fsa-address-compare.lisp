; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Address comparisons over the wires.
;
; crv-compare.lisp states the less-than and greater-than results as
; (r = 1) iff (funspec = 1), and assumes bitp of the result wire for the
; two negated forms.  With the public unit wire equal to 1, the two
; Field::to_bits_le decompositions make the x-coordinate bits booleans,
; and bits-lt-gadget then makes every rs wire a bit.  So the result wire
; equals the funspec, with no hypothesis on internal wires.  The only
; remaining hypotheses are that the input wires are the x-coordinates of
; edwards-bls12-pointp points, which Address::new establishes
; (group-wire-sound.lisp group-new-wire-sound), and the public unit
; wire.

(in-package "ALEOVM")

(include-book "crv-compare")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/last" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro fsa-lt-hyps (&rest more)
  `(and (symbolp x1) (symbol-listp xs1) (symbol-listp xrs1)
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
        (equal (lookup-equal u asg) 1)
        ,@more))

(defruledl bitp-of-car-last-when-bit-listp
  (implies (and (bit-listp l) (consp l))
           (bitp (car (last l))))
  :use (:instance acl2::bitp-when-member-equal-of-bit-listp
                  (a (car (last l))) (x l)))

(defruled fsa-field-lt-gadget-forces-result-bit
  (implies (fsa-lt-hyps
            (r1cs::r1cs-constraints-holdp
             (field-lt-gadget x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
             asg p))
           (bitp (car (last (lookup-equal-list rs asg)))))
  :do-not-induct t
  :enable (field-lt-gadget len-of-lookup-equal-list)
  :use ((:instance field-to-bits-soundness
                   (x x1) (xs xs1) (rs xrs1))
        (:instance field-to-bits-soundness
                   (x x2) (xs xs2) (rs xrs2))
        (:instance bits-lt-gadget-to-<-lendian-iff-bit1
                   (xs xs1) (ys xs2))
        (:instance bitp-of-car-last-when-bit-listp
                   (l (lookup-equal-list rs asg)))))

(defmacro fsa-pt-hyps ()
  `(and (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
        (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))))

(defruled fsa-address-is-less-than-wire-sound
  (implies (fsa-lt-hyps
            (fsa-pt-hyps)
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-less-than-gadget
              x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
             asg p))
           (equal (car (last (lookup-equal-list rs asg)))
                  (address-is-less-than-funspec p1 p2)))
  :do-not-induct t
  :in-theory (e/d (crv-address-is-less-than-gadget bitp)
                  (bitp-of-address-is-less-than-funspec))
  :use (crv-address-is-less-than-gadget-sound
        fsa-field-lt-gadget-forces-result-bit
        bitp-of-address-is-less-than-funspec))

(defruled fsa-address-is-greater-than-wire-sound
  (implies (fsa-lt-hyps
            (fsa-pt-hyps)
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-greater-than-gadget
              x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
             asg p))
           (equal (car (last (lookup-equal-list rs asg)))
                  (address-is-greater-than-funspec p1 p2)))
  :do-not-induct t
  :in-theory (enable crv-address-is-greater-than-gadget
                     address-is-greater-than-funspec)
  :use (:instance fsa-address-is-less-than-wire-sound
                  (x1 x2) (xs1 xs2) (xrs1 xrs2)
                  (x2 x1) (xs2 xs1) (xrs2 xrs1)
                  (p1 p2) (p2 p1)))

(defruled fsa-address-is-greater-than-or-equal-wire-sound
  (implies (fsa-lt-hyps
            (fsa-pt-hyps)
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-greater-than-or-equal-gadget
              x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
             asg p))
           (equal (pfield::sub 1 (car (last (lookup-equal-list rs asg))) p)
                  (address-is-greater-than-or-equal-funspec p1 p2)))
  :do-not-induct t
  :in-theory (enable crv-address-is-greater-than-or-equal-gadget
                     crv-address-is-less-than-gadget)
  :use (crv-address-is-greater-than-or-equal-gadget-sound
        fsa-field-lt-gadget-forces-result-bit))

(defruled fsa-address-is-less-than-or-equal-wire-sound
  (implies (fsa-lt-hyps
            (fsa-pt-hyps)
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-less-than-or-equal-gadget
              x1 xs1 xrs1 x2 xs2 xrs2 ds rs u p)
             asg p))
           (equal (pfield::sub 1 (car (last (lookup-equal-list rs asg))) p)
                  (address-is-less-than-or-equal-funspec p1 p2)))
  :do-not-induct t
  :in-theory (enable crv-address-is-less-than-or-equal-gadget
                     crv-address-is-greater-than-gadget
                     crv-address-is-greater-than-or-equal-gadget
                     address-is-less-than-or-equal-funspec)
  :use (:instance fsa-address-is-greater-than-or-equal-wire-sound
                  (x1 x2) (xs1 xs2) (xrs1 xrs2)
                  (x2 x1) (xs2 xs1) (xrs2 xrs1)
                  (p1 p2) (p2 p1)))
