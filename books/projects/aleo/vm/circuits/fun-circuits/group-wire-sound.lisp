; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group and address soundness over the wires, given the input points.
;
; Group::new (and Address::new) is enforce_in_group, which is now sound
; and complete without hypotheses (group-unconditional.lisp): the input
; wires are a groupp point, hence an edwards-bls12-pointp.  The
; equality, is_zero and ternary theorems in crv-equal.lisp and
; crv-ternary.lisp also assumed bitp of internal wires.  Those wires
; are forced by the constraints: (x - y) m = r and (x - y)(1 - r) = 0
; make r a bit, and the and-not output is then a bit as well.  The
; theorems below drop those internal hypotheses, so the only remaining
; one is that each input point was injected with Group::new (and,
; for ternary, that the condition is a Boolean::new bit).

(in-package "ALEOVM")

(include-book "crv-equal")
(include-book "crv-ternary")
(include-book "group-unconditional")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bitp-when-zero-test-equations
  (implies (and (equal p (base-prime))
                (pfield::fep delta p)
                (pfield::fep r p)
                (equal (pfield::mul delta m p) r)
                (equal (pfield::mul delta (pfield::sub 1 r p) p) 0))
           (bitp r))
  :hints (("Goal"
           :cases ((equal delta 0))
           :in-theory (e/d (bitp) ((:definition pfield::sub)))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x delta) (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub (x 1) (y r))))))

(defruled crv-field-is-not-equal-gadget-forces-bit
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (crv-field-is-not-equal-gadget x y m r p) asg p))
           (bitp (lookup-equal r asg)))
  :hints (("Goal"
           :in-theory (enable r1cs::fep-of-lookup-equal)
           :use (crv-field-is-not-equal-gadget-to-spec
                 (:instance bitp-when-zero-test-equations
                            (delta (pfield::sub (lookup-equal x asg)
                                                (lookup-equal y asg)
                                                p))
                            (m (lookup-equal m asg))
                            (r (lookup-equal r asg)))))))

(defruled field-is-zero-gadget-forces-bit
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (field-is-zero-gadget x m r p) asg p))
           (bitp (lookup-equal r asg)))
  :hints (("Goal"
           :in-theory (enable r1cs::fep-of-lookup-equal)
           :use (field-is-zero-gadget-to-spec
                 (:instance bitp-when-zero-test-equations
                            (delta (lookup-equal x asg))
                            (m (lookup-equal m asg))
                            (r (lookup-equal r asg)))))))

(defruled field-is-one-gadget-forces-bit
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (field-is-one-gadget x m r p) asg p))
           (bitp (lookup-equal r asg)))
  :hints (("Goal"
           :in-theory (enable r1cs::fep-of-lookup-equal)
           :use (field-is-one-gadget-to-spec
                 (:instance bitp-when-zero-test-equations
                            (delta (pfield::sub (lookup-equal x asg) 1 p))
                            (m (lookup-equal m asg))
                            (r (lookup-equal r asg)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro eq-wire-hyps (&rest more)
  `(and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
        (symbolp mx) (symbolp rx) (symbolp my) (symbolp ry)
        (symbolp out)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg x1)
        (r1cs::valuation-bindsp asg y1)
        (r1cs::valuation-bindsp asg x2)
        (r1cs::valuation-bindsp asg y2)
        (r1cs::valuation-bindsp asg mx)
        (r1cs::valuation-bindsp asg rx)
        (r1cs::valuation-bindsp asg my)
        (r1cs::valuation-bindsp asg ry)
        (r1cs::valuation-bindsp asg out)
        (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
        (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
        (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
        (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
        ,@more))

(defruled crv-group-is-equal-gadget-forces-bits
  (implies (eq-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
             asg p))
           (and (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))))
  :hints (("Goal"
           :in-theory (enable crv-group-is-equal-gadget)
           :use ((:instance crv-field-is-not-equal-gadget-forces-bit
                            (x x1) (y x2) (m mx) (r rx))
                 (:instance crv-field-is-not-equal-gadget-forces-bit
                            (x y1) (y y2) (m my) (r ry))))))

(defruled crv-group-is-equal-wire-sound
  :short "@('Group::is_equal') over the wires, for points injected with
          @('Group::new')."
  (implies (eq-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
             asg p))
           (equal (lookup-equal out asg)
                  (group-is-equal-funspec p1 p2)))
  :use (crv-group-is-equal-gadget-forces-bits
        crv-group-is-equal-gadget-sound))

(defruled crv-group-is-not-equal-wire-sound
  (implies (eq-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (crv-group-is-not-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
             asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (group-is-not-equal-funspec p1 p2)))
  :hints (("Goal"
           :in-theory (e/d (crv-group-is-not-equal-gadget)
                           (bitp))
           :use (crv-group-is-equal-gadget-forces-bits
                 crv-group-is-equal-wire-sound
                 (:instance bitp-of-group-is-equal-funspec)
                 crv-group-is-not-equal-gadget-sound))))

(defruled crv-address-is-equal-wire-sound
  (implies (eq-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
             asg p))
           (equal (lookup-equal out asg)
                  (address-is-equal-funspec p1 p2)))
  :hints (("Goal"
           :in-theory (enable crv-address-is-equal-gadget)
           :use (crv-group-is-equal-gadget-forces-bits
                 crv-address-is-equal-gadget-sound))))

(defruled crv-address-is-not-equal-wire-sound
  (implies (eq-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (crv-address-is-not-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
             asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (address-is-not-equal-funspec p1 p2)))
  :hints (("Goal"
           :in-theory (e/d (crv-address-is-not-equal-gadget
                            crv-address-is-equal-gadget
                            crv-group-is-not-equal-gadget)
                           (bitp))
           :use (crv-group-is-equal-gadget-forces-bits
                 crv-group-is-equal-wire-sound
                 (:instance bitp-of-group-is-equal-funspec)
                 crv-address-is-not-equal-gadget-sound))))

(defruled crv-group-is-zero-wire-sound
  (implies (and (symbolp x) (symbolp y)
                (symbolp mx) (symbolp rx) (symbolp my) (symbolp ry)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg mx)
                (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg my)
                (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg out)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (equal (lookup-equal y asg) (ecurve::point-finite->y p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-zero-gadget x y mx rx my ry out p) asg p))
           (equal (lookup-equal out asg)
                  (group-is-zero-funspec p0)))
  :hints (("Goal"
           :in-theory (enable crv-group-is-zero-gadget)
           :use ((:instance field-is-zero-gadget-forces-bit (m mx) (r rx))
                 (:instance field-is-one-gadget-forces-bit
                            (x y) (m my) (r ry))
                 crv-group-is-zero-gadget-sound))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ternary-wire-hyps (gadget)
  `(and (symbolp c) (symbolp x1) (symbolp y1)
        (symbolp x2) (symbolp y2) (symbolp rx) (symbolp ry)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg c)
        (r1cs::valuation-bindsp asg x1)
        (r1cs::valuation-bindsp asg y1)
        (r1cs::valuation-bindsp asg x2)
        (r1cs::valuation-bindsp asg y2)
        (r1cs::valuation-bindsp asg rx)
        (r1cs::valuation-bindsp asg ry)
        (bitp (lookup-equal c asg))
        (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
        (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
        (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
        (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
        (r1cs::r1cs-constraints-holdp
         (,gadget c x1 y1 x2 y2 rx ry p) asg p)))

(defruled crv-group-ternary-wire-sound
  (implies (ternary-wire-hyps crv-group-ternary-gadget)
           (equal (ecurve::point-finite (lookup-equal rx asg)
                                        (lookup-equal ry asg))
                  (group-ternary-funspec (lookup-equal c asg) p1 p2)))
  :hints (("Goal"
           :in-theory (enable fieldp r1cs::fep-of-lookup-equal)
           :use crv-group-ternary-gadget-sound)))

(defruled crv-address-ternary-wire-sound
  (implies (ternary-wire-hyps crv-address-ternary-gadget)
           (equal (ecurve::point-finite (lookup-equal rx asg)
                                        (lookup-equal ry asg))
                  (address-ternary-funspec (lookup-equal c asg) p1 p2)))
  :hints (("Goal"
           :in-theory (enable fieldp r1cs::fep-of-lookup-equal)
           :use crv-address-ternary-gadget-sound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled group-new-wire-sound
  :short "@('Group::new') over the wires: the point of the input wires is
          @(tsee groupp), and @(tsee group-new-funspec) returns it."
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (r1cs::r1cs-constraints-holdp
                 (group-enforce-in-group-gadget
                  x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p))
           (b* ((pt (ecurve::point-finite (lookup-equal x asg)
                                          (lookup-equal y asg))))
             (and (groupp pt)
                  (equal (group-new-funspec pt) pt)
                  (equal (address-new-funspec pt) pt)
                  (equal (group-enforce-in-group-funspec pt) nil))))
  :hints (("Goal"
           :in-theory (enable group-new-funspec
                              address-new-funspec
                              group-enforce-in-group-funspec)
           :use group-enforce-in-group-sound-unconditional)))
