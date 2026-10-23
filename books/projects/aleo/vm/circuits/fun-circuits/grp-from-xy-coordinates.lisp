; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::from_xy_coordinates (circuit/types/group/src/helpers/
; from_xy_coordinates.rs) builds the point from the two given field wires
; and calls enforce_in_group on it.  Its constraints are therefore exactly
; group-enforce-in-group-gadget on the x and y wires (the same gadget as
; Group::new without the allocation of x and y).

(in-package "ALEOVM")

(include-book "group-wire-sound")
(include-book "group-enforce-in-group-complete")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grp-from-xy-coordinates-gadget ((x symbolp) (y symbolp)
                                        (qx symbolp) (qy symbolp)
                                        (cx2 symbolp) (cy2 symbolp)
                                        (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                        (x3 symbolp) (y3 symbolp)
                                        (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                        (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Group::from_xy_coordinates'):
          @('enforce_in_group') on the input wires @('x') and @('y')."
  (group-enforce-in-group-gadget
   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))

(defmacro grp-from-xy-wire-hyps (&rest more)
  `(and (symbolp x) (symbolp y)
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
        ,@more))

(defruled grp-from-xy-coordinates-gadget-sound
  :short "R1CS-SOUND of @('Group::from_xy_coordinates'), without
          hypotheses on the input wires: the constraints imply that the
          funspec of the input values does not fail and returns the
          point of the input wires."
  (implies (grp-from-xy-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-from-xy-coordinates-gadget
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (group-from-xy-coordinates-funspec (lookup-equal x asg)
                                                     (lookup-equal y asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :hints (("Goal"
           :in-theory '(grp-from-xy-coordinates-gadget
                        group-from-xy-coordinates-funspec)
           :use group-new-wire-sound)))

(defruled grp-from-xy-coordinates-gadget-complete
  :short "R1CS-COMPLETE of @('Group::from_xy_coordinates'): when the
          funspec does not fail on field elements @('xv') and @('yv'),
          the canonical @('enforce_in_group') witnesses (the cofactor
          witness @($P/4$), its square products and doubling) satisfy the
          constraints with the input wires bound to @('xv') and @('yv')."
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (no-duplicatesp-equal
                 (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2))
                (equal p (base-prime))
                (fieldp xv)
                (fieldp yv)
                (not (reserrp (group-from-xy-coordinates-funspec xv yv))))
           (b* ((asg (group-enforce-in-group-assignment
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                      (ecurve::point-finite xv yv))))
             (and (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal x asg) xv)
                  (equal (lookup-equal y asg) yv)
                  (r1cs::r1cs-constraints-holdp
                   (grp-from-xy-coordinates-gadget
                    x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                   asg p))))
  :hints (("Goal"
           :in-theory '(grp-from-xy-coordinates-gadget
                        group-from-xy-coordinates-funspec
                        fieldp pfield::fep natp nfix
                        ecurve::point-finite->x-of-point-finite
                        ecurve::point-finite->y-of-point-finite
                        (:e spec-error) (:e reserrp))
           :use (:instance group-enforce-in-group-gadget-satisfiable
                           (pt (ecurve::point-finite xv yv))))))
