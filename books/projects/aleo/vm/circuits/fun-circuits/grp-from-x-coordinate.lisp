; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::from_x_coordinate (circuit/types/group/src/helpers/
; from_x_coordinate.rs) witnesses the ordinate y (the y-coordinate of the
; console from_x_coordinate, or 0) and calls from_xy_coordinates, i.e.
; enforce_in_group on (x, y).  The constraints are
; group-enforce-in-group-gadget with y an internal wire.  Since a subgroup
; point is determined by its abscissa (grp-edwards-abscissa.lisp), the
; constraints force the point to be the funspec's subgroup point.

(in-package "ALEOVM")

(include-book "grp-from-xy-coordinates")
(include-book "grp-edwards-abscissa")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grp-from-x-coordinate-gadget ((x symbolp) (y symbolp)
                                      (qx symbolp) (qy symbolp)
                                      (cx2 symbolp) (cy2 symbolp)
                                      (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                      (x3 symbolp) (y3 symbolp)
                                      (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                      (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Group::from_x_coordinate'):
          @('enforce_in_group') on the input wire @('x')
          and the witnessed ordinate wire @('y')."
  (group-enforce-in-group-gadget
   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))

(defrule grp-groupp-same-abscissa
  :short "Two @(tsee groupp) points with the same abscissa are equal."
  (implies (and (fieldp x) (fieldp y1) (fieldp y2)
                (groupp (ecurve::point-finite x y1))
                (groupp (ecurve::point-finite x y2)))
           (equal y1 y2))
  :rule-classes nil
  :use (:instance ecurve::grp-r-points-same-abscissa
                  (ecurve::x x) (ecurve::y1 y1) (ecurve::y2 y2))
  :in-theory '(fieldp groupp base-prime))

(defruled grp-curve-x-coordinate-to-group-unique
  (implies (and (fieldp x) (fieldp y)
                (groupp (ecurve::point-finite x y)))
           (equal (group-from-x-coordinate-funspec x)
                  (ecurve::point-finite x y)))
  :use ((:instance curve-x-coordinate-in-group-p-suff)
        (:instance grp-groupp-same-abscissa
                   (y1 y)
                   (y2 (curve-x-coordinate-in-group-witness x))))
  :in-theory '(group-from-x-coordinate-funspec
               curve-x-coordinate-to-group
               curve-x-coordinate-in-group-p
               fieldp pfield::fep-fw-to-natp nfix
               acl2::natp-compound-recognizer))

(defruled grp-from-x-coordinate-gadget-sound
  :short "R1CS-SOUND of @('Group::from_x_coordinate'), without
          hypotheses on the input wire: the constraints imply that the
          funspec of the input value does not fail and returns the point
          of the @('x') and @('y') wires."
  (implies (grp-from-xy-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-from-x-coordinate-gadget
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (group-from-x-coordinate-funspec (lookup-equal x asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :hints (("Goal"
           :in-theory '(grp-from-x-coordinate-gadget
                        fieldp r1cs::fep-of-lookup-equal)
           :use (group-new-wire-sound
                 (:instance grp-curve-x-coordinate-to-group-unique
                            (x (lookup-equal x asg))
                            (y (lookup-equal y asg)))))))

(define grp-from-x-coordinate-y-witness ((xv fieldp))
  :short "The canonical ordinate witness: the ordinate of the subgroup
          point with abscissa @('xv')."
  (ecurve::point-finite->y (curve-x-coordinate-to-group xv))
  :guard-hints (("Goal" :in-theory (enable fieldp curve-x-coordinate-to-group))))

(defruled grp-from-x-coordinate-gadget-complete
  :short "R1CS-COMPLETE of @('Group::from_x_coordinate'): when the
          funspec does not fail on @('xv'), the canonical witnesses
          (the ordinate of the subgroup point and the
          @('enforce_in_group') witnesses for it) satisfy the
          constraints with the input wire bound to @('xv')."
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
                (not (reserrp (group-from-x-coordinate-funspec xv))))
           (b* ((asg (group-enforce-in-group-assignment
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                      (group-from-x-coordinate-funspec xv))))
             (and (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal x asg) xv)
                  (equal (lookup-equal y asg)
                         (grp-from-x-coordinate-y-witness xv))
                  (r1cs::r1cs-constraints-holdp
                   (grp-from-x-coordinate-gadget
                    x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                   asg p))))
  :hints (("Goal"
           :in-theory '(grp-from-x-coordinate-gadget
                        group-from-x-coordinate-funspec
                        grp-from-x-coordinate-y-witness
                        curve-x-coordinate-to-group
                        ecurve::point-finite->x-of-point-finite
                        fieldp pfield::fep-fw-to-natp nfix
                        acl2::natp-compound-recognizer
                        (:e spec-error) (:e reserrp))
           :use ((:instance group-enforce-in-group-gadget-satisfiable
                            (pt (group-from-x-coordinate-funspec xv)))
                 (:instance groupp-of-curve-x-coordinate-to-group
                            (x xv))))))
