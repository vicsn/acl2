; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Address::from, from_field, from_bits_le, from_bits_be
; (circuit/types/address/src/helpers/from_field.rs, from_bits.rs).
;
; from_field(x) is Self::from_group(Group::from_x_coordinate(x)), from(x)
; is from_field(x), and from_bits_le/be(bits) is
; Self(Group::from_bits_le/be(bits)).  from_group and the tuple constructor
; only wrap the group value and emit no constraints, so the constraint
; systems are those of Group::from_x_coordinate (grp-from-x-coordinate.lisp,
; enforce_in_group, no square root) and Group::from_bits_le/be
; (grp-from-bits.lisp, Field::from_bits_le/be then from_x_coordinate).

(in-package "ALEOVM")

(include-book "grp-from-bits")
(include-book "../fun-specs/curve-address")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-address-from-field-gadget-sound
  :short "R1CS-SOUND of @('Address::from_field'), without hypotheses on
          the input wire."
  (implies (grp-from-xy-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-from-x-coordinate-gadget
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (address-from-field-funspec (lookup-equal x asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :in-theory '(address-from-field-funspec)
  :use grp-from-x-coordinate-gadget-sound)

(defruled fsa-address-from-gadget-sound
  :short "R1CS-SOUND of @('From<Field> for Address')."
  (implies (grp-from-xy-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-from-x-coordinate-gadget
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (address-from-funspec (lookup-equal x asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :in-theory '(address-from-funspec address-from-field-funspec)
  :use grp-from-x-coordinate-gadget-sound)

(defmacro fsa-address-xcoord-complete-hyps (funspec)
  `(and (symbolp x) (symbolp y)
        (symbolp qx) (symbolp qy)
        (symbolp cx2) (symbolp cy2)
        (symbolp dxy) (symbolp dx2) (symbolp dy2)
        (symbolp x3) (symbolp y3)
        (symbolp exy) (symbolp ex2) (symbolp ey2)
        (no-duplicatesp-equal
         (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2))
        (equal p (base-prime))
        (fieldp xv)
        (not (reserrp (,funspec xv)))))

(defmacro fsa-address-xcoord-complete-concl (funspec)
  `(b* ((asg (group-enforce-in-group-assignment
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
              (,funspec xv))))
     (and (r1cs::r1cs-valuationp asg p)
          (equal (lookup-equal x asg) xv)
          (equal (lookup-equal y asg)
                 (grp-from-x-coordinate-y-witness xv))
          (r1cs::r1cs-constraints-holdp
           (grp-from-x-coordinate-gadget
            x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
           asg p))))

(defruled fsa-address-from-field-gadget-complete
  :short "R1CS-COMPLETE of @('Address::from_field'): when the funspec
          does not fail, the canonical witnesses of
          @('Group::from_x_coordinate') satisfy the constraints."
  (implies (fsa-address-xcoord-complete-hyps address-from-field-funspec)
           (fsa-address-xcoord-complete-concl address-from-field-funspec))
  :in-theory '(address-from-field-funspec)
  :use grp-from-x-coordinate-gadget-complete)

(defruled fsa-address-from-gadget-complete
  :short "R1CS-COMPLETE of @('From<Field> for Address')."
  (implies (fsa-address-xcoord-complete-hyps address-from-funspec)
           (fsa-address-xcoord-complete-concl address-from-funspec))
  :in-theory '(address-from-funspec address-from-field-funspec)
  :use grp-from-x-coordinate-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-address-from-bits-le-gadget-sound
  :short "R1CS-SOUND of @('Address::from_bits_le') given
          @('Boolean::new') on each input bit (fewer than p bits)."
  (implies (grp-fb-hyps bits
            (r1cs::r1cs-constraints-holdp
             (grp-from-bits-le-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                      x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (address-from-bits-le-funspec (lookup-equal-list bits asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :in-theory '(address-from-bits-le-funspec)
  :use grp-from-bits-le-gadget-sound)

(defruled fsa-address-from-bits-be-gadget-sound
  :short "R1CS-SOUND of @('Address::from_bits_be') given
          @('Boolean::new') on each input bit (fewer than p bits)."
  (implies (grp-fb-hyps (rev bits)
            (r1cs::r1cs-constraints-holdp
             (grp-from-bits-be-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                      x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (address-from-bits-be-funspec (lookup-equal-list bits asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :in-theory '(address-from-bits-be-funspec)
  :use grp-from-bits-be-gadget-sound)

(defruled fsa-address-from-bits-le-gadget-complete
  :short "R1CS-COMPLETE of @('Address::from_bits_le'): the fold witness
          of @('Field::from_bits_le') and the canonical
          @('enforce_in_group') witnesses satisfy the constraints."
  (implies (grp-fb-hyps bits
            (grp-fb-canon bits address-from-bits-le-funspec))
           (r1cs::r1cs-constraints-holdp
            (grp-from-bits-le-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                     x3 y3 exy ex2 ey2 p)
            asg p))
  :in-theory '(address-from-bits-le-funspec)
  :use grp-from-bits-le-gadget-complete)

(defruled fsa-address-from-bits-be-gadget-complete
  :short "R1CS-COMPLETE of @('Address::from_bits_be')."
  (implies (grp-fb-hyps (rev bits)
            (grp-fb-canon (rev bits) address-from-bits-be-funspec))
           (r1cs::r1cs-constraints-holdp
            (grp-from-bits-be-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                     x3 y3 exy ex2 ey2 p)
            asg p))
  :in-theory '(address-from-bits-be-funspec)
  :use grp-from-bits-be-gadget-complete)
