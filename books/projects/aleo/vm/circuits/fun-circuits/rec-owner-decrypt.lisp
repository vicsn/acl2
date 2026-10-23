; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Owner::decrypt_with_randomizer, private case
; (circuit/program/src/data/record/decrypt.rs): the owner field is c - r
; and the address is Address::from_field(c - r), that is
; Group::from_x_coordinate on the linear combination c - r.  The linear
; combination is modelled by a wire x and the constraint x * 1 = c - r,
; which fixes x to the same value.  The public case emits no constraints.

(in-package "ALEOVM")

(include-book "grp-from-x-coordinate")
(include-book "../fun-specs/crypto-record")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled rec-groupp-is-point-finite
  (implies (groupp q)
           (and (equal (ecurve::point-finite (ecurve::point-finite->x q)
                                             (ecurve::point-finite->y q))
                       q)
                (equal (ecurve::point-kind q) :finite)
                (fieldp (ecurve::point-finite->x q))
                (fieldp (ecurve::point-finite->y q))))
  :enable (groupp ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p ecurve::twisted-edwards-zero
           fieldp base-prime ecurve::edwards-bls12-curve
           ecurve::edwards-bls12-q pfield::fep))

(defruled rec-groupp-is-bls12-point
  (implies (groupp q) (ecurve::edwards-bls12-pointp q))
  :enable (groupp ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p ecurve::twisted-edwards-zero
           ecurve::edwards-bls12-curve ecurve::edwards-bls12-q))

(defruled rec-crypto-group-from-x-unique
  (implies (and (fieldp x) (fieldp y)
                (groupp (ecurve::point-finite x y)))
           (equal (crypto-group-from-x x)
                  (ecurve::point-finite x y)))
  :hints (("Goal"
           :in-theory '(crypto-group-from-x crypto-group-x groupp
                        ecurve::edwards-bls12-point->u
                        ecurve::point-finite->x-of-point-finite
                        ecurve::point-finite->y-of-point-finite
                        ecurve::point-kind-of-point-finite
                        nfix fieldp pfield::fep
                        acl2::natp-compound-recognizer)
           :use ((:instance crypto-group-with-x
                            (p (ecurve::point-finite x y)))
                 (:instance rec-groupp-is-bls12-point (q (crypto-group-with-x x)))
                 (:instance rec-groupp-is-point-finite
                            (q (crypto-group-with-x x)))
                 (:instance grp-groupp-same-abscissa
                            (y1 y)
                            (y2 (ecurve::point-finite->y
                                 (crypto-group-with-x x))))))))

(defruled rec-not-reserrp-of-point-finite
  (not (reserrp (ecurve::point-finite a b)))
  :enable (reserrp ecurve::point-finite))

(defruled rec-from-x-gadget-crypto-group
  (implies (grp-from-xy-wire-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-from-x-coordinate-gadget
              x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (crypto-group-from-x (lookup-equal x asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :hints (("Goal"
           :in-theory '(fieldp r1cs::fep-of-lookup-equal reserrp
                        ecurve::point-kind-of-point-finite)
           :use (grp-from-x-coordinate-gadget-sound
                 (:instance rec-not-reserrp-of-point-finite (a (lookup-equal x asg)) (b (lookup-equal y asg)))
                 (:instance return-type-of-group-from-x-coordinate-funspec
                            (x (lookup-equal x asg)))
                 (:instance rec-crypto-group-from-x-unique
                            (x (lookup-equal x asg))
                            (y (lookup-equal y asg)))))))

(define rec-owner-decrypt-private-gadget
  ((c symbolp) (r symbolp)
   (x symbolp) (y symbolp) (qx symbolp) (qy symbolp)
   (cx2 symbolp) (cy2 symbolp) (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
   (x3 symbolp) (y3 symbolp) (exy symbolp) (ex2 symbolp) (ey2 symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cons (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c (list (list 1 c) (list (1- p) r)))
        (grp-from-x-coordinate-gadget
         x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)))

(defruled rec-owner-decrypt-sub-constraint
  (implies (and (symbolp x) (symbolp c) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list 1 x))
                    :b (list (list 1 1))
                    :c (list (list 1 c) (list (1- p) r)))
                   asg p)
                  (equal (lookup-equal x asg)
                         (pfield::sub (lookup-equal c asg)
                                      (lookup-equal r asg) p))))
  :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product pfield::sub
           pfield::neg))

(defruled rec-owner-decrypt-private-gadget-split
  (implies (and (symbolp x) (symbolp c) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraints-holdp
                   (rec-owner-decrypt-private-gadget
                    c r x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                   asg p)
                  (and (equal (lookup-equal x asg)
                              (pfield::sub (lookup-equal c asg)
                                           (lookup-equal r asg) p))
                       (r1cs::r1cs-constraints-holdp
                        (grp-from-x-coordinate-gadget
                         x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                        asg p))))
  :in-theory '(rec-owner-decrypt-private-gadget
               r1cs::r1cs-constraints-holdp-of-cons)
  :use rec-owner-decrypt-sub-constraint)

(defruled rec-owner-decrypt-private-gadget-sound
  :short "R1CS-SOUND of the private case of @('Owner::decrypt'): the
          constraints imply that the funspec on the ciphertext field
          and randomizer does not fail and returns the private owner at
          the point of the @('x') and @('y') wires."
  (implies (grp-from-xy-wire-hyps
            (symbolp c) (symbolp r)
            (r1cs::valuation-bindsp asg c)
            (r1cs::valuation-bindsp asg r)
            (r1cs::r1cs-constraints-holdp
             (rec-owner-decrypt-private-gadget
              c r x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (crypto-owner-decrypt
                   (crypto-ciphertext-owner-private
                    (list (lookup-equal c asg)))
                   (list (lookup-equal r asg)))
                  (owner-private (ecurve::point-finite (lookup-equal x asg)
                                                       (lookup-equal y asg)))))
  :hints (("Goal"
           :in-theory (e/d (crypto-owner-decrypt crypto-field-sub) (grp-from-x-coordinate-gadget rec-owner-decrypt-private-gadget pfield::sub))
           :use (rec-owner-decrypt-private-gadget-split
                 (:instance rec-from-x-gadget-crypto-group)
                 (:instance grp-from-x-coordinate-gadget-sound)
                 (:instance return-type-of-group-from-x-coordinate-funspec
                            (x (lookup-equal x asg)))
                 (:instance rec-not-reserrp-of-point-finite
                            (a (lookup-equal x asg)) (b (lookup-equal y asg)))))))

