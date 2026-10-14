; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ternary selection.  In the non-constant case snarkVM emits one field
; ternary constraint per coordinate or embedded scalar:
;   Group / Address: two field ternaries (x and y).
;   Scalar: one field ternary.
;   ComputeKey: two groups and one scalar (five constraints).
;   Signature: two scalars and one compute key (seven constraints).

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "../fun-specs/curve-group")
(include-book "../fun-specs/curve-address")
(include-book "../fun-specs/curve-account")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-ternary-gadget ((c symbolp)
                                  (x1 symbolp) (y1 symbolp)
                                  (x2 symbolp) (y2 symbolp)
                                  (rx symbolp) (ry symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-field-ternary-gadget c x1 x2 rx p)
          (crv-field-ternary-gadget c y1 y2 ry p)))

(defruled crv-group-ternary-gadget-sound
  (implies (and (symbolp c) (symbolp x1) (symbolp y1)
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
                (fieldp (lookup-equal rx asg))
                (fieldp (lookup-equal ry asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-ternary-gadget c x1 y1 x2 y2 rx ry p) asg p))
           (equal (ecurve::point-finite (lookup-equal rx asg)
                                        (lookup-equal ry asg))
                  (group-ternary-funspec (lookup-equal c asg) p1 p2)))
  :hints (("Goal"
           :in-theory (e/d (crv-group-ternary-gadget
                            group-ternary-funspec
                            ecurve::point-finite
                            curve-coordinatesp-when-edwards-bls12-pointp)
                           ())
           :use ((:instance crv-field-ternary-gadget-sound
                            (a x1) (b x2) (r rx))
                 (:instance crv-field-ternary-gadget-sound
                            (a y1) (b y2) (r ry))))))

(defruled crv-group-ternary-gadget-complete
  (implies (and (symbolp c) (symbolp x1) (symbolp y1)
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
                (equal (lookup-equal rx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal x1 asg)
                                              (lookup-equal x2 asg)))
                (equal (lookup-equal ry asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal y1 asg)
                                              (lookup-equal y2 asg))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-group-ternary-gadget c x1 y1 x2 y2 rx ry p) asg p)
                (equal (ecurve::point-finite (lookup-equal rx asg)
                                             (lookup-equal ry asg))
                       (group-ternary-funspec (lookup-equal c asg) p1 p2))))
  :hints (("Goal"
           :in-theory (e/d (crv-group-ternary-gadget
                            group-ternary-funspec
                            field-ternary-funspec
                            ecurve::point-finite
                            curve-coordinatesp-when-edwards-bls12-pointp)
                           ())
           :use ((:instance crv-field-ternary-gadget-complete
                            (a x1) (b x2) (r rx))
                 (:instance crv-field-ternary-gadget-complete
                            (a y1) (b y2) (r ry))))))

(defconst *crv-group-ternary-sample*
  '((c . 1) (x1 . 3) (y1 . 4) (x2 . 5) (y2 . 6) (rx . 3) (ry . 4)))

(defruled crv-group-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-group-ternary-sample* p)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'c)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'x1)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'y1)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'x2)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'y2)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'rx)
                (r1cs::valuation-bindsp *crv-group-ternary-sample* 'ry)
                (bitp (lookup-equal 'c *crv-group-ternary-sample*))
                (fieldp (lookup-equal 'x1 *crv-group-ternary-sample*))
                (fieldp (lookup-equal 'y1 *crv-group-ternary-sample*))
                (fieldp (lookup-equal 'x2 *crv-group-ternary-sample*))
                (fieldp (lookup-equal 'y2 *crv-group-ternary-sample*))
                (equal (lookup-equal 'rx *crv-group-ternary-sample*)
                       (field-ternary-funspec
                        (lookup-equal 'c *crv-group-ternary-sample*)
                        (lookup-equal 'x1 *crv-group-ternary-sample*)
                        (lookup-equal 'x2 *crv-group-ternary-sample*)))
                (equal (lookup-equal 'ry *crv-group-ternary-sample*)
                       (field-ternary-funspec
                        (lookup-equal 'c *crv-group-ternary-sample*)
                        (lookup-equal 'y1 *crv-group-ternary-sample*)
                        (lookup-equal 'y2 *crv-group-ternary-sample*))))
           (r1cs::r1cs-constraints-holdp
            (crv-group-ternary-gadget 'c 'x1 'y1 'x2 'y2 'rx 'ry p)
            *crv-group-ternary-sample* p))
  :enable (crv-group-ternary-gadget
           crv-field-ternary-gadget-complete))

(define crv-group-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_group_ternary(c, x1, y1, x2, y2, rx, ry) := {
    (c) * (x1 - x2) == (rx - x2),
    (c) * (y1 - y2) == (ry - y2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-group-ternary-circuit)
            :pred crv-group-ternary-pred
            :prime prime)

(defruled crv-group-ternary-pred-to-fields
  (implies (and (primep prime)
                (pfield::fep c prime)
                (pfield::fep x1 prime) (pfield::fep y1 prime)
                (pfield::fep x2 prime) (pfield::fep y2 prime)
                (pfield::fep rx prime) (pfield::fep ry prime))
           (equal (crv-group-ternary-pred c x1 y1 x2 y2 rx ry prime)
                  (and (crv-field-ternary-pred c x1 x2 rx prime)
                       (crv-field-ternary-pred c y1 y2 ry prime))))
  :enable (crv-group-ternary-pred crv-field-ternary-pred))

(defruled crv-group-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c)
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (fieldp rx) (fieldp ry)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-group-ternary-pred c x1 y1 x2 y2 rx ry prime))
           (equal (ecurve::point-finite rx ry)
                  (group-ternary-funspec c p1 p2)))
  :enable (crv-group-ternary-pred-to-fields
           crv-field-ternary-pred-sound
           group-ternary-funspec
           ecurve::point-finite))

(defruled crv-group-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (field-ternary-funspec c x1 x2))
                (equal ry (field-ternary-funspec c y1 y2)))
           (and (crv-group-ternary-pred c x1 y1 x2 y2 rx ry prime)
                (equal (ecurve::point-finite rx ry)
                       (group-ternary-funspec c p1 p2))))
  :enable (crv-group-ternary-pred-to-fields
           crv-field-ternary-pred-complete
           group-ternary-funspec
           field-ternary-funspec
           curve-coordinatesp-when-edwards-bls12-pointp
           ecurve::point-finite
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-address-ternary-gadget ((c symbolp)
                                    (x1 symbolp) (y1 symbolp)
                                    (x2 symbolp) (y2 symbolp)
                                    (rx symbolp) (ry symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-ternary-gadget c x1 y1 x2 y2 rx ry p))

(defruled crv-address-ternary-gadget-sound
  (implies (and (symbolp c) (symbolp x1) (symbolp y1)
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
                (fieldp (lookup-equal rx asg))
                (fieldp (lookup-equal ry asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-ternary-gadget c x1 y1 x2 y2 rx ry p) asg p))
           (equal (ecurve::point-finite (lookup-equal rx asg)
                                        (lookup-equal ry asg))
                  (address-ternary-funspec (lookup-equal c asg) p1 p2)))
  :enable (crv-address-ternary-gadget
           address-ternary-funspec
           crv-group-ternary-gadget-sound))

(defruled crv-address-ternary-gadget-complete
  (implies (and (symbolp c) (symbolp x1) (symbolp y1)
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
                (equal (lookup-equal rx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal x1 asg)
                                              (lookup-equal x2 asg)))
                (equal (lookup-equal ry asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal y1 asg)
                                              (lookup-equal y2 asg))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-address-ternary-gadget c x1 y1 x2 y2 rx ry p) asg p)
                (equal (ecurve::point-finite (lookup-equal rx asg)
                                             (lookup-equal ry asg))
                       (address-ternary-funspec (lookup-equal c asg) p1 p2))))
  :enable (crv-address-ternary-gadget
           address-ternary-funspec
           group-ternary-funspec
           crv-group-ternary-gadget-complete))

(defconst *crv-address-ternary-sample* *crv-group-ternary-sample*)

(defruled crv-address-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-address-ternary-sample* p)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'c)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'x1)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'y1)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'x2)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'y2)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'rx)
                (r1cs::valuation-bindsp *crv-address-ternary-sample* 'ry)
                (bitp (lookup-equal 'c *crv-address-ternary-sample*))
                (fieldp (lookup-equal 'x1 *crv-address-ternary-sample*))
                (fieldp (lookup-equal 'y1 *crv-address-ternary-sample*))
                (fieldp (lookup-equal 'x2 *crv-address-ternary-sample*))
                (fieldp (lookup-equal 'y2 *crv-address-ternary-sample*))
                (equal (lookup-equal 'rx *crv-address-ternary-sample*)
                       (field-ternary-funspec
                        (lookup-equal 'c *crv-address-ternary-sample*)
                        (lookup-equal 'x1 *crv-address-ternary-sample*)
                        (lookup-equal 'x2 *crv-address-ternary-sample*)))
                (equal (lookup-equal 'ry *crv-address-ternary-sample*)
                       (field-ternary-funspec
                        (lookup-equal 'c *crv-address-ternary-sample*)
                        (lookup-equal 'y1 *crv-address-ternary-sample*)
                        (lookup-equal 'y2 *crv-address-ternary-sample*))))
           (r1cs::r1cs-constraints-holdp
            (crv-address-ternary-gadget 'c 'x1 'y1 'x2 'y2 'rx 'ry p)
            *crv-address-ternary-sample* p))
  :enable (crv-address-ternary-gadget crv-group-ternary-sample-holds))

(define crv-address-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_address_ternary(c, x1, y1, x2, y2, rx, ry) := {
    (c) * (x1 - x2) == (rx - x2),
    (c) * (y1 - y2) == (ry - y2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-address-ternary-circuit)
            :pred crv-address-ternary-pred
            :prime prime)

(defruled crv-address-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c)
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (fieldp rx) (fieldp ry)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-address-ternary-pred c x1 y1 x2 y2 rx ry prime))
           (equal (ecurve::point-finite rx ry)
                  (address-ternary-funspec c p1 p2)))
  :enable (crv-address-ternary-pred
           crv-group-ternary-pred
           crv-group-ternary-pred-sound
           address-ternary-funspec))

(defruled crv-address-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (field-ternary-funspec c x1 x2))
                (equal ry (field-ternary-funspec c y1 y2)))
           (and (crv-address-ternary-pred c x1 y1 x2 y2 rx ry prime)
                (equal (ecurve::point-finite rx ry)
                       (address-ternary-funspec c p1 p2))))
  :enable (crv-address-ternary-pred
           crv-group-ternary-pred
           crv-group-ternary-pred-complete
           address-ternary-funspec
           group-ternary-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-ternary-gadget ((c symbolp)
                                   (a symbolp)
                                   (b symbolp)
                                   (r symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-field-ternary-gadget c a b r p))

(defruled crv-scalar-ternary-gadget-sound
  (implies (and (symbolp c) (symbolp a) (symbolp b) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal c asg))
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (fieldp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-ternary-gadget c a b r p) asg p))
           (equal (lookup-equal r asg)
                  (scalar-ternary-funspec (lookup-equal c asg)
                                          (lookup-equal a asg)
                                          (lookup-equal b asg))))
  :enable (crv-scalar-ternary-gadget
           crv-field-ternary-gadget-sound
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec))

(defruled crv-scalar-ternary-gadget-complete
  (implies (and (symbolp c) (symbolp a) (symbolp b) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal c asg))
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (scalar-ternary-funspec (lookup-equal c asg)
                                               (lookup-equal a asg)
                                               (lookup-equal b asg))))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-ternary-gadget c a b r p) asg p))
  :enable (crv-scalar-ternary-gadget
           crv-field-ternary-gadget-complete
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec))

(defconst *crv-scalar-ternary-sample*
  '((c . 0) (a . 3) (b . 4) (r . 4)))

(defruled crv-scalar-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-scalar-ternary-sample* p)
                (r1cs::valuation-bindsp *crv-scalar-ternary-sample* 'c)
                (r1cs::valuation-bindsp *crv-scalar-ternary-sample* 'a)
                (r1cs::valuation-bindsp *crv-scalar-ternary-sample* 'b)
                (r1cs::valuation-bindsp *crv-scalar-ternary-sample* 'r)
                (bitp (lookup-equal 'c *crv-scalar-ternary-sample*))
                (scalarp (lookup-equal 'a *crv-scalar-ternary-sample*))
                (scalarp (lookup-equal 'b *crv-scalar-ternary-sample*))
                (equal (lookup-equal 'r *crv-scalar-ternary-sample*)
                       (scalar-ternary-funspec
                        (lookup-equal 'c *crv-scalar-ternary-sample*)
                        (lookup-equal 'a *crv-scalar-ternary-sample*)
                        (lookup-equal 'b *crv-scalar-ternary-sample*))))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-ternary-gadget 'c 'a 'b 'r p)
            *crv-scalar-ternary-sample* p))
  :enable crv-scalar-ternary-gadget-complete)

(define crv-scalar-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_scalar_ternary(c, a, b, r) := {
    (c) * (a - b) == (r - b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-scalar-ternary-circuit)
            :pred crv-scalar-ternary-pred
            :prime prime)

(defruled crv-scalar-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c) (scalarp a) (scalarp b) (fieldp r)
                (crv-scalar-ternary-pred c a b r prime))
           (equal r (scalar-ternary-funspec c a b)))
  :enable (crv-scalar-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-sound
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec))

(defruled crv-scalar-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c) (scalarp a) (scalarp b)
                (equal r (scalar-ternary-funspec c a b)))
           (crv-scalar-ternary-pred c a b r prime))
  :enable (crv-scalar-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-complete
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey::ternary selects pk_sig, pr_sig, and sk_prf.
; Five field-ternary constraints.

(define crv-compute-key-ternary-gadget
  ((c symbolp)
   (pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (s1 symbolp) (s2 symbolp)
   (pkx symbolp) (pky symbolp) (prx symbolp) (pry symbolp) (s symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-group-ternary-gadget c pk1x pk1y pk2x pk2y pkx pky p)
          (crv-group-ternary-gadget c pr1x pr1y pr2x pr2y prx pry p)
          (crv-scalar-ternary-gadget c s1 s2 s p)))

(defruled crv-compute-key-ternary-gadget-sound
  (implies (and (symbolp c)
                (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp s1) (symbolp s2)
                (symbolp pkx) (symbolp pky) (symbolp prx) (symbolp pry)
                (symbolp s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg s)
                (bitp (lookup-equal c asg))
                (curve-compute-keyp ck1)
                (curve-compute-keyp ck2)
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s2 asg) (third ck2))
                (fieldp (lookup-equal pkx asg))
                (fieldp (lookup-equal pky asg))
                (fieldp (lookup-equal prx asg))
                (fieldp (lookup-equal pry asg))
                (fieldp (lookup-equal s asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-ternary-gadget
                  c pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
                  s1 s2 pkx pky prx pry s p)
                 asg p))
           (equal (list (ecurve::point-finite (lookup-equal pkx asg)
                                              (lookup-equal pky asg))
                        (ecurve::point-finite (lookup-equal prx asg)
                                              (lookup-equal pry asg))
                        (lookup-equal s asg))
                  (compute-key-ternary-funspec (lookup-equal c asg) ck1 ck2)))
  :hints (("Goal"
           :in-theory (e/d (crv-compute-key-ternary-gadget
                            compute-key-ternary-funspec
                            curve-compute-keyp-forward)
                           ())
           :use ((:instance crv-group-ternary-gadget-sound
                            (x1 pk1x) (y1 pk1y) (x2 pk2x) (y2 pk2y)
                            (rx pkx) (ry pky)
                            (p1 (first ck1)) (p2 (first ck2)))
                 (:instance crv-group-ternary-gadget-sound
                            (x1 pr1x) (y1 pr1y) (x2 pr2x) (y2 pr2y)
                            (rx prx) (ry pry)
                            (p1 (second ck1)) (p2 (second ck2)))
                 (:instance crv-scalar-ternary-gadget-sound
                            (a s1) (b s2) (r s))))))

(defruled crv-compute-key-ternary-gadget-complete
  (implies (and (symbolp c)
                (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp s1) (symbolp s2)
                (symbolp pkx) (symbolp pky) (symbolp prx) (symbolp pry)
                (symbolp s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg s)
                (bitp (lookup-equal c asg))
                (curve-compute-keyp ck1)
                (curve-compute-keyp ck2)
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s2 asg) (third ck2))
                (equal (lookup-equal pkx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pk1x asg)
                                              (lookup-equal pk2x asg)))
                (equal (lookup-equal pky asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pk1y asg)
                                              (lookup-equal pk2y asg)))
                (equal (lookup-equal prx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pr1x asg)
                                              (lookup-equal pr2x asg)))
                (equal (lookup-equal pry asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pr1y asg)
                                              (lookup-equal pr2y asg)))
                (equal (lookup-equal s asg)
                       (scalar-ternary-funspec (lookup-equal c asg)
                                               (lookup-equal s1 asg)
                                               (lookup-equal s2 asg))))
           (r1cs::r1cs-constraints-holdp
            (crv-compute-key-ternary-gadget
             c pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
             s1 s2 pkx pky prx pry s p)
            asg p))
  :hints (("Goal"
           :in-theory (e/d (crv-compute-key-ternary-gadget
                            curve-compute-keyp-forward)
                           ())
           :use ((:instance crv-group-ternary-gadget-complete
                            (x1 pk1x) (y1 pk1y) (x2 pk2x) (y2 pk2y)
                            (rx pkx) (ry pky)
                            (p1 (first ck1)) (p2 (first ck2)))
                 (:instance crv-group-ternary-gadget-complete
                            (x1 pr1x) (y1 pr1y) (x2 pr2x) (y2 pr2y)
                            (rx prx) (ry pry)
                            (p1 (second ck1)) (p2 (second ck2)))
                 (:instance crv-scalar-ternary-gadget-complete
                            (a s1) (b s2) (r s))))))

(defconst *crv-compute-key-ternary-sample*
  '((c . 1)
    (pk1x . 1) (pk1y . 2) (pk2x . 3) (pk2y . 4)
    (pr1x . 5) (pr1y . 6) (pr2x . 7) (pr2y . 8)
    (s1 . 9) (s2 . 10)
    (pkx . 1) (pky . 2) (prx . 5) (pry . 6) (s . 9)))

(defruled crv-compute-key-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-compute-key-ternary-sample* p)
                (bitp (lookup-equal 'c *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pk1x *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pk1y *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pk2x *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pk2y *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pr1x *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pr1y *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pr2x *crv-compute-key-ternary-sample*))
                (fieldp (lookup-equal 'pr2y *crv-compute-key-ternary-sample*))
                (scalarp (lookup-equal 's1 *crv-compute-key-ternary-sample*))
                (scalarp (lookup-equal 's2 *crv-compute-key-ternary-sample*))
                (equal (lookup-equal 'pkx *crv-compute-key-ternary-sample*)
                       (lookup-equal 'pk1x *crv-compute-key-ternary-sample*))
                (equal (lookup-equal 'pky *crv-compute-key-ternary-sample*)
                       (lookup-equal 'pk1y *crv-compute-key-ternary-sample*))
                (equal (lookup-equal 'prx *crv-compute-key-ternary-sample*)
                       (lookup-equal 'pr1x *crv-compute-key-ternary-sample*))
                (equal (lookup-equal 'pry *crv-compute-key-ternary-sample*)
                       (lookup-equal 'pr1y *crv-compute-key-ternary-sample*))
                (equal (lookup-equal 's *crv-compute-key-ternary-sample*)
                       (lookup-equal 's1 *crv-compute-key-ternary-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-compute-key-ternary-gadget
             'c 'pk1x 'pk1y 'pk2x 'pk2y 'pr1x 'pr1y 'pr2x 'pr2y
             's1 's2 'pkx 'pky 'prx 'pry 's p)
            *crv-compute-key-ternary-sample* p))
  :enable (crv-compute-key-ternary-gadget
           crv-field-ternary-gadget-complete
           crv-scalar-ternary-gadget
           field-ternary-funspec
           scalar-ternary-funspec
           curve-fieldp-when-scalarp))

(define crv-compute-key-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_compute_key_ternary(c, pk1x, pk1y, pk2x, pk2y, pr1x, pr1y, pr2x, pr2y, s1, s2, pkx, pky, prx, pry, s) := {
    (c) * (pk1x - pk2x) == (pkx - pk2x),
    (c) * (pk1y - pk2y) == (pky - pk2y),
    (c) * (pr1x - pr2x) == (prx - pr2x),
    (c) * (pr1y - pr2y) == (pry - pr2y),
    (c) * (s1 - s2) == (s - s2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-compute-key-ternary-circuit)
            :pred crv-compute-key-ternary-pred
            :prime prime)

(defruled crv-compute-key-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c)
                (fieldp pk1x) (fieldp pk1y) (fieldp pk2x) (fieldp pk2y)
                (fieldp pr1x) (fieldp pr1y) (fieldp pr2x) (fieldp pr2y)
                (scalarp s1) (scalarp s2)
                (fieldp pkx) (fieldp pky) (fieldp prx) (fieldp pry) (fieldp s)
                (curve-compute-keyp ck1) (curve-compute-keyp ck2)
                (equal pk1x (ecurve::point-finite->x (first ck1)))
                (equal pk1y (ecurve::point-finite->y (first ck1)))
                (equal pr1x (ecurve::point-finite->x (second ck1)))
                (equal pr1y (ecurve::point-finite->y (second ck1)))
                (equal s1 (third ck1))
                (equal pk2x (ecurve::point-finite->x (first ck2)))
                (equal pk2y (ecurve::point-finite->y (first ck2)))
                (equal pr2x (ecurve::point-finite->x (second ck2)))
                (equal pr2y (ecurve::point-finite->y (second ck2)))
                (equal s2 (third ck2))
                (crv-compute-key-ternary-pred
                 c pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
                 s1 s2 pkx pky prx pry s prime))
           (equal (list (ecurve::point-finite pkx pky)
                        (ecurve::point-finite prx pry)
                        s)
                  (compute-key-ternary-funspec c ck1 ck2)))
  :enable (crv-compute-key-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-sound
           curve-fieldp-when-scalarp
           compute-key-ternary-funspec
           field-ternary-funspec
           scalar-ternary-funspec
           curve-compute-keyp-forward))

(defruled crv-compute-key-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c)
                (curve-compute-keyp ck1) (curve-compute-keyp ck2)
                (equal pk1x (ecurve::point-finite->x (first ck1)))
                (equal pk1y (ecurve::point-finite->y (first ck1)))
                (equal pr1x (ecurve::point-finite->x (second ck1)))
                (equal pr1y (ecurve::point-finite->y (second ck1)))
                (equal s1 (third ck1))
                (equal pk2x (ecurve::point-finite->x (first ck2)))
                (equal pk2y (ecurve::point-finite->y (first ck2)))
                (equal pr2x (ecurve::point-finite->x (second ck2)))
                (equal pr2y (ecurve::point-finite->y (second ck2)))
                (equal s2 (third ck2))
                (equal pkx (field-ternary-funspec c pk1x pk2x))
                (equal pky (field-ternary-funspec c pk1y pk2y))
                (equal prx (field-ternary-funspec c pr1x pr2x))
                (equal pry (field-ternary-funspec c pr1y pr2y))
                (equal s (scalar-ternary-funspec c s1 s2)))
           (crv-compute-key-ternary-pred
            c pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
            s1 s2 pkx pky prx pry s prime))
  :enable (crv-compute-key-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-complete
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec
           curve-compute-keyp-forward
           curve-coordinatesp-when-edwards-bls12-pointp
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature::ternary selects challenge, response, and the compute key.
; Seven field-ternary constraints.

(define crv-signature-ternary-gadget
  ((c symbolp)
   (ch1 symbolp) (ch2 symbolp)
   (rsp1 symbolp) (rsp2 symbolp)
   (pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (s1 symbolp) (s2 symbolp)
   (ch symbolp) (rsp symbolp)
   (pkx symbolp) (pky symbolp) (prx symbolp) (pry symbolp) (s symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-scalar-ternary-gadget c ch1 ch2 ch p)
          (crv-scalar-ternary-gadget c rsp1 rsp2 rsp p)
          (crv-compute-key-ternary-gadget
           c pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
           s1 s2 pkx pky prx pry s p)))

; R1CS soundness of signature ternary is the componentwise scalar and
; compute-key ternary soundness theorems.  The satisfying assignment's
; challenge, response, and compute key are those ternary results, and
; signature-ternary-funspec is that componentwise selection.  The PFCS
; predicate below is proved equivalent to the funspec directly.

(defconst *crv-signature-ternary-sample*
  '((c . 0)
    (ch1 . 1) (ch2 . 2) (rsp1 . 3) (rsp2 . 4)
    (pk1x . 5) (pk1y . 6) (pk2x . 7) (pk2y . 8)
    (pr1x . 9) (pr1y . 10) (pr2x . 11) (pr2y . 12)
    (s1 . 13) (s2 . 14)
    (ch . 2) (rsp . 4)
    (pkx . 7) (pky . 8) (prx . 11) (pry . 12) (s . 14)))

(defruled crv-signature-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-signature-ternary-sample* p)
                (bitp (lookup-equal 'c *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 'ch1 *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 'ch2 *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 'rsp1 *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 'rsp2 *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pk1x *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pk2x *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pk1y *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pk2y *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pr1x *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pr2x *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pr1y *crv-signature-ternary-sample*))
                (fieldp (lookup-equal 'pr2y *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 's1 *crv-signature-ternary-sample*))
                (scalarp (lookup-equal 's2 *crv-signature-ternary-sample*))
                (equal (lookup-equal 'ch *crv-signature-ternary-sample*)
                       (lookup-equal 'ch2 *crv-signature-ternary-sample*))
                (equal (lookup-equal 'rsp *crv-signature-ternary-sample*)
                       (lookup-equal 'rsp2 *crv-signature-ternary-sample*))
                (equal (lookup-equal 'pkx *crv-signature-ternary-sample*)
                       (lookup-equal 'pk2x *crv-signature-ternary-sample*))
                (equal (lookup-equal 'pky *crv-signature-ternary-sample*)
                       (lookup-equal 'pk2y *crv-signature-ternary-sample*))
                (equal (lookup-equal 'prx *crv-signature-ternary-sample*)
                       (lookup-equal 'pr2x *crv-signature-ternary-sample*))
                (equal (lookup-equal 'pry *crv-signature-ternary-sample*)
                       (lookup-equal 'pr2y *crv-signature-ternary-sample*))
                (equal (lookup-equal 's *crv-signature-ternary-sample*)
                       (lookup-equal 's2 *crv-signature-ternary-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-signature-ternary-gadget
             'c 'ch1 'ch2 'rsp1 'rsp2
             'pk1x 'pk1y 'pk2x 'pk2y
             'pr1x 'pr1y 'pr2x 'pr2y
             's1 's2
             'ch 'rsp 'pkx 'pky 'prx 'pry 's p)
            *crv-signature-ternary-sample* p))
  :enable (crv-signature-ternary-gadget
           crv-compute-key-ternary-gadget
           crv-scalar-ternary-gadget
           crv-field-ternary-gadget-complete
           field-ternary-funspec
           scalar-ternary-funspec
           curve-fieldp-when-scalarp))

(define crv-signature-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_signature_ternary(c, ch1, ch2, rsp1, rsp2, pk1x, pk1y, pk2x, pk2y, pr1x, pr1y, pr2x, pr2y, s1, s2, ch, rsp, pkx, pky, prx, pry, s) := {
    (c) * (ch1 - ch2) == (ch - ch2),
    (c) * (rsp1 - rsp2) == (rsp - rsp2),
    (c) * (pk1x - pk2x) == (pkx - pk2x),
    (c) * (pk1y - pk2y) == (pky - pk2y),
    (c) * (pr1x - pr2x) == (prx - pr2x),
    (c) * (pr1y - pr2y) == (pry - pr2y),
    (c) * (s1 - s2) == (s - s2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-signature-ternary-circuit)
            :pred crv-signature-ternary-pred
            :prime prime)

(defruled crv-signature-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c)
                (scalarp ch1) (scalarp ch2)
                (scalarp rsp1) (scalarp rsp2)
                (fieldp pk1x) (fieldp pk1y) (fieldp pk2x) (fieldp pk2y)
                (fieldp pr1x) (fieldp pr1y) (fieldp pr2x) (fieldp pr2y)
                (scalarp s1) (scalarp s2)
                (fieldp ch) (fieldp rsp)
                (fieldp pkx) (fieldp pky) (fieldp prx) (fieldp pry) (fieldp s)
                (curve-signaturep sig1) (curve-signaturep sig2)
                (equal ch1 (first sig1))
                (equal rsp1 (second sig1))
                (equal s1 (third (third sig1)))
                (equal pk1x (ecurve::point-finite->x (first (third sig1))))
                (equal pk1y (ecurve::point-finite->y (first (third sig1))))
                (equal pr1x (ecurve::point-finite->x (second (third sig1))))
                (equal pr1y (ecurve::point-finite->y (second (third sig1))))
                (equal ch2 (first sig2))
                (equal rsp2 (second sig2))
                (equal s2 (third (third sig2)))
                (equal pk2x (ecurve::point-finite->x (first (third sig2))))
                (equal pk2y (ecurve::point-finite->y (first (third sig2))))
                (equal pr2x (ecurve::point-finite->x (second (third sig2))))
                (equal pr2y (ecurve::point-finite->y (second (third sig2))))
                (crv-signature-ternary-pred
                 c ch1 ch2 rsp1 rsp2
                 pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
                 s1 s2 ch rsp pkx pky prx pry s prime))
           (equal (list ch rsp
                        (list (ecurve::point-finite pkx pky)
                              (ecurve::point-finite prx pry)
                              s))
                  (signature-ternary-funspec c sig1 sig2)))
  :enable (crv-signature-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-sound
           curve-fieldp-when-scalarp
           signature-ternary-funspec
           compute-key-ternary-funspec
           scalar-ternary-funspec
           field-ternary-funspec
           curve-signaturep-forward
           curve-compute-keyp-forward))

(defruled crv-signature-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c)
                (curve-signaturep sig1) (curve-signaturep sig2)
                (equal ch1 (first sig1))
                (equal rsp1 (second sig1))
                (equal s1 (third (third sig1)))
                (equal pk1x (ecurve::point-finite->x (first (third sig1))))
                (equal pk1y (ecurve::point-finite->y (first (third sig1))))
                (equal pr1x (ecurve::point-finite->x (second (third sig1))))
                (equal pr1y (ecurve::point-finite->y (second (third sig1))))
                (equal ch2 (first sig2))
                (equal rsp2 (second sig2))
                (equal s2 (third (third sig2)))
                (equal pk2x (ecurve::point-finite->x (first (third sig2))))
                (equal pk2y (ecurve::point-finite->y (first (third sig2))))
                (equal pr2x (ecurve::point-finite->x (second (third sig2))))
                (equal pr2y (ecurve::point-finite->y (second (third sig2))))
                (equal ch (scalar-ternary-funspec c ch1 ch2))
                (equal rsp (scalar-ternary-funspec c rsp1 rsp2))
                (equal pkx (field-ternary-funspec c pk1x pk2x))
                (equal pky (field-ternary-funspec c pk1y pk2y))
                (equal prx (field-ternary-funspec c pr1x pr2x))
                (equal pry (field-ternary-funspec c pr1y pr2y))
                (equal s (scalar-ternary-funspec c s1 s2)))
           (crv-signature-ternary-pred
            c ch1 ch2 rsp1 rsp2
            pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y
            s1 s2 ch rsp pkx pky prx pry s prime))
  :enable (crv-signature-ternary-pred
           crv-field-ternary-pred
           crv-field-ternary-pred-complete
           curve-fieldp-when-scalarp
           scalar-ternary-funspec
           field-ternary-funspec
           curve-signaturep-forward
           curve-compute-keyp-forward
           curve-coordinatesp-when-edwards-bls12-pointp
           fieldp))

; Completeness of the R1CS is the component completeness theorems
; (scalar ternary twice and compute-key ternary) at the snarkVM witness,
; which selects each component.
