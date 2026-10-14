; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Equality, disequality, and zero/one tests for group, scalar, address,
; compute key, and signature.
;
; Group::is_equal is field is_equal on x and on y, then boolean and.
; The field is_equal bit is the linear combination 1 - r, so the and
; constraint is (1 - rx) * (1 - ry) = (out).  is_not_equal is boolean
; not of that result: same constraints, output 1 - out.
; Scalar::is_equal is field is_equal on the embedded base-field element.
; Address::is_equal delegates to the inner group.

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "field-zero-r1cs")
(include-book "../fun-specs/curve-group")
(include-book "../fun-specs/curve-address")
(include-book "../fun-specs/curve-account")
(include-book "../fun-specs/primitives-scalar")
(include-book "../r1cs/boolean-and")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled crv-fieldp-when-scalarp
  (implies (scalarp s)
           (fieldp s))
  :enable (scalarp fieldp pfield::fep)
  :use curve-fieldp-when-scalarp)

(defruled crv-bitand-is-boolean-and-funspec
  (implies (and (bitp x) (bitp y))
           (equal (bitand x y) (boolean-and-funspec x y)))
  :enable (bitand boolean-and-funspec))

(defruled crv-group-points-equal-iff-coordinates
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (equal (equal p1 p2)
                  (and (equal (ecurve::point-finite->x p1)
                              (ecurve::point-finite->x p2))
                       (equal (ecurve::point-finite->y p1)
                              (ecurve::point-finite->y p2)))))
  :hints (("Goal"
           :in-theory (e/d (ecurve::point-fix-when-finite
                            ecurve::equal-of-point-finite
                            ecurve::point-finite-when-edwards-bls12-pointp
                            ecurve::pointp-when-edwards-bls12-pointp)
                           ()))))

(defruled crv-not-of-equal-bit
  (implies (and (equal p (base-prime))
                (bitp b))
           (equal (pfield::sub 1 b p)
                  (if (equal b 0) 1 0)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (e/d (bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-is-equal-gadget ((x1 symbolp) (y1 symbolp)
                                   (x2 symbolp) (y2 symbolp)
                                   (mx symbolp) (rx symbolp)
                                   (my symbolp) (ry symbolp)
                                   (out symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Group::is_equal') when the coordinates are
          not both constant: two field inequalities and one boolean and."
  (append (crv-field-is-not-equal-gadget x1 x2 mx rx p)
          (crv-field-is-not-equal-gadget y1 y2 my ry p)
          (crv-and-not-gadget rx ry out p)))

(defruled crv-group-is-equal-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (group-is-equal-funspec p1 p2)))
  :hints (("Goal"
           :in-theory (e/d (crv-group-is-equal-gadget
                            crv-and-not-gadget-to-mul
                            crv-and-not-is-and-of-equals
                            crv-group-points-equal-iff-coordinates
                            group-is-equal-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-and-funspec
                            boolean-not-funspec
                            curve-coordinatesp-when-edwards-bls12-pointp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance crv-field-is-not-equal-gadget-sound
                            (x x1) (y x2) (m mx) (r rx))
                 (:instance crv-field-is-not-equal-gadget-sound
                            (x y1) (y y2) (m my) (r ry))))))

(defruled crv-group-is-equal-gadget-complete
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (equal (lookup-equal rx asg)
                       (if (equal (lookup-equal x1 asg)
                                  (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal mx asg)
                       (if (equal (lookup-equal x1 asg)
                                  (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal ry asg)
                       (if (equal (lookup-equal y1 asg)
                                  (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal my asg)
                       (if (equal (lookup-equal y1 asg)
                                  (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal out asg)
                       (group-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
            asg p))
  :hints (("Goal"
           :in-theory (e/d (crv-group-is-equal-gadget
                            crv-and-not-gadget-to-mul
                            crv-group-points-equal-iff-coordinates
                            group-is-equal-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-and-funspec
                            boolean-not-funspec
                            curve-coordinatesp-when-edwards-bls12-pointp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance crv-field-is-not-equal-gadget-complete
                            (x x1) (y x2) (m mx) (r rx))
                 (:instance crv-field-is-not-equal-gadget-complete
                            (x y1) (y y2) (m my) (r ry))))))

(defconst *crv-group-is-equal-sample*
  '((x1 . 0) (y1 . 1) (x2 . 0) (y2 . 1)
    (mx . 0) (rx . 0) (my . 0) (ry . 0) (out . 1)))

(defruled crv-group-is-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-group-is-equal-sample* p)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'x1)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'y1)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'x2)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'y2)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'mx)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'rx)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'my)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'ry)
                (r1cs::valuation-bindsp *crv-group-is-equal-sample* 'out)
                (fieldp (lookup-equal 'x1 *crv-group-is-equal-sample*))
                (fieldp (lookup-equal 'y1 *crv-group-is-equal-sample*))
                (fieldp (lookup-equal 'x2 *crv-group-is-equal-sample*))
                (fieldp (lookup-equal 'y2 *crv-group-is-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-equal-gadget 'x1 'y1 'x2 'y2 'mx 'rx 'my 'ry 'out p)
            *crv-group-is-equal-sample* p))
  :enable (crv-group-is-equal-gadget
           crv-field-is-not-equal-gadget-complete
           crv-and-not-gadget-to-mul
           lookup-equal)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(define crv-group-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_group_is_equal(x1, y1, x2, y2, mx, rx, my, ry, out) := {
    (x1 - x2) * (mx) == (rx),
    (x1 - x2) * (1 - rx) == (0),
    (y1 - y2) * (my) == (ry),
    (y1 - y2) * (1 - ry) == (0),
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-group-is-equal-circuit)
            :pred crv-group-is-equal-pred
            :prime prime)

(defruled crv-group-is-equal-pred-to-muls
  (implies (and (primep prime)
                (pfield::fep x1 prime) (pfield::fep y1 prime)
                (pfield::fep x2 prime) (pfield::fep y2 prime)
                (pfield::fep mx prime) (pfield::fep rx prime)
                (pfield::fep my prime) (pfield::fep ry prime)
                (pfield::fep out prime))
           (equal (crv-group-is-equal-pred x1 y1 x2 y2 mx rx my ry out prime)
                  (and (crv-field-is-not-equal-pred x1 x2 mx rx prime)
                       (crv-field-is-not-equal-pred y1 y2 my ry prime)
                       (crv-and-not-pred rx ry out prime))))
  :enable (crv-group-is-equal-pred
           crv-field-is-not-equal-pred
           crv-and-not-pred))

(defruled crv-group-is-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (bitp rx) (bitp ry)
                (pfield::fep mx prime) (pfield::fep my prime)
                (pfield::fep out prime)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-group-is-equal-pred x1 y1 x2 y2 mx rx my ry out prime))
           (equal out (group-is-equal-funspec p1 p2)))
  :enable (crv-group-is-equal-pred-to-muls
           crv-field-is-not-equal-pred-sound
           crv-and-not-pred-sound
           crv-group-points-equal-iff-coordinates
           group-is-equal-funspec
           field-is-equal-funspec
           boolean-and-funspec
           boolean-not-funspec
           fieldp))

(defruled crv-group-is-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (if (equal x1 x2) 0 1))
                (equal mx (if (equal x1 x2)
                              0
                            (pfield::inv (pfield::sub x1 x2 prime) prime)))
                (equal ry (if (equal y1 y2) 0 1))
                (equal my (if (equal y1 y2)
                              0
                            (pfield::inv (pfield::sub y1 y2 prime) prime)))
                (equal out (group-is-equal-funspec p1 p2)))
           (crv-group-is-equal-pred x1 y1 x2 y2 mx rx my ry out prime))
  :enable (crv-group-is-equal-pred-to-muls
           crv-field-is-not-equal-pred-complete
           crv-and-not-pred-to-mul
           crv-group-points-equal-iff-coordinates
           group-is-equal-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-and-funspec
           boolean-not-funspec
           curve-coordinatesp-when-edwards-bls12-pointp
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-is-not-equal-gadget ((x1 symbolp) (y1 symbolp)
                                       (x2 symbolp) (y2 symbolp)
                                       (mx symbolp) (rx symbolp)
                                       (my symbolp) (ry symbolp)
                                       (out symbolp)
                                       (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as @('is_equal').  The result boolean is @($1 - out$)."
  (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p))

(defruled crv-group-is-not-equal-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (bitp (lookup-equal out asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-not-equal-gadget
                  x1 y1 x2 y2 mx rx my ry out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (group-is-not-equal-funspec p1 p2)))
  :enable (crv-group-is-not-equal-gadget
           crv-group-is-equal-gadget-sound
           group-is-not-equal-funspec
           group-is-equal-funspec
           crv-not-of-equal-bit))

(defruled crv-group-is-not-equal-gadget-complete
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (equal (lookup-equal rx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal mx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal ry asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal my asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal out asg) (group-is-equal-funspec p1 p2)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-group-is-not-equal-gadget
                  x1 y1 x2 y2 mx rx my ry out p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal out asg) p)
                       (group-is-not-equal-funspec p1 p2))))
  :enable (crv-group-is-not-equal-gadget
           crv-group-is-equal-gadget-complete
           group-is-not-equal-funspec
           group-is-equal-funspec
           crv-not-of-equal-bit))

(defconst *crv-group-is-not-equal-sample*
  *crv-group-is-equal-sample*)

(defruled crv-group-is-not-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-group-is-not-equal-sample* p)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'x1)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'y1)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'x2)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'y2)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'mx)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'rx)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'my)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'ry)
                (r1cs::valuation-bindsp *crv-group-is-not-equal-sample* 'out)
                (fieldp (lookup-equal 'x1 *crv-group-is-not-equal-sample*))
                (fieldp (lookup-equal 'y1 *crv-group-is-not-equal-sample*))
                (fieldp (lookup-equal 'x2 *crv-group-is-not-equal-sample*))
                (fieldp (lookup-equal 'y2 *crv-group-is-not-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-not-equal-gadget
             'x1 'y1 'x2 'y2 'mx 'rx 'my 'ry 'out p)
            *crv-group-is-not-equal-sample* p))
  :enable (crv-group-is-not-equal-gadget
           crv-group-is-equal-sample-holds))

(define crv-group-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Same equality system.  The disequality bit is @($1 - out$)."
  (pfcs::parse-def
   "crv_group_is_not_equal(x1, y1, x2, y2, mx, rx, my, ry, out) := {
    (x1 - x2) * (mx) == (rx),
    (x1 - x2) * (1 - rx) == (0),
    (y1 - y2) * (my) == (ry),
    (y1 - y2) * (1 - ry) == (0),
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-group-is-not-equal-circuit)
            :pred crv-group-is-not-equal-pred
            :prime prime)

(defruled crv-group-is-not-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (bitp rx) (bitp ry) (bitp out)
                (pfield::fep mx prime) (pfield::fep my prime)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-group-is-not-equal-pred
                 x1 y1 x2 y2 mx rx my ry out prime))
           (equal (pfield::sub 1 out prime)
                  (group-is-not-equal-funspec p1 p2)))
  :enable (crv-group-is-not-equal-pred
           crv-group-is-equal-pred
           crv-group-is-equal-pred-sound
           group-is-not-equal-funspec
           group-is-equal-funspec
           crv-not-of-equal-bit))

(defruled crv-group-is-not-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (if (equal x1 x2) 0 1))
                (equal mx (if (equal x1 x2)
                              0
                            (pfield::inv (pfield::sub x1 x2 prime) prime)))
                (equal ry (if (equal y1 y2) 0 1))
                (equal my (if (equal y1 y2)
                              0
                            (pfield::inv (pfield::sub y1 y2 prime) prime)))
                (equal out (group-is-equal-funspec p1 p2)))
           (and (crv-group-is-not-equal-pred
                 x1 y1 x2 y2 mx rx my ry out prime)
                (equal (pfield::sub 1 out prime)
                       (group-is-not-equal-funspec p1 p2))))
  :enable (crv-group-is-not-equal-pred
           crv-group-is-equal-pred
           crv-group-is-equal-pred-complete
           group-is-not-equal-funspec
           group-is-equal-funspec
           crv-not-of-equal-bit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-is-equal-gadget ((a symbolp) (b symbolp)
                                    (m symbolp) (r symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Scalar::is_equal'): field is_equal on the embedding."
  (crv-field-is-not-equal-gadget a b m r p))

(defruled crv-scalar-is-equal-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-equal-gadget a b m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (scalar-is-equal-funspec (lookup-equal a asg)
                                           (lookup-equal b asg))))
  :enable (crv-scalar-is-equal-gadget
           crv-field-is-not-equal-gadget-sound
           crv-fieldp-when-scalarp
           scalar-is-equal-funspec
           field-is-equal-funspec))

(defruled crv-scalar-is-equal-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal a asg) (lookup-equal b asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal a asg) (lookup-equal b asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal a asg)
                                                   (lookup-equal b asg) p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-equal-gadget a b m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (scalar-is-equal-funspec (lookup-equal a asg)
                                                (lookup-equal b asg)))))
  :enable (crv-scalar-is-equal-gadget
           crv-field-is-not-equal-gadget-complete
           crv-fieldp-when-scalarp
           scalar-is-equal-funspec
           field-is-equal-funspec))

(defconst *crv-scalar-is-equal-sample*
  '((a . 1) (b . 1) (m . 0) (r . 0)))

(defruled crv-scalar-is-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-scalar-is-equal-sample* p)
                (r1cs::valuation-bindsp *crv-scalar-is-equal-sample* 'a)
                (r1cs::valuation-bindsp *crv-scalar-is-equal-sample* 'b)
                (r1cs::valuation-bindsp *crv-scalar-is-equal-sample* 'm)
                (r1cs::valuation-bindsp *crv-scalar-is-equal-sample* 'r)
                (scalarp (lookup-equal 'a *crv-scalar-is-equal-sample*))
                (scalarp (lookup-equal 'b *crv-scalar-is-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-is-equal-gadget 'a 'b 'm 'r p)
            *crv-scalar-is-equal-sample* p))
  :enable (crv-scalar-is-equal-gadget-complete lookup-equal))

(define crv-scalar-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_scalar_is_equal(a, b, m, r) := {
    (a - b) * (m) == (r),
    (a - b) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-scalar-is-equal-circuit)
            :pred crv-scalar-is-equal-pred
            :prime prime)

(defruled crv-scalar-is-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (scalarp a) (scalarp b) (bitp r)
                (pfield::fep m prime)
                (crv-scalar-is-equal-pred a b m r prime))
           (equal (pfield::sub 1 r prime)
                  (scalar-is-equal-funspec a b)))
  :enable (crv-scalar-is-equal-pred
           crv-field-is-not-equal-pred
           crv-field-is-not-equal-pred-sound
           crv-fieldp-when-scalarp
           scalar-is-equal-funspec
           field-is-equal-funspec))

(defruled crv-scalar-is-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (scalarp a) (scalarp b)
                (equal r (if (equal a b) 0 1))
                (equal m (if (equal a b)
                             0
                           (pfield::inv (pfield::sub a b prime) prime))))
           (and (crv-scalar-is-equal-pred a b m r prime)
                (equal (pfield::sub 1 r prime)
                       (scalar-is-equal-funspec a b))))
  :enable (crv-scalar-is-equal-pred
           crv-field-is-not-equal-pred
           crv-field-is-not-equal-pred-complete
           crv-fieldp-when-scalarp
           scalar-is-equal-funspec
           field-is-equal-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-is-not-equal-gadget ((a symbolp) (b symbolp)
                                        (m symbolp) (r symbolp)
                                        (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-scalar-is-equal-gadget a b m r p))

(defruled crv-scalar-is-not-equal-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-not-equal-gadget a b m r p) asg p))
           (equal (lookup-equal r asg)
                  (scalar-is-not-equal-funspec (lookup-equal a asg)
                                               (lookup-equal b asg))))
  :enable (crv-scalar-is-not-equal-gadget
           crv-scalar-is-equal-gadget-sound
           scalar-is-not-equal-funspec
           scalar-is-equal-funspec
           boolean-not-funspec
           crv-not-of-equal-bit))

(defruled crv-scalar-is-not-equal-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal a asg) (lookup-equal b asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal a asg) (lookup-equal b asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal a asg)
                                                   (lookup-equal b asg) p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-not-equal-gadget a b m r p) asg p)
                (equal (lookup-equal r asg)
                       (scalar-is-not-equal-funspec (lookup-equal a asg)
                                                    (lookup-equal b asg)))))
  :enable (crv-scalar-is-not-equal-gadget
           crv-scalar-is-equal-gadget-complete
           scalar-is-not-equal-funspec
           scalar-is-equal-funspec
           boolean-not-funspec
           crv-not-of-equal-bit))

(defconst *crv-scalar-is-not-equal-sample*
  '((a . 1) (b . 1) (m . 0) (r . 0)))

(defruled crv-scalar-is-not-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-scalar-is-not-equal-sample* p)
                (r1cs::valuation-bindsp *crv-scalar-is-not-equal-sample* 'a)
                (r1cs::valuation-bindsp *crv-scalar-is-not-equal-sample* 'b)
                (r1cs::valuation-bindsp *crv-scalar-is-not-equal-sample* 'm)
                (r1cs::valuation-bindsp *crv-scalar-is-not-equal-sample* 'r)
                (scalarp (lookup-equal 'a *crv-scalar-is-not-equal-sample*))
                (scalarp (lookup-equal 'b *crv-scalar-is-not-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-is-not-equal-gadget 'a 'b 'm 'r p)
            *crv-scalar-is-not-equal-sample* p))
  :enable (crv-scalar-is-not-equal-gadget
           crv-scalar-is-equal-sample-holds))

(define crv-scalar-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_scalar_is_not_equal(a, b, m, r) := {
    (a - b) * (m) == (r),
    (a - b) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-scalar-is-not-equal-circuit)
            :pred crv-scalar-is-not-equal-pred
            :prime prime)

(defruled crv-scalar-is-not-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (scalarp a) (scalarp b) (bitp r)
                (pfield::fep m prime)
                (crv-scalar-is-not-equal-pred a b m r prime))
           (equal r (scalar-is-not-equal-funspec a b)))
  :enable (crv-scalar-is-not-equal-pred
           crv-scalar-is-equal-pred
           crv-scalar-is-equal-pred-sound
           scalar-is-not-equal-funspec
           scalar-is-equal-funspec
           boolean-not-funspec
           crv-not-of-equal-bit))

(defruled crv-scalar-is-not-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (scalarp a) (scalarp b)
                (equal r (if (equal a b) 0 1))
                (equal m (if (equal a b)
                             0
                           (pfield::inv (pfield::sub a b prime) prime))))
           (and (crv-scalar-is-not-equal-pred a b m r prime)
                (equal r (scalar-is-not-equal-funspec a b))))
  :enable (crv-scalar-is-not-equal-pred
           crv-scalar-is-equal-pred
           crv-scalar-is-equal-pred-complete
           scalar-is-not-equal-funspec
           scalar-is-equal-funspec
           boolean-not-funspec
           crv-not-of-equal-bit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-is-zero-gadget ((a symbolp) (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('Scalar::is_zero') is @('is_equal') against the constant 0."
  (field-is-zero-gadget a m r p))

(defruled crv-scalar-is-zero-gadget-sound
  (implies (and (symbolp a) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-zero-gadget a m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (scalar-is-zero-funspec (lookup-equal a asg))))
  :enable (crv-scalar-is-zero-gadget
           field-is-zero-gadget-sound
           crv-fieldp-when-scalarp
           scalar-is-zero-funspec
           scalar-is-equal-funspec
           field-is-zero-funspec
           field-is-equal-funspec))

(defruled crv-scalar-is-zero-gadget-complete
  (implies (and (symbolp a) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal a asg) 0) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal a asg) 0)
                           0
                         (pfield::inv (lookup-equal a asg) p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-zero-gadget a m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (scalar-is-zero-funspec (lookup-equal a asg)))))
  :enable (crv-scalar-is-zero-gadget
           field-is-zero-gadget-complete
           crv-fieldp-when-scalarp
           scalar-is-zero-funspec
           scalar-is-equal-funspec
           field-is-zero-funspec
           field-is-equal-funspec))

(defconst *crv-scalar-is-zero-sample*
  '((a . 0) (m . 0) (r . 0)))

(defruled crv-scalar-is-zero-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-scalar-is-zero-sample* p)
                (r1cs::valuation-bindsp *crv-scalar-is-zero-sample* 'a)
                (r1cs::valuation-bindsp *crv-scalar-is-zero-sample* 'm)
                (r1cs::valuation-bindsp *crv-scalar-is-zero-sample* 'r)
                (scalarp (lookup-equal 'a *crv-scalar-is-zero-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-is-zero-gadget 'a 'm 'r p)
            *crv-scalar-is-zero-sample* p))
  :enable (crv-scalar-is-zero-gadget-complete lookup-equal))

(define crv-scalar-is-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_scalar_is_zero(a, m, r) := {
    (a) * (m) == (r),
    (a) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-scalar-is-zero-circuit)
            :pred crv-scalar-is-zero-pred
            :prime prime)

(defruled crv-scalar-is-zero-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep a prime)
                (pfield::fep m prime)
                (pfield::fep r prime))
           (equal (crv-scalar-is-zero-pred a m r prime)
                  (and (equal (pfield::mul a m prime) r)
                       (equal (pfield::mul a (pfield::sub 1 r prime) prime)
                              0))))
  :enable crv-scalar-is-zero-pred)

(defruled crv-scalar-is-zero-pred-sound
  (implies (and (equal prime (base-prime))
                (scalarp a) (bitp r) (pfield::fep m prime)
                (crv-scalar-is-zero-pred a m r prime))
           (equal (pfield::sub 1 r prime) (scalar-is-zero-funspec a)))
  :enable (crv-scalar-is-zero-pred-to-mul
           crv-field-is-not-equal-when-constraints
           crv-fieldp-when-scalarp
           scalar-is-zero-funspec
           scalar-is-equal-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           fieldp))

(defruled crv-scalar-is-zero-pred-complete
  (implies (and (equal prime (base-prime))
                (scalarp a)
                (equal r (if (equal a 0) 0 1))
                (equal m (if (equal a 0) 0 (pfield::inv a prime))))
           (and (crv-scalar-is-zero-pred a m r prime)
                (equal (pfield::sub 1 r prime) (scalar-is-zero-funspec a))))
  :enable (crv-scalar-is-zero-pred-to-mul
           crv-field-is-not-equal-constraints-when-witness
           crv-fieldp-when-scalarp
           scalar-is-zero-funspec
           scalar-is-equal-funspec
           field-is-equal-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-is-one-gadget ((a symbolp) (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-is-one-gadget a m r p))

(defruled crv-scalar-is-one-gadget-sound
  (implies (and (symbolp a) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-one-gadget a m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (scalar-is-one-funspec (lookup-equal a asg))))
  :enable (crv-scalar-is-one-gadget
           field-is-one-gadget-sound
           crv-fieldp-when-scalarp
           scalar-is-one-funspec
           scalar-is-equal-funspec
           field-is-one-funspec
           field-is-equal-funspec))

(defruled crv-scalar-is-one-gadget-complete
  (implies (and (symbolp a) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal a asg) 1) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal a asg) 1)
                           0
                         (pfield::inv (pfield::sub (lookup-equal a asg) 1 p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-one-gadget a m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (scalar-is-one-funspec (lookup-equal a asg)))))
  :enable (crv-scalar-is-one-gadget
           field-is-one-gadget-complete
           crv-fieldp-when-scalarp
           scalar-is-one-funspec
           scalar-is-equal-funspec
           field-is-one-funspec
           field-is-equal-funspec))

(defconst *crv-scalar-is-one-sample*
  '((a . 1) (m . 0) (r . 0)))

(defruled crv-scalar-is-one-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-scalar-is-one-sample* p)
                (r1cs::valuation-bindsp *crv-scalar-is-one-sample* 'a)
                (r1cs::valuation-bindsp *crv-scalar-is-one-sample* 'm)
                (r1cs::valuation-bindsp *crv-scalar-is-one-sample* 'r)
                (scalarp (lookup-equal 'a *crv-scalar-is-one-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-scalar-is-one-gadget 'a 'm 'r p)
            *crv-scalar-is-one-sample* p))
  :enable (crv-scalar-is-one-gadget-complete lookup-equal))

(define crv-scalar-is-one-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_scalar_is_one(a, m, r) := {
    (a - 1) * (m) == (r),
    (a - 1) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-scalar-is-one-circuit)
            :pred crv-scalar-is-one-pred
            :prime prime)

(defruled crv-scalar-is-one-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep a prime)
                (pfield::fep m prime)
                (pfield::fep r prime))
           (equal (crv-scalar-is-one-pred a m r prime)
                  (and (equal (pfield::mul (pfield::sub a 1 prime) m prime) r)
                       (equal (pfield::mul (pfield::sub a 1 prime)
                                           (pfield::sub 1 r prime)
                                           prime)
                              0))))
  :enable crv-scalar-is-one-pred)

(defruled crv-scalar-is-one-pred-sound
  (implies (and (equal prime (base-prime))
                (scalarp a) (bitp r) (pfield::fep m prime)
                (crv-scalar-is-one-pred a m r prime))
           (equal (pfield::sub 1 r prime) (scalar-is-one-funspec a)))
  :enable (crv-scalar-is-one-pred-to-mul
           crv-field-is-not-equal-when-constraints
           crv-fieldp-when-scalarp
           scalar-is-one-funspec
           scalar-is-equal-funspec
           field-is-equal-funspec
           fieldp))

(defruled crv-scalar-is-one-pred-complete
  (implies (and (equal prime (base-prime))
                (scalarp a)
                (equal r (if (equal a 1) 0 1))
                (equal m (if (equal a 1)
                             0
                           (pfield::inv (pfield::sub a 1 prime) prime))))
           (and (crv-scalar-is-one-pred a m r prime)
                (equal (pfield::sub 1 r prime) (scalar-is-one-funspec a))))
  :enable (crv-scalar-is-one-pred-to-mul
           crv-field-is-not-equal-constraints-when-witness
           crv-fieldp-when-scalarp
           scalar-is-one-funspec
           scalar-is-equal-funspec
           field-is-equal-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::is_zero is is_equal(x, 0) and is_equal(y, 1).  The constants are
; inlined, so the constraints are Field::is_zero, Field::is_one, and the and.

(define crv-group-is-zero-gadget ((x symbolp) (y symbolp)
                                  (mx symbolp) (rx symbolp)
                                  (my symbolp) (ry symbolp)
                                  (out symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (field-is-zero-gadget x mx rx p)
          (field-is-one-gadget y my ry p)
          (crv-and-not-gadget rx ry out p)))

(defruled crv-group-is-zero-gadget-sound
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
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-zero-gadget x y mx rx my ry out p) asg p))
           (equal (lookup-equal out asg)
                  (group-is-zero-funspec p0)))
  :hints (("Goal"
           :in-theory (e/d (crv-group-is-zero-gadget
                            crv-and-not-gadget-to-mul
                            crv-and-not-is-and-of-equals
                            group-is-zero-funspec
                            ecurve::twisted-edwards-zero
                            field-is-zero-funspec
                            field-is-one-funspec
                            field-is-equal-funspec
                            boolean-and-funspec
                            boolean-not-funspec
                            crv-group-points-equal-iff-coordinates)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance field-is-zero-gadget-sound (x x) (m mx) (r rx))
                 (:instance field-is-one-gadget-sound (x y) (m my) (r ry))))))

(defruled crv-group-is-zero-gadget-complete
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
                (equal (lookup-equal rx asg)
                       (if (equal (lookup-equal x asg) 0) 0 1))
                (equal (lookup-equal mx asg)
                       (if (equal (lookup-equal x asg) 0)
                           0
                         (pfield::inv (lookup-equal x asg) p)))
                (equal (lookup-equal ry asg)
                       (if (equal (lookup-equal y asg) 1) 0 1))
                (equal (lookup-equal my asg)
                       (if (equal (lookup-equal y asg) 1)
                           0
                         (pfield::inv (pfield::sub (lookup-equal y asg) 1 p)
                                      p)))
                (equal (lookup-equal out asg) (group-is-zero-funspec p0)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-zero-gadget x y mx rx my ry out p) asg p))
  :hints (("Goal"
           :in-theory (e/d (crv-group-is-zero-gadget
                            crv-and-not-gadget-to-mul
                            group-is-zero-funspec
                            ecurve::twisted-edwards-zero
                            field-is-zero-funspec
                            field-is-one-funspec
                            field-is-equal-funspec
                            boolean-and-funspec
                            boolean-not-funspec
                            crv-group-points-equal-iff-coordinates)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance field-is-zero-gadget-complete
                            (x x) (m mx) (r rx))
                 (:instance field-is-one-gadget-complete
                            (x y) (m my) (r ry))))))

(defconst *crv-group-is-zero-sample*
  '((x . 0) (y . 1) (mx . 0) (rx . 0) (my . 0) (ry . 0) (out . 1)))

(defruled crv-group-is-zero-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-group-is-zero-sample* p)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'x)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'y)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'mx)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'rx)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'my)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'ry)
                (r1cs::valuation-bindsp *crv-group-is-zero-sample* 'out)
                (fieldp (lookup-equal 'x *crv-group-is-zero-sample*))
                (fieldp (lookup-equal 'y *crv-group-is-zero-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-zero-gadget 'x 'y 'mx 'rx 'my 'ry 'out p)
            *crv-group-is-zero-sample* p))
  :enable (crv-group-is-zero-gadget
           field-is-zero-gadget-complete
           field-is-one-gadget-complete
           crv-and-not-gadget-to-mul
           lookup-equal)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

(define crv-group-is-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_group_is_zero(x, y, mx, rx, my, ry, out) := {
    (x) * (mx) == (rx),
    (x) * (1 - rx) == (0),
    (y - 1) * (my) == (ry),
    (y - 1) * (1 - ry) == (0),
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-group-is-zero-circuit)
            :pred crv-group-is-zero-pred
            :prime prime)

(defruled crv-group-is-zero-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x) (fieldp y)
                (bitp rx) (bitp ry)
                (pfield::fep mx prime) (pfield::fep my prime)
                (pfield::fep out prime)
                (ecurve::edwards-bls12-pointp p0)
                (equal x (ecurve::point-finite->x p0))
                (equal y (ecurve::point-finite->y p0))
                (crv-group-is-zero-pred x y mx rx my ry out prime))
           (equal out (group-is-zero-funspec p0)))
  :enable (crv-group-is-zero-pred
           crv-field-is-not-equal-pred-to-mul
           crv-scalar-is-zero-pred-to-mul
           crv-scalar-is-one-pred-to-mul
           crv-and-not-pred-to-mul
           crv-field-is-not-equal-when-constraints
           crv-and-not-is-and-of-equals
           group-is-zero-funspec
           ecurve::twisted-edwards-zero
           field-is-zero-funspec
           field-is-one-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-and-funspec
           boolean-not-funspec
           crv-group-points-equal-iff-coordinates
           fieldp)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

(defruled crv-group-is-zero-pred-complete
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p0)
                (equal x (ecurve::point-finite->x p0))
                (equal y (ecurve::point-finite->y p0))
                (equal rx (if (equal x 0) 0 1))
                (equal mx (if (equal x 0) 0 (pfield::inv x prime)))
                (equal ry (if (equal y 1) 0 1))
                (equal my (if (equal y 1)
                              0
                            (pfield::inv (pfield::sub y 1 prime) prime)))
                (equal out (group-is-zero-funspec p0)))
           (crv-group-is-zero-pred x y mx rx my ry out prime))
  :enable (crv-group-is-zero-pred
           crv-scalar-is-zero-pred-to-mul
           crv-scalar-is-one-pred-to-mul
           crv-and-not-pred-to-mul
           crv-field-is-not-equal-constraints-when-witness
           group-is-zero-funspec
           ecurve::twisted-edwards-zero
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-and-funspec
           boolean-not-funspec
           crv-group-points-equal-iff-coordinates
           curve-coordinatesp-when-edwards-bls12-pointp
           fieldp)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-address-is-equal-gadget ((x1 symbolp) (y1 symbolp)
                                     (x2 symbolp) (y2 symbolp)
                                     (mx symbolp) (rx symbolp)
                                     (my symbolp) (ry symbolp)
                                     (out symbolp)
                                     (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('Address::is_equal') is @('Group::is_equal') on the inner point."
  (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p))

(defruled crv-address-is-equal-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (address-is-equal-funspec p1 p2)))
  :enable (crv-address-is-equal-gadget
           address-is-equal-funspec
           crv-group-is-equal-gadget-sound))

(defruled crv-address-is-equal-gadget-complete
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (equal (lookup-equal rx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal mx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal ry asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal my asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal out asg) (address-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
            asg p))
  :enable (crv-address-is-equal-gadget
           address-is-equal-funspec
           group-is-equal-funspec
           crv-group-is-equal-gadget-complete))

(defconst *crv-address-is-equal-sample* *crv-group-is-equal-sample*)

(defruled crv-address-is-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-address-is-equal-sample* p)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'x1)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'y1)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'x2)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'y2)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'mx)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'rx)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'my)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'ry)
                (r1cs::valuation-bindsp *crv-address-is-equal-sample* 'out)
                (fieldp (lookup-equal 'x1 *crv-address-is-equal-sample*))
                (fieldp (lookup-equal 'y1 *crv-address-is-equal-sample*))
                (fieldp (lookup-equal 'x2 *crv-address-is-equal-sample*))
                (fieldp (lookup-equal 'y2 *crv-address-is-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-equal-gadget
             'x1 'y1 'x2 'y2 'mx 'rx 'my 'ry 'out p)
            *crv-address-is-equal-sample* p))
  :enable (crv-address-is-equal-gadget crv-group-is-equal-sample-holds))

(define crv-address-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_address_is_equal(x1, y1, x2, y2, mx, rx, my, ry, out) := {
    (x1 - x2) * (mx) == (rx),
    (x1 - x2) * (1 - rx) == (0),
    (y1 - y2) * (my) == (ry),
    (y1 - y2) * (1 - ry) == (0),
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-address-is-equal-circuit)
            :pred crv-address-is-equal-pred
            :prime prime)

(defruled crv-address-is-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (bitp rx) (bitp ry)
                (pfield::fep mx prime) (pfield::fep my prime)
                (pfield::fep out prime)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-address-is-equal-pred x1 y1 x2 y2 mx rx my ry out prime))
           (equal out (address-is-equal-funspec p1 p2)))
  :enable (crv-address-is-equal-pred
           crv-group-is-equal-pred
           crv-group-is-equal-pred-sound
           address-is-equal-funspec))

(defruled crv-address-is-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (if (equal x1 x2) 0 1))
                (equal mx (if (equal x1 x2)
                              0
                            (pfield::inv (pfield::sub x1 x2 prime) prime)))
                (equal ry (if (equal y1 y2) 0 1))
                (equal my (if (equal y1 y2)
                              0
                            (pfield::inv (pfield::sub y1 y2 prime) prime)))
                (equal out (address-is-equal-funspec p1 p2)))
           (crv-address-is-equal-pred x1 y1 x2 y2 mx rx my ry out prime))
  :enable (crv-address-is-equal-pred
           crv-group-is-equal-pred
           crv-group-is-equal-pred-complete
           address-is-equal-funspec
           group-is-equal-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-address-is-not-equal-gadget ((x1 symbolp) (y1 symbolp)
                                         (x2 symbolp) (y2 symbolp)
                                         (mx symbolp) (rx symbolp)
                                         (my symbolp) (ry symbolp)
                                         (out symbolp)
                                         (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p))

(defruled crv-address-is-not-equal-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (bitp (lookup-equal out asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-not-equal-gadget
                  x1 y1 x2 y2 mx rx my ry out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (address-is-not-equal-funspec p1 p2)))
  :enable (crv-address-is-not-equal-gadget
           crv-group-is-not-equal-gadget
           crv-group-is-not-equal-gadget-sound
           address-is-not-equal-funspec
           group-is-not-equal-funspec))

(defruled crv-address-is-not-equal-gadget-complete
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
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
                (equal (lookup-equal rx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal mx asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal ry asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal my asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal out asg) (group-is-equal-funspec p1 p2)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-address-is-not-equal-gadget
                  x1 y1 x2 y2 mx rx my ry out p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal out asg) p)
                       (address-is-not-equal-funspec p1 p2))))
  :enable (crv-address-is-not-equal-gadget
           crv-group-is-not-equal-gadget-complete
           address-is-not-equal-funspec
           group-is-not-equal-funspec))

(defconst *crv-address-is-not-equal-sample* *crv-group-is-equal-sample*)

(defruled crv-address-is-not-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-address-is-not-equal-sample* p)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'x1)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'y1)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'x2)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'y2)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'mx)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'rx)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'my)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'ry)
                (r1cs::valuation-bindsp *crv-address-is-not-equal-sample* 'out)
                (fieldp (lookup-equal 'x1 *crv-address-is-not-equal-sample*))
                (fieldp (lookup-equal 'y1 *crv-address-is-not-equal-sample*))
                (fieldp (lookup-equal 'x2 *crv-address-is-not-equal-sample*))
                (fieldp (lookup-equal 'y2 *crv-address-is-not-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-not-equal-gadget
             'x1 'y1 'x2 'y2 'mx 'rx 'my 'ry 'out p)
            *crv-address-is-not-equal-sample* p))
  :enable (crv-address-is-not-equal-gadget
           crv-group-is-not-equal-sample-holds))

(define crv-address-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_address_is_not_equal(x1, y1, x2, y2, mx, rx, my, ry, out) := {
    (x1 - x2) * (mx) == (rx),
    (x1 - x2) * (1 - rx) == (0),
    (y1 - y2) * (my) == (ry),
    (y1 - y2) * (1 - ry) == (0),
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-address-is-not-equal-circuit)
            :pred crv-address-is-not-equal-pred
            :prime prime)

(defruled crv-address-is-not-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x1) (fieldp y1) (fieldp x2) (fieldp y2)
                (bitp rx) (bitp ry) (bitp out)
                (pfield::fep mx prime) (pfield::fep my prime)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (crv-address-is-not-equal-pred
                 x1 y1 x2 y2 mx rx my ry out prime))
           (equal (pfield::sub 1 out prime)
                  (address-is-not-equal-funspec p1 p2)))
  :enable (crv-address-is-not-equal-pred
           crv-group-is-not-equal-pred
           crv-group-is-not-equal-pred-sound
           address-is-not-equal-funspec
           group-is-not-equal-funspec))

(defruled crv-address-is-not-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (equal rx (if (equal x1 x2) 0 1))
                (equal mx (if (equal x1 x2)
                              0
                            (pfield::inv (pfield::sub x1 x2 prime) prime)))
                (equal ry (if (equal y1 y2) 0 1))
                (equal my (if (equal y1 y2)
                              0
                            (pfield::inv (pfield::sub y1 y2 prime) prime)))
                (equal out (group-is-equal-funspec p1 p2)))
           (and (crv-address-is-not-equal-pred
                 x1 y1 x2 y2 mx rx my ry out prime)
                (equal (pfield::sub 1 out prime)
                       (address-is-not-equal-funspec p1 p2))))
  :enable (crv-address-is-not-equal-pred
           crv-group-is-not-equal-pred
           crv-group-is-not-equal-pred-complete
           address-is-not-equal-funspec
           group-is-not-equal-funspec))
