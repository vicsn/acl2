; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS for snarkVM Group::new / enforce_in_group (private or public mode).
;
; Field::new of the two coordinates emits nothing.  enforce_in_group then
; allocates a private cofactor witness Q = (qx, qy) and emits:
;
;   square(qx), square(qy),
;   enforce_on_curve(Q):  y2 * (d*x2 - 1) = (a*x2 - 1)
;     with a = -1 and d = 3021 on Edwards-BLS12,
;   double(Q): three products xy, x2, y2 and the two doubling enforces
;     x3 * (a*x2 + y2) = 2*xy
;     y3 * (2 - (a*x2 + y2)) = y2 - a*x2,
;   enforce_double of that double against the input point, same two
;     enforces, with the three products recomputed on the double.
;
; Constant mode host-checks the same predicates and emits nothing; this
; gadget is the variable-mode constraint list.  a is the coefficient
; (1- p) = p-1.  Addition and scaling by the constant a are linear
; combinations, so they are not extra constraints.
;
; The equations are proved equivalent to the gadget.  Existence of Q for
; every subgroup point, and agreement of the doubling formulas with
; edwards-bls12-add, are not proved here (see fun-specs/README.md).

(in-package "ALEOVM")

(include-book "../fun-specs/curve-group")
(include-book "environment-r1cs")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable (:e base-prime) (:e scalar-prime)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled group-inject-coeff-neg-one
  (implies (equal p (base-prime))
           (and (equal (mod (1- p) p) (pfield::neg 1 p))
                (equal (ecurve::edwards-bls12-a) (pfield::neg 1 p))
                (equal (ecurve::edwards-bls12-d) 3021)
                (< 3021 p)))
  :hints (("Goal"
           :in-theory (enable (:e base-prime)
                              (:e <)
                              (:e ecurve::edwards-bls12-q)
                              pfield::neg
                              ecurve::edwards-bls12-a
                              ecurve::edwards-bls12-d
                              curve-base-prime-is-edwards-bls12-q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; y2 * (d*x2 - 1) = (a*x2 - 1)

(define group-on-curve-gadget ((y2 symbolp) (x2 symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single constraint of @('Group::enforce_on_curve')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 y2))
         :b (list (list (ecurve::edwards-bls12-d) x2)
                  (list (1- p) 1))
         :c (list (list (1- p) x2)
                  (list (1- p) 1)))))

(define group-on-curve-equation ((y2 integerp) (x2 integerp) (p primep))
  :returns (yes/no booleanp)
  :verify-guards nil
  (equal (pfield::mul y2
                      (pfield::add (pfield::mul (ecurve::edwards-bls12-d) x2 p)
                                   (pfield::neg 1 p)
                                   p)
                      p)
         (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                      (pfield::neg 1 p)
                      p)))

(defruled group-on-curve-gadget-to-equation
  (implies (and (symbolp y2)
                (symbolp x2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg x2))
           (equal (r1cs::r1cs-constraints-holdp
                   (group-on-curve-gadget y2 x2 p) asg p)
                  (group-on-curve-equation (lookup-equal y2 asg)
                                           (lookup-equal x2 asg)
                                           p)))
  :hints (("Goal"
           :in-theory (e/d (group-on-curve-gadget
                            group-on-curve-equation
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            group-inject-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            (:definition pfield::sub))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; x3 * (a*x2 + y2) = 2*xy

(define group-double-x-gadget ((x3 symbolp)
                               (x2 symbolp)
                               (y2 symbolp)
                               (xy symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x3))
         :b (list (list (1- p) x2)
                  (list 1 y2))
         :c (list (list 2 xy)))))

(define group-double-x-equation ((x3 integerp)
                                 (x2 integerp)
                                 (y2 integerp)
                                 (xy integerp)
                                 (p primep))
  :returns (yes/no booleanp)
  :verify-guards nil
  (equal (pfield::mul x3
                      (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                   y2
                                   p)
                      p)
         (pfield::mul 2 xy p)))

(defruled group-double-x-gadget-to-equation
  (implies (and (symbolp x3) (symbolp x2) (symbolp y2) (symbolp xy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg xy))
           (equal (r1cs::r1cs-constraints-holdp
                   (group-double-x-gadget x3 x2 y2 xy p) asg p)
                  (group-double-x-equation (lookup-equal x3 asg)
                                           (lookup-equal x2 asg)
                                           (lookup-equal y2 asg)
                                           (lookup-equal xy asg)
                                           p)))
  :hints (("Goal"
           :in-theory (e/d (group-double-x-gadget
                            group-double-x-equation
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            group-inject-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            (:definition pfield::sub))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; y3 * (2 - (a*x2 + y2)) = y2 - a*x2
; With a = -1 this is y3 * (2 + x2 - y2) = y2 + x2.

(define group-double-y-gadget ((y3 symbolp)
                               (x2 symbolp)
                               (y2 symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 y3))
         :b (list (list 2 1)
                  (list 1 x2)
                  (list (1- p) y2))
         :c (list (list 1 y2)
                  (list 1 x2)))))

(define group-double-y-equation ((y3 integerp)
                                 (x2 integerp)
                                 (y2 integerp)
                                 (p primep))
  :returns (yes/no booleanp)
  :verify-guards nil
  (equal (pfield::mul y3
                      (pfield::sub 2
                                   (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                                y2
                                                p)
                                   p)
                      p)
         (pfield::sub y2
                      (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                      p)))

(defruled group-double-y-gadget-to-equation
  (implies (and (symbolp y3) (symbolp x2) (symbolp y2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2))
           (equal (r1cs::r1cs-constraints-holdp
                   (group-double-y-gadget y3 x2 y2 p) asg p)
                  (group-double-y-equation (lookup-equal y3 asg)
                                           (lookup-equal x2 asg)
                                           (lookup-equal y2 asg)
                                           p)))
  :hints (("Goal"
           :in-theory (e/d (group-double-y-gadget
                            group-double-y-equation
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            group-inject-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Products are ordinary field multiplications.  enforce-gadget is (a)*(b)=(c).

(define group-enforce-in-group-gadget ((x symbolp) (y symbolp)
                                       (qx symbolp) (qy symbolp)
                                       (cx2 symbolp) (cy2 symbolp)
                                       (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                       (x3 symbolp) (y3 symbolp)
                                       (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                       (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Variable-mode constraints of @('Group::new') / @('enforce_in_group')."
  (append (enforce-gadget qx qx cx2)
          (enforce-gadget qy qy cy2)
          (group-on-curve-gadget cy2 cx2 p)
          (enforce-gadget qx qy dxy)
          (enforce-gadget qx qx dx2)
          (enforce-gadget qy qy dy2)
          (group-double-x-gadget x3 dx2 dy2 dxy p)
          (group-double-y-gadget y3 dx2 dy2 p)
          (enforce-gadget x3 y3 exy)
          (enforce-gadget x3 x3 ex2)
          (enforce-gadget y3 y3 ey2)
          (group-double-x-gadget x ex2 ey2 exy p)
          (group-double-y-gadget y ex2 ey2 p)))

(define group-enforce-in-group-equations
  ((x integerp) (y integerp)
   (qx integerp) (qy integerp)
   (cx2 integerp) (cy2 integerp)
   (dxy integerp) (dx2 integerp) (dy2 integerp)
   (x3 integerp) (y3 integerp)
   (exy integerp) (ex2 integerp) (ey2 integerp)
   (p primep))
  :returns (yes/no booleanp)
  :verify-guards nil
  (and (equal (pfield::mul qx qx p) cx2)
       (equal (pfield::mul qy qy p) cy2)
       (group-on-curve-equation cy2 cx2 p)
       (equal (pfield::mul qx qy p) dxy)
       (equal (pfield::mul qx qx p) dx2)
       (equal (pfield::mul qy qy p) dy2)
       (group-double-x-equation x3 dx2 dy2 dxy p)
       (group-double-y-equation y3 dx2 dy2 p)
       (equal (pfield::mul x3 y3 p) exy)
       (equal (pfield::mul x3 x3 p) ex2)
       (equal (pfield::mul y3 y3 p) ey2)
       (group-double-x-equation x ex2 ey2 exy p)
       (group-double-y-equation y ex2 ey2 p)))

(defruled group-enforce-in-group-gadget-to-equations
  :short "R1CS-SPEC of @('enforce_in_group'): the gadget holds iff the
          snarkVM field equations hold of the wires."
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
                (r1cs::valuation-bindsp asg ey2))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (qx$ (lookup-equal qx asg))
                (qy$ (lookup-equal qy asg))
                (cx2$ (lookup-equal cx2 asg))
                (cy2$ (lookup-equal cy2 asg))
                (dxy$ (lookup-equal dxy asg))
                (dx2$ (lookup-equal dx2 asg))
                (dy2$ (lookup-equal dy2 asg))
                (x3$ (lookup-equal x3 asg))
                (y3$ (lookup-equal y3 asg))
                (exy$ (lookup-equal exy asg))
                (ex2$ (lookup-equal ex2 asg))
                (ey2$ (lookup-equal ey2 asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (group-enforce-in-group-gadget
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                     asg p)
                    (group-enforce-in-group-equations
                     x$ y$ qx$ qy$ cx2$ cy2$ dxy$ dx2$ dy2$
                     x3$ y3$ exy$ ex2$ ey2$ p))))
  :hints (("Goal"
           :in-theory (e/d (group-enforce-in-group-gadget
                            group-enforce-in-group-equations
                            group-on-curve-gadget-to-equation
                            group-double-x-gadget-to-equation
                            group-double-y-gadget-to-equation
                            enforce-gadget-to-mul)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            (:definition pfield::sub))))))
