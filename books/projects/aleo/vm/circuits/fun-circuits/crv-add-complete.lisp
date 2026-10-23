; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness of variable/variable Group::add.
;
; The canonical witnesses are u = (x1 + y1)(x2 + y2), v0 = x1 y2,
; v1 = x2 y1, v01 = v0 v1, and (x3, y3) = edwards-bls12-add of the two
; points.  The two division enforces hold because x3 and y3 are the
; numerators divided by 1 + d v01 and 1 - d v01, which are non-zero on a
; complete curve (1+d.x1.x2.y1.y2-not-0 and 1-d.x1.x2.y1.y2-not-0).

(in-package "ALEOVM")

(include-book "crv-curve")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl crv-add-q-is-base-prime
  (equal (ecurve::edwards-bls12-q) (base-prime))
  :in-theory '((:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruledl crv-add-primep-base-prime
  (primep (base-prime))
  :in-theory '(primep-of-base-prime))

(defruledl crv-add-curve-fields
  (and (equal (ecurve::twisted-edwards-curve->p (ecurve::edwards-bls12-curve))
              (base-prime))
       (equal (ecurve::twisted-edwards-curve->a (ecurve::edwards-bls12-curve))
              (ecurve::edwards-bls12-a))
       (equal (ecurve::twisted-edwards-curve->d (ecurve::edwards-bls12-curve))
              (ecurve::edwards-bls12-d)))
  :enable (ecurve::edwards-bls12-curve
           base-prime
           ecurve::edwards-bls12-q)
  :use (curve-fep-of-edwards-bls12-d
        curve-fep-of-edwards-bls12-a))

(defruledl crv-add-num-x-shape
  (implies (primep p)
           (equal (pfield::add (pfield::mul x1 y2 p) (pfield::mul y1 x2 p) p)
                  (pfield::add (pfield::mul x1 y2 p) (pfield::mul x2 y1 p) p)))
  :use (:instance pfield::mul-commutative (x y1) (y x2)))

(defruledl crv-add-coordinates
  (implies (ecurve::edwards-bls12-pointp q)
           (and (pfield::fep (ecurve::point-finite->x q) (base-prime))
                (pfield::fep (ecurve::point-finite->y q) (base-prime))
                (equal (ecurve::point-kind q) :finite)))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           crv-add-q-is-base-prime))

(defruledl crv-add-mul-div-cancel
  (implies (and (primep p)
                (pfield::fep n p)
                (pfield::fep f p)
                (not (equal f 0)))
           (equal (pfield::mul (pfield::div n f p) f p) n))
  :use (:instance pfield::mul-of-div-same-arg2 (x f) (y n)))

(defruledl crv-add-den-shape
  (implies (primep p)
           (equal (pfield::mul (pfield::mul x1 y2 p) (pfield::mul x2 y1 p) p)
                  (pfield::mul x1 (pfield::mul x2 (pfield::mul y1 y2 p) p) p))))

(defruledl crv-add-neg-one-times
  (implies (and (primep p) (pfield::fep z p))
           (equal (pfield::mul (+ -1 p) z p)
                  (pfield::neg z p)))
  :enable (pfield::mul pfield::neg pfield::fep)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl crv-add-num-y-shape
  (implies (and (primep p)
                (pfield::fep x1 p) (pfield::fep y1 p)
                (pfield::fep x2 p) (pfield::fep y2 p))
           (equal (pfield::sub (pfield::sub (pfield::mul (pfield::add x1 y1 p)
                                                         (pfield::add x2 y2 p)
                                                         p)
                                            (pfield::mul x1 y2 p)
                                            p)
                               (pfield::mul x2 y1 p)
                               p)
                  (pfield::add (pfield::mul y1 y2 p)
                               (pfield::mul x1 x2 p)
                               p)))
  :enable (pfield::mul pfield::add pfield::sub pfield::neg pfield::fep)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl crv-add-num-y-normal
  (implies (and (primep p)
                (pfield::fep x1 p) (pfield::fep y1 p)
                (pfield::fep x2 p) (pfield::fep y2 p))
           (equal (pfield::add (pfield::neg (pfield::mul x1 y2 p) p)
                               (pfield::add (pfield::neg (pfield::mul x2 y1 p) p)
                                            (pfield::mul (pfield::add x1 y1 p)
                                                         (pfield::add x2 y2 p)
                                                         p)
                                            p)
                               p)
                  (pfield::add (pfield::mul x1 x2 p)
                               (pfield::mul y1 y2 p)
                               p)))
  :enable (pfield::mul pfield::add pfield::neg pfield::fep)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl crv-add-num-y-of-a
  (implies (and (primep p)
                (equal (ecurve::edwards-bls12-a) (1- p))
                (pfield::fep x1 p) (pfield::fep y1 p)
                (pfield::fep x2 p) (pfield::fep y2 p))
           (equal (pfield::sub (pfield::mul y1 y2 p)
                               (pfield::mul (ecurve::edwards-bls12-a)
                                            (pfield::mul x1 x2 p)
                                            p)
                               p)
                  (pfield::add (pfield::mul y1 y2 p)
                               (pfield::mul x1 x2 p)
                               p)))
  :use (:instance crv-add-neg-one-times (z (pfield::mul x1 x2 p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled crv-group-add-equations-complete
  :short "The sum of two curve points satisfies the two division enforces
          of @('Group::add') on the canonical products."
  (implies (and (equal p (base-prime))
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (b* ((x1 (ecurve::point-finite->x p1))
                (y1 (ecurve::point-finite->y p1))
                (x2 (ecurve::point-finite->x p2))
                (y2 (ecurve::point-finite->y p2))
                (s (ecurve::edwards-bls12-add p1 p2))
                (v0 (pfield::mul x1 y2 p))
                (v1 (pfield::mul x2 y1 p))
                (u (pfield::mul (pfield::add x1 y1 p) (pfield::add x2 y2 p) p))
                (dv (pfield::mul (ecurve::edwards-bls12-d)
                                 (pfield::mul v0 v1 p) p)))
             (and (equal (pfield::mul (ecurve::point-finite->x s)
                                      (pfield::add 1 dv p) p)
                         (pfield::add v0 v1 p))
                  (equal (pfield::mul (ecurve::point-finite->y s)
                                      (pfield::sub 1 dv p) p)
                         (pfield::sub (pfield::sub u v0 p) v1 p)))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (ecurve::edwards-bls12-add
                            ecurve::twisted-edwards-add
                            crv-add-curve-fields
                            crv-add-num-x-shape
                            crv-add-q-is-base-prime
                            crv-add-primep-base-prime
                            crv-add-coordinates
                            crv-add-den-shape
                            crv-add-mul-div-cancel
                            crv-add-num-y-shape
                            crv-add-num-y-of-a
                            crv-add-num-y-normal
                            crv-edwards-a-is-minus-one)
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-commutative
                            pfield::mul-commutative-2
                            pfield::mul-associative))
           :use ((:instance crv-add-coordinates (q p1))
                 (:instance crv-add-coordinates (q p2))
                 (:instance crv-add-num-y-normal
                            (p (primes::bls12-377-scalar-field-prime))
                            (x1 (ecurve::point-finite->x p1))
                            (y1 (ecurve::point-finite->y p1))
                            (x2 (ecurve::point-finite->x p2))
                            (y2 (ecurve::point-finite->y p2)))
                 (:instance ecurve::1+d.x1.x2.y1.y2-not-0
                            (point1 p1) (point2 p2)
                            (curve (ecurve::edwards-bls12-curve)))
                 (:instance ecurve::1-d.x1.x2.y1.y2-not-0
                            (point1 p1) (point2 p2)
                            (curve (ecurve::edwards-bls12-curve)))
                 (:instance ecurve::edwards-bls12-pointp (x p1))
                 (:instance ecurve::edwards-bls12-pointp (x p2))
                 ecurve::twisted-edwards-curve-completep-of-edwards-bls12-curve))))

(defruled crv-group-add-gadget-complete
  :short "R1CS-COMPLETE of variable/variable @('Group::add'): the canonical
          products and the coordinates of the sum satisfy the gadget."
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                (symbolp x3) (symbolp y3)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg v0)
                (r1cs::valuation-bindsp asg v1)
                (r1cs::valuation-bindsp asg v01)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (equal (lookup-equal u asg)
                       (pfield::mul (pfield::add (lookup-equal x1 asg)
                                                 (lookup-equal y1 asg) p)
                                    (pfield::add (lookup-equal x2 asg)
                                                 (lookup-equal y2 asg) p)
                                    p))
                (equal (lookup-equal v0 asg)
                       (pfield::mul (lookup-equal x1 asg) (lookup-equal y2 asg) p))
                (equal (lookup-equal v1 asg)
                       (pfield::mul (lookup-equal x2 asg) (lookup-equal y1 asg) p))
                (equal (lookup-equal v01 asg)
                       (pfield::mul (lookup-equal v0 asg) (lookup-equal v1 asg) p))
                (equal (lookup-equal x3 asg)
                       (ecurve::point-finite->x (group-add-funspec p1 p2)))
                (equal (lookup-equal y3 asg)
                       (ecurve::point-finite->y (group-add-funspec p1 p2))))
           (r1cs::r1cs-constraints-holdp
            (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (group-add-funspec primep-of-base-prime)
                           (crv-group-add-equations-complete))
           :use (crv-group-add-gadget-to-products
                 crv-group-add-equations-complete))))
