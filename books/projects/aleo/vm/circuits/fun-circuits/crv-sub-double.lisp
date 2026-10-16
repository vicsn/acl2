; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness and completeness of Group::sub, Group::double, and
; Group::enforce_double, and wire soundness of enforce_on_curve.
;
; Group::sub is the add gadget on (x1, y1) and (-x2, y2), so both directions
; reduce to the add theorems on P1 and -P2.  Group::double uses the curve
; equation y^2 - x^2 = 1 + d x^2 y^2 to turn its denominators into those of
; add(P, P).

(in-package "ALEOVM")

(include-book "crv-add-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled crv-group-sub-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                (symbolp x3) (symbolp y3)
                (equal p (base-prime))
                (primep p)
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
                (r1cs::r1cs-constraints-holdp
                 (crv-group-sub-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal x3 asg)
                                        (lookup-equal y3 asg))
                  (group-sub-funspec p1 p2)))
  :use ((:instance crv-group-add-from-equations
                   (p2 (ecurve::edwards-bls12-neg p2))
                   (x1 (ecurve::point-finite->x p1))
                   (y1 (ecurve::point-finite->y p1))
                   (x2 (pfield::neg (ecurve::point-finite->x p2) p))
                   (y2 (ecurve::point-finite->y p2))
                   (u (lookup-equal u asg))
                   (v0 (lookup-equal v0 asg))
                   (v1 (lookup-equal v1 asg))
                   (v01 (lookup-equal v01 asg))
                   (x3 (lookup-equal x3 asg))
                   (y3 (lookup-equal y3 asg)))
        (:instance crv-neg-point-coordinates (pt p2))
        crv-group-sub-gadget-to-products)
  :enable (group-sub-funspec
           r1cs::fep-of-lookup-equal)
  :disable (crv-group-add-from-equations
            crv-neg-point-coordinates
            crv-group-sub-gadget-to-products))

(defruled crv-group-sub-gadget-complete
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
                                    (pfield::add (pfield::neg (lookup-equal x2 asg) p)
                                                 (lookup-equal y2 asg) p)
                                    p))
                (equal (lookup-equal v0 asg)
                       (pfield::mul (lookup-equal x1 asg) (lookup-equal y2 asg) p))
                (equal (lookup-equal v1 asg)
                       (pfield::mul (pfield::neg (lookup-equal x2 asg) p)
                                    (lookup-equal y1 asg) p))
                (equal (lookup-equal v01 asg)
                       (pfield::mul (lookup-equal v0 asg) (lookup-equal v1 asg) p))
                (equal (lookup-equal x3 asg)
                       (ecurve::point-finite->x (group-sub-funspec p1 p2)))
                (equal (lookup-equal y3 asg)
                       (ecurve::point-finite->y (group-sub-funspec p1 p2))))
           (r1cs::r1cs-constraints-holdp
            (crv-group-sub-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (group-sub-funspec primep-of-base-prime)
                           (crv-group-add-equations-complete
                            crv-neg-point-coordinates
                            crv-group-sub-gadget-to-products
                            pfield::move-negation-1
                            pfield::equal-of-add-of-neg-simple
                            pfield::mul-of-neg-arg1
                            pfield::mul-of-neg-arg2
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2))
           :use (crv-group-sub-gadget-to-products
                 (:instance crv-neg-point-coordinates (pt p2))
                 (:instance crv-group-add-equations-complete
                            (p2 (ecurve::edwards-bls12-neg p2)))))))

(defruled crv-group-sub-assign-gadget-sound
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                (symbolp x3) (symbolp y3)
                (equal p (base-prime))
                (primep p)
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
                (r1cs::r1cs-constraints-holdp
                 (crv-group-sub-assign-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal x3 asg)
                                        (lookup-equal y3 asg))
                  (group-sub-assign-funspec p1 p2)))
  :use crv-group-sub-gadget-sound
  :enable (crv-group-sub-assign-gadget group-sub-assign-funspec))

(defruled crv-group-sub-assign-gadget-complete
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
                                    (pfield::add (pfield::neg (lookup-equal x2 asg) p)
                                                 (lookup-equal y2 asg) p)
                                    p))
                (equal (lookup-equal v0 asg)
                       (pfield::mul (lookup-equal x1 asg) (lookup-equal y2 asg) p))
                (equal (lookup-equal v1 asg)
                       (pfield::mul (pfield::neg (lookup-equal x2 asg) p)
                                    (lookup-equal y1 asg) p))
                (equal (lookup-equal v01 asg)
                       (pfield::mul (lookup-equal v0 asg) (lookup-equal v1 asg) p))
                (equal (lookup-equal x3 asg)
                       (ecurve::point-finite->x (group-sub-assign-funspec p1 p2)))
                (equal (lookup-equal y3 asg)
                       (ecurve::point-finite->y (group-sub-assign-funspec p1 p2))))
           (r1cs::r1cs-constraints-holdp
            (crv-group-sub-assign-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
            asg p))
  :use crv-group-sub-gadget-complete
  :enable (crv-group-sub-assign-gadget group-sub-assign-funspec)
  :disable crv-group-sub-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Doubling.  On the curve y^2 (d x^2 - 1) = -x^2 - 1, so
; y^2 - x^2 = 1 + d (xy)^2 and 2 - (y^2 - x^2) = 1 - d (xy)^2.

(defruledl crv-double-identity-plus
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep d p))
           (equal (pfield::sub (pfield::add 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                                          (pfield::mul x y p)
                                                                          p)
                                                           p)
                                            p)
                               (pfield::sub (pfield::mul y y p) (pfield::mul x x p) p)
                               p)
                  (pfield::sub (pfield::mul (pfield::mul y y p)
                                            (pfield::sub (pfield::mul d (pfield::mul x x p) p) 1 p)
                                            p)
                               (pfield::sub (pfield::neg (pfield::mul x x p) p) 1 p)
                               p)))
  :enable (pfield::mul pfield::add pfield::sub pfield::neg pfield::fep)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)
               (include-book "kestrel/arithmetic-light/times" :dir :system)
               (include-book "kestrel/arithmetic-light/plus" :dir :system)
               (include-book "kestrel/arithmetic-light/minus" :dir :system)))

(defruledl crv-double-identity-minus
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep d p))
           (equal (pfield::sub (pfield::sub 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                                          (pfield::mul x y p)
                                                                          p)
                                                           p)
                                            p)
                               (pfield::sub 2 (pfield::sub (pfield::mul y y p)
                                                           (pfield::mul x x p) p)
                                            p)
                               p)
                  (pfield::neg
                   (pfield::sub (pfield::mul (pfield::mul y y p)
                                             (pfield::sub (pfield::mul d (pfield::mul x x p) p) 1 p)
                                             p)
                                (pfield::sub (pfield::neg (pfield::mul x x p) p) 1 p)
                                p)
                   p)))
  :enable (pfield::mul pfield::add pfield::sub pfield::neg pfield::fep)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)
               (include-book "kestrel/arithmetic-light/times" :dir :system)
               (include-book "kestrel/arithmetic-light/plus" :dir :system)
               (include-book "kestrel/arithmetic-light/minus" :dir :system)))

(defrulel crv-sub-zero-equal
  (implies (and (primep p) (pfield::fep a p) (pfield::fep b p)
                (equal (pfield::sub a b p) 0))
           (equal a b))
  :rule-classes nil
  :use (:instance pfield::equal-of-0-and-sub (pfield::x a) (pfield::y b) (pfield::p p))
  :in-theory '(primep))

(defruledl crv-double-curve-plus
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep d p)
                (equal (pfield::mul (pfield::mul y y p)
                                    (pfield::sub (pfield::mul d (pfield::mul x x p) p) 1 p)
                                    p)
                       (pfield::sub (pfield::neg (pfield::mul x x p) p) 1 p)))
           (equal (pfield::add 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                             (pfield::mul x y p)
                                                             p)
                                              p)
                               p)
                  (pfield::sub (pfield::mul y y p) (pfield::mul x x p) p)))
  :use (crv-double-identity-plus
        (:instance crv-sub-zero-equal
                   (a (pfield::add 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                                 (pfield::mul x y p)
                                                                 p)
                                                  p)
                                   p))
                   (b (pfield::sub (pfield::mul y y p) (pfield::mul x x p) p))))
  :in-theory '(pfield::sub-same pfield::fep-of-add pfield::fep-of-sub
               pfield::fep-of-mul acl2::primep-forward-to-posp))

(defruledl crv-double-curve-minus
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep d p)
                (equal (pfield::mul (pfield::mul y y p)
                                    (pfield::sub (pfield::mul d (pfield::mul x x p) p) 1 p)
                                    p)
                       (pfield::sub (pfield::neg (pfield::mul x x p) p) 1 p)))
           (equal (pfield::sub 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                             (pfield::mul x y p)
                                                             p)
                                              p)
                               p)
                  (pfield::sub 2 (pfield::sub (pfield::mul y y p) (pfield::mul x x p) p)
                               p)))
  :use (crv-double-identity-minus
        (:instance crv-sub-zero-equal
                   (a (pfield::sub 1 (pfield::mul d (pfield::mul (pfield::mul x y p)
                                                                 (pfield::mul x y p)
                                                                 p)
                                                  p)
                                   p))
                   (b (pfield::sub 2 (pfield::sub (pfield::mul y y p)
                                                  (pfield::mul x x p) p)
                                   p))))
  :in-theory '(pfield::sub-same pfield::neg-of-0 pfield::fep-of-add pfield::fep-of-sub
               pfield::fep-of-mul acl2::primep-forward-to-posp))

(defruledl crv-double-add-same
  (implies (and (primep p) (pfield::fep z p))
           (equal (pfield::add z z p) (pfield::mul 2 z p)))
  :enable (pfield::mul pfield::add pfield::fep)
  :use (:instance (:theorem (implies (acl2-numberp z) (equal (+ z z) (* 2 z))))))

(defruledl crv-double-y-numerator
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p))
           (equal (pfield::sub (pfield::sub (pfield::mul (pfield::add x y p)
                                                         (pfield::add x y p) p)
                                            (pfield::mul x y p) p)
                               (pfield::mul x y p) p)
                  (pfield::add (pfield::mul y y p) (pfield::mul x x p) p)))
  :enable (pfield::mul pfield::add pfield::sub pfield::neg pfield::fep)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl crv-double-equations-iff-add
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep d p)
                (equal (pfield::mul (pfield::mul y y p)
                                    (pfield::sub (pfield::mul d (pfield::mul x x p) p) 1 p)
                                    p)
                       (pfield::sub (pfield::neg (pfield::mul x x p) p) 1 p)))
           (b* ((xy (pfield::mul x y p))
                (dt (pfield::mul d (pfield::mul xy xy p) p))
                (dif (pfield::sub (pfield::mul y y p) (pfield::mul x x p) p)))
             (and (equal (equal (pfield::mul x3 (pfield::add 1 dt p) p)
                                (pfield::add xy xy p))
                         (equal (pfield::mul x3 dif p)
                                (pfield::mul 2 xy p)))
                  (equal (equal (pfield::mul y3 (pfield::sub 1 dt p) p)
                                (pfield::sub (pfield::sub (pfield::mul (pfield::add x y p)
                                                                       (pfield::add x y p) p)
                                                          xy p)
                                             xy p))
                         (equal (pfield::mul y3 (pfield::sub 2 dif p) p)
                                (pfield::add (pfield::mul y y p) (pfield::mul x x p) p))))))
  :in-theory '(crv-double-curve-plus crv-double-curve-minus
               crv-double-add-same crv-double-y-numerator
               pfield::fep-of-mul acl2::primep-forward-to-posp))

(defruled crv-group-double-gadget-sound
  (implies (and (symbolp x) (symbolp y)
                (symbolp xy) (symbolp x2) (symbolp y2)
                (symbolp x3) (symbolp y3)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg xy)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-double-gadget x y xy x2 y2 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal x3 asg)
                                        (lookup-equal y3 asg))
                  (group-double-funspec pt)))
  :do-not-induct t
  :hints (("Goal"
           :use (crv-group-double-gadget-to-products
                 (:instance crv-curve-coordinates-on-curve-iff-snarkvm)
                 (:instance crv-fep-of-edwards-bls12-coords)
                 (:instance crv-double-equations-iff-add
                            (x (ecurve::point-finite->x pt))
                            (y (ecurve::point-finite->y pt))
                            (d (ecurve::edwards-bls12-d))
                            (x3 (lookup-equal x3 asg))
                            (y3 (lookup-equal y3 asg)))
                 (:instance crv-group-add-from-equations
                            (p1 pt) (p2 pt)
                            (x1 (ecurve::point-finite->x pt))
                            (y1 (ecurve::point-finite->y pt))
                            (x2 (ecurve::point-finite->x pt))
                            (y2 (ecurve::point-finite->y pt))
                            (u (pfield::mul (pfield::add (ecurve::point-finite->x pt)
                                                         (ecurve::point-finite->y pt) p)
                                            (pfield::add (ecurve::point-finite->x pt)
                                                         (ecurve::point-finite->y pt) p)
                                            p))
                            (v0 (pfield::mul (ecurve::point-finite->x pt)
                                             (ecurve::point-finite->y pt) p))
                            (v1 (pfield::mul (ecurve::point-finite->x pt)
                                             (ecurve::point-finite->y pt) p))
                            (v01 (pfield::mul (pfield::mul (ecurve::point-finite->x pt)
                                                           (ecurve::point-finite->y pt) p)
                                              (pfield::mul (ecurve::point-finite->x pt)
                                                           (ecurve::point-finite->y pt) p)
                                              p))
                            (x3 (lookup-equal x3 asg))
                            (y3 (lookup-equal y3 asg))))
           :in-theory '(group-double-funspec
                        r1cs::fep-of-lookup-equal
                        curve-coordinatesp-when-edwards-bls12-pointp
                        curve-fep-of-edwards-bls12-d
                        primep-of-base-prime))))

(defruled crv-group-double-gadget-complete
  (implies (and (symbolp x) (symbolp y)
                (symbolp xy) (symbolp x2) (symbolp y2)
                (symbolp x3) (symbolp y3)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg xy)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                (equal (lookup-equal xy asg)
                       (pfield::mul (lookup-equal x asg) (lookup-equal y asg) p))
                (equal (lookup-equal x2 asg)
                       (pfield::mul (lookup-equal x asg) (lookup-equal x asg) p))
                (equal (lookup-equal y2 asg)
                       (pfield::mul (lookup-equal y asg) (lookup-equal y asg) p))
                (equal (lookup-equal x3 asg)
                       (ecurve::point-finite->x (group-double-funspec pt)))
                (equal (lookup-equal y3 asg)
                       (ecurve::point-finite->y (group-double-funspec pt))))
           (r1cs::r1cs-constraints-holdp
            (crv-group-double-gadget x y xy x2 y2 x3 y3 p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (crv-group-double-gadget-to-products
                 (:instance crv-curve-coordinates-on-curve-iff-snarkvm)
                 (:instance crv-fep-of-edwards-bls12-coords)
                 (:instance crv-double-equations-iff-add
                            (x (ecurve::point-finite->x pt))
                            (y (ecurve::point-finite->y pt))
                            (d (ecurve::edwards-bls12-d))
                            (x3 (lookup-equal x3 asg))
                            (y3 (lookup-equal y3 asg)))
                 (:instance crv-group-add-equations-complete
                            (p1 pt) (p2 pt)))
           :in-theory '(group-double-funspec
                        curve-coordinatesp-when-edwards-bls12-pointp
                        curve-fep-of-edwards-bls12-d
                        primep-of-base-prime))))
