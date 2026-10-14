; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group curve check, addition, subtraction, and doubling, in the
; variable/variable case.
;
; Edwards-BLS12 has a = -1, so the snarkVM sum
;   U = (-a x1 + y1) (x2 + y2)
; is the product (x1 + y1) (x2 + y2).  Constant multiplications by a and d
; are coefficients, not constraints.  Variable/variable addition is the
; four products u, v0, v1, v0*v1 and the two division enforces.
; Doubling is xy, x^2, y^2 and the two division enforces.
; Subtraction is addition of (x, y) and (-x2, y2); negation is a coefficient.
;
; These constraints are the snarkVM formulas (curve-raw-add / curve-raw-double).
; They are not yet proved equal to ecurve::edwards-bls12-add, which is what
; the arithmetic funspecs return.  See bugs-crv.txt.  enforce_on_curve is the
; rearranged curve equation; linking it to point-on-twisted-edwards-p is the
; same algebraic gap, so its funspec soundness is not claimed here.

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "../fun-specs/curve-group")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled crv-edwards-a-is-minus-one
  (implies (equal p (base-prime))
           (equal (ecurve::edwards-bls12-a) (1- p)))
  :enable (ecurve::edwards-bls12-a
           base-prime
           ecurve::edwards-bls12-q
           pfield::neg))

; Variable/variable addition.  d-coeff is edwards-bls12-d, used as a coefficient.

(define crv-group-add-gadget ((x1 symbolp) (y1 symbolp)
                              (x2 symbolp) (y2 symbolp)
                              (u symbolp) (v0 symbolp) (v1 symbolp) (v01 symbolp)
                              (x3 symbolp) (y3 symbolp)
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (b* ((d (ecurve::edwards-bls12-d))
       (neg-d (pfield::neg d p)))
    (append
     ;; u = (x1 + y1) (x2 + y2)     because -a = 1
     (list (r1cs::make-r1cs-constraint
            :a (list (list 1 x1) (list 1 y1))
            :b (list (list 1 x2) (list 1 y2))
            :c (list (list 1 u)))
           ;; v0 = x1 * y2
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x1))
            :b (list (list 1 y2))
            :c (list (list 1 v0)))
           ;; v1 = x2 * y1
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x2))
            :b (list (list 1 y1))
            :c (list (list 1 v1)))
           ;; v01 = v0 * v1, and v2 = d * v01 is the linear combination
           (r1cs::make-r1cs-constraint
            :a (list (list 1 v0))
            :b (list (list 1 v1))
            :c (list (list 1 v01)))
           ;; x3 * (1 + d v01) = v0 + v1
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x3))
            :b (list (list 1 1) (list d v01))
            :c (list (list 1 v0) (list 1 v1)))
           ;; y3 * (1 - d v01) = u + a v0 - v1, with a = -1
           (r1cs::make-r1cs-constraint
            :a (list (list 1 y3))
            :b (list (list 1 1) (list neg-d v01))
            :c (list (list 1 u)
                     (list (1- p) v0)
                     (list (1- p) v1)))))))

(defruled crv-group-add-gadget-to-products
  :short "The six constraints are the snarkVM products and division enforces."
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                (symbolp x3) (symbolp y3)
                (primep p)
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
                (r1cs::valuation-bindsp asg y3))
           (b* ((x1$ (lookup-equal x1 asg))
                (y1$ (lookup-equal y1 asg))
                (x2$ (lookup-equal x2 asg))
                (y2$ (lookup-equal y2 asg))
                (u$ (lookup-equal u asg))
                (v0$ (lookup-equal v0 asg))
                (v1$ (lookup-equal v1 asg))
                (v01$ (lookup-equal v01 asg))
                (x3$ (lookup-equal x3 asg))
                (y3$ (lookup-equal y3 asg))
                (d (ecurve::edwards-bls12-d)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
                     asg p)
                    (and (equal u$ (pfield::mul (pfield::add x1$ y1$ p)
                                                (pfield::add x2$ y2$ p) p))
                         (equal v0$ (pfield::mul x1$ y2$ p))
                         (equal v1$ (pfield::mul x2$ y1$ p))
                         (equal v01$ (pfield::mul v0$ v1$ p))
                         (equal (pfield::mul x3$
                                             (pfield::add 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::add v0$ v1$ p))
                         (equal (pfield::mul y3$
                                             (pfield::sub 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::sub (pfield::sub u$ v0$ p) v1$ p))))))
  :enable (crv-group-add-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           crv-edwards-a-is-minus-one))

(define crv-group-sub-gadget ((x1 symbolp) (y1 symbolp)
                              (x2 symbolp) (y2 symbolp)
                              (u symbolp) (v0 symbolp) (v1 symbolp) (v01 symbolp)
                              (x3 symbolp) (y3 symbolp)
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Addition against the negated point.  The x2 coefficient is @($-1$)."
  (b* ((d (ecurve::edwards-bls12-d))
       (neg-d (pfield::neg d p)))
    (append
     (list (r1cs::make-r1cs-constraint
            :a (list (list 1 x1) (list 1 y1))
            :b (list (list (1- p) x2) (list 1 y2))
            :c (list (list 1 u)))
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x1))
            :b (list (list 1 y2))
            :c (list (list 1 v0)))
           (r1cs::make-r1cs-constraint
            :a (list (list (1- p) x2))
            :b (list (list 1 y1))
            :c (list (list 1 v1)))
           (r1cs::make-r1cs-constraint
            :a (list (list 1 v0))
            :b (list (list 1 v1))
            :c (list (list 1 v01)))
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x3))
            :b (list (list 1 1) (list d v01))
            :c (list (list 1 v0) (list 1 v1)))
           (r1cs::make-r1cs-constraint
            :a (list (list 1 y3))
            :b (list (list 1 1) (list neg-d v01))
            :c (list (list 1 u)
                     (list (1- p) v0)
                     (list (1- p) v1)))))))

(define crv-group-add-assign-gadget ((x1 symbolp) (y1 symbolp)
                                     (x2 symbolp) (y2 symbolp)
                                     (u symbolp) (v0 symbolp) (v1 symbolp)
                                     (v01 symbolp)
                                     (x3 symbolp) (y3 symbolp)
                                     (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p))

(define crv-group-sub-assign-gadget ((x1 symbolp) (y1 symbolp)
                                     (x2 symbolp) (y2 symbolp)
                                     (u symbolp) (v0 symbolp) (v1 symbolp)
                                     (v01 symbolp)
                                     (x3 symbolp) (y3 symbolp)
                                     (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-sub-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-double-gadget ((x symbolp) (y symbolp)
                                 (xy symbolp) (x2 symbolp) (y2 symbolp)
                                 (x3 symbolp) (y3 symbolp)
                                 (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "xy, x^2, y^2, and the two doubling division enforces.
          @($a x^2$) is the coefficient @($-x^2$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 xy)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 x))
         :c (list (list 1 x2)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 y))
         :b (list (list 1 y))
         :c (list (list 1 y2)))
        ;; x3 * (y2 - x2) = 2 xy     because a = -1, so ax^2 + y^2 = y^2 - x^2
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x3))
         :b (list (list 1 y2) (list (1- p) x2))
         :c (list (list 2 xy)))
        ;; y3 * (2 - (y2 - x2)) = y2 - a x2 = y2 + x2
        (r1cs::make-r1cs-constraint
         :a (list (list 1 y3))
         :b (list (list 2 1)
                  (list (1- p) y2)
                  (list 1 x2))
         :c (list (list 1 y2) (list 1 x2)))))

(define crv-group-enforce-double-gadget ((x symbolp) (y symbolp)
                                         (xy symbolp) (x2 symbolp) (y2 symbolp)
                                         (x3 symbolp) (y3 symbolp)
                                         (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as double; the double is an input, not a fresh witness."
  (crv-group-double-gadget x y xy x2 y2 x3 y3 p))

(define crv-group-mul-by-cofactor-gadget
  ((x symbolp) (y symbolp)
   (xy1 symbolp) (x21 symbolp) (y21 symbolp)
   (x4 symbolp) (y4 symbolp)
   (xy2 symbolp) (x22 symbolp) (y22 symbolp)
   (x3 symbolp) (y3 symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Two doublings.  The cofactor is 4."
  (append (crv-group-double-gadget x y xy1 x21 y21 x4 y4 p)
          (crv-group-double-gadget x4 y4 xy2 x22 y22 x3 y3 p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-enforce-on-curve-gadget ((x symbolp) (y symbolp)
                                           (x2 symbolp) (y2 symbolp)
                                           (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "x^2, y^2, and @($y^2 (d x^2 - 1) = a x^2 - 1$) with @($a = -1$)."
  (b* ((d (ecurve::edwards-bls12-d)))
    (list (r1cs::make-r1cs-constraint
           :a (list (list 1 x))
           :b (list (list 1 x))
           :c (list (list 1 x2)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 y))
           :b (list (list 1 y))
           :c (list (list 1 y2)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 y2))
           :b (list (list d x2)
                    (list (1- p) 1))
           :c (list (list (1- p) x2)
                    (list (1- p) 1))))))

(defruled crv-group-enforce-on-curve-gadget-to-equation
  (implies (and (symbolp x) (symbolp y) (symbolp x2) (symbolp y2)
                (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (x2$ (lookup-equal x2 asg))
                (y2$ (lookup-equal y2 asg))
                (d (ecurve::edwards-bls12-d)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crv-group-enforce-on-curve-gadget x y x2 y2 p)
                     asg p)
                    (and (equal x2$ (pfield::mul x$ x$ p))
                         (equal y2$ (pfield::mul y$ y$ p))
                         (equal (pfield::mul y2$
                                             (pfield::sub (pfield::mul d x2$ p)
                                                          1 p)
                                             p)
                                (pfield::sub (pfield::neg x2$ p) 1 p))))))
  :enable (crv-group-enforce-on-curve-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           crv-edwards-a-is-minus-one))

(defconst *crv-group-enforce-on-curve-sample*
  '((x . 0) (y . 1) (x2 . 0) (y2 . 1)))

(defruled crv-group-enforce-on-curve-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-group-enforce-on-curve-sample* p)
                (r1cs::valuation-bindsp *crv-group-enforce-on-curve-sample* 'x)
                (r1cs::valuation-bindsp *crv-group-enforce-on-curve-sample* 'y)
                (r1cs::valuation-bindsp *crv-group-enforce-on-curve-sample* 'x2)
                (r1cs::valuation-bindsp *crv-group-enforce-on-curve-sample* 'y2)
                (fieldp 0)
                (fieldp 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-enforce-on-curve-gadget 'x 'y 'x2 'y2 p)
            *crv-group-enforce-on-curve-sample* p))
  :enable (crv-group-enforce-on-curve-gadget-to-equation
           lookup-equal)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One double-and-add step of scalar multiplication.  The add is always
; constrained; the bit selects between the sum and the double.

(define crv-group-mul-step-gadget
  ((bit symbolp)
   (bx symbolp) (by symbolp)
   (ax symbolp) (ay symbolp)
   (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
   (dx symbolp) (dy symbolp)
   (u symbolp) (v0 symbolp) (v1 symbolp) (v01 symbolp)
   (sx symbolp) (sy symbolp)
   (ox symbolp) (oy symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-group-double-gadget ax ay dxy dx2 dy2 dx dy p)
          (crv-group-add-gadget bx by dx dy u v0 v1 v01 sx sy p)
          (crv-field-ternary-gadget bit sx dx ox p)
          (crv-field-ternary-gadget bit sy dy oy p)))

; Group::mul and Group::mul_assign emit scalar to_bits_be (251 bits) and then
; one crv-group-mul-step-gadget per bit, starting from the zero point.
; The first iteration constant-folds double(0) and add(base, 0).  The proved
; unit is the variable step above; the 251-fold chain is not a single theorem.
