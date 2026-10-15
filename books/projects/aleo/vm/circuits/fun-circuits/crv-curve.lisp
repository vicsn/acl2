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
; Variable/variable addition is proved equal to ecurve::edwards-bls12-add.
; Subtraction is that sum with x2 negated.  Doubling and enforce_double are
; addition of a curve point with itself.  enforce_on_curve is the twisted
; Edwards equation.  Its PFCS predicate is equivalent to the funspec.
; mul_by_cofactor is two doublings; the funspec multiplies
; by 4, and 4P = double(double(P)) needs the unproved associativity
; assumption, so that soundness is not claimed.  Group::mul's 251-step
; double-and-add is not a theorem.

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "../fun-specs/curve-group")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

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
  :guard (equal p (base-prime))
  :guard-hints (("Goal" :in-theory (enable pfield::fep
                                           ecurve::edwards-bls12-d
                                           ecurve::edwards-bls12-q
                                           base-prime)))
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
  :guard (equal p (base-prime))
  :guard-hints (("Goal" :in-theory (enable pfield::fep
                                           ecurve::edwards-bls12-d
                                           ecurve::edwards-bls12-q
                                           base-prime)))
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
  :guard (equal p (base-prime))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p))

(define crv-group-sub-assign-gadget ((x1 symbolp) (y1 symbolp)
                                     (x2 symbolp) (y2 symbolp)
                                     (u symbolp) (v0 symbolp) (v1 symbolp)
                                     (v01 symbolp)
                                     (x3 symbolp) (y3 symbolp)
                                     (p primep))
  :guard (equal p (base-prime))
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
  :guard (equal p (base-prime))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-group-double-gadget ax ay dxy dx2 dy2 dx dy p)
          (crv-group-add-gadget bx by dx dy u v0 v1 v01 sx sy p)
          (crv-field-ternary-gadget bit sx dx ox p)
          (crv-field-ternary-gadget bit sy dy oy p)))

; Group::mul and Group::mul_assign emit scalar to_bits_be (251 bits) and then
; one crv-group-mul-step-gadget per bit, starting from the zero point.
; The first iteration constant-folds double(0) and add(base, 0).  The proved
; unit is the variable step above; the 251-fold chain is not a single theorem.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keep the 253-bit prime folded.  a = -1 is (neg 1 p), not a ground expansion.

(local (in-theory (disable base-prime
                           (:e base-prime)
                           ecurve::edwards-bls12-q
                           (:e ecurve::edwards-bls12-q)
                           ecurve::edwards-bls12-a
                           (:e ecurve::edwards-bls12-a)
                           ecurve::edwards-bls12-d
                           (:e ecurve::edwards-bls12-d)
                           ecurve::edwards-bls12-r
                           (:e ecurve::edwards-bls12-r)
                           primes::bls12-377-scalar-field-prime
                           (:e primes::bls12-377-scalar-field-prime)
                           (:e expt))))

(defruled crv-edwards-a-is-neg-one
  (equal (ecurve::edwards-bls12-a)
         (pfield::neg 1 (base-prime)))
  :enable (ecurve::edwards-bls12-a
           curve-base-prime-is-edwards-bls12-q)
  :disable (ecurve::edwards-bls12-q
            (:e ecurve::edwards-bls12-q)
            base-prime
            (:e base-prime)))

(defruled crv-neg-one-is-p-minus-one
  (implies (and (posp p)
                (< 1 p))
           (equal (pfield::neg 1 p)
                  (1- p)))
  :enable pfield::neg
  :use (:instance acl2::mod-when-<-of-0 (x -1) (y p)))

;; Polynomial identity, proved by opening the field operations.
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (in-theory (disable pfield::mul-of-add-arg1
                             pfield::mul-of-add-arg2
                             pfield::mul-of-sub-arg1
                             pfield::mul-of-sub-arg2
                             pfield::mul-commutative
                             pfield::mul-commutative-2
                             pfield::add-commutative
                             pfield::add-commutative-2)))

  (defruled crv-group-add-y-numerator
    :short "@($U + a v_0 - v_1 = y_1 y_2 - a x_1 x_2$) with @($a = -1$)."
    (implies (and (primep p)
                  (< 2 p)
                  (pfield::fep x1 p)
                  (pfield::fep y1 p)
                  (pfield::fep x2 p)
                  (pfield::fep y2 p)
                  (equal a (pfield::neg 1 p)))
             (equal (pfield::sub
                     (pfield::sub (pfield::mul (pfield::add x1 y1 p)
                                               (pfield::add x2 y2 p)
                                               p)
                                  (pfield::mul x1 y2 p)
                                  p)
                     (pfield::mul x2 y1 p)
                     p)
                    (pfield::sub (pfield::mul y1 y2 p)
                                 (pfield::mul a (pfield::mul x1 x2 p) p)
                                 p)))
    :hints (("Goal" :in-theory (enable pfield::add
                                       pfield::mul
                                       pfield::neg
                                       pfield::sub
                                       pfield::fep))))

)

(defruled crv-snarkvm-curve-diffs-equal
  :short "The two curve checks differ from zero by the same field element."
  (implies (and (primep p)
                (< 2 p)
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (pfield::fep d p))
           (equal (pfield::sub (pfield::mul y2
                                            (pfield::sub (pfield::mul d x2 p)
                                                         1 p)
                                            p)
                               (pfield::sub (pfield::neg x2 p) 1 p)
                               p)
                  (pfield::sub (pfield::add 1
                                            (pfield::mul d
                                                         (pfield::mul x2 y2 p)
                                                         p)
                                            p)
                               (pfield::add (pfield::neg x2 p) y2 p)
                               p)))
  :hints (("Goal"
           :in-theory (e/d (pfield::sub
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-associative
                            pfield::mul-commutative
                            pfield::mul-commutative-2
                            pfield::add-associative
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::neg-of-add
                            pfield::neg-of-neg)
                           ((:definition pfield::add)
                            (:definition pfield::mul)
                            (:definition pfield::neg))))))

(defruled crv-snarkvm-curve-eq-iff-twisted-edwards
  :short "@($y^2(d x^2-1) = -x^2-1$) iff @($-x^2 + y^2 = 1 + d x^2 y^2$)."
  (implies (and (primep p)
                (< 2 p)
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (pfield::fep d p))
           (equal (equal (pfield::mul y2
                                      (pfield::sub (pfield::mul d x2 p) 1 p)
                                      p)
                         (pfield::sub (pfield::neg x2 p) 1 p))
                  (equal (pfield::add (pfield::neg x2 p) y2 p)
                         (pfield::add 1
                                      (pfield::mul d (pfield::mul x2 y2 p) p)
                                      p))))
  :hints (("Goal"
           :use (:instance crv-snarkvm-curve-diffs-equal)
           :cases ((equal (pfield::mul y2
                                       (pfield::sub (pfield::mul d x2 p) 1 p)
                                       p)
                          (pfield::sub (pfield::neg x2 p) 1 p)))
           :in-theory (e/d (pfield::equal-of-0-and-sub
                            pfield::sub-same)
                           (crv-snarkvm-curve-diffs-equal
                            (:definition pfield::add)
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition pfield::neg)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))))

(defruled crv-edwards-gamma-product
  (implies (posp p)
           (equal (pfield::mul d
                               (pfield::mul (pfield::mul x1 y2 p)
                                            (pfield::mul x2 y1 p)
                                            p)
                               p)
                  (pfield::mul d
                               (pfield::mul x1
                                            (pfield::mul x2
                                                         (pfield::mul y1 y2 p)
                                                         p)
                                            p)
                               p))))

(defruled crv-gamma-of-products
  (implies (and (posp p)
                (equal v0 (pfield::mul x1 y2 p))
                (equal v1 (pfield::mul x2 y1 p))
                (equal v01 (pfield::mul v0 v1 p)))
           (equal (pfield::mul d v01 p)
                  (pfield::mul d
                               (pfield::mul x1
                                            (pfield::mul x2
                                                         (pfield::mul y1 y2 p)
                                                         p)
                                            p)
                               p)))
  :enable crv-edwards-gamma-product
  :disable ((:definition pfield::mul)))

(encapsulate
  ()
  (local (in-theory (enable base-prime
                            (:e base-prime)
                            ecurve::edwards-bls12-q
                            (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-a
                            ecurve::edwards-bls12-d)))

(defruled crv-curve-coordinates-on-curve-iff-snarkvm
  (implies (and (equal p (base-prime))
                (primep p)
                (curve-coordinatesp pt))
           (b* ((x (ecurve::point-finite->x pt))
                (y (ecurve::point-finite->y pt))
                (x2 (pfield::mul x x p))
                (y2 (pfield::mul y y p))
                (d (ecurve::edwards-bls12-d)))
             (equal (ecurve::edwards-bls12-pointp pt)
                    (equal (pfield::mul y2
                                        (pfield::sub (pfield::mul d x2 p) 1 p)
                                        p)
                           (pfield::sub (pfield::neg x2 p) 1 p)))))
  :hints (("Goal"
           :use (:instance crv-snarkvm-curve-eq-iff-twisted-edwards
                           (x2 (pfield::mul (ecurve::point-finite->x pt)
                                            (ecurve::point-finite->x pt)
                                            p))
                           (y2 (pfield::mul (ecurve::point-finite->y pt)
                                            (ecurve::point-finite->y pt)
                                            p))
                           (d (ecurve::edwards-bls12-d))
                           (p p))
           :in-theory (e/d (curve-coordinatesp
                            fieldp
                            ecurve::edwards-bls12-pointp
                            ecurve::point-on-twisted-edwards-p
                            ecurve::edwards-bls12-curve
                            curve-base-prime-is-edwards-bls12-q
                            crv-edwards-a-is-neg-one)
                           (crv-snarkvm-curve-eq-iff-twisted-edwards
                            ecurve::point-finite->x
                            ecurve::point-finite->y
                            ecurve::point-kind
                            ecurve::pointp
                            nfix
                            pfield::equal-of-add-move-negations-bind-free-2a
                            pfield::equal-of-add-move-negations-bind-free-2b
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))))

)

(defruled crv-group-enforce-on-curve-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp x2) (symbolp y2)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (curve-coordinatesp pt)
                (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-enforce-on-curve-gadget x y x2 y2 p)
                 asg p))
           (equal (group-enforce-on-curve-funspec pt) nil))
  :enable (crv-group-enforce-on-curve-gadget-to-equation
           crv-curve-coordinates-on-curve-iff-snarkvm
           group-enforce-on-curve-funspec))

(defruled crv-group-enforce-on-curve-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp x2) (symbolp y2)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                (equal (lookup-equal x2 asg)
                       (pfield::mul (lookup-equal x asg)
                                    (lookup-equal x asg)
                                    p))
                (equal (lookup-equal y2 asg)
                       (pfield::mul (lookup-equal y asg)
                                    (lookup-equal y asg)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-enforce-on-curve-gadget x y x2 y2 p)
            asg p))
  :hints (("Goal"
           :use (:instance crv-curve-coordinates-on-curve-iff-snarkvm)
           :in-theory (e/d (crv-group-enforce-on-curve-gadget-to-equation
                            curve-coordinatesp-when-edwards-bls12-pointp)
                           (crv-curve-coordinates-on-curve-iff-snarkvm
                            pfield::equal-of-add-move-negations-bind-free-2a
                            pfield::equal-of-add-move-negations-bind-free-2b
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS for enforce_on_curve.  d = 3021 is edwards-bls12-d, a coefficient.
; a = -1, so the right side a*x^2 - 1 is -x2 - 1.

(define crv-group-enforce-on-curve-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Squares and @($y^2 (d x^2 - 1) = -x^2 - 1$), the Edwards-BLS12 check."
  (pfcs::parse-def
   "crv_group_enforce_on_curve(x, y, x2, y2) := {
    (x) * (x) == (x2),
    (y) * (y) == (y2),
    (y2) * (3021 * x2 - 1) == (- x2 - 1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-group-enforce-on-curve-circuit)
            :pred crv-group-enforce-on-curve-pred
            :prime prime)

(defruledl crv-enforce-on-curve-mod-consts
  (implies (equal prime (base-prime))
           (and (equal (mod 1 prime) 1)
                (equal (mod 3021 prime) (ecurve::edwards-bls12-d))))
  :hints (("Goal"
           :in-theory (enable ecurve::edwards-bls12-d
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)
                              (:e ecurve::edwards-bls12-d)))))

(defruledl crv-group-enforce-on-curve-pred-to-snarkvm
  (implies (equal prime (base-prime))
           (equal (crv-group-enforce-on-curve-pred x y x2 y2 prime)
                  (and (equal (pfield::mul x x prime) x2)
                       (equal (pfield::mul y y prime) y2)
                       (equal (pfield::mul
                               y2
                               (pfield::sub
                                (pfield::mul (ecurve::edwards-bls12-d)
                                             x2 prime)
                                1 prime)
                               prime)
                              (pfield::sub (pfield::neg x2 prime) 1 prime)))))
  :hints (("Goal"
           :in-theory (e/d (crv-group-enforce-on-curve-pred
                            crv-enforce-on-curve-mod-consts)
                           ((:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition pfield::neg)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))))

(defruledl crv-on-curve-squares-iff-funspec-nil
  (implies (and (equal prime (base-prime))
                (primep prime)
                (curve-coordinatesp pt)
                (equal x (ecurve::point-finite->x pt))
                (equal y (ecurve::point-finite->y pt))
                (equal (pfield::mul x x prime) x2)
                (equal (pfield::mul y y prime) y2))
           (equal (equal (pfield::mul
                          y2
                          (pfield::sub
                           (pfield::mul (ecurve::edwards-bls12-d) x2 prime)
                           1 prime)
                          prime)
                         (pfield::sub (pfield::neg x2 prime) 1 prime))
                  (equal (group-enforce-on-curve-funspec pt) nil)))
  :hints (("Goal"
           :do-not-induct t
           :use (:instance crv-curve-coordinates-on-curve-iff-snarkvm
                           (p prime))
           :in-theory (e/d (group-enforce-on-curve-funspec
                            (:e spec-error))
                           (crv-curve-coordinates-on-curve-iff-snarkvm
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition pfield::neg)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::equal-of-add-move-negations-bind-free-2a
                            pfield::equal-of-add-move-negations-bind-free-2b)))))

(local
 (defthm crv-eoc-combine
   (implies (and h-prime
                 h-primep
                 h-coords
                 h-x
                 h-y
                 (implies h-prime
                          (equal pred (and a b c)))
                 (implies (and h-prime h-primep h-coords h-x h-y a b)
                          (equal c d)))
            (equal pred (and a b d)))
   :rule-classes nil
   :hints (("Goal" :cases ((and a b))))))

(defruled crv-group-enforce-on-curve-pred-to-funspec
  :short "The enforce-on-curve predicate holds exactly when the witnesses
          are the squares and the point is on the Edwards-BLS12 curve."
  (implies (and (equal prime (base-prime))
                (primep prime)
                (curve-coordinatesp pt)
                (equal x (ecurve::point-finite->x pt))
                (equal y (ecurve::point-finite->y pt)))
           (equal (crv-group-enforce-on-curve-pred x y x2 y2 prime)
                  (and (equal (pfield::mul x x prime) x2)
                       (equal (pfield::mul y y prime) y2)
                       (equal (group-enforce-on-curve-funspec pt) nil))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory nil
           :use ((:instance crv-group-enforce-on-curve-pred-to-snarkvm)
                 (:instance crv-on-curve-squares-iff-funspec-nil)
                 (:instance crv-eoc-combine
                            (h-prime (equal prime (base-prime)))
                            (h-primep (primep prime))
                            (h-coords (curve-coordinatesp pt))
                            (h-x (equal x (ecurve::point-finite->x pt)))
                            (h-y (equal y (ecurve::point-finite->y pt)))
                            (pred (crv-group-enforce-on-curve-pred
                                   x y x2 y2 prime))
                            (a (equal (pfield::mul x x prime) x2))
                            (b (equal (pfield::mul y y prime) y2))
                            (c (equal (pfield::mul
                                       y2
                                       (pfield::sub
                                        (pfield::mul (ecurve::edwards-bls12-d)
                                                     x2 prime)
                                        1 prime)
                                       prime)
                                      (pfield::sub (pfield::neg x2 prime)
                                                   1 prime)))
                            (d (equal (group-enforce-on-curve-funspec pt)
                                      nil)))))))

(defruled crv-fep-of-edwards-bls12-coords
  (implies (and (equal p (base-prime))
                (primep p)
                (ecurve::edwards-bls12-pointp pt))
           (and (pfield::fep (ecurve::point-finite->x pt) p)
                (pfield::fep (ecurve::point-finite->y pt) p)))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           ecurve::point-finite-when-edwards-bls12-pointp
           ecurve::pointp-when-edwards-bls12-pointp
           pfield::fep
           curve-base-prime-is-edwards-bls12-q)
  :disable ((:e ecurve::edwards-bls12-q)
            (:e base-prime)
            (:e ecurve::edwards-bls12-a)
            (:e ecurve::edwards-bls12-d)
            (:e ecurve::edwards-bls12-curve)
            ecurve::point-finite->x
            ecurve::point-finite->y))

(defthmd crv-coord-matches-div
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p)
                (pfield::fep z p)
                (not (equal z 0))
                (equal (pfield::mul x z p) y))
           (equal (nfix (pfield::div y z p))
                  (nfix x)))
  :hints (("Goal"
           :in-theory (e/d (pfield::equal-of-div
                            pfield::natp-of-div
                            acl2::nfix-when-natp)
                           (nfix)))))

(defruled crv-add-dens-nonzero
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (b* ((q (ecurve::edwards-bls12-q))
                (d (ecurve::edwards-bls12-d))
                (x1 (ecurve::point-finite->x p1))
                (y1 (ecurve::point-finite->y p1))
                (x2 (ecurve::point-finite->x p2))
                (y2 (ecurve::point-finite->y p2))
                (g (pfield::mul d
                                (pfield::mul x1
                                             (pfield::mul x2
                                                          (pfield::mul y1 y2 q)
                                                          q)
                                             q)
                                q)))
             (and (not (equal (pfield::add 1 g q) 0))
                  (not (equal (pfield::sub 1 g q) 0)))))
  :hints (("Goal"
           :use ((:instance ecurve::1+d.x1.x2.y1.y2-not-0
                            (curve (ecurve::edwards-bls12-curve))
                            (point1 p1)
                            (point2 p2))
                 (:instance ecurve::1-d.x1.x2.y1.y2-not-0
                            (curve (ecurve::edwards-bls12-curve))
                            (point1 p1)
                            (point2 p2))
                 ecurve::twisted-edwards-curve-completep-of-edwards-bls12-curve)
           :in-theory (e/d (ecurve::edwards-bls12-pointp
                            ecurve::edwards-bls12-curve)
                           ((:e ecurve::twisted-edwards-curve-completep)
                            (:e ecurve::pfield-squarep)
                            (:e ecurve::edwards-bls12-q)
                            (:e ecurve::edwards-bls12-a)
                            (:e ecurve::edwards-bls12-d)
                            (:e ecurve::edwards-bls12-curve))))))

(defruled crv-edwards-bls12-add-to-divs
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (b* ((q (ecurve::edwards-bls12-q))
                (a (ecurve::edwards-bls12-a))
                (d (ecurve::edwards-bls12-d))
                (x1 (ecurve::point-finite->x p1))
                (y1 (ecurve::point-finite->y p1))
                (x2 (ecurve::point-finite->x p2))
                (y2 (ecurve::point-finite->y p2))
                (g (pfield::mul d
                                (pfield::mul x1
                                             (pfield::mul x2
                                                          (pfield::mul y1 y2 q)
                                                          q)
                                             q)
                                q)))
             (equal (ecurve::edwards-bls12-add p1 p2)
                    (ecurve::point-finite
                     (pfield::div (pfield::add (pfield::mul x1 y2 q)
                                               (pfield::mul y1 x2 q)
                                               q)
                                  (pfield::add 1 g q)
                                  q)
                     (pfield::div (pfield::sub (pfield::mul y1 y2 q)
                                               (pfield::mul a
                                                            (pfield::mul x1 x2 q)
                                                            q)
                                               q)
                                  (pfield::sub 1 g q)
                                  q)))))
  :hints (("Goal"
           :in-theory (e/d (ecurve::edwards-bls12-add
                            ecurve::twisted-edwards-add
                            ecurve::edwards-bls12-curve
                            ecurve::edwards-bls12-pointp
                            ecurve::point-finite-when-edwards-bls12-pointp
                            ecurve::pointp-when-edwards-bls12-pointp)
                           ((:e ecurve::twisted-edwards-curve-completep)
                            (:e ecurve::pfield-squarep)
                            (:e ecurve::edwards-bls12-q)
                            (:e ecurve::edwards-bls12-a)
                            (:e ecurve::edwards-bls12-d)
                            (:e ecurve::edwards-bls12-curve))))))

(defruled crv-group-add-from-coordinates
  (implies (and (equal p (base-prime))
                (primep p)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (pfield::fep x3 p)
                (pfield::fep y3 p)
                (equal (pfield::mul x3
                                    (pfield::add 1
                                                 (pfield::mul (ecurve::edwards-bls12-d)
                                                              (pfield::mul (pfield::mul x1 y2 p)
                                                                           (pfield::mul x2 y1 p)
                                                                           p)
                                                              p)
                                                 p)
                                    p)
                       (pfield::add (pfield::mul x1 y2 p)
                                    (pfield::mul x2 y1 p)
                                    p))
                (equal (pfield::mul y3
                                    (pfield::sub 1
                                                 (pfield::mul (ecurve::edwards-bls12-d)
                                                              (pfield::mul (pfield::mul x1 y2 p)
                                                                           (pfield::mul x2 y1 p)
                                                                           p)
                                                              p)
                                                 p)
                                    p)
                       (pfield::sub (pfield::mul y1 y2 p)
                                    (pfield::mul (ecurve::edwards-bls12-a)
                                                 (pfield::mul x1 x2 p)
                                                 p)
                                    p)))
           (equal (ecurve::edwards-bls12-add p1 p2)
                  (ecurve::point-finite x3 y3)))
  :hints (("Goal"
           :use (crv-edwards-bls12-add-to-divs
                 crv-add-dens-nonzero
                 (:instance crv-coord-matches-div
                            (x x3)
                            (y (pfield::add (pfield::mul x1 y2 p)
                                            (pfield::mul y1 x2 p)
                                            p))
                            (z (pfield::add
                                1
                                (pfield::mul (ecurve::edwards-bls12-d)
                                             (pfield::mul x1
                                                          (pfield::mul x2
                                                                       (pfield::mul y1 y2 p)
                                                                       p)
                                                          p)
                                             p)
                                p))
                            (p p))
                 (:instance crv-coord-matches-div
                            (x y3)
                            (y (pfield::sub (pfield::mul y1 y2 p)
                                            (pfield::mul (ecurve::edwards-bls12-a)
                                                         (pfield::mul x1 x2 p)
                                                         p)
                                            p))
                            (z (pfield::sub
                                1
                                (pfield::mul (ecurve::edwards-bls12-d)
                                             (pfield::mul x1
                                                          (pfield::mul x2
                                                                       (pfield::mul y1 y2 p)
                                                                       p)
                                                          p)
                                             p)
                                p))
                            (p p)))
           :in-theory (e/d (curve-base-prime-is-edwards-bls12-q
                            ecurve::equal-of-point-finite
                            ecurve::point-finite->x-of-point-finite
                            ecurve::point-finite->y-of-point-finite
                            ecurve::point-kind-of-point-finite
                            ecurve::pointp-of-point-finite
                            pfield::mul-commutative
                            pfield::mul-commutative-2
                            pfield::mul-associative
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::fep-of-add
                            pfield::fep-of-mul
                            pfield::fep-of-sub)
                           (crv-edwards-bls12-add-to-divs
                            crv-add-dens-nonzero
                            crv-coord-matches-div
                            ecurve::edwards-bls12-add
                            ecurve::twisted-edwards-add
                            nfix
                            (:e ecurve::edwards-bls12-q)
                            (:e ecurve::edwards-bls12-a)
                            (:e ecurve::edwards-bls12-d)
                            (:e ecurve::edwards-bls12-curve)
                            (:e ecurve::twisted-edwards-curve-completep)
                            (:e ecurve::pfield-squarep))))))

(defruled crv-group-add-from-equations
  (implies (and (equal p (base-prime))
                (primep p)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal x1 (ecurve::point-finite->x p1))
                (equal y1 (ecurve::point-finite->y p1))
                (equal x2 (ecurve::point-finite->x p2))
                (equal y2 (ecurve::point-finite->y p2))
                (pfield::fep x3 p)
                (pfield::fep y3 p)
                (equal u (pfield::mul (pfield::add x1 y1 p)
                                      (pfield::add x2 y2 p)
                                      p))
                (equal v0 (pfield::mul x1 y2 p))
                (equal v1 (pfield::mul x2 y1 p))
                (equal v01 (pfield::mul v0 v1 p))
                (equal (pfield::mul x3
                                    (pfield::add 1
                                                 (pfield::mul (ecurve::edwards-bls12-d)
                                                              v01 p)
                                                 p)
                                    p)
                       (pfield::add v0 v1 p))
                (equal (pfield::mul y3
                                    (pfield::sub 1
                                                 (pfield::mul (ecurve::edwards-bls12-d)
                                                              v01 p)
                                                 p)
                                    p)
                       (pfield::sub (pfield::sub u v0 p) v1 p)))
           (equal (ecurve::point-finite x3 y3)
                  (ecurve::edwards-bls12-add p1 p2)))
  :hints (("Goal"
           :use (crv-group-add-from-coordinates
                 (:instance crv-group-add-y-numerator
                            (a (pfield::neg 1 p)))
                 (:instance crv-fep-of-edwards-bls12-coords (pt p1))
                 (:instance crv-fep-of-edwards-bls12-coords (pt p2)))
           :in-theory (e/d (crv-edwards-a-is-neg-one
                            crv-edwards-gamma-product
                            curve-base-prime-is-edwards-bls12-q
                            pfield::mul-commutative
                            pfield::mul-commutative-2
                            pfield::mul-associative)
                           (crv-group-add-from-coordinates
                            crv-group-add-y-numerator
                            crv-fep-of-edwards-bls12-coords
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            ecurve::edwards-bls12-add
                            ecurve::twisted-edwards-add
                            nfix
                            (:e ecurve::edwards-bls12-q)
                            (:e ecurve::edwards-bls12-a)
                            (:e ecurve::edwards-bls12-d)
                            (:e base-prime)
                            ecurve::point-finite->x
                            ecurve::point-finite->y)))))

(defruled crv-group-add-gadget-sound
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
                 (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal x3 asg)
                                        (lookup-equal y3 asg))
                  (group-add-funspec p1 p2)))
  :use (:instance crv-group-add-from-equations
                  (x1 (ecurve::point-finite->x p1))
                  (y1 (ecurve::point-finite->y p1))
                  (x2 (ecurve::point-finite->x p2))
                  (y2 (ecurve::point-finite->y p2))
                  (u (lookup-equal u asg))
                  (v0 (lookup-equal v0 asg))
                  (v1 (lookup-equal v1 asg))
                  (v01 (lookup-equal v01 asg))
                  (x3 (lookup-equal x3 asg))
                  (y3 (lookup-equal y3 asg)))
  :enable (crv-group-add-gadget-to-products
           group-add-funspec
           r1cs::fep-of-lookup-equal)
  :disable (crv-group-add-from-equations))

; The canonical witnesses satisfy the add constraints only after
; (mul (div num den) den) = num is identified with the v01 product.
; That direction is not a theorem here; soundness is crv-group-add-gadget-sound.


(defruled crv-group-add-assign-gadget-sound
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
                 (crv-group-add-assign-gadget
                  x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal x3 asg)
                                        (lookup-equal y3 asg))
                  (group-add-assign-funspec p1 p2)))
  :use (:instance crv-group-add-gadget-sound)
  :enable (crv-group-add-assign-gadget
           group-add-assign-funspec)
  :disable (crv-group-add-gadget-sound))

(defruled crv-neg-point-coordinates
  (implies (and (equal p (base-prime))
                (ecurve::edwards-bls12-pointp pt))
           (and (equal (ecurve::point-finite->x (ecurve::edwards-bls12-neg pt))
                       (pfield::neg (ecurve::point-finite->x pt) p))
                (equal (ecurve::point-finite->y (ecurve::edwards-bls12-neg pt))
                       (ecurve::point-finite->y pt))
                (ecurve::edwards-bls12-pointp (ecurve::edwards-bls12-neg pt))))
  :hints (("Goal"
           :use ((:instance ecurve::point-on-twisted-edwards-p-of-twisted-edwards-neg
                            (point pt)
                            (curve (ecurve::edwards-bls12-curve)))
                 ecurve::twisted-edwards-curve-completep-of-edwards-bls12-curve)
           :in-theory (e/d (ecurve::edwards-bls12-neg
                            ecurve::twisted-edwards-neg
                            ecurve::edwards-bls12-curve
                            ecurve::edwards-bls12-pointp
                            ecurve::point-finite->x-of-point-finite
                            ecurve::point-finite->y-of-point-finite
                            curve-base-prime-is-edwards-bls12-q
                            pfield::natp-of-neg
                            acl2::nfix-when-natp)
                           (ecurve::point-finite->x
                            ecurve::point-finite->y
                            ecurve::point-on-twisted-edwards-p
                            ecurve::point-on-twisted-edwards-p-of-twisted-edwards-neg
                            (:e ecurve::edwards-bls12-q)
                            (:e base-prime)
                            (:e ecurve::twisted-edwards-curve-completep)
                            (:e ecurve::pfield-squarep)
                            nfix
                            pfield::fep-of-neg)))))

(defruled crv-group-sub-gadget-to-products
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
                (x2$ (pfield::neg (lookup-equal x2 asg) p))
                (y2$ (lookup-equal y2 asg))
                (u$ (lookup-equal u asg))
                (v0$ (lookup-equal v0 asg))
                (v1$ (lookup-equal v1 asg))
                (v01$ (lookup-equal v01 asg))
                (x3$ (lookup-equal x3 asg))
                (y3$ (lookup-equal y3 asg))
                (d (ecurve::edwards-bls12-d)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crv-group-sub-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
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
  :enable (crv-group-sub-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           crv-neg-one-is-p-minus-one))

; Subtraction is addition of (x1,y1) and (-x2,y2).  The negated
; coordinates are crv-neg-point-coordinates; the sum equality is not
; connected to the sub gadget in a theorem here.
; Doubling is add(P,P).  That identification is not a theorem here.


(defconst *crv-group-add-sample*
  '((x1 . 0) (y1 . 1) (x2 . 0) (y2 . 1)
    (u . 1) (v0 . 0) (v1 . 0) (v01 . 0)
    (x3 . 0) (y3 . 1)))

(defruled crv-group-add-sample-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp *crv-group-add-sample* p)
                (fieldp 0)
                (fieldp 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-add-gadget
             'x1 'y1 'x2 'y2 'u 'v0 'v1 'v01 'x3 'y3 p)
            *crv-group-add-sample* p))
  :enable (crv-group-add-gadget-to-products
           lookup-equal)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

(defconst *crv-group-sub-sample*
  *crv-group-add-sample*)

(defruled crv-group-sub-sample-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp *crv-group-sub-sample* p)
                (fieldp 0)
                (fieldp 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-sub-gadget
             'x1 'y1 'x2 'y2 'u 'v0 'v1 'v01 'x3 'y3 p)
            *crv-group-sub-sample* p))
  :enable (crv-group-sub-gadget-to-products
           lookup-equal)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::neg))

(defruled crv-group-double-gadget-to-products
  (implies (and (symbolp x) (symbolp y)
                (symbolp xy) (symbolp x2) (symbolp y2)
                (symbolp x3) (symbolp y3)
                (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg xy)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (xy$ (lookup-equal xy asg))
                (x2$ (lookup-equal x2 asg))
                (y2$ (lookup-equal y2 asg))
                (x3$ (lookup-equal x3 asg))
                (y3$ (lookup-equal y3 asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crv-group-double-gadget x y xy x2 y2 x3 y3 p)
                     asg p)
                    (and (equal xy$ (pfield::mul x$ y$ p))
                         (equal x2$ (pfield::mul x$ x$ p))
                         (equal y2$ (pfield::mul y$ y$ p))
                         (equal (pfield::mul x3$ (pfield::sub y2$ x2$ p) p)
                                (pfield::mul 2 xy$ p))
                         (equal (pfield::mul y3$
                                             (pfield::sub 2 (pfield::sub y2$ x2$ p) p)
                                             p)
                                (pfield::add y2$ x2$ p))))))
  :enable (crv-group-double-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           crv-neg-one-is-p-minus-one))


(defconst *crv-group-double-sample*
  '((x . 0) (y . 1) (xy . 0) (x2 . 0) (y2 . 1) (x3 . 0) (y3 . 1)))

(defruled crv-group-double-sample-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp *crv-group-double-sample* p)
                (fieldp 0)
                (fieldp 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-double-gadget 'x 'y 'xy 'x2 'y2 'x3 'y3 p)
            *crv-group-double-sample* p))
  :enable (crv-group-double-gadget-to-products
           lookup-equal)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))
