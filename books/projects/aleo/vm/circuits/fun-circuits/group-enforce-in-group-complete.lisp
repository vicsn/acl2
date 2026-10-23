; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE of Group::new / enforce_in_group.
;
; For a groupp point P the cofactor witness is Q = k P with k = 4^-1 mod r
; (group-cofactor-witness).  Scalar multiplication distributes over scalar
; addition now that edwards-bls12-add is associative
; (twisted-edwards-add-associativity-holds), so 2Q + 2Q = (4k) P.  Since
; 4k = 1 mod r and r P = 0, that is P.  The zero point has Q = 0.
;
; The other wires are the products and the coordinates of 2Q that the
; gadget computes.  On a curve point the doubling denominators are
; nonzero, so the doubling coordinates satisfy the two enforces.
;
; The converse (no assignment when the input is not groupp) is the
; contrapositive of group-enforce-in-group-sound and so takes the
; hypothesis edwards-bls12-cofactor-clears.

(in-package "ALEOVM")

(include-book "group-inject-sound")
(include-book "../edwards-assoc/edwards-bls12-associativity")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system))

(local (in-theory (disable (:e base-prime) (:e scalar-prime)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The witness Q = k P and 2Q + 2Q = P.

(define group-cofactor-inverse ()
  :returns (k natp)
  :short "The inverse of the cofactor 4 modulo the subgroup order @($r$),
          that is @($(r + 1) / 4$)."
  527778859339273151515551558673846658209717731602102048798421311598680340096
  ///
  (in-theory (disable (:e group-cofactor-inverse))))

(defruledl group-cofactor-inverse-times-4
  (equal (mod (+ (group-cofactor-inverse)
                 (+ (group-cofactor-inverse)
                    (+ (group-cofactor-inverse) (group-cofactor-inverse))))
              (ecurve::edwards-bls12-r))
         1)
  :in-theory '((:e group-cofactor-inverse)
               (:e ecurve::edwards-bls12-r)
               (:e mod)
               (:e binary-+)))

(define group-cofactor-witness ((pt ecurve::edwards-bls12-pointp))
  :returns (q ecurve::edwards-bls12-pointp :hyp :guard)
  :short "The cofactor witness @($Q = (4^{-1} \\bmod r) P$) that
          @('enforce_in_group') allocates for the point @($P$)."
  (ecurve::edwards-bls12-mul (group-cofactor-inverse) pt))

(defruledl group-complete-add-of-mul
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (integerp a)
                (integerp b))
           (equal (ecurve::edwards-bls12-add (ecurve::edwards-bls12-mul a pt)
                                             (ecurve::edwards-bls12-mul b pt))
                  (ecurve::edwards-bls12-mul (+ a b) pt)))
  :use (:instance ecurve::twisted-edwards-mul-of-scalar-addition-converse
                  (scalar1 a)
                  (scalar2 b)
                  (point pt)
                  (curve (ecurve::edwards-bls12-curve)))
  :enable (ecurve::edwards-bls12-add
           ecurve::edwards-bls12-mul
           ecurve::edwards-bls12-pointp))

(defruledl group-complete-mul-4k
  (implies (groupp pt)
           (equal (ecurve::edwards-bls12-mul
                   (+ (group-cofactor-inverse)
                      (+ (group-cofactor-inverse)
                         (+ (group-cofactor-inverse) (group-cofactor-inverse))))
                   pt)
                  pt))
  :hints (("Goal"
           :cases ((equal pt (ecurve::twisted-edwards-zero)))
           :use ((:instance ecurve::twisted-edwards-mul-of-mod-order
                            (scalar
                             (+ (group-cofactor-inverse)
                                (+ (group-cofactor-inverse)
                                   (+ (group-cofactor-inverse)
                                      (group-cofactor-inverse)))))
                            (point pt)
                            (order (ecurve::edwards-bls12-r))
                            (curve (ecurve::edwards-bls12-curve)))
                 group-cofactor-inverse-times-4)
           :in-theory (e/d (groupp
                            ecurve::edwards-bls12-r-pointp
                            ecurve::edwards-bls12-pointp
                            ecurve::edwards-bls12-mul)
                           (ecurve::twisted-edwards-mul-of-mod-order)))))

(defruled group-cofactor-witness-4q
  :short "The witness is a curve point and @($2Q + 2Q = P$) under
          @(tsee ecurve::edwards-bls12-add), for every @(tsee groupp)
          point @($P$)."
  (implies (groupp pt)
           (and (ecurve::edwards-bls12-pointp (group-cofactor-witness pt))
                (equal (ecurve::edwards-bls12-add
                        (ecurve::edwards-bls12-add (group-cofactor-witness pt)
                                                   (group-cofactor-witness pt))
                        (ecurve::edwards-bls12-add (group-cofactor-witness pt)
                                                   (group-cofactor-witness pt)))
                       pt)))
  :enable (group-cofactor-witness
           groupp
           group-complete-add-of-mul
           group-complete-mul-4k))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field equations of a curve point and of its double.

(defruledl group-complete-q-is-base-prime
  (equal (ecurve::edwards-bls12-q) (base-prime))
  :in-theory '((:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruledl group-complete-posp-base-prime
  (posp (base-prime))
  :in-theory '((:e base-prime) (:e posp)))

(defruledl group-complete-point-coordinates
  (implies (ecurve::edwards-bls12-pointp q)
           (and (equal (ecurve::point-finite (ecurve::point-finite->x q)
                                             (ecurve::point-finite->y q))
                       q)
                (pfield::fep (ecurve::point-finite->x q) (base-prime))
                (pfield::fep (ecurve::point-finite->y q) (base-prime))))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           group-complete-q-is-base-prime
           pfield::fep))

(defruledl group-complete-on-curve-xy
  (implies (and (equal p (base-prime))
                (pfield::fep x0 p)
                (pfield::fep y0 p)
                (ecurve::edwards-bls12-pointp (ecurve::point-finite x0 y0)))
           (equal (pfield::add (pfield::mul (ecurve::edwards-bls12-a)
                                            (pfield::mul x0 x0 p) p)
                               (pfield::mul y0 y0 p) p)
                  (pfield::add 1
                               (pfield::mul (ecurve::edwards-bls12-d)
                                            (pfield::mul (pfield::mul x0 x0 p)
                                                         (pfield::mul y0 y0 p)
                                                         p)
                                            p)
                               p)))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           group-complete-q-is-base-prime
           pfield::fep))

(defruledl group-complete-on-curve-equation-iff
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p))
           (equal (group-on-curve-equation y2 x2 p)
                  (equal (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                      y2 p)
                         (pfield::add 1
                                      (pfield::mul (ecurve::edwards-bls12-d)
                                                   (pfield::mul x2 y2 p)
                                                   p)
                                      p))))
  :enable (group-on-curve-equation))

(defruledl group-complete-on-curve-of-coordinates
  (implies (and (equal p (base-prime))
                (pfield::fep qx p)
                (pfield::fep qy p)
                (ecurve::edwards-bls12-pointp (ecurve::point-finite qx qy)))
           (group-on-curve-equation (pfield::mul qy qy p)
                                    (pfield::mul qx qx p)
                                    p))
  :use ((:instance group-complete-on-curve-equation-iff
                   (x2 (pfield::mul qx qx p))
                   (y2 (pfield::mul qy qy p)))
        (:instance group-complete-on-curve-xy (x0 qx) (y0 qy)))
  :in-theory '(pfield::fep-of-mul group-complete-posp-base-prime))

(defruled group-on-curve-complete
  :short "A curve point satisfies @('enforce_on_curve') on the squares of
          its coordinates."
  (implies (and (equal p (base-prime))
                (ecurve::edwards-bls12-pointp q))
           (group-on-curve-equation
            (pfield::mul (ecurve::point-finite->y q)
                         (ecurve::point-finite->y q)
                         p)
            (pfield::mul (ecurve::point-finite->x q)
                         (ecurve::point-finite->x q)
                         p)
            p))
  :use (:instance group-complete-on-curve-of-coordinates
                  (qx (ecurve::point-finite->x q))
                  (qy (ecurve::point-finite->y q)))
  :in-theory '(group-complete-point-coordinates))

(defruledl group-complete-mul-div-of-equal
  (implies (and (primep p)
                (pfield::fep n p)
                (pfield::fep f p)
                (not (equal f 0))
                (equal e f))
           (equal (pfield::mul (pfield::div n f p) e p) n))
  :enable pfield::div)

(defruledl group-complete-sub-2-of-add-1
  (implies (primep p)
           (equal (pfield::sub 2 (pfield::add 1 w p) p)
                  (pfield::sub 1 w p))))

(defruledl group-complete-double-x
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (pfield::fep xy p)
                (equal (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                    y2 p)
                       (pfield::add 1
                                    (pfield::mul (ecurve::edwards-bls12-d)
                                                 (pfield::mul x2 y2 p)
                                                 p)
                                    p))
                (not (equal (pfield::add 1
                                         (pfield::mul (ecurve::edwards-bls12-d)
                                                      (pfield::mul x2 y2 p)
                                                      p)
                                         p)
                            0)))
           (group-double-x-equation
            (pfield::div (pfield::mul 2 xy p)
                         (pfield::add 1
                                      (pfield::mul (ecurve::edwards-bls12-d)
                                                   (pfield::mul x2 y2 p)
                                                   p)
                                      p)
                         p)
            x2 y2 xy p))
  :use (:instance group-complete-mul-div-of-equal
                  (n (pfield::mul 2 xy p))
                  (e (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                  y2 p))
                  (f (pfield::add 1
                                  (pfield::mul (ecurve::edwards-bls12-d)
                                               (pfield::mul x2 y2 p)
                                               p)
                                  p)))
  :in-theory '(group-double-x-equation
               primep-of-base-prime
               group-complete-posp-base-prime
               pfield::fep-of-mul
               pfield::fep-of-add))

(defruledl group-complete-double-y
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (equal (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                    y2 p)
                       (pfield::add 1
                                    (pfield::mul (ecurve::edwards-bls12-d)
                                                 (pfield::mul x2 y2 p)
                                                 p)
                                    p))
                (not (equal (pfield::sub 1
                                         (pfield::mul (ecurve::edwards-bls12-d)
                                                      (pfield::mul x2 y2 p)
                                                      p)
                                         p)
                            0)))
           (group-double-y-equation
            (pfield::div (pfield::sub y2
                                      (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                      p)
                         (pfield::sub 1
                                      (pfield::mul (ecurve::edwards-bls12-d)
                                                   (pfield::mul x2 y2 p)
                                                   p)
                                      p)
                         p)
            x2 y2 p))
  :use ((:instance group-complete-mul-div-of-equal
                   (n (pfield::sub y2
                                   (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                   p))
                   (e (pfield::sub 2
                                   (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                                y2 p)
                                   p))
                   (f (pfield::sub 1
                                   (pfield::mul (ecurve::edwards-bls12-d)
                                                (pfield::mul x2 y2 p)
                                                p)
                                   p)))
        (:instance group-complete-sub-2-of-add-1
                   (w (pfield::mul (ecurve::edwards-bls12-d)
                                   (pfield::mul x2 y2 p)
                                   p))))
  :in-theory '(group-double-y-equation
               primep-of-base-prime
               group-complete-posp-base-prime
               pfield::fep-of-sub))

(defruledl group-complete-add-same
  (equal (pfield::add x x p)
         (pfield::mul 2 x p))
  :enable (pfield::add pfield::mul)
  :cases ((equal (+ (ifix x) (ifix x)) (* 2 (ifix x)))))

(defruledl group-complete-add-self
  (implies (and (equal p (base-prime))
                (pfield::fep x0 p)
                (pfield::fep y0 p))
           (equal (ecurve::edwards-bls12-add (ecurve::point-finite x0 y0)
                                             (ecurve::point-finite x0 y0))
                  (ecurve::point-finite
                   (pfield::div (pfield::mul 2 (pfield::mul x0 y0 p) p)
                                (pfield::add 1
                                             (pfield::mul (ecurve::edwards-bls12-d)
                                                          (pfield::mul (pfield::mul x0 x0 p)
                                                                       (pfield::mul y0 y0 p)
                                                                       p)
                                                          p)
                                             p)
                                p)
                   (pfield::div (pfield::sub (pfield::mul y0 y0 p)
                                             (pfield::mul (ecurve::edwards-bls12-a)
                                                          (pfield::mul x0 x0 p)
                                                          p)
                                             p)
                                (pfield::sub 1
                                             (pfield::mul (ecurve::edwards-bls12-d)
                                                          (pfield::mul (pfield::mul x0 x0 p)
                                                                       (pfield::mul y0 y0 p)
                                                                       p)
                                                          p)
                                             p)
                                p))))
  :enable (ecurve::edwards-bls12-add
           ecurve::twisted-edwards-add
           ecurve::edwards-bls12-curve
           group-complete-q-is-base-prime
           group-complete-add-same
           pfield::fep))

(defruledl group-complete-denominators-not-0
  (implies (and (equal p (base-prime))
                (pfield::fep x0 p)
                (pfield::fep y0 p)
                (ecurve::edwards-bls12-pointp (ecurve::point-finite x0 y0)))
           (b* ((w (pfield::mul (ecurve::edwards-bls12-d)
                                (pfield::mul (pfield::mul x0 x0 p)
                                             (pfield::mul y0 y0 p)
                                             p)
                                p)))
             (and (not (equal (pfield::add 1 w p) 0))
                  (not (equal (pfield::sub 1 w p) 0)))))
  :use (ecurve::twisted-edwards-curve-completep-of-edwards-bls12-curve
        (:instance ecurve::1+d.x1.x2.y1.y2-not-0
                   (curve (ecurve::edwards-bls12-curve))
                   (point1 (ecurve::point-finite x0 y0))
                   (point2 (ecurve::point-finite x0 y0)))
        (:instance ecurve::1-d.x1.x2.y1.y2-not-0
                   (curve (ecurve::edwards-bls12-curve))
                   (point1 (ecurve::point-finite x0 y0))
                   (point2 (ecurve::point-finite x0 y0))))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::edwards-bls12-curve
           group-complete-q-is-base-prime
           pfield::fep))

(defruledl group-complete-nfix-of-div
  (implies (posp p)
           (equal (nfix (pfield::div x y p))
                  (pfield::div x y p))))

(defruledl group-complete-double-of-coordinates
  (implies (and (equal p (base-prime))
                (pfield::fep x0 p)
                (pfield::fep y0 p)
                (ecurve::edwards-bls12-pointp (ecurve::point-finite x0 y0)))
           (b* ((q (ecurve::point-finite x0 y0))
                (q2 (ecurve::edwards-bls12-add q q)))
             (and (group-double-x-equation (ecurve::point-finite->x q2)
                                           (pfield::mul x0 x0 p)
                                           (pfield::mul y0 y0 p)
                                           (pfield::mul x0 y0 p)
                                           p)
                  (group-double-y-equation (ecurve::point-finite->y q2)
                                           (pfield::mul x0 x0 p)
                                           (pfield::mul y0 y0 p)
                                           p))))
  :use (group-complete-add-self
        group-complete-on-curve-xy
        group-complete-denominators-not-0
        (:instance group-complete-double-x
                   (x2 (pfield::mul x0 x0 p))
                   (y2 (pfield::mul y0 y0 p))
                   (xy (pfield::mul x0 y0 p)))
        (:instance group-complete-double-y
                   (x2 (pfield::mul x0 x0 p))
                   (y2 (pfield::mul y0 y0 p))))
  :in-theory '(pfield::fep-of-mul
               group-complete-posp-base-prime
               group-complete-nfix-of-div
               ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite))

(defruled group-double-complete
  :short "The coordinates of @($2Q$) satisfy the two doubling enforces
          on the products of the coordinates of a curve point @($Q$)."
  (implies (and (equal p (base-prime))
                (ecurve::edwards-bls12-pointp q))
           (b* ((qx (ecurve::point-finite->x q))
                (qy (ecurve::point-finite->y q))
                (q2 (ecurve::edwards-bls12-add q q)))
             (and (group-double-x-equation (ecurve::point-finite->x q2)
                                           (pfield::mul qx qx p)
                                           (pfield::mul qy qy p)
                                           (pfield::mul qx qy p)
                                           p)
                  (group-double-y-equation (ecurve::point-finite->y q2)
                                           (pfield::mul qx qx p)
                                           (pfield::mul qy qy p)
                                           p))))
  :use (:instance group-complete-double-of-coordinates
                  (x0 (ecurve::point-finite->x q))
                  (y0 (ecurve::point-finite->y q)))
  :in-theory '(group-complete-point-coordinates))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The wire values of the witness, in gadget order.

(define group-cofactor-double ((pt ecurve::edwards-bls12-pointp))
  :returns (q2 ecurve::edwards-bls12-pointp :hyp :guard)
  :short "The point @($2Q$) that @('double') computes from the witness."
  (b* ((q (group-cofactor-witness pt)))
    (ecurve::edwards-bls12-add q q)))

(defruled group-enforce-in-group-equations-complete
  :short "For every @(tsee groupp) point @($P$), the witness
          @($Q = (4^{-1} \\bmod r) P$), its products, @($2Q$) and the products
          of @($2Q$) satisfy the @('enforce_in_group') equations with
          @($P$)'s coordinates as the input."
  (implies (and (equal p (base-prime))
                (groupp pt))
           (b* ((q (group-cofactor-witness pt))
                (qx (ecurve::point-finite->x q))
                (qy (ecurve::point-finite->y q))
                (q2 (group-cofactor-double pt))
                (x3 (ecurve::point-finite->x q2))
                (y3 (ecurve::point-finite->y q2)))
             (group-enforce-in-group-equations
              (ecurve::point-finite->x pt) (ecurve::point-finite->y pt)
              qx qy
              (pfield::mul qx qx p) (pfield::mul qy qy p)
              (pfield::mul qx qy p) (pfield::mul qx qx p) (pfield::mul qy qy p)
              x3 y3
              (pfield::mul x3 y3 p) (pfield::mul x3 x3 p) (pfield::mul y3 y3 p)
              p)))
  :do-not-induct t
  :use ((:instance group-on-curve-complete (q (group-cofactor-witness pt)))
        (:instance group-double-complete (q (group-cofactor-witness pt)))
        (:instance group-double-complete (q (group-cofactor-double pt))))
  :in-theory '(group-enforce-in-group-equations
               group-cofactor-double
               group-cofactor-witness-4q
               ecurve::edwards-bls12-pointp-of-edwards-bls12-add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled group-enforce-in-group-gadget-complete
  :short "R1CS-COMPLETE of @('enforce_in_group'): for every
          @(tsee groupp) point @($P$), an assignment that binds the input
          wires to @($P$)'s coordinates and the private wires to the witness
          values satisfies the gadget."
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (groupp pt)
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
                (r1cs::valuation-bindsp asg ey2)
                (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                (equal (lookup-equal qx asg)
                       (ecurve::point-finite->x (group-cofactor-witness pt)))
                (equal (lookup-equal qy asg)
                       (ecurve::point-finite->y (group-cofactor-witness pt)))
                (equal (lookup-equal cx2 asg)
                       (pfield::mul (lookup-equal qx asg) (lookup-equal qx asg) p))
                (equal (lookup-equal cy2 asg)
                       (pfield::mul (lookup-equal qy asg) (lookup-equal qy asg) p))
                (equal (lookup-equal dxy asg)
                       (pfield::mul (lookup-equal qx asg) (lookup-equal qy asg) p))
                (equal (lookup-equal dx2 asg)
                       (pfield::mul (lookup-equal qx asg) (lookup-equal qx asg) p))
                (equal (lookup-equal dy2 asg)
                       (pfield::mul (lookup-equal qy asg) (lookup-equal qy asg) p))
                (equal (lookup-equal x3 asg)
                       (ecurve::point-finite->x (group-cofactor-double pt)))
                (equal (lookup-equal y3 asg)
                       (ecurve::point-finite->y (group-cofactor-double pt)))
                (equal (lookup-equal exy asg)
                       (pfield::mul (lookup-equal x3 asg) (lookup-equal y3 asg) p))
                (equal (lookup-equal ex2 asg)
                       (pfield::mul (lookup-equal x3 asg) (lookup-equal x3 asg) p))
                (equal (lookup-equal ey2 asg)
                       (pfield::mul (lookup-equal y3 asg) (lookup-equal y3 asg) p)))
           (r1cs::r1cs-constraints-holdp
            (group-enforce-in-group-gadget
             x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
            asg p))
  :do-not-induct t
  :use (group-enforce-in-group-gadget-to-equations
        group-enforce-in-group-equations-complete)
  :in-theory nil)

(define group-enforce-in-group-witness-lookupsp
  ((x symbolp) (y symbolp)
   (qx symbolp) (qy symbolp)
   (cx2 symbolp) (cy2 symbolp)
   (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
   (x3 symbolp) (y3 symbolp)
   (exy symbolp) (ex2 symbolp) (ey2 symbolp)
   (pt groupp)
   (asg alistp)
   (p primep))
  :returns (yes/no booleanp)
  :short "The hypotheses on the wires of
          @(tsee group-enforce-in-group-gadget-complete): the input wires are
          @($P$)'s coordinates and the private wires hold the witness
          values."
  :verify-guards nil
  (and (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
       (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
       (equal (lookup-equal qx asg)
              (ecurve::point-finite->x (group-cofactor-witness pt)))
       (equal (lookup-equal qy asg)
              (ecurve::point-finite->y (group-cofactor-witness pt)))
       (equal (lookup-equal cx2 asg)
              (pfield::mul (lookup-equal qx asg) (lookup-equal qx asg) p))
       (equal (lookup-equal cy2 asg)
              (pfield::mul (lookup-equal qy asg) (lookup-equal qy asg) p))
       (equal (lookup-equal dxy asg)
              (pfield::mul (lookup-equal qx asg) (lookup-equal qy asg) p))
       (equal (lookup-equal dx2 asg)
              (pfield::mul (lookup-equal qx asg) (lookup-equal qx asg) p))
       (equal (lookup-equal dy2 asg)
              (pfield::mul (lookup-equal qy asg) (lookup-equal qy asg) p))
       (equal (lookup-equal x3 asg)
              (ecurve::point-finite->x (group-cofactor-double pt)))
       (equal (lookup-equal y3 asg)
              (ecurve::point-finite->y (group-cofactor-double pt)))
       (equal (lookup-equal exy asg)
              (pfield::mul (lookup-equal x3 asg) (lookup-equal y3 asg) p))
       (equal (lookup-equal ex2 asg)
              (pfield::mul (lookup-equal x3 asg) (lookup-equal x3 asg) p))
       (equal (lookup-equal ey2 asg)
              (pfield::mul (lookup-equal y3 asg) (lookup-equal y3 asg) p))))

(defruled group-enforce-in-group-equations-when-witness-lookupsp
  :short "Wires that hold the witness values for a @(tsee groupp) point
          satisfy @(tsee group-enforce-in-group-equations)."
  (implies (and (equal p (base-prime))
                (groupp pt)
                (group-enforce-in-group-witness-lookupsp
                 x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 pt asg p))
           (group-enforce-in-group-equations
            (lookup-equal x asg) (lookup-equal y asg)
            (lookup-equal qx asg) (lookup-equal qy asg)
            (lookup-equal cx2 asg) (lookup-equal cy2 asg)
            (lookup-equal dxy asg) (lookup-equal dx2 asg)
            (lookup-equal dy2 asg)
            (lookup-equal x3 asg) (lookup-equal y3 asg)
            (lookup-equal exy asg) (lookup-equal ex2 asg)
            (lookup-equal ey2 asg)
            p))
  :use group-enforce-in-group-equations-complete
  :in-theory '(group-enforce-in-group-witness-lookupsp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An explicit satisfying assignment, for distinct wire names.

(define group-enforce-in-group-assignment
  ((x symbolp) (y symbolp)
   (qx symbolp) (qy symbolp)
   (cx2 symbolp) (cy2 symbolp)
   (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
   (x3 symbolp) (y3 symbolp)
   (exy symbolp) (ex2 symbolp) (ey2 symbolp)
   (pt groupp))
  :short "The assignment of @('enforce_in_group') for the input @($P$)."
  :verify-guards nil
  (b* ((p (base-prime))
       (q (group-cofactor-witness pt))
       (qx$ (ecurve::point-finite->x q))
       (qy$ (ecurve::point-finite->y q))
       (q2 (group-cofactor-double pt))
       (x3$ (ecurve::point-finite->x q2))
       (y3$ (ecurve::point-finite->y q2)))
    (list (cons x (ecurve::point-finite->x pt))
          (cons y (ecurve::point-finite->y pt))
          (cons qx qx$)
          (cons qy qy$)
          (cons cx2 (pfield::mul qx$ qx$ p))
          (cons cy2 (pfield::mul qy$ qy$ p))
          (cons dxy (pfield::mul qx$ qy$ p))
          (cons dx2 (pfield::mul qx$ qx$ p))
          (cons dy2 (pfield::mul qy$ qy$ p))
          (cons x3 x3$)
          (cons y3 y3$)
          (cons exy (pfield::mul x3$ y3$ p))
          (cons ex2 (pfield::mul x3$ x3$ p))
          (cons ey2 (pfield::mul y3$ y3$ p)))))

(defruledl group-complete-groupp-coordinates
  (implies (groupp pt)
           (and (pfield::fep (ecurve::point-finite->x pt) (base-prime))
                (pfield::fep (ecurve::point-finite->y pt) (base-prime))))
  :use (:instance group-complete-point-coordinates (q pt))
  :enable groupp)

(defmacro group-complete-asg ()
  '(group-enforce-in-group-assignment
    x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 pt))

(defmacro group-complete-wires-distinct ()
  '(no-duplicatesp-equal
    (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2)))

(defruledl group-complete-member-strip-cars
  (implies (member-equal (cons key val) al)
           (member-equal key (strip-cars al))))

(defruledl group-complete-lookup-when-member
  (implies (and (no-duplicatesp-equal (strip-cars al))
                (member-equal (cons key val) al))
           (equal (lookup-equal key al) val))
  :enable (lookup-equal group-complete-member-strip-cars))

(defruledl group-complete-member-cons-same
  (member-equal x (cons x l)))

(defruledl group-complete-member-cons-later
  (implies (member-equal x l)
           (member-equal x (cons y l))))

(defruledl group-complete-assignment-lookups
  (implies (group-complete-wires-distinct)
           (and (equal (lookup-equal x (group-complete-asg))
                       (ecurve::point-finite->x pt))
                (equal (lookup-equal y (group-complete-asg))
                       (ecurve::point-finite->y pt))
                (equal (lookup-equal qx (group-complete-asg))
                       (ecurve::point-finite->x (group-cofactor-witness pt)))
                (equal (lookup-equal qy (group-complete-asg))
                       (ecurve::point-finite->y (group-cofactor-witness pt)))
                (equal (lookup-equal cx2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                    (ecurve::point-finite->x (group-cofactor-witness pt))
                                    (base-prime)))
                (equal (lookup-equal cy2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->y (group-cofactor-witness pt))
                                    (ecurve::point-finite->y (group-cofactor-witness pt))
                                    (base-prime)))
                (equal (lookup-equal dxy (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                    (ecurve::point-finite->y (group-cofactor-witness pt))
                                    (base-prime)))
                (equal (lookup-equal dx2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                    (ecurve::point-finite->x (group-cofactor-witness pt))
                                    (base-prime)))
                (equal (lookup-equal dy2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->y (group-cofactor-witness pt))
                                    (ecurve::point-finite->y (group-cofactor-witness pt))
                                    (base-prime)))
                (equal (lookup-equal x3 (group-complete-asg))
                       (ecurve::point-finite->x (group-cofactor-double pt)))
                (equal (lookup-equal y3 (group-complete-asg))
                       (ecurve::point-finite->y (group-cofactor-double pt)))
                (equal (lookup-equal exy (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->x (group-cofactor-double pt))
                                    (ecurve::point-finite->y (group-cofactor-double pt))
                                    (base-prime)))
                (equal (lookup-equal ex2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->x (group-cofactor-double pt))
                                    (ecurve::point-finite->x (group-cofactor-double pt))
                                    (base-prime)))
                (equal (lookup-equal ey2 (group-complete-asg))
                       (pfield::mul (ecurve::point-finite->y (group-cofactor-double pt))
                                    (ecurve::point-finite->y (group-cofactor-double pt))
                                    (base-prime)))))
  :use ((:instance group-complete-lookup-when-member
                   (key x) (al (group-complete-asg))
                   (val (ecurve::point-finite->x pt)))
        (:instance group-complete-lookup-when-member
                   (key y) (al (group-complete-asg))
                   (val (ecurve::point-finite->y pt)))
        (:instance group-complete-lookup-when-member
                   (key qx) (al (group-complete-asg))
                   (val (ecurve::point-finite->x (group-cofactor-witness pt))))
        (:instance group-complete-lookup-when-member
                   (key qy) (al (group-complete-asg))
                   (val (ecurve::point-finite->y (group-cofactor-witness pt))))
        (:instance group-complete-lookup-when-member
                   (key cx2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                     (ecurve::point-finite->x (group-cofactor-witness pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key cy2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->y (group-cofactor-witness pt))
                                     (ecurve::point-finite->y (group-cofactor-witness pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key dxy) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                     (ecurve::point-finite->y (group-cofactor-witness pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key dx2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->x (group-cofactor-witness pt))
                                     (ecurve::point-finite->x (group-cofactor-witness pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key dy2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->y (group-cofactor-witness pt))
                                     (ecurve::point-finite->y (group-cofactor-witness pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key x3) (al (group-complete-asg))
                   (val (ecurve::point-finite->x (group-cofactor-double pt))))
        (:instance group-complete-lookup-when-member
                   (key y3) (al (group-complete-asg))
                   (val (ecurve::point-finite->y (group-cofactor-double pt))))
        (:instance group-complete-lookup-when-member
                   (key exy) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->x (group-cofactor-double pt))
                                     (ecurve::point-finite->y (group-cofactor-double pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key ex2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->x (group-cofactor-double pt))
                                     (ecurve::point-finite->x (group-cofactor-double pt))
                                     (base-prime))))
        (:instance group-complete-lookup-when-member
                   (key ey2) (al (group-complete-asg))
                   (val (pfield::mul (ecurve::point-finite->y (group-cofactor-double pt))
                                     (ecurve::point-finite->y (group-cofactor-double pt))
                                     (base-prime)))))
  :in-theory '(group-enforce-in-group-assignment
               strip-cars
               car-cons
               cdr-cons
               group-complete-member-cons-same
               group-complete-member-cons-later))

(defruledl group-complete-assignment-binds
  (and (r1cs::valuation-bindsp (group-complete-asg) x)
       (r1cs::valuation-bindsp (group-complete-asg) y)
       (r1cs::valuation-bindsp (group-complete-asg) qx)
       (r1cs::valuation-bindsp (group-complete-asg) qy)
       (r1cs::valuation-bindsp (group-complete-asg) cx2)
       (r1cs::valuation-bindsp (group-complete-asg) cy2)
       (r1cs::valuation-bindsp (group-complete-asg) dxy)
       (r1cs::valuation-bindsp (group-complete-asg) dx2)
       (r1cs::valuation-bindsp (group-complete-asg) dy2)
       (r1cs::valuation-bindsp (group-complete-asg) x3)
       (r1cs::valuation-bindsp (group-complete-asg) y3)
       (r1cs::valuation-bindsp (group-complete-asg) exy)
       (r1cs::valuation-bindsp (group-complete-asg) ex2)
       (r1cs::valuation-bindsp (group-complete-asg) ey2))
  :in-theory '(group-enforce-in-group-assignment
               r1cs::valuation-bindsp
               strip-cars
               member-equal
               car-cons
               cdr-cons))

(defruledl group-complete-assignment-valuationp
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (group-complete-wires-distinct)
                (groupp pt))
           (r1cs::r1cs-valuationp (group-complete-asg) (base-prime)))
  :use (group-complete-groupp-coordinates
        (:instance group-complete-point-coordinates
                   (q (group-cofactor-witness pt)))
        (:instance group-complete-point-coordinates
                   (q (group-cofactor-double pt)))
        group-cofactor-witness-4q
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (point1 (group-cofactor-witness pt))
                   (point2 (group-cofactor-witness pt))))
  :in-theory '(group-enforce-in-group-assignment
               group-cofactor-double
               r1cs::r1cs-valuationp
               r1cs::var-listp
               alistp
               symbol-listp
               strip-cars
               strip-cdrs
               pfield::fe-listp
               pfield::fep-of-mul
               group-complete-posp-base-prime
               car-cons
               cdr-cons))

(defruled group-enforce-in-group-gadget-satisfiable
  :short "For every @(tsee groupp) point @($P$) and distinct wire names,
          @(tsee group-enforce-in-group-assignment) is a valuation that
          binds the input wires to @($P$)'s coordinates and satisfies
          @('enforce_in_group')."
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (no-duplicatesp-equal
                 (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2))
                (equal p (base-prime))
                (groupp pt))
           (b* ((asg (group-enforce-in-group-assignment
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 pt)))
             (and (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                  (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                  (r1cs::r1cs-constraints-holdp
                   (group-enforce-in-group-gadget
                    x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                   asg p))))
  :do-not-induct t
  :use (:instance group-enforce-in-group-gadget-complete
                  (asg (group-complete-asg)))
  :in-theory '(group-complete-assignment-lookups
               group-complete-assignment-binds
               group-complete-assignment-valuationp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled group-enforce-in-group-unsat-when-not-groupp
  :short "The unsatisfiable direction: no assignment satisfies
          @('enforce_in_group') when the input wires are not a
          @(tsee groupp) point.  This is conditional on
          @(tsee edwards-bls12-cofactor-clears)."
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
                (r1cs::valuation-bindsp asg ey2)
                (edwards-bls12-cofactor-clears)
                (not (groupp (ecurve::point-finite (lookup-equal x asg)
                                                   (lookup-equal y asg)))))
           (not (r1cs::r1cs-constraints-holdp
                 (group-enforce-in-group-gadget
                  x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p)))
  :use group-enforce-in-group-sound
  :in-theory nil)
