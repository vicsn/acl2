; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND of Group::new / enforce_in_group over the wire values.
;
; group-enforce-in-group-equations says Q = (qx, qy) satisfies the curve
; equation, (x3, y3) satisfies the doubling equations of Q, and (x, y)
; satisfies the doubling equations of (x3, y3).  On a complete twisted
; Edwards curve the doubling denominators are nonzero, so the equations
; determine (x3, y3) = Q + Q and (x, y) = 2Q + 2Q under edwards-bls12-add.
; That is group-enforce-in-group-equations-to-4q.
;
; The output is in the order-r subgroup when 4Q is, for every curve point Q.
; That holds because the curve order is 4r (cofactor edwards-bls12-h).  The
; curve order is not formalised in the libraries, so the fact is the named
; hypothesis edwards-bls12-cofactor-clears.  group-enforce-in-group-sound is
; conditional on it (fun-specs/README.md).

(in-package "ALEOVM")

(include-book "group-inject-r1cs")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system))

(local (in-theory (disable (:e base-prime) (:e scalar-prime)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl group-sound-q-is-base-prime
  (equal (ecurve::edwards-bls12-q) (base-prime))
  :in-theory '((:e base-prime) (:e ecurve::edwards-bls12-q)))

(defruledl group-sound-posp-base-prime
  (posp (base-prime))
  :in-theory '((:e base-prime) (:e posp)))

(defruledl group-sound-div-of-equal
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep e p)
                (not (equal e 0))
                (equal (pfield::mul x e p) n)
                (equal e f))
           (equal (pfield::div n f p) x))
  :enable pfield::div)

(defruledl group-sound-on-curve-equation-iff
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

(defruledl group-sound-double-x
  (implies (and (equal p (base-prime))
                (pfield::fep x3 p)
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
                            0))
                (group-double-x-equation x3 x2 y2 xy p))
           (equal (pfield::div (pfield::mul 2 xy p)
                               (pfield::add 1
                                            (pfield::mul (ecurve::edwards-bls12-d)
                                                         (pfield::mul x2 y2 p)
                                                         p)
                                            p)
                               p)
                  x3))
  :use (:instance group-sound-div-of-equal
                  (x x3)
                  (e (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                  y2 p))
                  (f (pfield::add 1
                                  (pfield::mul (ecurve::edwards-bls12-d)
                                               (pfield::mul x2 y2 p)
                                               p)
                                  p))
                  (n (pfield::mul 2 xy p)))
  :in-theory '(group-double-x-equation
               primep-of-base-prime
               group-sound-posp-base-prime
               pfield::fep-of-add))

(defruledl group-sound-sub-2-of-add-1
  (implies (primep p)
           (equal (pfield::sub 2 (pfield::add 1 w p) p)
                  (pfield::sub 1 w p))))

(defruledl group-sound-double-y
  (implies (and (equal p (base-prime))
                (pfield::fep y3 p)
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
                            0))
                (group-double-y-equation y3 x2 y2 p))
           (equal (pfield::div (pfield::sub y2
                                            (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                            p)
                               (pfield::sub 1
                                            (pfield::mul (ecurve::edwards-bls12-d)
                                                         (pfield::mul x2 y2 p)
                                                         p)
                                            p)
                               p)
                  y3))
  :use ((:instance group-sound-div-of-equal
                   (x y3)
                   (e (pfield::sub 2
                                   (pfield::add (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                                y2 p)
                                   p))
                   (f (pfield::sub 1
                                   (pfield::mul (ecurve::edwards-bls12-d)
                                                (pfield::mul x2 y2 p)
                                                p)
                                   p))
                   (n (pfield::sub y2
                                   (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                   p)))
        (:instance group-sound-sub-2-of-add-1
                   (w (pfield::mul (ecurve::edwards-bls12-d)
                                   (pfield::mul x2 y2 p)
                                   p))))
  :in-theory '(group-double-y-equation
               primep-of-base-prime
               group-sound-posp-base-prime
               pfield::fep-of-sub))

(defruledl group-sound-add-same
  (equal (pfield::add x x p)
         (pfield::mul 2 x p))
  :enable (pfield::add pfield::mul)
  :cases ((equal (+ (ifix x) (ifix x)) (* 2 (ifix x)))))

(defruledl group-sound-add-self
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
           group-sound-q-is-base-prime
           group-sound-add-same
           pfield::fep))

(defruledl group-sound-on-curve-xy
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
           group-sound-q-is-base-prime
           pfield::fep))

(defruledl group-sound-denominators-not-0
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
           group-sound-q-is-base-prime
           pfield::fep))

(defruled group-sound-double
  (implies (and (equal p (base-prime))
                (pfield::fep x0 p)
                (pfield::fep y0 p)
                (pfield::fep x3 p)
                (pfield::fep y3 p)
                (ecurve::edwards-bls12-pointp (ecurve::point-finite x0 y0))
                (group-double-x-equation x3
                                         (pfield::mul x0 x0 p)
                                         (pfield::mul y0 y0 p)
                                         (pfield::mul x0 y0 p)
                                         p)
                (group-double-y-equation y3
                                         (pfield::mul x0 x0 p)
                                         (pfield::mul y0 y0 p)
                                         p))
           (equal (ecurve::edwards-bls12-add (ecurve::point-finite x0 y0)
                                             (ecurve::point-finite x0 y0))
                  (ecurve::point-finite x3 y3)))
  :use (group-sound-add-self
        group-sound-on-curve-xy
        group-sound-denominators-not-0
        (:instance group-sound-double-x
                   (x2 (pfield::mul x0 x0 p))
                   (y2 (pfield::mul y0 y0 p))
                   (xy (pfield::mul x0 y0 p)))
        (:instance group-sound-double-y
                   (x2 (pfield::mul x0 x0 p))
                   (y2 (pfield::mul y0 y0 p))))
  :in-theory '(pfield::fep-of-mul
               group-sound-posp-base-prime))

(defruled group-sound-on-curve
  (implies (and (equal p (base-prime))
                (pfield::fep qx p)
                (pfield::fep qy p)
                (group-on-curve-equation (pfield::mul qy qy p)
                                         (pfield::mul qx qx p)
                                         p))
           (ecurve::edwards-bls12-pointp (ecurve::point-finite qx qy)))
  :use (:instance group-sound-on-curve-equation-iff
                  (x2 (pfield::mul qx qx p))
                  (y2 (pfield::mul qy qy p)))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           group-sound-q-is-base-prime
           pfield::fep))

(defruled group-enforce-in-group-equations-to-4q
  (implies (and (equal p (base-prime))
                (pfield::fep x p) (pfield::fep y p)
                (pfield::fep qx p) (pfield::fep qy p)
                (pfield::fep x3 p) (pfield::fep y3 p)
                (group-enforce-in-group-equations
                 x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))
           (b* ((q (ecurve::point-finite qx qy))
                (q2 (ecurve::edwards-bls12-add q q)))
             (and (ecurve::edwards-bls12-pointp q)
                  (equal (ecurve::point-finite x3 y3) q2)
                  (equal (ecurve::point-finite x y)
                         (ecurve::edwards-bls12-add q2 q2)))))
  :use ((:instance group-sound-on-curve)
        (:instance group-sound-double (x0 qx) (y0 qy))
        (:instance group-sound-double (x0 x3) (y0 y3) (x3 x) (y3 y))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (point1 (ecurve::point-finite qx qy))
                   (point2 (ecurve::point-finite qx qy))))
  :in-theory '(group-enforce-in-group-equations))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk edwards-bls12-cofactor-clears ()
  :short "For every Edwards-BLS12 point @($Q$), @($2Q + 2Q$) is in the
          order-@($r$) subgroup."
  :long "<p>This follows from the curve order being @($4r$).  It is a
         hypothesis because the curve order is not formalised.</p>"
  (forall (q)
          (implies (ecurve::edwards-bls12-pointp q)
                   (b* ((q2 (ecurve::edwards-bls12-add q q)))
                     (ecurve::edwards-bls12-r-pointp
                      (ecurve::edwards-bls12-add q2 q2))))))

(defruled group-enforce-in-group-sound
  :short "R1CS-SOUND of @('enforce_in_group') over the wires: the output
          wires are @($4Q$) for a curve point @($Q$), and a group element
          given @(tsee edwards-bls12-cofactor-clears)."
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
                (r1cs::r1cs-constraints-holdp
                 (group-enforce-in-group-gadget
                  x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p))
           (b* ((pt (ecurve::point-finite (lookup-equal x asg)
                                          (lookup-equal y asg)))
                (q (ecurve::point-finite (lookup-equal qx asg)
                                         (lookup-equal qy asg)))
                (q2 (ecurve::edwards-bls12-add q q)))
             (and (ecurve::edwards-bls12-pointp q)
                  (equal pt (ecurve::edwards-bls12-add q2 q2))
                  (implies (edwards-bls12-cofactor-clears)
                           (groupp pt)))))
  :do-not-induct t
  :use ((:instance group-enforce-in-group-gadget-to-equations)
        (:instance group-enforce-in-group-equations-to-4q
                   (x (lookup-equal x asg))
                   (y (lookup-equal y asg))
                   (qx (lookup-equal qx asg))
                   (qy (lookup-equal qy asg))
                   (cx2 (lookup-equal cx2 asg))
                   (cy2 (lookup-equal cy2 asg))
                   (dxy (lookup-equal dxy asg))
                   (dx2 (lookup-equal dx2 asg))
                   (dy2 (lookup-equal dy2 asg))
                   (x3 (lookup-equal x3 asg))
                   (y3 (lookup-equal y3 asg))
                   (exy (lookup-equal exy asg))
                   (ex2 (lookup-equal ex2 asg))
                   (ey2 (lookup-equal ey2 asg)))
        (:instance edwards-bls12-cofactor-clears-necc
                   (q (ecurve::point-finite (lookup-equal qx asg)
                                            (lookup-equal qy asg)))))
  :in-theory '(groupp
               r1cs::fep-of-lookup-equal))
