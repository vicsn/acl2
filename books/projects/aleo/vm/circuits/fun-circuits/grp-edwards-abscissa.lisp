; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two Edwards-BLS12 subgroup points with the same abscissa are equal.
; The points of the curve with abscissa x are (x, y) and (x, -y), and
; (x, -y) = -((0, -1) + (x, y)).  Scalar multiplication distributes over
; point addition (by associativity and commutativity), the order-2 point
; T = (0, -1) satisfies r T = T since r is odd, so if r (x, y) = 0 then
; r (x, -y) = -T = T, which is not zero.

(in-package "ECURVE")

(include-book "../edwards-order/exponent")
(include-book "../edwards-order/bls12-points")
(include-book "../edwards-order/field-lemmas")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(local (defun grp-nat-ind (k) (if (zp k) k (grp-nat-ind (1- k)))))
(defrule grp-te-mul-dist
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp p1) (point-on-twisted-edwards-p p1 curve)
                (pointp p2) (point-on-twisted-edwards-p p2 curve)
                (natp k))
           (equal (twisted-edwards-mul k (twisted-edwards-add p1 p2 curve) curve)
                  (twisted-edwards-add (twisted-edwards-mul k p1 curve)
                                       (twisted-edwards-mul k p2 curve)
                                       curve)))
  :rule-classes nil
  :induct (grp-nat-ind k)
  :hints (("Subgoal *1/2"
           :use ((:instance twisted-edwards-mul-succ (n (1- k)) (point p1))
                 (:instance twisted-edwards-mul-succ (n (1- k)) (point p2))
                 (:instance twisted-edwards-mul-succ (n (1- k))
                            (point (twisted-edwards-add p1 p2 curve)))
                 (:instance twisted-edwards-add-commutative-2
                            (a p2) (b (twisted-edwards-mul (1- k) p1 curve))
                            (c (twisted-edwards-mul (1- k) p2 curve))))))
  :disable (twisted-edwards-mul-of-scalar-addition))

(defruled grp-r-point-killed
  (implies (edwards-bls12-r-pointp pt)
           (equal (twisted-edwards-mul (edwards-bls12-r) pt (edwards-bls12-curve))
                  (twisted-edwards-zero)))
  :enable (edwards-bls12-r-pointp twisted-edwards-point-orderp)
  :disable ((:e edwards-bls12-r)))

(defruled grp-add-minus-one
  (implies (and (fep x (edwards-bls12-q)) (fep y (edwards-bls12-q)))
           (equal (twisted-edwards-add
                   (point-finite 0 (neg 1 (edwards-bls12-q)))
                   (point-finite x y)
                   (edwards-bls12-curve))
                  (point-finite (neg x (edwards-bls12-q))
                                (neg y (edwards-bls12-q)))))
  :enable (twisted-edwards-add edwards-bls12-curve pfield::mul-of--1-becomes-neg)
  :disable ((:e edwards-bls12-q) (:e edwards-bls12-curve)))

(defruled grp-minus-one-on-curve
  (and (pointp (point-finite 0 (neg 1 (edwards-bls12-q))))
       (point-on-twisted-edwards-p (point-finite 0 (neg 1 (edwards-bls12-q)))
                                   (edwards-bls12-curve)))
  :use bls12-order-t4-multiples
  :in-theory '((:e point-on-twisted-edwards-p) (:e pointp) (:e point-finite)
               (:e neg) (:e edwards-bls12-q) (:e edwards-bls12-curve)))

(defruled grp-zero-is
  (equal (point-finite 0 1) (twisted-edwards-zero))
  :enable twisted-edwards-zero)

(defruled grp-curve-p
  (equal (twisted-edwards-curve->p (edwards-bls12-curve)) (edwards-bls12-q))
  :enable edwards-bls12-curve)

(defruled grp-r-times-minus-one
  (equal (twisted-edwards-mul (edwards-bls12-r)
                              (point-finite 0 (neg 1 (edwards-bls12-q)))
                              (edwards-bls12-curve))
         (point-finite 0 (neg 1 (edwards-bls12-q))))
  :use (bls12-double-of-minus-one
        (:instance twisted-edwards-mul-of-scalar-addition
                   (scalar1 1) (scalar2 (1- (edwards-bls12-r)))
                   (point (point-finite 0 (neg 1 (edwards-bls12-q))))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar (/ (1- (edwards-bls12-r)) 2)) (scalar1 2)
                   (point (point-finite 0 (neg 1 (edwards-bls12-q))))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-succ (n 1)
                   (point (point-finite 0 (neg 1 (edwards-bls12-q))))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-zero
                   (scalar (/ (1- (edwards-bls12-r)) 2))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-1
                   (point (point-finite 0 (neg 1 (edwards-bls12-q))))
                   (curve (edwards-bls12-curve))))
  :in-theory '((:e edwards-bls12-r) grp-curve-p grp-minus-one-on-curve point-fix-when-pointp grp-zero-is
               (:e integerp)
               (:e natp) (:e twisted-edwards-add-associativity)
               (:e binary-+) (:e binary-*)
               (:e unary--) (:e unary-/)
               twisted-edwards-add-associativity-holds
               twisted-edwards-add-of-twisted-edwards-zero-right
               twisted-edwards-curve-completep-of-edwards-bls12-curve))

(defruled grp-curve-a
  (equal (twisted-edwards-curve->a (edwards-bls12-curve)) (edwards-bls12-a))
  :enable edwards-bls12-curve)

(defruled grp-curve-d
  (equal (twisted-edwards-curve->d (edwards-bls12-curve)) (edwards-bls12-d))
  :enable edwards-bls12-curve)

(defruled grp-posp-q
  (and (posp (edwards-bls12-q)) (< 2 (edwards-bls12-q)))
  :enable ((:e edwards-bls12-q)))

(defruled grp-on-curve-y2
  (implies (and (fep x (edwards-bls12-q)) (fep y (edwards-bls12-q))
                (point-on-twisted-edwards-p (point-finite x y) (edwards-bls12-curve)))
           (equal (mul y y (edwards-bls12-q))
                  (mul (add 1 (neg (mul (edwards-bls12-a) (mul x x (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q))
                       (pfield::inv (add 1 (neg (mul (edwards-bls12-d) (mul x x (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q))
                                    (edwards-bls12-q))
                       (edwards-bls12-q))))
  :use ((:instance pfield-curve-equation-rearrange
                   (p (edwards-bls12-q)) (a (edwards-bls12-a)) (d (edwards-bls12-d))
                   (xx (mul x x (edwards-bls12-q))) (yy (mul y y (edwards-bls12-q))))
        (:instance pfield-solve-mul
                   (p (edwards-bls12-q))
                   (yy (mul y y (edwards-bls12-q)))
                   (n (add 1 (neg (mul (edwards-bls12-a) (mul x x (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q)))
                   (den (add 1 (neg (mul (edwards-bls12-d) (mul x x (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q)) (edwards-bls12-q))))
        (:instance pfield-not-square-one-minus-not-zero
                   (p (edwards-bls12-q)) (d (edwards-bls12-d))))
  :in-theory '(point-on-twisted-edwards-p grp-curve-p
               (:t edwards-bls12-q)
               primep-of-edwards-bls12-q
               return-type-of-edwards-bls12-a return-type-of-edwards-bls12-d
               not-pfield-squarep-of-edwards-bls12-d
               pfield::fep-of-mul pfield::fep-of-add pfield::fep-of-neg pfield::fep-of-inv
               point-finite->x-of-point-finite point-finite->y-of-point-finite
               point-kind-of-point-finite
               grp-curve-a grp-curve-d
               pfield::fep-fw-to-natp
               nfix (:t pfield::fep) (:t mul) (:t add) grp-posp-q
               acl2::natp-compound-recognizer acl2::posp-compound-recognizer))

(defruled grp-same-x-y-or-neg
  (implies (and (fep x (edwards-bls12-q)) (fep y1 (edwards-bls12-q)) (fep y2 (edwards-bls12-q))
                (point-on-twisted-edwards-p (point-finite x y1) (edwards-bls12-curve))
                (point-on-twisted-edwards-p (point-finite x y2) (edwards-bls12-curve)))
           (or (equal y1 y2) (equal y1 (neg y2 (edwards-bls12-q)))))
  :use ((:instance grp-on-curve-y2 (y y1))
        (:instance grp-on-curve-y2 (y y2))
        (:instance pfield-equal-squares (p (edwards-bls12-q)) (y y1) (s y2)))
  :in-theory '(primep-of-edwards-bls12-q))

(defruled grp-neg-y-form
  (implies (and (fep x (edwards-bls12-q)) (fep y (edwards-bls12-q)))
           (equal (twisted-edwards-neg
                   (twisted-edwards-add (point-finite 0 (neg 1 (edwards-bls12-q)))
                                        (point-finite x y)
                                        (edwards-bls12-curve))
                   (edwards-bls12-curve))
                  (point-finite x (neg y (edwards-bls12-q)))))
  :use grp-add-minus-one
  :in-theory '(twisted-edwards-neg grp-curve-p pfield::neg-of-neg pfield::neg-of-0
               pfield::natp-of-neg (:t pfield::natp-of-neg)
               point-finite->x-of-point-finite point-finite->y-of-point-finite
               pfield::fep-of-neg pfield::fep-fw-to-natp nfix grp-posp-q (:t edwards-bls12-q)
               acl2::natp-compound-recognizer acl2::posp-compound-recognizer))

(defruled grp-minus-one-neg
  (equal (twisted-edwards-neg (point-finite 0 (neg 1 (edwards-bls12-q)))
                              (edwards-bls12-curve))
         (point-finite 0 (neg 1 (edwards-bls12-q))))
  :in-theory '(twisted-edwards-neg grp-curve-p pfield::neg-of-0 nfix
               pfield::natp-of-neg (:t pfield::natp-of-neg)
               point-finite->x-of-point-finite point-finite->y-of-point-finite))

(defruled grp-minus-one-not-zero
  (not (equal (point-finite 0 (neg 1 (edwards-bls12-q))) (twisted-edwards-zero)))
  :in-theory '((:e point-finite) (:e neg) (:e edwards-bls12-q) (:e twisted-edwards-zero) (:e equal)))

(defruled grp-r-points-not-neg-y
  (implies (and (fep x (edwards-bls12-q)) (fep y (edwards-bls12-q))
                (edwards-bls12-r-pointp (point-finite x y)))
           (not (edwards-bls12-r-pointp (point-finite x (neg y (edwards-bls12-q))))))
  :use (grp-neg-y-form grp-minus-one-neg grp-minus-one-not-zero grp-minus-one-on-curve
        grp-r-times-minus-one
        (:instance grp-r-point-killed (pt (point-finite x y)))
        (:instance grp-r-point-killed (pt (point-finite x (neg y (edwards-bls12-q)))))
        (:instance twisted-edwards-mul-of-neg
                   (scalar (edwards-bls12-r))
                   (point (twisted-edwards-add (point-finite 0 (neg 1 (edwards-bls12-q)))
                                               (point-finite x y)
                                               (edwards-bls12-curve)))
                   (curve (edwards-bls12-curve)))
        (:instance grp-te-mul-dist (k (edwards-bls12-r))
                   (p1 (point-finite 0 (neg 1 (edwards-bls12-q))))
                   (p2 (point-finite x y))
                   (curve (edwards-bls12-curve)))
        (:instance edwards-bls12-pointp-when-edwards-bls12-r-pointp (x (point-finite x y))))
  :in-theory '(twisted-edwards-add-associativity-holds
               twisted-edwards-curve-completep-of-edwards-bls12-curve
               edwards-bls12-pointp
               point-on-twisted-edwards-p-of-twisted-edward-add
               pointp-of-twisted-edwards-add
               twisted-edwards-add-of-twisted-edwards-zero-right
               twisted-edwards-neg-of-zero point-fix-when-pointp
               (:e natp) (:e integerp) (:e edwards-bls12-r)))

(defrule grp-r-points-same-abscissa
  (implies (and (fep x (edwards-bls12-q))
                (fep y1 (edwards-bls12-q))
                (fep y2 (edwards-bls12-q))
                (edwards-bls12-r-pointp (point-finite x y1))
                (edwards-bls12-r-pointp (point-finite x y2)))
           (equal y1 y2))
  :rule-classes nil
  :use (grp-same-x-y-or-neg
        (:instance grp-r-points-not-neg-y (y y2))
        (:instance edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (x (point-finite x y1)))
        (:instance edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (x (point-finite x y2))))
  :in-theory '(edwards-bls12-pointp))

