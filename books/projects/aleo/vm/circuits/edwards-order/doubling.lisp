; Coordinates of a doubled twisted Edwards point
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; For P = (x, y) on a complete curve, 2P = (2xy / (1 + d x^2 y^2),
;; (y^2 - a x^2) / (1 - d x^2 y^2)).  We record: the abscissa of 2P is 0 only
;; if x = 0 or y = 0; if y = 0 then 2P = (0, -1); and if the ordinate of 2P is
;; 0 then y^2 = a x^2.

(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defruledl curve-components
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve)))
    (and (dm::primep p)
         (posp p)
         (< 2 p)
         (fep a p)
         (fep d p)))
  :enable (twisted-edwards-curve->p
           twisted-edwards-curve->a
           twisted-edwards-curve->d))

(defruledl div-zero
  (implies (and (dm::primep p)
                (fep n p) (fep den p)
                (not (equal den 0)))
           (equal (equal (div n den p) 0)
                  (equal n 0)))
  :enable div
  :use ((:instance pfield::equal-of-0-and-mul
                   (pfield::p p) (x n) (y (pfield::inv den p)))
        (:instance pfield::mul-of-inv-arg2 (pfield::p p) (x den))))

(defruledl fep-of-point-coordinates
  (implies (point-on-twisted-edwards-p pt curve)
           (and (fep (point-finite->x pt) (twisted-edwards-curve->p curve))
                (fep (point-finite->y pt) (twisted-edwards-curve->p curve))))
  :enable (point-on-twisted-edwards-p fep))

(defruled twisted-edwards-double-x-zero
  (implies (and (twisted-edwards-curve-completep curve)
                (point-on-twisted-edwards-p pt curve)
                (equal (point-finite->x (twisted-edwards-add pt pt curve)) 0))
           (or (equal (point-finite->x pt) 0)
               (equal (point-finite->y pt) 0)))
  :use (curve-components
        fep-of-point-coordinates
        (:instance 1+d.x1.x2.y1.y2-not-0 (point1 pt) (point2 pt))
        (:instance div-zero
                   (p (twisted-edwards-curve->p curve))
                   (n (add (mul (point-finite->x pt) (point-finite->y pt)
                                (twisted-edwards-curve->p curve))
                           (mul (point-finite->y pt) (point-finite->x pt)
                                (twisted-edwards-curve->p curve))
                           (twisted-edwards-curve->p curve)))
                   (den (add 1
                             (mul (twisted-edwards-curve->d curve)
                                  (mul (point-finite->x pt)
                                       (mul (point-finite->x pt)
                                            (mul (point-finite->y pt)
                                                 (point-finite->y pt)
                                                 (twisted-edwards-curve->p curve))
                                            (twisted-edwards-curve->p curve))
                                       (twisted-edwards-curve->p curve))
                                  (twisted-edwards-curve->p curve))
                             (twisted-edwards-curve->p curve))))
        (:instance pfield::equal-of-0-and-mul
                   (pfield::p (twisted-edwards-curve->p curve))
                   (x 2)
                   (y (mul (point-finite->x pt) (point-finite->y pt)
                           (twisted-edwards-curve->p curve))))
        (:instance pfield::equal-of-0-and-mul
                   (pfield::p (twisted-edwards-curve->p curve))
                   (x (point-finite->x pt))
                   (y (point-finite->y pt))))
  :enable (twisted-edwards-add fep)
  :disable (1+d.x1.x2.y1.y2-not-0 1-d.x1.x2.y1.y2-not-0
            pfield::equal-of-0-and-mul))

(defrulel inv-of-1-local
  (implies (dm::primep p)
           (equal (pfield::inv 1 p) 1))
  :use (:instance pfield::mul-of-inv-arg2 (pfield::p p) (x 1)))

(defruled twisted-edwards-double-when-y-zero
  (implies (and (twisted-edwards-curve-completep curve)
                (point-on-twisted-edwards-p pt curve)
                (equal (point-finite->y pt) 0))
           (equal (twisted-edwards-add pt pt curve)
                  (point-finite 0 (neg 1 (twisted-edwards-curve->p curve)))))
  :use (curve-components
        fep-of-point-coordinates)
  :enable (twisted-edwards-add point-on-twisted-edwards-p div))

(defruled twisted-edwards-double-y-zero
  (implies (and (twisted-edwards-curve-completep curve)
                (point-on-twisted-edwards-p pt curve)
                (equal (point-finite->y (twisted-edwards-add pt pt curve)) 0))
           (equal (mul (point-finite->y pt) (point-finite->y pt)
                       (twisted-edwards-curve->p curve))
                  (mul (twisted-edwards-curve->a curve)
                       (mul (point-finite->x pt) (point-finite->x pt)
                            (twisted-edwards-curve->p curve))
                       (twisted-edwards-curve->p curve))))
  :use (curve-components
        fep-of-point-coordinates
        (:instance 1-d.x1.x2.y1.y2-not-0 (point1 pt) (point2 pt))
        (:instance div-zero
                   (p (twisted-edwards-curve->p curve))
                   (n (sub (mul (point-finite->y pt) (point-finite->y pt)
                                (twisted-edwards-curve->p curve))
                           (mul (twisted-edwards-curve->a curve)
                                (mul (point-finite->x pt) (point-finite->x pt)
                                     (twisted-edwards-curve->p curve))
                                (twisted-edwards-curve->p curve))
                           (twisted-edwards-curve->p curve)))
                   (den (sub 1
                             (mul (twisted-edwards-curve->d curve)
                                  (mul (point-finite->x pt)
                                       (mul (point-finite->x pt)
                                            (mul (point-finite->y pt)
                                                 (point-finite->y pt)
                                                 (twisted-edwards-curve->p curve))
                                            (twisted-edwards-curve->p curve))
                                       (twisted-edwards-curve->p curve))
                                  (twisted-edwards-curve->p curve))
                             (twisted-edwards-curve->p curve)))))
  :enable (twisted-edwards-add fep)
  :disable (1+d.x1.x2.y1.y2-not-0 1-d.x1.x2.y1.y2-not-0))
