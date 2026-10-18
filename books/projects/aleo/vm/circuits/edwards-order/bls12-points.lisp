; Concrete points of Edwards-BLS12 used in the group-order argument
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; A point G of order r (the Aleo generator), a point T4 = (sqrt(-1), 0) of
;; order 4, and the non-squareness of 1 + d.

(include-book "basics")
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

(defun te-add-exec (point1 point2 curve)
  (declare (xargs :verify-guards nil))
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve))
       ((unless (eq (point-kind point1) :finite)) (point-finite 0 0))
       ((unless (eq (point-kind point2) :finite)) (point-finite 0 0))
       (x1 (point-finite->x point1))
       (y1 (point-finite->y point1))
       (x2 (point-finite->x point2))
       (y2 (point-finite->y point2))
       (d.x1.x2.y1.y2 (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p))
       (x3-numerator (add (mul x1 y2 p) (mul y1 x2 p) p))
       (x3-denominator (add 1 d.x1.x2.y1.y2 p))
       (y3-numerator (sub (mul y1 y2 p) (mul a (mul x1 x2 p) p) p))
       (y3-denominator (sub 1 d.x1.x2.y1.y2 p))
       (x3 (div x3-numerator x3-denominator p))
       (y3 (div y3-numerator y3-denominator p)))
    (point-finite x3 y3)))

(defruled twisted-edwards-add-is-exec
  (equal (twisted-edwards-add point1 point2 curve)
         (te-add-exec point1 point2 curve))
  :enable twisted-edwards-add)

(defun te-mul-fast-exec (scalar point curve)
  (declare (xargs :verify-guards nil :measure (nfix scalar)))
  (if (zp scalar)
      (twisted-edwards-zero)
    (if (evenp scalar)
        (let ((half (te-mul-fast-exec (/ scalar 2) point curve)))
          (te-add-exec half half curve))
      (te-add-exec point
                   (te-mul-fast-exec (- scalar 1) point curve)
                   curve))))

(defruled twisted-edwards-mul-fast-nonneg-is-exec
  (implies (natp scalar)
           (equal (twisted-edwards-mul-fast-nonneg scalar point curve)
                  (te-mul-fast-exec scalar point curve)))
  :induct (te-mul-fast-exec scalar point curve)
  :enable (twisted-edwards-mul-fast-nonneg twisted-edwards-add-is-exec))

(defruled twisted-edwards-mul-is-exec
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve)
                (natp scalar))
           (equal (twisted-edwards-mul scalar point curve)
                  (te-mul-fast-exec scalar point curve)))
  :use (twisted-edwards-mul-fast-nonneg-is-exec
        (:instance twisted-edwards-mul-fast-nonneg-is-mul (n scalar))))

(define bls12-order-g ()
  :returns (g pointp)
  (point-finite
   522678458525321116977504528531602186870683848189190546523208313015552693483
   4625467284263880392848236339834904393692054417272076479096796531274999498606))

(define bls12-order-t4 ()
  :returns (t4 pointp)
  (point-finite
   880904806456922042258150504921383618666682042621506879489
   0))

(in-theory (disable (:e bls12-order-g) (:e bls12-order-t4)))

(defrule edwards-bls12-curve-completep
  (twisted-edwards-curve-completep (edwards-bls12-curve)))

(defrule bls12-order-g-on-curve
  (point-on-twisted-edwards-p (bls12-order-g) (edwards-bls12-curve))
  :in-theory '((:e point-on-twisted-edwards-p)
               (:e edwards-bls12-curve)
               (:e bls12-order-g)))

(defrule bls12-order-t4-on-curve
  (point-on-twisted-edwards-p (bls12-order-t4) (edwards-bls12-curve))
  :in-theory '((:e point-on-twisted-edwards-p)
               (:e edwards-bls12-curve)
               (:e bls12-order-t4)))

(defrule bls12-order-g-not-zero
  (not (equal (bls12-order-g) (twisted-edwards-zero)))
  :in-theory '((:e bls12-order-g) (:e twisted-edwards-zero)))

(defruled bls12-order-r-kills-g-exec
  (equal (te-mul-fast-exec (edwards-bls12-r)
                           (bls12-order-g)
                           (edwards-bls12-curve))
         (twisted-edwards-zero))
  :in-theory '((:e te-mul-fast-exec)
               (:e edwards-bls12-r)
               (:e edwards-bls12-curve)
               (:e bls12-order-g)
               (:e twisted-edwards-zero)))

(defrule bls12-order-r-kills-g
  (equal (twisted-edwards-mul (edwards-bls12-r)
                              (bls12-order-g)
                              (edwards-bls12-curve))
         (twisted-edwards-zero))
  :use (bls12-order-r-kills-g-exec
        (:instance twisted-edwards-mul-is-exec
                   (scalar (edwards-bls12-r))
                   (point (bls12-order-g))
                   (curve (edwards-bls12-curve))))
  :in-theory '(edwards-bls12-curve-completep
               bls12-order-g-on-curve
               pointp-of-bls12-order-g
               (:e natp) (:e edwards-bls12-r)))

(defruledl bls12-order-t4-multiples-exec
  (and (not (equal (te-mul-fast-exec 1 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (not (equal (te-mul-fast-exec 2 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (not (equal (te-mul-fast-exec 3 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (equal (te-mul-fast-exec 4 (bls12-order-t4) (edwards-bls12-curve))
              (twisted-edwards-zero)))
  :in-theory '((:e te-mul-fast-exec)
               (:e edwards-bls12-curve)
               (:e bls12-order-t4)
               (:e twisted-edwards-zero)))

(defruled bls12-order-t4-multiples
  (and (not (equal (twisted-edwards-mul 1 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (not (equal (twisted-edwards-mul 2 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (not (equal (twisted-edwards-mul 3 (bls12-order-t4) (edwards-bls12-curve))
                   (twisted-edwards-zero)))
       (equal (twisted-edwards-mul 4 (bls12-order-t4) (edwards-bls12-curve))
              (twisted-edwards-zero)))
  :use (bls12-order-t4-multiples-exec
        (:instance twisted-edwards-mul-is-exec (scalar 1) (point (bls12-order-t4))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-is-exec (scalar 2) (point (bls12-order-t4))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-is-exec (scalar 3) (point (bls12-order-t4))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-is-exec (scalar 4) (point (bls12-order-t4))
                   (curve (edwards-bls12-curve))))
  :in-theory '((:e natp)
               edwards-bls12-curve-completep
               bls12-order-t4-on-curve
               pointp-of-bls12-order-t4))

(defruled bls12-double-of-minus-one
  (equal (twisted-edwards-add
          (point-finite 0 (neg 1 (twisted-edwards-curve->p (edwards-bls12-curve))))
          (point-finite 0 (neg 1 (twisted-edwards-curve->p (edwards-bls12-curve))))
          (edwards-bls12-curve))
         (point-finite 0 1))
  :use (:instance twisted-edwards-add-is-exec
                  (point1 (point-finite 0 (neg 1 (twisted-edwards-curve->p
                                                  (edwards-bls12-curve)))))
                  (point2 (point-finite 0 (neg 1 (twisted-edwards-curve->p
                                                  (edwards-bls12-curve)))))
                  (curve (edwards-bls12-curve)))
  :in-theory '((:e te-add-exec)
               (:e edwards-bls12-curve)
               (:e twisted-edwards-curve->p)
               (:e neg)
               (:e point-finite)
               (:e equal)))
