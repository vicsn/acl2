; Group facts for twisted Edwards scalar multiplication
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; Fast scalar multiplication equals the plain one, and a point killed by a
;; prime r and by an integer not divisible by r is the neutral point.

(include-book "../edwards-assoc/twisted-edwards-associativity")
(include-book "projects/numbers/euclid" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

(defrule twisted-edwards-mul-fast-nonneg-is-mul
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve))
           (equal (twisted-edwards-mul-fast-nonneg n point curve)
                  (twisted-edwards-mul (nfix n) point curve)))
  :induct (twisted-edwards-mul-fast-nonneg n point curve)
  :enable twisted-edwards-mul-fast-nonneg
  :hints (("Subgoal *1/3"
           :use (:instance twisted-edwards-mul-of-scalar-addition
                           (scalar1 1) (scalar2 (+ -1 n))))
          ("Subgoal *1/2"
           :use (:instance twisted-edwards-mul-of-scalar-addition
                           (scalar1 (/ n 2)) (scalar2 (/ n 2))))))

(defrule twisted-edwards-mul-fast-is-mul
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve))
           (equal (twisted-edwards-mul-fast n point curve)
                  (twisted-edwards-mul n point curve)))
  :enable (twisted-edwards-mul-fast twisted-edwards-mul))

(defruled twisted-edwards-mul-succ
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve)
                (natp n))
           (equal (twisted-edwards-mul (+ 1 n) point curve)
                  (twisted-edwards-add point
                                       (twisted-edwards-mul n point curve)
                                       curve)))
  :use (:instance twisted-edwards-mul-of-scalar-addition
                  (scalar1 1) (scalar2 n)))

(defrule twisted-edwards-zero-when-coprime-multiples-zero
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve)
                (dm::primep r)
                (integerp k)
                (not (dm::divides r k))
                (equal (twisted-edwards-mul k point curve)
                       (twisted-edwards-zero))
                (equal (twisted-edwards-mul r point curve)
                       (twisted-edwards-zero)))
           (equal point (twisted-edwards-zero)))
  :rule-classes nil
  :use ((:instance dm::gcd-linear-combination (x k) (y r))
        (:instance dm::gcd-prime (p r) (a k))
        (:instance dm::gcd-commutative (x k) (y r))
        (:instance twisted-edwards-mul-of-scalar-addition
                   (scalar1 (* (dm::r k r) k))
                   (scalar2 (* (dm::s k r) r)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar (dm::r k r)) (scalar1 k))
        (:instance twisted-edwards-mul-of-mul
                   (scalar (dm::s k r)) (scalar1 r)))
  :disable (twisted-edwards-mul-of-mul))

(defruled twisted-edwards-point-orderp-when-prime-kills
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp point)
                (point-on-twisted-edwards-p point curve)
                (dm::primep r)
                (not (equal point (twisted-edwards-zero)))
                (equal (twisted-edwards-mul r point curve)
                       (twisted-edwards-zero)))
           (twisted-edwards-point-orderp point r curve))
  :enable (twisted-edwards-point-orderp twisted-edwards-point-order-leastp)
  :use ((:instance twisted-edwards-zero-when-coprime-multiples-zero
                   (k (twisted-edwards-point-order-leastp-witness
                       point (nfix r) curve)))
        (:instance dm::divides-leq
                   (x r)
                   (y (twisted-edwards-point-order-leastp-witness
                       point (nfix r) curve)))))
