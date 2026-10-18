; Prime field lemmas used to count twisted Edwards points
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system))

(defruled pfield-equal-squares
  (implies (and (dm::primep p)
                (fep y p)
                (fep s p)
                (equal (mul y y p) (mul s s p)))
           (or (equal y s)
               (equal y (neg s p))))
  :use ((:instance pfield::equal-of-0-and-mul (pfield::p p)
                   (x (add y (neg s p) p))
                   (y (add y s p)))))

(defrule pfield-mul-neg-neg-same
  (implies (dm::primep p)
           (equal (mul (neg s p) (neg s p) p)
                  (mul s s p))))

(defruled pfield-neg-equal-self
  (implies (and (dm::primep p)
                (< 2 p)
                (fep s p)
                (not (equal s 0)))
           (not (equal (neg s p) s)))
  :use ((:instance pfield::equal-of-0-and-mul (pfield::p p) (x 2) (y s)))
  :enable fep)

(defruled pfield-curve-equation-rearrange
  (implies (and (dm::primep p)
                (fep a p) (fep d p) (fep xx p) (fep yy p))
           (equal (equal (add (mul a xx p) yy p)
                         (add 1 (mul d (mul xx yy p) p) p))
                  (equal (mul yy (add 1 (neg (mul d xx p) p) p) p)
                         (add 1 (neg (mul a xx p) p) p)))))

(defruled pfield-solve-mul
  (implies (and (dm::primep p)
                (fep yy p) (fep n p) (fep den p)
                (not (equal den 0)))
           (equal (equal (mul yy den p) n)
                  (equal yy (mul n (pfield::inv den p) p))))
  :cases ((equal (mul yy den p) n))
  :hints (("Subgoal 2"
           :use (:instance pfield::mul-of-inv-mul-of-inv (pfield::p p)
                           (a den) (x yy)))))

(defruled pfield-not-square-times-square-not-1
  (implies (and (dm::primep p)
                (fep d p) (fep x p)
                (not (pfield-squarep d p)))
           (not (equal (mul d (mul x x p) p) 1)))
  :use ((:instance pfield-squarep-suff
                   (r (pfield::inv x p)) (x d))
        (:instance pfield::mul-of-inv-mul-of-inv (pfield::p p)
                   (a (mul x x p)) (x d))))

(defruled pfield-not-square-one-minus-not-zero
  (implies (and (dm::primep p)
                (fep d p) (fep x p)
                (not (pfield-squarep d p)))
           (not (equal (add 1 (neg (mul d (mul x x p) p) p) p) 0)))
  :use pfield-not-square-times-square-not-1)
