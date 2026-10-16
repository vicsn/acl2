; Edwards-BLS12 has no point whose double has ordinate 0
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; If the ordinate of 2P is 0 then y^2 = a x^2 = -x^2, and the curve equation
;; gives 2 y^2 = 1 - d y^4, i.e. (d y^2 + 1)^2 = d + 1.  But d + 1 = 3022 is
;; not a square modulo q (Euler's criterion).  So the points (+-sqrt(-1), 0)
;; of order 4 are not doubles, and there is no point of order 8.

(include-book "doubling")
(include-book "bls12-points")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defruledl square-identity-step1
  (implies (and (dm::primep p)
                (fep xx p) (fep yy p) (fep d p)
                (equal yy (mul (neg 1 p) xx p))
                (equal (add (mul (neg 1 p) xx p) yy p)
                       (add 1 (mul d (mul xx yy p) p) p)))
           (equal (add (mul d (mul yy yy p) p) (add yy yy p) p)
                  1)))

(defruledl square-identity-step2
  (implies (and (dm::primep p)
                (fep yy p) (fep d p)
                (equal (mul d (add (mul d (mul yy yy p) p) (add yy yy p) p) p)
                       d))
           (equal (mul (add (mul d yy p) 1 p) (add (mul d yy p) 1 p) p)
                  (add d 1 p))))

(defruledl mul-by-1-local
  (implies (and (dm::primep p) (fep d p))
           (equal (mul d 1 p) d)))

(defruledl square-identity
  (implies (and (dm::primep p)
                (fep xx p) (fep yy p) (fep d p)
                (equal yy (mul (neg 1 p) xx p))
                (equal (add (mul (neg 1 p) xx p) yy p)
                       (add 1 (mul d (mul xx yy p) p) p)))
           (equal (mul (add (mul d yy p) 1 p) (add (mul d yy p) 1 p) p)
                  (add d 1 p)))
  :use (square-identity-step1 square-identity-step2)
  :in-theory '(mul-by-1-local pfield::fep-of-mul pfield::fep-of-add
               (:t pfield::mul) (:t pfield::add)))

(local (include-book "arithmetic-3/top" :dir :system))

(defruledl mod-expt-fast-lemma
  (not (equal (acl2::mod-expt-fast 3022
                                   (/ (1- (edwards-bls12-q)) 2)
                                   (edwards-bls12-q))
              1))
  :enable edwards-bls12-q)

(defruledl mod-expt-lemma
  (not (equal (mod (expt 3022 (/ (1- (edwards-bls12-q)) 2))
                   (edwards-bls12-q))
              1))
  :use (mod-expt-fast-lemma
        (:instance acl2::mod-expt-fast
                   (a 3022)
                   (i (/ (1- (edwards-bls12-q)) 2))
                   (n (edwards-bls12-q))))
  :enable edwards-bls12-q
  :disable ((:e expt)))

(local (include-book "kestrel/crypto/ecurve/prime-field-squares-euler-criterion" :dir :system))

(defruled not-pfield-squarep-of-3022
  (not (pfield-squarep 3022 (edwards-bls12-q)))
  :enable (weak-euler-criterion-contrapositive edwards-bls12-q fep)
  :use mod-expt-lemma
  :disable ((:e expt)))

(defruledl edwards-bls12-curve-components
  (and (equal (twisted-edwards-curve->p (edwards-bls12-curve)) (edwards-bls12-q))
       (equal (twisted-edwards-curve->a (edwards-bls12-curve))
              (neg 1 (edwards-bls12-q)))
       (equal (twisted-edwards-curve->d (edwards-bls12-curve)) 3021)
       (equal (add 3021 1 (edwards-bls12-q)) 3022)
       (posp (edwards-bls12-q))
       (fep 3021 (edwards-bls12-q)))
  :in-theory '((:e twisted-edwards-curve->p)
               (:e twisted-edwards-curve->a)
               (:e twisted-edwards-curve->d)
               (:e edwards-bls12-curve)
               (:e edwards-bls12-q)
               (:e neg)
               (:e add)
               (:e posp)
               (:e fep)
               (:e equal)))

(defruled edwards-bls12-double-y-not-zero
  (implies (point-on-twisted-edwards-p pt (edwards-bls12-curve))
           (not (equal (point-finite->y
                        (twisted-edwards-add pt pt (edwards-bls12-curve)))
                       0)))
  :use (not-pfield-squarep-of-3022
        (:instance twisted-edwards-double-y-zero (curve (edwards-bls12-curve)))
        (:instance square-identity
                   (p (edwards-bls12-q))
                   (d 3021)
                   (xx (mul (point-finite->x pt) (point-finite->x pt)
                            (edwards-bls12-q)))
                   (yy (mul (point-finite->y pt) (point-finite->y pt)
                            (edwards-bls12-q))))
        (:instance pfield-squarep-suff
                   (x 3022)
                   (p (edwards-bls12-q))
                   (r (add (mul 3021 (mul (point-finite->y pt) (point-finite->y pt)
                                          (edwards-bls12-q))
                                (edwards-bls12-q))
                           1 (edwards-bls12-q)))))
  :in-theory '(point-on-twisted-edwards-p
               edwards-bls12-curve-completep
               pfield::fep-of-mul pfield::fep-of-add
               primep-of-edwards-bls12-q
               edwards-bls12-curve-components
               (:e fep) (:t edwards-bls12-q)))
