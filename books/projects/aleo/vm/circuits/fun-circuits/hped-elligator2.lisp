; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Elligator2::encode (circuit/algorithms/src/elligator2/encode.rs) on a
; variable input, against hped-elligator2-encode (fun-specs/hash-elligator2).
;
; Constraints, in snarkVM order (LC = linear combination, no constraint):
;   assert_neq(input, 0)             input * m1 = 1
;   ur2 = D * input^2                input * input = s; ur2 = D s (LC)
;   assert_neq(a^2 ur2, b (1+ur2)^2) (1+ur2)^2 = t; (a^2 ur2 - b t) * m2 = 1
;   v = -a / (1 + ur2)               (1+ur2) * w = 1; v = -a w (LC)
;   v2, v3                           v * v = v2; v2 * v = v3
;   e = g.pow((p-1)/2)               g = v3 + a v2 + b v (LC); square-and-
;                                    multiply on the constant bits
;   x = e v - (1 - e) a/2            e * v = ev; x (LC)
;   x2, x3                           x * x = x2; x2 * x = x3; rhs (LC)
;   witness root; to_bits_be         Field::to_bits_le of the root (boolean
;                                    bits, sum, range check against p - 1)
;   assert(!lsb)                     (1 - b0) * 1 = 1
;   y = -e * root                    (-e) * root = y
;   assert_neq(v e x y, 0)           v * e = ve; ve * x = vex; vex * y = vexy;
;                                    vexy * m3 = 1
;   assert_eq(y^2, rhs)              y * y = y2; y2 * 1 = rhs
;   Montgomery assert_eq             B^3 y2 * 1 = B^3 x3 + A B^2 x2 + B x
;   x' = u / v'                      (B y) * iv = 1; (B x) * iv = xe
;   y' = (u - 1) / (u + 1)           (B x + 1) * iu = 1; (B x - 1) * iu = ye
;   enforce_on_curve(x', y')         crv-group-enforce-on-curve-gadget
;   mul_by_cofactor                  crv-group-mul-by-cofactor-gadget
;
; The square root is a free witness, but the constraints fix it: the bits
; are the canonical bits (the range check makes them unique), the LSB is 0,
; and y^2 = rhs with e = +-1 gives root^2 = rhs.  A field element has at most
; one even square root (hped-ell2-even-root), so the output is determined.

(in-package "ALEOVM")

(include-book "hped-pow")
(include-book "hped-ell2-field")
(include-book "fb2-field-bits")
(include-book "crv-sub-double")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "../edwards-order/group-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hped-ell2-a-half ()
  :returns (ah (pfield::fep ah (ecurve::edwards-bls12-q))
               :hints (("Goal" :in-theory (enable ecurve::edwards-bls12-q pfield::fep))))
  :short "@('a * Field::half()')."
  (pfield::mul (hped-ell2-a)
               (pfield::inv 2 (ecurve::edwards-bls12-q))
               (ecurve::edwards-bls12-q)))

(in-theory (disable (:e hped-ell2-a-half)))

(define hped-be-bits ((n natp))
  :verify-guards nil
  :short "Minimal big-endian bits of @('n')."
  (rev (acl2::nat=>lebits* n)))

(define hped-ell2-exp-bits ()
  :verify-guards nil
  :short "The bits of @('MODULUS_MINUS_ONE_DIV_TWO') after the leading 1."
  (cdr (hped-be-bits (hped-ell2-legendre-exp))))

(defruled hped-ell2-exp-bits-facts
  (and (bit-listp (hped-ell2-exp-bits))
       (equal (hped-pow-exp (hped-ell2-exp-bits) 1) (hped-ell2-legendre-exp)))
  :enable ((:e hped-ell2-exp-bits) (:e hped-ell2-legendre-exp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro hped-ell2-w (name)
  (let ((pos (position name '(m1 s t m2 winv v2 v3 ev x2 x3 q y ve vex vexy m3
                              y2 iv xe iu ye ox2 oy2 xy1 x21 y21 x4 y4 xy2 x22
                              y22 outx outy))))
    `(nth ,pos w)))

(defconst *hped-ell2-nwires* 33)

(define hped-ell2-g-lc (w)
  :verify-guards nil
  :short "@('v^3 + A v^2 + B v'), with @('v = -a w')."
  (b* ((p (ecurve::edwards-bls12-q))
       (a (hped-ell2-a))
       (b (hped-ell2-b))
       (v (hped-lc-scale (pfield::neg a p) (hped-lc-v (hped-ell2-w winv)))))
    (hped-lc-add (hped-lc-add (hped-lc-v (hped-ell2-w v3))
                              (hped-lc-scale a (hped-lc-v (hped-ell2-w v2))))
                 (hped-lc-scale b v))))

(define hped-ell2-e-lc (w pw)
  :verify-guards nil
  (hped-pow-out (hped-ell2-exp-bits) pw (hped-ell2-g-lc w)))

(define hped-ell2-gadget ((in symbolp)
                          (w symbol-listp)
                          (pw true-listp)
                          (bits symbol-listp)
                          (rs symbol-listp)
                          (u symbolp))
  :verify-guards nil
  :short "Constraints of @('Elligator2::encode') on a variable input."
  (b* ((p (ecurve::edwards-bls12-q))
       (a (hped-ell2-a))
       (b (hped-ell2-b))
       (ah (hped-ell2-a-half))
       (d (ecurve::edwards-bls12-d))
       (ma (hped-ell2-montgomery-a))
       (mb (hped-ell2-montgomery-b))
       (mb2 (pfield::mul mb mb p))
       (mb3 (pfield::mul mb2 mb p))
       (one (hped-lc-1))
       (ur2 (hped-lc-scale d (hped-lc-v (hped-ell2-w s))))
       (one+ur2 (hped-lc-add one ur2))
       (v (hped-lc-scale (pfield::neg a p) (hped-lc-v (hped-ell2-w winv))))
       (g (hped-ell2-g-lc w))
       (e (hped-ell2-e-lc w pw))
       (x (hped-lc-sub (hped-lc-v (hped-ell2-w ev))
                       (hped-lc-scale ah (hped-lc-sub one e))))
       (rhs (hped-lc-add (hped-lc-add (hped-lc-v (hped-ell2-w x3))
                                      (hped-lc-scale a (hped-lc-v (hped-ell2-w x2))))
                         (hped-lc-scale b x)))
       (um (hped-lc-scale mb x))
       (q (hped-ell2-w q)))
    (append
     (list (hped-c (hped-lc-v in) (hped-lc-v (hped-ell2-w m1)) one)
           (hped-c (hped-lc-v in) (hped-lc-v in) (hped-lc-v (hped-ell2-w s)))
           (hped-c one+ur2 one+ur2 (hped-lc-v (hped-ell2-w t)))
           (hped-c (hped-lc-sub (hped-lc-scale (pfield::mul a a p) ur2)
                                (hped-lc-scale b (hped-lc-v (hped-ell2-w t))))
                   (hped-lc-v (hped-ell2-w m2))
                   one)
           (hped-c one+ur2 (hped-lc-v (hped-ell2-w winv)) one)
           (hped-c v v (hped-lc-v (hped-ell2-w v2)))
           (hped-c (hped-lc-v (hped-ell2-w v2)) v (hped-lc-v (hped-ell2-w v3))))
     (hped-pow-gadget g (hped-ell2-exp-bits) pw g)
     (list (hped-c e v (hped-lc-v (hped-ell2-w ev)))
           (hped-c x x (hped-lc-v (hped-ell2-w x2)))
           (hped-c (hped-lc-v (hped-ell2-w x2)) x (hped-lc-v (hped-ell2-w x3))))
     (fb-field-write-bits-le-gadget q bits rs u p)
     (list (hped-c (hped-lc-sub one (hped-lc-v (car bits))) one one)
           (hped-c (hped-lc-neg e) (hped-lc-v q) (hped-lc-v (hped-ell2-w y)))
           (hped-c v e (hped-lc-v (hped-ell2-w ve)))
           (hped-c (hped-lc-v (hped-ell2-w ve)) x (hped-lc-v (hped-ell2-w vex)))
           (hped-c (hped-lc-v (hped-ell2-w vex)) (hped-lc-v (hped-ell2-w y))
                   (hped-lc-v (hped-ell2-w vexy)))
           (hped-c (hped-lc-v (hped-ell2-w vexy)) (hped-lc-v (hped-ell2-w m3)) one)
           (hped-c (hped-lc-v (hped-ell2-w y)) (hped-lc-v (hped-ell2-w y))
                   (hped-lc-v (hped-ell2-w y2)))
           (hped-c (hped-lc-v (hped-ell2-w y2)) one rhs)
           (hped-c (hped-lc-scale mb3 (hped-lc-v (hped-ell2-w y2)))
                   one
                   (hped-lc-add (hped-lc-add (hped-lc-scale mb3 (hped-lc-v (hped-ell2-w x3)))
                                             (hped-lc-scale ma (hped-lc-scale mb2 (hped-lc-v (hped-ell2-w x2)))))
                                um))
           (hped-c (hped-lc-scale mb (hped-lc-v (hped-ell2-w y)))
                   (hped-lc-v (hped-ell2-w iv))
                   one)
           (hped-c um (hped-lc-v (hped-ell2-w iv)) (hped-lc-v (hped-ell2-w xe)))
           (hped-c (hped-lc-add um one) (hped-lc-v (hped-ell2-w iu)) one)
           (hped-c (hped-lc-sub um one) (hped-lc-v (hped-ell2-w iu))
                   (hped-lc-v (hped-ell2-w ye))))
     (crv-group-enforce-on-curve-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                        (hped-ell2-w ox2) (hped-ell2-w oy2) p)
     (crv-group-mul-by-cofactor-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                       (hped-ell2-w xy1) (hped-ell2-w x21) (hped-ell2-w y21)
                                       (hped-ell2-w x4) (hped-ell2-w y4)
                                       (hped-ell2-w xy2) (hped-ell2-w x22) (hped-ell2-w y22)
                                       (hped-ell2-w outx) (hped-ell2-w outy)
                                       p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Value-level soundness: the constraint equations determine the point.

(defruled hped-ell2-x-cases
  (b* ((p (ecurve::edwards-bls12-q))
       (a (hped-ell2-a))
       (ah (hped-ell2-a-half)))
    (implies (and (pfield::fep v p)
                  (or (equal e 1) (equal e (pfield::neg 1 p))))
             (equal (pfield::sub (pfield::mul e v p)
                                 (pfield::mul ah (pfield::sub 1 e p) p)
                                 p)
                    (if (equal e 1) v (pfield::sub (pfield::neg v p) a p)))))
  :do-not-induct t
  :enable (hped-ell2-a-half hped-ell2-a ecurve::edwards-bls12-q
           hped-ell2-montgomery-a hped-ell2-montgomery-b))

(defruled hped-ell2-y-cases
  (b* ((p (ecurve::edwards-bls12-q)))
    (implies (and (pfield::fep rt p)
                  (or (equal e 1) (equal e (pfield::neg 1 p))))
             (and (equal (pfield::mul (pfield::neg e p) rt p)
                         (if (equal e 1) (pfield::neg rt p) rt))
                  (equal (pfield::mul (pfield::mul (pfield::neg e p) rt p)
                                      (pfield::mul (pfield::neg e p) rt p)
                                      p)
                         (pfield::mul rt rt p)))))
  :do-not-induct t
  :enable ecurve::edwards-bls12-q)

(defruled hped-ell2-montgomery-iff
  (b* ((p (ecurve::edwards-bls12-q))
       (ma (hped-ell2-montgomery-a))
       (mb (hped-ell2-montgomery-b))
       (mb2 (pfield::mul mb mb p))
       (mb3 (pfield::mul mb2 mb p))
       (x2 (pfield::mul x x p))
       (x3 (pfield::mul x2 x p))
       (y2 (pfield::mul y y p))
       (u (pfield::mul mb x p))
       (vm (pfield::mul mb y p))
       (u2 (pfield::mul u u p)))
    (implies (and (pfield::fep x p) (pfield::fep y p))
             (equal (equal (pfield::mul (pfield::mul mb3 y2 p) 1 p)
                           (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                                     (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                                     p)
                                        u p))
                    (equal (pfield::mul mb (pfield::mul vm vm p) p)
                           (pfield::add (pfield::add (pfield::mul u2 u p)
                                                     (pfield::mul ma u2 p)
                                                     p)
                                        u p)))))
  :do-not-induct t)

(defruled hped-ell2-not-reserrp-of-point-finite
  (not (reserrp (ecurve::point-finite x y)))
  :enable (reserrp ecurve::point-finite))

(set-ignore-ok t)

(defmacro hped-ell2-let (body)
  `(b* ((p (ecurve::edwards-bls12-q))
        (a (hped-ell2-a))
        (b (hped-ell2-b))
        (ah (hped-ell2-a-half))
        (d (ecurve::edwards-bls12-d))
        (ma (hped-ell2-montgomery-a))
        (mb (hped-ell2-montgomery-b))
        (mb2 (pfield::mul mb mb p))
        (mb3 (pfield::mul mb2 mb p))
        (s (pfield::mul r r p))
        (ur2 (pfield::mul d s p))
        (o (pfield::add 1 ur2 p))
        (w (pfield::inv o p))
        (vv (pfield::mul (pfield::neg a p) w p))
        (v2 (pfield::mul vv vv p))
        (v3 (pfield::mul v2 vv p))
        (g (pfield::add (pfield::add v3 (pfield::mul a v2 p) p) (pfield::mul b vv p) p))
        (ev (pfield::mul e vv p))
        (x (pfield::sub ev (pfield::mul ah (pfield::sub 1 e p) p) p))
        (x2 (pfield::mul x x p))
        (x3 (pfield::mul x2 x p))
        (rhs (pfield::add (pfield::add x3 (pfield::mul a x2 p) p) (pfield::mul b x p) p))
        (y (pfield::mul (pfield::neg e p) rt p))
        (y2 (pfield::mul y y p))
        (um (pfield::mul mb x p))
        (iv (pfield::inv (pfield::mul mb y p) p))
        (xe (pfield::mul um iv p))
        (iu (pfield::inv (pfield::add um 1 p) p))
        (ye (pfield::mul (pfield::sub um 1 p) iu p)))
     ,body))

(defmacro hped-ell2-facts ()
  '(and (pfield::fep r p)
        (pfield::fep rt p)
        (not (equal r 0))
        (not (equal (pfield::mul (pfield::mul a a p) ur2 p)
                    (pfield::mul b (pfield::mul o o p) p)))
        (not (equal o 0))
        (equal (hped-ell2-legendre g) e)
        (or (equal e 1) (equal e (pfield::neg 1 p)))
        (not (equal vv 0))
        (not (equal x 0))
        (not (equal y 0))
        (evenp rt)
        (equal (pfield::mul rt rt p) rhs)
        (equal (pfield::mul (pfield::mul mb3 y2 p) 1 p)
               (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                         (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                         p)
                            um p))
        (not (equal (pfield::mul mb y p) 0))
        (not (equal (pfield::add um 1 p) 0))
        (ecurve::edwards-bls12-pointp (ecurve::point-finite xe ye))))

;; Rewrite forms for the minimal theory of hped-ell2-values-sound, with the
;; field (ecurve::edwards-bls12-q) kept unevaluated.

(defruledl hped-ell2-q-bounds
  (and (posp (ecurve::edwards-bls12-q))
       (integerp (ecurve::edwards-bls12-q))
       (< 1 (ecurve::edwards-bls12-q)))
  :enable ecurve::edwards-bls12-q)

(defruledl hped-ell2-minus-one-facts
  (and (not (equal (pfield::neg 1 (ecurve::edwards-bls12-q)) 0))
       (not (equal (pfield::neg 1 (ecurve::edwards-bls12-q)) 1)))
  :enable ecurve::edwards-bls12-q)

(defruledl hped-ell2-a-half-twice
  (equal (pfield::mul (hped-ell2-a-half)
                      (pfield::sub 1 (pfield::neg 1 (ecurve::edwards-bls12-q))
                                   (ecurve::edwards-bls12-q))
                      (ecurve::edwards-bls12-q))
         (hped-ell2-a))
  :enable (hped-ell2-a-half hped-ell2-a ecurve::edwards-bls12-q
           hped-ell2-montgomery-a hped-ell2-montgomery-b))

(defruledl hped-ell2-y2-of-neg
  (equal (pfield::mul (pfield::neg rt (ecurve::edwards-bls12-q))
                      (pfield::neg rt (ecurve::edwards-bls12-q))
                      (ecurve::edwards-bls12-q))
         (pfield::mul rt rt (ecurve::edwards-bls12-q))))

(defruledl hped-ell2-y-form
  (implies (and (pfield::fep rt (ecurve::edwards-bls12-q))
                (or (equal e 1) (equal e (pfield::neg 1 (ecurve::edwards-bls12-q)))))
           (equal (pfield::mul (pfield::neg e (ecurve::edwards-bls12-q)) rt
                               (ecurve::edwards-bls12-q))
                  (if (equal e 1) (pfield::neg rt (ecurve::edwards-bls12-q)) rt)))
  :use hped-ell2-y-cases)

(defruledl hped-ell2-even-root-rewrite
  (implies (and (equal (pfield::mul q q (ecurve::edwards-bls12-q)) rhs)
                (pfield::fep q (ecurve::edwards-bls12-q))
                (evenp q))
           (and (ecurve::pfield-even-squarep rhs (ecurve::edwards-bls12-q))
                (equal (pfield::fep-fix (ecurve::pfield-square->even-root
                                         rhs (ecurve::edwards-bls12-q))
                                        (ecurve::edwards-bls12-q))
                       q)))
  :use hped-ell2-even-root)

(defruledl hped-ell2-even-root-of-square
  (implies (and (pfield::fep q (ecurve::edwards-bls12-q))
                (evenp q))
           (and (ecurve::pfield-even-squarep (pfield::mul q q (ecurve::edwards-bls12-q))
                                             (ecurve::edwards-bls12-q))
                (equal (pfield::fep-fix (ecurve::pfield-square->even-root
                                         (pfield::mul q q (ecurve::edwards-bls12-q))
                                         (ecurve::edwards-bls12-q))
                                        (ecurve::edwards-bls12-q))
                       q)))
  :use (:instance hped-ell2-even-root (rhs (pfield::mul q q (ecurve::edwards-bls12-q)))))

(defruled hped-ell2-values-sound
  (hped-ell2-let
   (implies (hped-ell2-facts)
            (equal (hped-elligator2-encode-without-cofactor-clear r)
                   (ecurve::point-finite xe ye))))
  :do-not-induct t
  :cases ((equal e 1))
  :in-theory (union-theories
              '(hped-elligator2-encode-without-cofactor-clear
                hped-ell2-x-cases hped-ell2-y-form hped-ell2-y2-of-neg
                hped-ell2-even-root-rewrite hped-ell2-even-root-of-square
                hped-ell2-montgomery-iff
                hped-ell2-q-bounds hped-ell2-minus-one-facts hped-ell2-a-half-twice
                return-type-of-hped-ell2-a-half return-type-of-hped-ell2-a
                return-type-of-hped-ell2-b return-type-of-hped-ell2-legendre
                hped-ell2-fep-of-montgomery-a
                hped-ell2-fep-of-montgomery-b
                pfield::fep-of-mul pfield::fep-of-neg pfield::fep-of-add
                pfield::fep-of-sub pfield::fep-of-inv)
              (theory 'minimal-theory)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The constraint equations over plain variables (one variable per wire).

(defrulel hped-ell2-mul-nonzero
  (implies (not (equal (pfield::mul x y p) 0))
           (and (not (equal x 0)) (not (equal y 0))))
  :rule-classes nil)

(defrulel hped-ell2-sub-nonzero
  (implies (and (pfield::fep x p)
                (not (equal (pfield::sub x y p) 0)))
           (not (equal x y)))
  :rule-classes nil
  :enable pfield::sub)

(defmacro hped-ell2-eq-let (body)
  `(b* ((p (ecurve::edwards-bls12-q))
        (a (hped-ell2-a))
        (b (hped-ell2-b))
        (ah (hped-ell2-a-half))
        (d (ecurve::edwards-bls12-d))
        (ma (hped-ell2-montgomery-a))
        (mb (hped-ell2-montgomery-b))
        (mb2 (pfield::mul mb mb p))
        (mb3 (pfield::mul mb2 mb p))
        (ur2 (pfield::mul d s p))
        (o (pfield::add 1 ur2 p))
        (v (pfield::mul (pfield::neg a p) winv p))
        (g (pfield::add (pfield::add v3 (pfield::mul a v2 p) p) (pfield::mul b v p) p))
        (x (pfield::sub ev (pfield::mul ah (pfield::sub 1 e p) p) p))
        (rhs (pfield::add (pfield::add x3 (pfield::mul a x2 p) p) (pfield::mul b x p) p))
        (um (pfield::mul mb x p)))
     ,body))

(defmacro hped-ell2-eqs ()
  '(and (pfield::fep r p) (pfield::fep m1 p) (pfield::fep s p) (pfield::fep tt p)
        (pfield::fep m2 p) (pfield::fep winv p) (pfield::fep v2 p) (pfield::fep v3 p)
        (pfield::fep e p) (pfield::fep ev p) (pfield::fep x2 p) (pfield::fep x3 p)
        (pfield::fep rt p) (pfield::fep y p) (pfield::fep ve p) (pfield::fep vex p)
        (pfield::fep vexy p) (pfield::fep m3 p) (pfield::fep y2 p) (pfield::fep iv p)
        (pfield::fep xe p) (pfield::fep iu p) (pfield::fep ye p)
        (equal (pfield::mul r m1 p) 1)
        (equal (pfield::mul r r p) s)
        (equal (pfield::mul o o p) tt)
        (equal (pfield::mul (pfield::sub (pfield::mul (pfield::mul a a p) ur2 p)
                                         (pfield::mul b tt p) p)
                            m2 p)
               1)
        (equal (pfield::mul o winv p) 1)
        (equal (pfield::mul v v p) v2)
        (equal (pfield::mul v2 v p) v3)
        (equal (hped-ell2-legendre g) e)
        (equal (pfield::mul e v p) ev)
        (equal (pfield::mul x x p) x2)
        (equal (pfield::mul x2 x p) x3)
        (evenp rt)
        (equal (pfield::mul (pfield::neg e p) rt p) y)
        (equal (pfield::mul v e p) ve)
        (equal (pfield::mul ve x p) vex)
        (equal (pfield::mul vex y p) vexy)
        (equal (pfield::mul vexy m3 p) 1)
        (equal (pfield::mul y y p) y2)
        (equal (pfield::mul y2 1 p) rhs)
        (equal (pfield::mul (pfield::mul mb3 y2 p) 1 p)
               (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                         (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                         p)
                            um p))
        (equal (pfield::mul (pfield::mul mb y p) iv p) 1)
        (equal (pfield::mul um iv p) xe)
        (equal (pfield::mul (pfield::add um 1 p) iu p) 1)
        (equal (pfield::mul (pfield::sub um 1 p) iu p) ye)
        (ecurve::edwards-bls12-pointp (ecurve::point-finite xe ye))))

(defruledl hped-ell2-inv-of-witness
  (implies (and (equal (pfield::mul x w p) 1)
                (primep p)
                (pfield::fep x p)
                (pfield::fep w p))
           (equal (pfield::inv x p) w))
  :use hped-ell2-inv-witness)

(defruledl hped-ell2-nonzero-of-witness
  (implies (equal (pfield::mul x w p) 1)
           (not (equal x 0))))

(defruledl hped-ell2-neq-of-witness
  (implies (and (equal (pfield::mul (pfield::sub x y p) w p) 1)
                (pfield::fep x p))
           (not (equal x y)))
  :use ((:instance hped-ell2-sub-nonzero)))

(defrulel hped-ell2-nonzero-chain
  (implies (equal (pfield::mul (pfield::mul (pfield::mul (pfield::mul v e p) x p) y p) m p) 1)
           (and (not (equal v 0)) (not (equal e 0)) (not (equal x 0)) (not (equal y 0))))
  :rule-classes nil)

(defruled hped-ell2-equations-sound
  (hped-ell2-eq-let
   (implies (hped-ell2-eqs)
            (equal (hped-elligator2-encode-without-cofactor-clear r)
                   (ecurve::point-finite xe ye))))
  :do-not-induct t
  :use ((:instance hped-ell2-values-sound)
        hped-ell2-q-facts
        (:instance hped-ell2-legendre-cases (g (hped-ell2-eq-let g)))
        (:instance hped-ell2-nonzero-chain (p (ecurve::edwards-bls12-q))
                   (v (hped-ell2-eq-let v)) (x (hped-ell2-eq-let x)) (m m3)))
  :cases ((equal e 1))
  :in-theory (union-theories
              '(hped-ell2-y-form hped-ell2-y2-of-neg
                hped-ell2-q-bounds hped-ell2-minus-one-facts
                return-type-of-hped-ell2-a-half return-type-of-hped-ell2-a
                return-type-of-hped-ell2-b return-type-of-hped-ell2-legendre
                hped-ell2-fep-of-montgomery-a hped-ell2-fep-of-montgomery-b
                pfield::mul-of-1-arg2 pfield::mul-of-0-arg1 pfield::mul-of-0-arg2
                hped-ell2-inv-of-witness
                hped-ell2-nonzero-of-witness hped-ell2-neq-of-witness
                pfield::fep-of-mul pfield::fep-of-neg pfield::fep-of-add
                pfield::fep-of-sub pfield::fep-of-inv)
              (theory 'minimal-theory)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From the R1CS to the equations.

(defruledl hped-ell2-nth-wire
  (implies (and (symbol-listp w)
                (r1cs::valuation-binds-allp asg w)
                (natp n)
                (< n (len w)))
           (and (symbolp (nth n w))
                (r1cs::valuation-bindsp asg (nth n w))))
  :induct (nth n w)
  :enable (nth r1cs::valuation-binds-allp))

(defruledl hped-ell2-car-wire
  (implies (and (symbol-listp w)
                (r1cs::valuation-binds-allp asg w)
                (< 0 (len w)))
           (and (symbolp (car w))
                (r1cs::valuation-bindsp asg (car w))))
  :enable r1cs::valuation-binds-allp)

(defruledl hped-ell2-integer-length-q
  (equal (integer-length (ecurve::edwards-bls12-q)) 253)
  :enable ecurve::edwards-bls12-q)

(defruledl hped-ell2-car-of-nat=>lebits
  (implies (and (posp width)
                (natp n)
                (< n (expt 2 width)))
           (equal (car (acl2::nat=>lebits width n))
                  (mod n 2)))
  :do-not-induct t
  :cases ((zp n))
  :expand ((acl2::nat=>lendian* 2 n)
           (repeat width 0))
  :enable (acl2::nat=>lebits
           acl2::nat=>lendian
           acl2::mod-when-<
           repeat))

(defruled hped-ell2-bits-even
  :short "The root's bits are canonical and the LSB constraint makes it even."
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget x bits rs u p) asg p)
                (equal (pfield::mul (pfield::sub 1 (lookup-equal (car bits) asg) p) 1 p) 1))
           (evenp (lookup-equal x asg)))
  :do-not-induct t
  :use ((:instance fb-field-write-bits-le-gadget-sound (acc nil))
        primep-of-base-prime
        fb-base-prime-below-2-253
        (:instance r1cs::fep-of-lookup-equal (r1cs::valuation asg) (r1cs::prime p) (r1cs::var x))
        (:instance hped-ell2-car-of-nat=>lebits
                   (width (base-field-size-in-bits))
                   (n (lookup-equal x asg))))
  :enable (field-write-bits-le-funspec field-bits-le
           pfield::fep-fix-when-fep base-field-size-in-bits evenp
           curve-base-prime-is-edwards-bls12-q pfield::fep)
  :disable (fb-field-write-bits-le-gadget-sound r1cs::fep-of-lookup-equal
            r1cs::<-of-lookup-equal-when-r1cs-valuationp)
  :cases ((consp bits))
  :hints (("Subgoal 1" :in-theory (enable lookup-equal-list))))

(defruled hped-ell2-cofactor-sound
  (implies (and (symbolp xe) (symbolp ye) (symbolp ox2) (symbolp oy2)
                (symbolp xy1) (symbolp x21) (symbolp y21)
                (symbolp x4) (symbolp y4)
                (symbolp xy2) (symbolp x22) (symbolp y22)
                (symbolp outx) (symbolp outy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xe) (r1cs::valuation-bindsp asg ye)
                (r1cs::valuation-bindsp asg ox2) (r1cs::valuation-bindsp asg oy2)
                (r1cs::valuation-bindsp asg xy1) (r1cs::valuation-bindsp asg x21)
                (r1cs::valuation-bindsp asg y21) (r1cs::valuation-bindsp asg x4)
                (r1cs::valuation-bindsp asg y4) (r1cs::valuation-bindsp asg xy2)
                (r1cs::valuation-bindsp asg x22) (r1cs::valuation-bindsp asg y22)
                (r1cs::valuation-bindsp asg outx) (r1cs::valuation-bindsp asg outy)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-enforce-on-curve-gadget xe ye ox2 oy2 p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-mul-by-cofactor-gadget
                  xe ye xy1 x21 y21 x4 y4 xy2 x22 y22 outx outy p)
                 asg p))
           (b* ((pt (ecurve::point-finite (lookup-equal xe asg) (lookup-equal ye asg)))
                (pt2 (ecurve::edwards-bls12-add pt pt)))
             (and (ecurve::edwards-bls12-pointp pt)
                  (equal (ecurve::point-finite (lookup-equal outx asg)
                                               (lookup-equal outy asg))
                         (ecurve::edwards-bls12-add pt2 pt2)))))
  :do-not-induct t
  :use (primep-of-base-prime
        (:instance crv-group-enforce-on-curve-wire-sound
                   (x xe) (y ye) (x2 ox2) (y2 oy2))
        (:instance crv-group-mul-by-cofactor-gadget-sound
                   (x xe) (y ye) (x3 outx) (y3 outy)
                   (pt (ecurve::point-finite (lookup-equal xe asg) (lookup-equal ye asg))))
        (:instance crv-mul-by-cofactor-is-double-double
                   (pt (ecurve::point-finite (lookup-equal xe asg) (lookup-equal ye asg)))))
  :enable (group-double-funspec r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type)
  :disable (crv-group-enforce-on-curve-wire-sound
            crv-group-mul-by-cofactor-gadget-sound))

(defruled hped-ell2-encode-of-point
  (b* ((pt (ecurve::point-finite x y))
       (pt2 (ecurve::edwards-bls12-add pt pt)))
    (implies (and (equal (hped-elligator2-encode-without-cofactor-clear r) pt)
                  (pfield::fep r (ecurve::edwards-bls12-q))
                  (ecurve::edwards-bls12-pointp pt))
             (and (hped-elligator2-encode-validp r)
                  (equal (hped-elligator2-encode r)
                         (ecurve::edwards-bls12-add pt2 pt2)))))
  :do-not-induct t
  :use ((:instance ecurve::edwards-bls12-r-pointp-of-4q (ecurve::q (ecurve::point-finite x y)))
        hped-ell2-not-reserrp-of-point-finite)
  :enable (hped-elligator2-encode hped-elligator2-encode-validp))

(defruledl hped-ell2-holdp-of-nil
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(defruledl hped-ell2-fep-of-d
  (pfield::fep (ecurve::edwards-bls12-d) (ecurve::edwards-bls12-q))
  :enable (ecurve::edwards-bls12-d ecurve::edwards-bls12-q))

(defruledl hped-ell2-pow-is-legendre
  (equal (pfield::pow g (hped-ell2-legendre-exp) (ecurve::edwards-bls12-q))
         (hped-ell2-legendre g))
  :enable hped-ell2-legendre)

(defmacro hped-ell2-wv (name)
  `(lookup-equal (hped-ell2-w ,name) asg))

(defmacro hped-ell2-gadget-hyps ()
  '(and (equal p (base-prime))
        (symbolp in)
        (symbol-listp w)
        (equal (len w) *hped-ell2-nwires*)
        (symbol-listp bits)
        (symbol-listp rs)
        (symbolp u)
        (equal (len bits) (integer-length p))
        (equal (len rs) (bits-lt-prime-rlen p))
        (hped-pw-boundp (hped-ell2-exp-bits) pw asg)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg in)
        (r1cs::valuation-binds-allp asg w)
        (r1cs::valuation-binds-allp asg bits)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)))

(defmacro hped-ell2-wire-let (body)
  `(b* ((r (lookup-equal in asg))
        (m1 (hped-ell2-wv m1)) (s (hped-ell2-wv s)) (tt (hped-ell2-wv t))
        (m2 (hped-ell2-wv m2)) (winv (hped-ell2-wv winv))
        (v2 (hped-ell2-wv v2)) (v3 (hped-ell2-wv v3))
        (e (r1cs::dot-product (hped-ell2-e-lc w pw) asg (ecurve::edwards-bls12-q)))
        (ev (hped-ell2-wv ev)) (x2 (hped-ell2-wv x2)) (x3 (hped-ell2-wv x3))
        (rt (hped-ell2-wv q)) (y (hped-ell2-wv y)) (ve (hped-ell2-wv ve))
        (vex (hped-ell2-wv vex)) (vexy (hped-ell2-wv vexy))
        (m3 (hped-ell2-wv m3)) (y2 (hped-ell2-wv y2)) (iv (hped-ell2-wv iv))
        (xe (hped-ell2-wv xe)) (iu (hped-ell2-wv iu)) (ye (hped-ell2-wv ye)))
     ,body))

(defmacro hped-ell2-expansion-theory ()
  '(union-theories
    '(hped-ell2-gadget hped-ell2-g-lc hped-ell2-e-lc
      r1cs::r1cs-constraints-holdp-of-append
      r1cs::r1cs-constraints-holdp-of-cons
      hped-ell2-holdp-of-nil
      hped-holdsp-of-c
      hped-dot-of-lc-v hped-dot-of-lc-1 hped-dot-of-lc-add
      hped-dot-of-lc-scale hped-dot-of-lc-neg hped-dot-of-lc-sub
      curve-base-prime-is-edwards-bls12-q
      hped-ell2-nth-wire hped-ell2-car-wire hped-ell2-integer-length-q
      hped-ell2-q-bounds hped-ell2-fep-of-d
      r1cs::fep-of-lookup-equal r1cs::fep-of-dot-product
      return-type-of-hped-ell2-a-half return-type-of-hped-ell2-a
      return-type-of-hped-ell2-b return-type-of-hped-ell2-legendre
      hped-ell2-fep-of-montgomery-a hped-ell2-fep-of-montgomery-b
      pfield::fep-of-mul pfield::fep-of-neg pfield::fep-of-add
      pfield::fep-of-sub pfield::fep-of-inv
      (:e len) (:e nth) (:e <) (:e natp) (:e integer-length) (:e bits-lt-prime-rlen))
    (theory 'minimal-theory)))

(defmacro hped-ell2-arith-eqs ()
  '(and (equal (pfield::mul r m1 p) 1)
                       (equal (pfield::mul r r p) s)
                       (equal (pfield::mul o o p) tt)
                       (equal (pfield::mul (pfield::sub (pfield::mul (pfield::mul a a p) ur2 p)
                                                        (pfield::mul b tt p) p)
                                           m2 p)
                              1)
                       (equal (pfield::mul o winv p) 1)
                       (equal (pfield::mul v v p) v2)
                       (equal (pfield::mul v2 v p) v3)
                       (equal (pfield::mul e v p) ev)
                       (equal (pfield::mul x x p) x2)
                       (equal (pfield::mul x2 x p) x3)
                       (equal (pfield::mul (pfield::neg e p) rt p) y)
                       (equal (pfield::mul v e p) ve)
                       (equal (pfield::mul ve x p) vex)
                       (equal (pfield::mul vex y p) vexy)
                       (equal (pfield::mul vexy m3 p) 1)
                       (equal (pfield::mul y y p) y2)
                       (equal (pfield::mul y2 1 p) rhs)
                       (equal (pfield::mul (pfield::mul mb3 y2 p) 1 p)
                              (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                                        (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                                        p)
                                           um p))
                       (equal (pfield::mul (pfield::mul mb y p) iv p) 1)
                       (equal (pfield::mul um iv p) xe)
                       (equal (pfield::mul (pfield::add um 1 p) iu p) 1)
                       (equal (pfield::mul (pfield::sub um 1 p) iu p) ye)))

(defruled hped-ell2-gadget-expand
  (implies (and (hped-ell2-gadget-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hped-ell2-gadget in w pw bits rs u) asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (hped-pow-gadget (hped-ell2-g-lc w) (hped-ell2-exp-bits) pw
                                  (hped-ell2-g-lc w))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget (hped-ell2-w q) bits rs u p) asg p)
                (equal (pfield::mul (pfield::sub 1 (lookup-equal (car bits) asg) p) 1 p) 1)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-enforce-on-curve-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                                    (hped-ell2-w ox2) (hped-ell2-w oy2) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-mul-by-cofactor-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                                   (hped-ell2-w xy1) (hped-ell2-w x21)
                                                   (hped-ell2-w y21) (hped-ell2-w x4)
                                                   (hped-ell2-w y4) (hped-ell2-w xy2)
                                                   (hped-ell2-w x22) (hped-ell2-w y22)
                                                   (hped-ell2-w outx) (hped-ell2-w outy)
                                                   p)
                 asg p)
                (hped-ell2-wire-let
                 (hped-ell2-eq-let
                  (hped-ell2-arith-eqs)))))
  :do-not-induct t
  :use hped-ell2-q-facts
  :in-theory (hped-ell2-expansion-theory))

(defruled hped-elligator2-gadget-sound
  :short "Soundness over the wires: the constraints imply that Elligator2
          succeeds on the input and that the output wires are its point."
  (implies (and (hped-ell2-gadget-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hped-ell2-gadget in w pw bits rs u) asg p))
           (b* ((r (lookup-equal in asg)))
             (and (hped-elligator2-encode-validp r)
                  (equal (ecurve::point-finite (hped-ell2-wv outx) (hped-ell2-wv outy))
                         (hped-elligator2-encode r)))))
  :do-not-induct t
  :use (hped-ell2-q-facts
        hped-ell2-gadget-expand
        (:instance hped-ell2-equations-sound
                   (r (lookup-equal in asg))
                   (m1 (hped-ell2-wv m1)) (s (hped-ell2-wv s)) (tt (hped-ell2-wv t))
                   (m2 (hped-ell2-wv m2)) (winv (hped-ell2-wv winv))
                   (v2 (hped-ell2-wv v2)) (v3 (hped-ell2-wv v3))
                   (e (r1cs::dot-product (hped-ell2-e-lc w pw) asg (ecurve::edwards-bls12-q)))
                   (ev (hped-ell2-wv ev)) (x2 (hped-ell2-wv x2)) (x3 (hped-ell2-wv x3))
                   (rt (hped-ell2-wv q)) (y (hped-ell2-wv y)) (ve (hped-ell2-wv ve))
                   (vex (hped-ell2-wv vex)) (vexy (hped-ell2-wv vexy))
                   (m3 (hped-ell2-wv m3)) (y2 (hped-ell2-wv y2)) (iv (hped-ell2-wv iv))
                   (xe (hped-ell2-wv xe)) (iu (hped-ell2-wv iu)) (ye (hped-ell2-wv ye)))
        (:instance hped-pow-gadget-sound
                   (cs (hped-ell2-exp-bits))
                   (g (hped-ell2-g-lc w))
                   (acc (hped-ell2-g-lc w))
                   (k 1))
        (:instance hped-ell2-bits-even (x (hped-ell2-w q)))
        (:instance hped-ell2-cofactor-sound
                   (xe (hped-ell2-w xe)) (ye (hped-ell2-w ye))
                   (ox2 (hped-ell2-w ox2)) (oy2 (hped-ell2-w oy2))
                   (xy1 (hped-ell2-w xy1)) (x21 (hped-ell2-w x21)) (y21 (hped-ell2-w y21))
                   (x4 (hped-ell2-w x4)) (y4 (hped-ell2-w y4))
                   (xy2 (hped-ell2-w xy2)) (x22 (hped-ell2-w x22)) (y22 (hped-ell2-w y22))
                   (outx (hped-ell2-w outx)) (outy (hped-ell2-w outy)))
        (:instance hped-ell2-encode-of-point
                   (r (lookup-equal in asg))
                   (x (hped-ell2-wv xe)) (y (hped-ell2-wv ye))))
  :in-theory (union-theories '(hped-ell2-exp-bits-facts hped-ell2-pow-is-legendre
                               pfield::pow-of-1-arg2)
                             (hped-ell2-expansion-theory)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness: on a valid input, the canonical witness satisfies the
;; constraints.

(defruledl hped-ell2-mul-inv
  (implies (and (primep p)
                (pfield::fep x p)
                (not (equal x 0)))
           (equal (pfield::mul x (pfield::inv x p) p) 1)))

(defruledl hped-ell2-mul-not-zero
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p)
                (not (equal x 0))
                (not (equal y 0)))
           (not (equal (pfield::mul x y p) 0))))

(defruledl hped-ell2-sub-not-zero
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p)
                (not (equal x y)))
           (not (equal (pfield::sub x y p) 0))))

(defruledl hped-ell2-even-root-facts
  (b* ((rt (pfield::fep-fix (ecurve::pfield-square->even-root rhs (ecurve::edwards-bls12-q))
                            (ecurve::edwards-bls12-q))))
    (implies (ecurve::pfield-even-squarep rhs (ecurve::edwards-bls12-q))
             (and (pfield::fep rt (ecurve::edwards-bls12-q))
                  (evenp rt))))
  :enable (ecurve::pfield-even-squarep pfield::fep-fix-when-fep))

(defruledl hped-ell2-reserrp-of-reserr
  (reserrp (reserr x))
  :enable reserrp)

(defruledl hped-ell2-montgomery-iff-1
  (b* ((p (ecurve::edwards-bls12-q))
       (ma (hped-ell2-montgomery-a))
       (mb (hped-ell2-montgomery-b))
       (mb2 (pfield::mul mb mb p))
       (mb3 (pfield::mul mb2 mb p))
       (x2 (pfield::mul x x p))
       (x3 (pfield::mul x2 x p))
       (y2 (pfield::mul y y p))
       (u (pfield::mul mb x p))
       (vm (pfield::mul mb y p))
       (u2 (pfield::mul u u p)))
    (implies (and (pfield::fep x p) (pfield::fep y p))
             (equal (equal (pfield::mul mb3 y2 p)
                           (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                                     (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                                     p)
                                        u p))
                    (equal (pfield::mul mb (pfield::mul vm vm p) p)
                           (pfield::add (pfield::add (pfield::mul u2 u p)
                                                     (pfield::mul ma u2 p)
                                                     p)
                                        u p)))))
  :use hped-ell2-montgomery-iff
  :in-theory (enable pfield::mul-of-1-arg2))

(defruledl hped-ell2-montgomery-iff-neg
  (b* ((p (ecurve::edwards-bls12-q))
       (ma (hped-ell2-montgomery-a))
       (mb (hped-ell2-montgomery-b))
       (mb2 (pfield::mul mb mb p))
       (mb3 (pfield::mul mb2 mb p))
       (x2 (pfield::mul x x p))
       (x3 (pfield::mul x2 x p))
       (y2 (pfield::mul rt rt p))
       (u (pfield::mul mb x p))
       (vm (pfield::mul mb (pfield::neg rt p) p))
       (u2 (pfield::mul u u p)))
    (implies (and (pfield::fep x p) (pfield::fep rt p))
             (equal (equal (pfield::mul mb3 y2 p)
                           (pfield::add (pfield::add (pfield::mul mb3 x3 p)
                                                     (pfield::mul ma (pfield::mul mb2 x2 p) p)
                                                     p)
                                        u p))
                    (equal (pfield::mul mb (pfield::mul vm vm p) p)
                           (pfield::add (pfield::add (pfield::mul u2 u p)
                                                     (pfield::mul ma u2 p)
                                                     p)
                                        u p)))))
  :use ((:instance hped-ell2-montgomery-iff-1 (y (pfield::neg rt (ecurve::edwards-bls12-q))))
        hped-ell2-y2-of-neg hped-ell2-q-bounds)
  :in-theory '(pfield::fep-of-neg))

(defruledl hped-ell2-fep-of-1
  (pfield::fep 1 (ecurve::edwards-bls12-q))
  :enable ecurve::edwards-bls12-q)

(defruled hped-ell2-validp-forward
  (implies (hped-elligator2-encode-validp r)
           (and (pfield::fep r (ecurve::edwards-bls12-q))
                (not (reserrp (hped-elligator2-encode-without-cofactor-clear r)))))
  :enable (hped-elligator2-encode-validp hped-elligator2-encode))

(defmacro hped-ell2-canon-let (body)
  `(b* ((p (ecurve::edwards-bls12-q))
        (a (hped-ell2-a))
        (b (hped-ell2-b))
        (ah (hped-ell2-a-half))
        (d (ecurve::edwards-bls12-d))
        (mb (hped-ell2-montgomery-b))
        (s (pfield::mul r r p))
        (o (pfield::add 1 (pfield::mul d s p) p))
        (winv (pfield::inv o p))
        (v (pfield::mul (pfield::neg a p) winv p))
        (v2 (pfield::mul v v p))
        (v3 (pfield::mul v2 v p))
        (g (pfield::add (pfield::add v3 (pfield::mul a v2 p) p) (pfield::mul b v p) p))
        (e (hped-ell2-legendre g))
        (ev (pfield::mul e v p))
        (x (pfield::sub ev (pfield::mul ah (pfield::sub 1 e p) p) p))
        (x2 (pfield::mul x x p))
        (x3 (pfield::mul x2 x p))
        (rhs (pfield::add (pfield::add x3 (pfield::mul a x2 p) p) (pfield::mul b x p) p))
        (rt (pfield::fep-fix (ecurve::pfield-square->even-root rhs p) p))
        (y (pfield::mul (pfield::neg e p) rt p))
        (ve (pfield::mul v e p))
        (vex (pfield::mul ve x p))
        (vexy (pfield::mul vex y p))
        (y2 (pfield::mul y y p))
        (um (pfield::mul mb x p))
        (iv (pfield::inv (pfield::mul mb y p) p))
        (xe (pfield::mul um iv p))
        (iu (pfield::inv (pfield::add um 1 p) p))
        (ye (pfield::mul (pfield::sub um 1 p) iu p))
        (m1 (pfield::inv r p))
        (tt (pfield::mul o o p))
        (m2 (pfield::inv (pfield::sub (pfield::mul (pfield::mul a a p) (pfield::mul d s p) p)
                                      (pfield::mul b tt p) p)
                         p))
        (m3 (pfield::inv vexy p)))
     ,body))

(defmacro hped-ell2-canon-theory ()
  '(union-theories
               '(hped-elligator2-encode-without-cofactor-clear
                 hped-ell2-x-cases hped-ell2-y-form hped-ell2-y2-of-neg
                 hped-ell2-montgomery-iff-1 hped-ell2-even-root-facts
                 hped-ell2-mul-inv hped-ell2-mul-not-zero hped-ell2-sub-not-zero
                 hped-ell2-q-bounds hped-ell2-minus-one-facts hped-ell2-a-half-twice
                 hped-ell2-fep-of-d hped-ell2-fep-of-1
                 return-type-of-hped-ell2-a-half return-type-of-hped-ell2-a
                 return-type-of-hped-ell2-b return-type-of-hped-ell2-legendre
                 hped-ell2-fep-of-montgomery-a hped-ell2-fep-of-montgomery-b
                 pfield::mul-of-1-arg2 pfield::fep-of-fep-fix
                 pfield::fep-of-mul pfield::fep-of-neg pfield::fep-of-add
                 pfield::fep-of-sub pfield::fep-of-inv
                 hped-ell2-reserrp-of-reserr)
               (theory 'minimal-theory)))

(defrule hped-ell2-canonical-equations
  (implies (and (pfield::fep r (ecurve::edwards-bls12-q))
                (not (reserrp (hped-elligator2-encode-without-cofactor-clear r))))
           (hped-ell2-canon-let
            (hped-ell2-eq-let (hped-ell2-eqs))))
  :rule-classes nil
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance hped-ell2-legendre-cases (g (hped-ell2-canon-let g))))
  :cases ((equal (hped-ell2-canon-let e) 1))
  :in-theory (hped-ell2-canon-theory)
  :hints (("Subgoal 1" :in-theory (union-theories '(hped-ell2-montgomery-iff-neg)
                                                    (hped-ell2-canon-theory)))))

(defmacro hped-ell2-wire-vars ()
  '(and (equal (lookup-equal in asg) r)
        (equal (hped-ell2-wv m1) m1) (equal (hped-ell2-wv s) s) (equal (hped-ell2-wv t) tt)
        (equal (hped-ell2-wv m2) m2) (equal (hped-ell2-wv winv) winv)
        (equal (hped-ell2-wv v2) v2) (equal (hped-ell2-wv v3) v3)
        (equal (hped-ell2-wv ev) ev) (equal (hped-ell2-wv x2) x2) (equal (hped-ell2-wv x3) x3)
        (equal (hped-ell2-wv q) rt) (equal (hped-ell2-wv y) y) (equal (hped-ell2-wv ve) ve)
        (equal (hped-ell2-wv vex) vex) (equal (hped-ell2-wv vexy) vexy)
        (equal (hped-ell2-wv m3) m3) (equal (hped-ell2-wv y2) y2) (equal (hped-ell2-wv iv) iv)
        (equal (hped-ell2-wv xe) xe) (equal (hped-ell2-wv iu) iu) (equal (hped-ell2-wv ye) ye)))

(defruled hped-ell2-gadget-unexpand
  (implies (and (hped-ell2-gadget-hyps)
                (hped-ell2-wire-vars)
                (equal (r1cs::dot-product (hped-ell2-e-lc w pw) asg p) e)
                (r1cs::r1cs-constraints-holdp
                 (hped-pow-gadget (hped-ell2-g-lc w) (hped-ell2-exp-bits) pw
                                  (hped-ell2-g-lc w))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget (hped-ell2-w q) bits rs u p) asg p)
                (equal (pfield::mul (pfield::sub 1 (lookup-equal (car bits) asg) p) 1 p) 1)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-enforce-on-curve-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                                    (hped-ell2-w ox2) (hped-ell2-w oy2) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-mul-by-cofactor-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                                   (hped-ell2-w xy1) (hped-ell2-w x21)
                                                   (hped-ell2-w y21) (hped-ell2-w x4)
                                                   (hped-ell2-w y4) (hped-ell2-w xy2)
                                                   (hped-ell2-w x22) (hped-ell2-w y22)
                                                   (hped-ell2-w outx) (hped-ell2-w outy)
                                                   p)
                 asg p)
                (hped-ell2-eq-let (hped-ell2-arith-eqs)))
           (r1cs::r1cs-constraints-holdp
            (hped-ell2-gadget in w pw bits rs u) asg p))
  :do-not-induct t
  :use hped-ell2-q-facts
  :in-theory (hped-ell2-expansion-theory))

(defruled hped-ell2-lsb-complete
  (implies (and (consp bits)
                (equal (lookup-equal-list bits asg) (field-bits-le rt))
                (pfield::fep rt (ecurve::edwards-bls12-q))
                (evenp rt))
           (equal (pfield::mul (pfield::sub 1 (lookup-equal (car bits) asg)
                                            (ecurve::edwards-bls12-q))
                               1 (ecurve::edwards-bls12-q))
                  1))
  :do-not-induct t
  :use ((:instance hped-ell2-even-lsb-zero (y rt))
        (:instance hped-ell2-lookup-list-car (keys bits) (alist asg)))
  :prep-lemmas
  ((defruled hped-ell2-even-lsb-zero
     (implies (and (pfield::fep y (ecurve::edwards-bls12-q))
                   (evenp y))
              (equal (car (field-bits-le y)) 0))
     :use (fb-base-prime-below-2-253
           (:instance hped-ell2-car-of-nat=>lebits
                      (width (base-field-size-in-bits))
                      (n y)))
     :enable (field-bits-le pfield::fep-fix-when-fep base-field-size-in-bits
              curve-base-prime-is-edwards-bls12-q pfield::fep evenp
              ecurve::edwards-bls12-q))
   (defruled hped-ell2-lookup-list-car
     (implies (consp keys)
              (equal (car (lookup-equal-list keys alist))
                     (lookup-equal (car keys) alist)))
     :enable lookup-equal-list)))

(defmacro hped-ell2-aux-wires ()
  '(b* ((pt (ecurve::point-finite xe ye))
        (pt2 (group-double-funspec pt)))
     (and (equal (hped-ell2-wv ox2) (pfield::mul xe xe p))
          (equal (hped-ell2-wv oy2) (pfield::mul ye ye p))
          (equal (hped-ell2-wv xy1) (pfield::mul xe ye p))
          (equal (hped-ell2-wv x21) (pfield::mul xe xe p))
          (equal (hped-ell2-wv y21) (pfield::mul ye ye p))
          (equal (hped-ell2-wv x4) (ecurve::point-finite->x pt2))
          (equal (hped-ell2-wv y4) (ecurve::point-finite->y pt2))
          (equal (hped-ell2-wv xy2) (pfield::mul (ecurve::point-finite->x pt2)
                                                 (ecurve::point-finite->y pt2) p))
          (equal (hped-ell2-wv x22) (pfield::mul (ecurve::point-finite->x pt2)
                                                 (ecurve::point-finite->x pt2) p))
          (equal (hped-ell2-wv y22) (pfield::mul (ecurve::point-finite->y pt2)
                                                 (ecurve::point-finite->y pt2) p))
          (equal (hped-ell2-wv outx)
                 (ecurve::point-finite->x (group-mul-by-cofactor-funspec pt)))
          (equal (hped-ell2-wv outy)
                 (ecurve::point-finite->y (group-mul-by-cofactor-funspec pt))))))

(defmacro hped-ell2-bit-wires ()
  '(and (equal (lookup-equal-list bits asg) (field-bits-le rt))
        (equal (lookup-equal-list rs asg)
               (fb-bits-lte-const-witness (lookup-equal-list bits asg)
                                          (acl2::nat=>lebits* (1- p))))
        (hped-pw-canonp (hped-ell2-g-lc w) (hped-ell2-exp-bits) pw (hped-ell2-g-lc w) asg p)))

(defmacro hped-ell2-complete-hyps ()
  '(and (hped-ell2-gadget-hyps)
        (hped-ell2-wire-vars)
        (hped-ell2-eq-let (hped-ell2-eqs))
        (hped-ell2-bit-wires)
        (hped-ell2-aux-wires)))

(defmacro hped-ell2-complete-theory (&rest names)
  `(union-theories '(hped-ell2-exp-bits-facts hped-ell2-pow-is-legendre
                     pfield::pow-of-1-arg2
                     ecurve::point-finite->x-of-point-finite
                     ecurve::point-finite->y-of-point-finite
                     hped-ell2-nfix-of-wire fieldp hped-ell2-consp-of-len
                     r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type
                     ,@names)
                   (hped-ell2-expansion-theory)))

(defruledl hped-ell2-nfix-of-wire
  (implies (and (r1cs::r1cs-valuationp asg p)
                (symbol-listp w)
                (r1cs::valuation-binds-allp asg w)
                (natp n)
                (< n (len w)))
           (equal (nfix (lookup-equal (nth n w) asg))
                  (lookup-equal (nth n w) asg)))
  :use hped-ell2-nth-wire)

(defruledl hped-ell2-consp-of-len
  (implies (< 0 (len x)) (consp x)))

(defruledl hped-ell2-complete-pow
  (implies (hped-ell2-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (hped-pow-gadget (hped-ell2-g-lc w) (hped-ell2-exp-bits) pw (hped-ell2-g-lc w))
            asg p))
  :do-not-induct t
  :use (primep-of-base-prime
        (:instance hped-pow-gadget-complete
                   (cs (hped-ell2-exp-bits)) (g (hped-ell2-g-lc w)) (acc (hped-ell2-g-lc w))))
  :in-theory '(curve-base-prime-is-edwards-bls12-q))

(defruledl hped-ell2-complete-e
  (implies (hped-ell2-complete-hyps)
           (equal (r1cs::dot-product (hped-ell2-e-lc w pw) asg p) e))
  :do-not-induct t
  :use (hped-ell2-q-facts
        hped-ell2-complete-pow
        (:instance hped-pow-gadget-sound
                   (cs (hped-ell2-exp-bits)) (g (hped-ell2-g-lc w)) (acc (hped-ell2-g-lc w))
                   (k 1)))
  :in-theory (hped-ell2-complete-theory))

(defruledl hped-ell2-complete-bits
  (implies (hped-ell2-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (fb-field-write-bits-le-gadget (hped-ell2-w q) bits rs u p) asg p))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance fb2-field-write-bits-le-gadget-complete (x (hped-ell2-w q))))
  :in-theory (hped-ell2-complete-theory))

(defruledl hped-ell2-complete-lsb
  (implies (hped-ell2-complete-hyps)
           (equal (pfield::mul (pfield::sub 1 (lookup-equal (car bits) asg) p) 1 p) 1))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance hped-ell2-lsb-complete))
  :in-theory (hped-ell2-complete-theory))

(defruledl hped-ell2-complete-on-curve
  (implies (hped-ell2-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (crv-group-enforce-on-curve-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                               (hped-ell2-w ox2) (hped-ell2-w oy2) p)
            asg p))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance crv-group-enforce-on-curve-gadget-complete
                   (x (hped-ell2-w xe)) (y (hped-ell2-w ye))
                   (x2 (hped-ell2-w ox2)) (y2 (hped-ell2-w oy2))
                   (pt (ecurve::point-finite xe ye))))
  :in-theory (hped-ell2-complete-theory))

(defruledl hped-ell2-complete-cofactor
  (implies (hped-ell2-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (crv-group-mul-by-cofactor-gadget (hped-ell2-w xe) (hped-ell2-w ye)
                                              (hped-ell2-w xy1) (hped-ell2-w x21)
                                              (hped-ell2-w y21) (hped-ell2-w x4)
                                              (hped-ell2-w y4) (hped-ell2-w xy2)
                                              (hped-ell2-w x22) (hped-ell2-w y22)
                                              (hped-ell2-w outx) (hped-ell2-w outy)
                                              p)
            asg p))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance crv-group-mul-by-cofactor-gadget-complete
                   (x (hped-ell2-w xe)) (y (hped-ell2-w ye))
                   (xy1 (hped-ell2-w xy1)) (x21 (hped-ell2-w x21)) (y21 (hped-ell2-w y21))
                   (x4 (hped-ell2-w x4)) (y4 (hped-ell2-w y4))
                   (xy2 (hped-ell2-w xy2)) (x22 (hped-ell2-w x22)) (y22 (hped-ell2-w y22))
                   (x3 (hped-ell2-w outx)) (y3 (hped-ell2-w outy))
                   (pt (ecurve::point-finite xe ye))))
  :in-theory (hped-ell2-complete-theory))

(defruled hped-ell2-gadget-complete-vars
  (implies (hped-ell2-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (hped-ell2-gadget in w pw bits rs u) asg p))
  :do-not-induct t
  :use (hped-ell2-gadget-unexpand
        hped-ell2-complete-pow hped-ell2-complete-e hped-ell2-complete-bits
        hped-ell2-complete-lsb hped-ell2-complete-on-curve hped-ell2-complete-cofactor)
  :in-theory nil)

(defruled hped-elligator2-gadget-complete
  :short "Completeness: on a valid input, the canonical witness (inverses,
          products, snarkVM's Legendre power, the even square root and its
          canonical bits, and the curve and doubling intermediates)
          satisfies the constraints."
  (implies (and (hped-ell2-gadget-hyps)
                (hped-elligator2-encode-validp (lookup-equal in asg))
                (b* ((r (lookup-equal in asg)))
                  (hped-ell2-canon-let
                   (and (hped-ell2-wire-vars)
                        (hped-ell2-bit-wires)
                        (hped-ell2-aux-wires)))))
           (r1cs::r1cs-constraints-holdp
            (hped-ell2-gadget in w pw bits rs u) asg p))
  :do-not-induct t
  :use ((:instance hped-ell2-validp-forward (r (lookup-equal in asg)))
        (:instance hped-ell2-canonical-equations (r (lookup-equal in asg)))
        (:instance hped-ell2-gadget-complete-vars
                   (r (lookup-equal in asg))
                   (m1 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let m1)))
                   (s (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let s)))
                   (tt (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let tt)))
                   (m2 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let m2)))
                   (winv (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let winv)))
                   (v2 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let v2)))
                   (v3 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let v3)))
                   (e (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let e)))
                   (ev (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let ev)))
                   (x2 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let x2)))
                   (x3 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let x3)))
                   (rt (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let rt)))
                   (y (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let y)))
                   (ve (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let ve)))
                   (vex (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let vex)))
                   (vexy (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let vexy)))
                   (m3 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let m3)))
                   (y2 (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let y2)))
                   (iv (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let iv)))
                   (xe (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let xe)))
                   (iu (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let iu)))
                   (ye (b* ((r (lookup-equal in asg))) (hped-ell2-canon-let ye)))))
  :in-theory '(curve-base-prime-is-edwards-bls12-q))
