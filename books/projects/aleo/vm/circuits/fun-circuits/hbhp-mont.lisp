; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Montgomery form used by BHPHasher, on Edwards-BLS12 points.
;
; A point (x, y) with x /= 0 has Montgomery image
;   u = (1 + y) / (1 - y),  v = u / x
; (BHPHasher::Inject::new); x /= 0 rules out y = 1 and y = -1.  The
; Montgomery coefficients are snarkVM's MONTGOMERY_A = 2 (a + d) / (a - d)
; and MONTGOMERY_B = 4 / (a - d).
;
; montgomery_add (three constraints) is sound and complete for the image of
; P1 + P2 when x(P1), x(P2), x(P1 + P2) are nonzero and y(P1) /= y(P2); its
; output is the image of the Edwards sum.  Outside these conditions the
; chord formula is undefined (u1 = u2) or the image does not exist (x = 0);
; hbhp-window.lisp shows that the hasher never reaches those cases.
;
; The conversion back (two div_unchecked constraints, ex * v = u and
; ey * (u + 1) = u - 1) recovers the Edwards point exactly when x /= 0.

(in-package "ALEOVM")

(include-book "crv-curve")
(include-book "hbhp-cert-check")
(include-book "hbhp-field")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel" :dir :system))
(local (in-theory (disable pfield::equal-of-add-and-add-cancel-1-gen)))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled hbhp-base-prime-facts
  (and (posp (base-prime))
       (integerp (base-prime))
       (< 1 (base-prime))
       (< 2 (base-prime))
       (primep (base-prime)))
  :use primep-of-base-prime
  :in-theory '((:e base-prime) (:e posp) (:e integerp) (:e <)))

(defruled hbhp-q-facts
  (and (posp (ecurve::edwards-bls12-q))
       (integerp (ecurve::edwards-bls12-q))
       (< 1 (ecurve::edwards-bls12-q))
       (primep (ecurve::edwards-bls12-q)))
  :use (hbhp-base-prime-facts curve-base-prime-is-edwards-bls12-q)
  :in-theory nil)

(defmacro hbhp-x (pt) `(ecurve::point-finite->x ,pt))
(defmacro hbhp-y (pt) `(ecurve::point-finite->y ,pt))

(defruled hbhp-point-facts
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime)))
           (and (pfield::fep (hbhp-x pt) p)
                (pfield::fep (hbhp-y pt) p)
                (equal (ecurve::point-finite (hbhp-x pt) (hbhp-y pt)) pt)
                (hbhpf-curve (ecurve::edwards-bls12-a) (ecurve::edwards-bls12-d)
                             (hbhp-x pt) (hbhp-y pt) p)))
  :use (crv-fep-of-edwards-bls12-coords
        (:instance ecurve::point-finite-when-edwards-bls12-pointp (ecurve::x pt)))
  :enable (ecurve::edwards-bls12-pointp
           ecurve::point-on-twisted-edwards-p
           ecurve::edwards-bls12-curve
           curve-base-prime-is-edwards-bls12-q
           ecurve::point-fix
           ecurve::pointp-when-edwards-bls12-pointp)
  :disable (ecurve::point-finite-when-edwards-bls12-pointp))

(defruled hbhp-y-not-pm1
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime))
                (not (equal (hbhp-x pt) 0)))
           (and (not (equal (hbhp-y pt) 1))
                (not (equal (hbhp-y pt) (pfield::neg 1 p)))
                (not (equal (pfield::sub 1 (hbhp-y pt) p) 0))
                (not (equal (pfield::add 1 (hbhp-y pt) p) 0))))
  :use (hbhp-point-facts
        (:instance hbhp-x-zero-when-y-one
                   (a (ecurve::edwards-bls12-a)) (d (ecurve::edwards-bls12-d))
                   (x (hbhp-x pt)))
        (:instance hbhp-x-zero-when-y-minus-one
                   (a (ecurve::edwards-bls12-a)) (d (ecurve::edwards-bls12-d))
                   (x (hbhp-x pt))))
  :enable (pfield::equal-of-0-and-sub pfield::equal-of-0-and-add
           primep-of-base-prime)
  :disable (pfield::equal-of-neg-solve))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hbhp-mont-a ()
  :short "@('MONTGOMERY_A') of Edwards-BLS12 (curves/src/edwards_bls12/parameters.rs)."
  3990301581132929505568273333084066329187552697088022219156688740916631500114)

(define hbhp-mont-b ()
  :short "@('MONTGOMERY_B') of Edwards-BLS12."
  4454160168295440918680551605697480202188346638066041608778544715000777738925)

(defruled hbhp-mont-coeffs
  (implies (equal p (base-prime))
           (b* ((a (ecurve::edwards-bls12-a))
                (d (ecurve::edwards-bls12-d)))
             (and (pfield::fep (hbhp-mont-a) p)
                  (pfield::fep (hbhp-mont-b) p)
                  (equal (pfield::mul (pfield::sub a d p) (hbhp-mont-a) p)
                         (pfield::add (pfield::add a d p) (pfield::add a d p) p))
                  (equal (pfield::mul (pfield::sub a d p) (hbhp-mont-b) p)
                         (pfield::add (pfield::add 1 1 p) (pfield::add 1 1 p) p))
                  (not (equal (pfield::sub a d p) 0)))))
  :in-theory '((:e base-prime) (:e ecurve::edwards-bls12-a)
               (:e ecurve::edwards-bls12-d) (:e hbhp-mont-a) (:e hbhp-mont-b)
               (:e pfield::fep) (:e pfield::mul) (:e pfield::sub) (:e pfield::add)
               (:e equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hbhp-mu (pt)
  :verify-guards nil
  :short "Montgomery abscissa @($(1 + y) / (1 - y)$)."
  (b* ((p (base-prime))
       (y (hbhp-y pt)))
    (pfield::div (pfield::add 1 y p) (pfield::sub 1 y p) p)))

(define hbhp-mv (pt)
  :verify-guards nil
  :short "Montgomery ordinate @($u / x$)."
  (pfield::div (hbhp-mu pt) (hbhp-x pt) (base-prime)))

(defruledl hbhp-u-facts
  (implies (and (primep p) (< 2 p)
                (pfield::fep y p) (pfield::fep u p)
                (not (equal (pfield::add 1 y p) 0))
                (equal (pfield::mul (pfield::sub 1 y p) u p) (pfield::add 1 y p)))
           (and (not (equal u 0))
                (not (equal (pfield::add u 1 p) 0))))
  :use (:instance hbhp-u-minus-one)
  :prep-lemmas
  ((defruled hbhp-u-minus-one
     (implies (and (primep p) (< 2 p) (pfield::fep y p))
              (not (equal (pfield::mul (pfield::sub 1 y p) (pfield::neg 1 p) p)
                          (pfield::add 1 y p))))
     :use ((:instance hbhp-two-ne-0)
           (:instance pfield::equal-of-add-and-add-cancel-1-gen
                      (pfield::x y) (pfield::y -1) (pfield::z 1) (pfield::p p))
           (:instance hbhp-mod-minus-1))
     :disable (pfield::equal-of-add-and-add-cancel-1-gen)
     :prep-lemmas
     ((defruled hbhp-two-ne-0
        (implies (and (primep p) (< 2 p))
                 (not (equal (pfield::add 1 1 p) 0)))
        :enable pfield::add)
      (defruled hbhp-mod-minus-1
        (implies (and (integerp p) (< 2 p))
                 (not (equal (mod -1 p) (mod 1 p))))
        :enable (mod)
        :prep-books ((include-book "arithmetic-5/top" :dir :system))))))
  :prep-books ((include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free"
                             :dir :system)
))

(defruled hbhp-mont-image
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime))
                (not (equal (hbhp-x pt) 0)))
           (and (pfield::fep (hbhp-mu pt) p)
                (pfield::fep (hbhp-mv pt) p)
                (equal (pfield::mul (pfield::sub 1 (hbhp-y pt) p) (hbhp-mu pt) p)
                       (pfield::add 1 (hbhp-y pt) p))
                (equal (pfield::mul (hbhp-x pt) (hbhp-mv pt) p) (hbhp-mu pt))
                (not (equal (hbhp-mu pt) 0))
                (not (equal (hbhp-mv pt) 0))
                (not (equal (pfield::add (hbhp-mu pt) 1 p) 0))))
  :use (hbhp-point-facts hbhp-y-not-pm1 hbhp-mont-eqns
        (:instance hbhp-u-facts (y (hbhp-y pt)) (u (hbhp-mu pt))))
  :in-theory '(primep-of-base-prime curve-base-prime-lower-bound
               pfield::mul-of-0-arg2)
  :prep-lemmas
  ((defruled hbhp-mont-eqns
     (implies (and (ecurve::edwards-bls12-pointp pt)
                   (equal p (base-prime))
                   (not (equal (hbhp-x pt) 0)))
              (and (pfield::fep (hbhp-mu pt) p)
                   (pfield::fep (hbhp-mv pt) p)
                   (equal (pfield::mul (pfield::sub 1 (hbhp-y pt) p) (hbhp-mu pt) p)
                          (pfield::add 1 (hbhp-y pt) p))
                   (equal (pfield::mul (hbhp-x pt) (hbhp-mv pt) p) (hbhp-mu pt))))
     :use (hbhp-point-facts hbhp-y-not-pm1
           (:instance hbhp-mul-div (x (pfield::sub 1 (hbhp-y pt) p))
                      (y (pfield::add 1 (hbhp-y pt) p)))
           (:instance hbhp-mul-div (x (hbhp-x pt)) (y (hbhp-mu pt))))
     :in-theory '(hbhp-mu hbhp-mv hbhp-base-prime-facts pfield::fep-of-div
                  pfield::fep-of-add pfield::fep-of-sub)
     :prep-lemmas
     ((defruled hbhp-mul-div
        (implies (and (primep p) (pfield::fep x p) (pfield::fep y p)
                      (not (equal x 0)))
                 (equal (pfield::mul x (pfield::div y x p) p) y)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel hbhp-mul-cancel
  (implies (and (primep p)
                (pfield::fep a p) (pfield::fep b p) (pfield::fep c p)
                (not (equal c 0))
                (equal (pfield::mul c a p) (pfield::mul c b p)))
           (equal a b))
  :rule-classes nil
  :use (:instance pfield::equal-of-0-and-mul
                  (pfield::x c) (pfield::y (pfield::sub a b p)) (pfield::p p))
  :disable (pfield::equal-of-0-and-mul))

(defruledl hbhp-coords-of-point-finite
  (implies (and (pfield::fep x p) (pfield::fep y p))
           (and (equal (ecurve::point-finite->x (ecurve::point-finite x y)) x)
                (equal (ecurve::point-finite->y (ecurve::point-finite x y)) y)))
  :enable pfield::fep)

(defmacro hbhp-gden (p1 p2 p)
  `(pfield::mul (ecurve::edwards-bls12-d)
                (pfield::mul (hbhp-x ,p1)
                             (pfield::mul (hbhp-x ,p2)
                                          (pfield::mul (hbhp-y ,p1) (hbhp-y ,p2) ,p)
                                          ,p)
                             ,p)
                ,p))

(defruled hbhp-add-coords
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal p (base-prime)))
           (b* ((p3 (ecurve::edwards-bls12-add p1 p2))
                (g (hbhp-gden p1 p2 p)))
             (and (equal (pfield::mul (pfield::add 1 g p) (hbhp-x p3) p)
                         (pfield::add (pfield::mul (hbhp-x p1) (hbhp-y p2) p)
                                      (pfield::mul (hbhp-y p1) (hbhp-x p2) p)
                                      p))
                  (equal (pfield::mul (pfield::sub 1 g p) (hbhp-y p3) p)
                         (pfield::sub (pfield::mul (hbhp-y p1) (hbhp-y p2) p)
                                      (pfield::mul (ecurve::edwards-bls12-a)
                                                   (pfield::mul (hbhp-x p1) (hbhp-x p2) p)
                                                   p)
                                      p))
                  (not (equal (pfield::add 1 g p) 0))
                  (not (equal (pfield::sub 1 g p) 0)))))
  :use (crv-edwards-bls12-add-to-divs
        crv-add-dens-nonzero
        (:instance hbhp-coords-of-point-finite
                   (x (pfield::div (pfield::add (pfield::mul (hbhp-x p1) (hbhp-y p2) p)
                                                (pfield::mul (hbhp-y p1) (hbhp-x p2) p)
                                                p)
                                   (pfield::add 1 (hbhp-gden p1 p2 p) p)
                                   p))
                   (y (pfield::div (pfield::sub (pfield::mul (hbhp-y p1) (hbhp-y p2) p)
                                                (pfield::mul (ecurve::edwards-bls12-a)
                                                             (pfield::mul (hbhp-x p1) (hbhp-x p2) p)
                                                             p)
                                                p)
                                   (pfield::sub 1 (hbhp-gden p1 p2 p) p)
                                   p))))
  :in-theory '(curve-base-prime-is-edwards-bls12-q
               hbhp-q-facts
               pfield::fep-of-div pfield::fep-of-add pfield::fep-of-sub
               pfield::fep-of-mul pfield::mul-of-div-same-arg2))

(defmacro hbhp-mont-add-eqns (u1 v1 u2 v2 lam u3 v3 p)
  `(and (equal (pfield::mul (pfield::sub ,u2 ,u1 ,p) ,lam ,p)
               (pfield::sub ,v2 ,v1 ,p))
        (equal (pfield::mul (pfield::mul (hbhp-mont-b) ,lam ,p) ,lam ,p)
               (pfield::add (pfield::add (pfield::add (hbhp-mont-a) ,u1 ,p) ,u2 ,p) ,u3 ,p))
        (equal (pfield::mul (pfield::sub ,u1 ,u3 ,p) ,lam ,p)
               (pfield::add ,v1 ,v3 ,p))))

(defmacro hbhp-mont-add-ok (p1 p2)
  `(and (not (equal (hbhp-x ,p1) 0))
        (not (equal (hbhp-x ,p2) 0))
        (not (equal (hbhp-x (ecurve::edwards-bls12-add ,p1 ,p2)) 0))
        (not (equal (hbhp-y ,p1) (hbhp-y ,p2)))))

(defruled hbhp-mont-u-differ
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal p (base-prime))
                (not (equal (hbhp-x p1) 0))
                (not (equal (hbhp-x p2) 0))
                (not (equal (hbhp-y p1) (hbhp-y p2))))
           (not (equal (pfield::sub (hbhp-mu p2) (hbhp-mu p1) p) 0)))
  :use ((:instance hbhp-mont-image (pt p1))
        (:instance hbhp-mont-image (pt p2))
        (:instance hbhp-point-facts (pt p1))
        (:instance hbhp-point-facts (pt p2))
        (:instance hbhp-same-u-abstract
                   (y1 (hbhp-y p1)) (y2 (hbhp-y p2))
                   (u1 (hbhp-mu p1)) (u2 (hbhp-mu p2)))
        (:instance pfield::equal-of-0-and-sub
                   (pfield::x (hbhp-mu p2)) (pfield::y (hbhp-mu p1))
                   (pfield::p p)))
  :in-theory '(hbhp-base-prime-facts))

(defruled hbhp-mont-add-sound-eqns
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal p (base-prime))
                (hbhp-mont-add-ok p1 p2)
                (pfield::fep lam p) (pfield::fep u3 p) (pfield::fep v3 p)
                (hbhp-mont-add-eqns (hbhp-mu p1) (hbhp-mv p1)
                                    (hbhp-mu p2) (hbhp-mv p2) lam u3 v3 p))
           (b* ((p3 (ecurve::edwards-bls12-add p1 p2)))
             (and (equal (pfield::mul (pfield::sub 1 (hbhp-y p3) p) u3 p)
                         (pfield::add 1 (hbhp-y p3) p))
                  (equal (pfield::mul (hbhp-x p3) v3 p) u3))))
  :use ((:instance hbhp-mont-add-abstract
                   (a (ecurve::edwards-bls12-a)) (d (ecurve::edwards-bls12-d))
                   (ma (hbhp-mont-a)) (mb (hbhp-mont-b))
                   (x1 (hbhp-x p1)) (y1 (hbhp-y p1))
                   (x2 (hbhp-x p2)) (y2 (hbhp-y p2))
                   (u1 (hbhp-mu p1)) (v1 (hbhp-mv p1))
                   (u2 (hbhp-mu p2)) (v2 (hbhp-mv p2))
                   (x3 (hbhp-x (ecurve::edwards-bls12-add p1 p2)))
                   (y3 (hbhp-y (ecurve::edwards-bls12-add p1 p2))))
        hbhp-mont-coeffs
        hbhp-add-coords
        hbhp-mont-u-differ
        (:instance hbhp-point-facts (pt p1))
        (:instance hbhp-point-facts (pt p2))
        (:instance hbhp-point-facts (pt (ecurve::edwards-bls12-add p1 p2)))
        (:instance hbhp-mont-image (pt p1))
        (:instance hbhp-mont-image (pt p2))
        (:instance hbhp-y-not-pm1 (pt p1))
        (:instance hbhp-y-not-pm1 (pt p2))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 p1) (ecurve::point2 p2)))
  :in-theory '(hbhp-base-prime-facts curve-fep-of-edwards-bls12-a
               curve-fep-of-edwards-bls12-d ecurve::edwards-bls12-d-not-zero))

(defruled hbhp-mont-add-sound
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal p (base-prime))
                (hbhp-mont-add-ok p1 p2)
                (pfield::fep lam p) (pfield::fep u3 p) (pfield::fep v3 p)
                (hbhp-mont-add-eqns (hbhp-mu p1) (hbhp-mv p1)
                                    (hbhp-mu p2) (hbhp-mv p2) lam u3 v3 p))
           (b* ((p3 (ecurve::edwards-bls12-add p1 p2)))
             (and (equal (hbhp-mu p3) u3)
                  (equal (hbhp-mv p3) v3))))
  :use (hbhp-mont-add-sound-eqns
        (:instance hbhp-point-facts (pt (ecurve::edwards-bls12-add p1 p2)))
        (:instance hbhp-mont-image (pt (ecurve::edwards-bls12-add p1 p2)))
        (:instance hbhp-y-not-pm1 (pt (ecurve::edwards-bls12-add p1 p2)))
        (:instance hbhp-mul-cancel
                   (c (pfield::sub 1 (hbhp-y (ecurve::edwards-bls12-add p1 p2)) p))
                   (a u3) (b (hbhp-mu (ecurve::edwards-bls12-add p1 p2))))
        (:instance hbhp-mul-cancel
                   (c (hbhp-x (ecurve::edwards-bls12-add p1 p2)))
                   (a v3) (b (hbhp-mv (ecurve::edwards-bls12-add p1 p2))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 p1) (ecurve::point2 p2)))
  :in-theory '(hbhp-base-prime-facts pfield::fep-of-sub))

(defun hbhp-mont-lam (u1 v1 u2 v2)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime)))
    (pfield::div (pfield::sub v2 v1 p) (pfield::sub u2 u1 p) p)))

(defun hbhp-mont-sum-u (u1 u2 lam)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime)))
    (pfield::sub (pfield::sub (pfield::sub (pfield::mul (pfield::mul (hbhp-mont-b) lam p) lam p)
                                           (hbhp-mont-a) p)
                              u1 p)
                 u2 p)))

(defun hbhp-mont-sum-v (u1 v1 lam u3)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime)))
    (pfield::neg (pfield::add v1 (pfield::mul lam (pfield::sub u3 u1 p) p) p) p)))

(defruled hbhp-mont-add-witness-eqns
  :short "snarkVM's witnesses satisfy the three constraints when @($u_1 \\neq u_2$)."
  (implies (and (equal p (base-prime))
                (pfield::fep u1 p) (pfield::fep v1 p)
                (pfield::fep u2 p) (pfield::fep v2 p)
                (not (equal (pfield::sub u2 u1 p) 0)))
           (b* ((lam (hbhp-mont-lam u1 v1 u2 v2))
                (u3 (hbhp-mont-sum-u u1 u2 lam))
                (v3 (hbhp-mont-sum-v u1 v1 lam u3)))
             (and (pfield::fep lam p) (pfield::fep u3 p) (pfield::fep v3 p)
                  (hbhp-mont-add-eqns u1 v1 u2 v2 lam u3 v3 p))))
  :use hbhp-mont-coeffs
  :enable (hbhp-base-prime-facts)
  :disable ((:e hbhp-mont-a) (:e hbhp-mont-b)))

(defruled hbhp-mont-add-complete
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal p (base-prime))
                (hbhp-mont-add-ok p1 p2))
           (b* ((u1 (hbhp-mu p1)) (v1 (hbhp-mv p1))
                (u2 (hbhp-mu p2)) (v2 (hbhp-mv p2))
                (lam (hbhp-mont-lam u1 v1 u2 v2))
                (u3 (hbhp-mont-sum-u u1 u2 lam))
                (v3 (hbhp-mont-sum-v u1 v1 lam u3))
                (p3 (ecurve::edwards-bls12-add p1 p2)))
             (and (pfield::fep lam p)
                  (hbhp-mont-add-eqns u1 v1 u2 v2 lam u3 v3 p)
                  (equal (hbhp-mu p3) u3)
                  (equal (hbhp-mv p3) v3))))
  :use ((:instance hbhp-mont-add-witness-eqns
                   (u1 (hbhp-mu p1)) (v1 (hbhp-mv p1))
                   (u2 (hbhp-mu p2)) (v2 (hbhp-mv p2)))
        (:instance hbhp-mont-add-sound
                   (lam (hbhp-mont-lam (hbhp-mu p1) (hbhp-mv p1) (hbhp-mu p2) (hbhp-mv p2)))
                   (u3 (hbhp-mont-sum-u (hbhp-mu p1) (hbhp-mu p2)
                                        (hbhp-mont-lam (hbhp-mu p1) (hbhp-mv p1)
                                                       (hbhp-mu p2) (hbhp-mv p2))))
                   (v3 (hbhp-mont-sum-v (hbhp-mu p1) (hbhp-mv p1)
                                        (hbhp-mont-lam (hbhp-mu p1) (hbhp-mv p1)
                                                       (hbhp-mu p2) (hbhp-mv p2))
                                        (hbhp-mont-sum-u (hbhp-mu p1) (hbhp-mu p2)
                                                         (hbhp-mont-lam (hbhp-mu p1) (hbhp-mv p1)
                                                                        (hbhp-mu p2) (hbhp-mv p2))))))
        hbhp-mont-u-differ
        (:instance hbhp-mont-image (pt p1))
        (:instance hbhp-mont-image (pt p2)))
  :in-theory nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro hbhp-to-edwards-eqns (u v ex ey p)
  `(and (equal (pfield::mul ,ex ,v ,p) ,u)
        (equal (pfield::mul ,ey (pfield::add ,u 1 ,p) ,p)
               (pfield::sub ,u 1 ,p))))

(defruledl hbhp-y-from-u
  (implies (and (primep p) (pfield::fep y p) (pfield::fep u p)
                (equal (pfield::mul (pfield::sub 1 y p) u p) (pfield::add 1 y p)))
           (equal (pfield::mul y (pfield::add u 1 p) p)
                  (pfield::sub u 1 p)))
  :use (:instance hbhp-add-1-solve (s (pfield::add y (pfield::mul u y p) p)))
  :prep-lemmas
  ((defruled hbhp-add-1-solve
     (implies (and (primep p) (pfield::fep s p)
                   (equal (pfield::add 1 s p) u))
              (equal (pfield::add -1 u p) s)))))

(defruled hbhp-to-edwards-sound
  :short "The two div_unchecked constraints recover the Edwards point."
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime))
                (not (equal (hbhp-x pt) 0))
                (pfield::fep ex p) (pfield::fep ey p)
                (hbhp-to-edwards-eqns (hbhp-mu pt) (hbhp-mv pt) ex ey p))
           (equal (ecurve::point-finite ex ey) pt))
  :use (hbhp-point-facts
        hbhp-mont-image
        (:instance hbhp-y-from-u (y (hbhp-y pt)) (u (hbhp-mu pt)))
        (:instance hbhp-mul-cancel (c (hbhp-mv pt)) (a ex) (b (hbhp-x pt)))
        (:instance hbhp-mul-cancel (c (pfield::add (hbhp-mu pt) 1 p))
                   (a ey) (b (hbhp-y pt))))
  :in-theory '(hbhp-base-prime-facts pfield::fep-of-add pfield::mul-commutative))

(defruled hbhp-to-edwards-complete
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime))
                (not (equal (hbhp-x pt) 0)))
           (hbhp-to-edwards-eqns (hbhp-mu pt) (hbhp-mv pt) (hbhp-x pt) (hbhp-y pt) p))
  :use (hbhp-point-facts
        hbhp-mont-image
        (:instance hbhp-y-from-u (y (hbhp-y pt)) (u (hbhp-mu pt))))
  :in-theory '(hbhp-base-prime-facts pfield::mul-commutative))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled hbhp-neg-coords
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime)))
           (equal (ecurve::edwards-bls12-neg pt)
                  (ecurve::point-finite (pfield::neg (hbhp-x pt) p) (hbhp-y pt))))
  :enable (ecurve::edwards-bls12-neg ecurve::twisted-edwards-neg
           ecurve::edwards-bls12-curve curve-base-prime-is-edwards-bls12-q))

(defruledl hbhp-neg-zero
  (implies (and (pfield::fep x p) (primep p))
           (equal (equal (pfield::neg x p) 0) (equal x 0)))
  :enable (pfield::neg pfield::fep))

(defruled hbhp-mont-of-neg
  (implies (and (ecurve::edwards-bls12-pointp pt)
                (equal p (base-prime))
                (not (equal (hbhp-x pt) 0)))
           (b* ((np (ecurve::edwards-bls12-neg pt)))
             (and (ecurve::edwards-bls12-pointp np)
                  (equal (hbhp-x np) (pfield::neg (hbhp-x pt) p))
                  (equal (hbhp-y np) (hbhp-y pt))
                  (not (equal (hbhp-x np) 0))
                  (equal (hbhp-mu np) (hbhp-mu pt))
                  (equal (hbhp-mv np) (pfield::neg (hbhp-mv pt) p)))))
  :use (hbhp-point-facts hbhp-mont-image
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-neg
                   (ecurve::point1 pt)))
  :enable (hbhp-mu hbhp-mv hbhp-base-prime-facts pfield::equal-of-div
           hbhp-neg-coords hbhp-coords-of-point-finite hbhp-neg-zero)
  :disable (pfield::equal-of-neg-solve ecurve::edwards-bls12-pointp-of-edwards-bls12-neg))
