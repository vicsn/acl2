; Associativity of twisted Edwards addition
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; Associativity of twisted-edwards-add on complete curves, which discharges
;; the nullary hypothesis twisted-edwards-add-associativity.
;;
;; The algebra is the pair of certificates in certificates.lisp.  Here we
;; evaluate them at the coordinates of the points and of the intermediate
;; sums.  The division equations hold because each denominator is nonzero
;; (Kestrel's 1+d.x1.x2.y1.y2-not-0 and 1-d.x1.x2.y1.y2-not-0, applied also to
;; P1+P2 and P2+P3, which are on the curve by closure).  Since the product of
;; the six denominators is nonzero, the two x coordinates are equal, and
;; likewise the two y coordinates.

(include-book "certificates")
(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl mod-of-1
  (implies (and (integerp p)
                (< 1 p))
           (equal (mod 1 p) 1))
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruledl equal-of-sub-and-0
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal (sub x y p) 0)
                  (equal x y)))
  :use (:instance pfield::equal-of-0-and-sub
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable (pfield::equal-of-0-and-sub sub))

(defruledl equal-of-mul-and-0
  (implies (and (fep x p)
                (fep y p)
                (dm::primep p))
           (equal (equal (mul x y p) 0)
                  (or (equal x 0)
                      (equal y 0))))
  :use (:instance pfield::equal-of-0-and-mul
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable pfield::equal-of-0-and-mul)

(defruledl mul-of-div-same
  (implies (and (fep x p)
                (fep y p)
                (dm::primep p))
           (equal (mul x (div y x p) p)
                  (if (equal x 0)
                      0
                    y)))
  :prep-books
  ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruledl integerp-when-fep
  (implies (fep x p)
           (integerp x))
  :enable fep)

(defruledl mod-when-fep
  (implies (fep x p)
           (equal (mod x p) x))
  :enable fep
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruledl posp-when-primep
  (implies (dm::primep p)
           (posp p))
  :rule-classes :forward-chaining
  :enable dm::primep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-assoc-oncurvep (x y a d p)
  :verify-guards nil
  (equal (add (mul a (mul x x p) p) (mul y y p) p)
         (add 1 (mul d (mul (mul x x p) (mul y y p) p) p) p)))

(defmacro edwards-assoc-den+ (x1 y1 x2 y2)
  `(add 1 (mul d (mul ,x1 (mul ,x2 (mul ,y1 ,y2 p) p) p) p) p))

(defmacro edwards-assoc-den- (x1 y1 x2 y2)
  `(sub 1 (mul d (mul ,x1 (mul ,x2 (mul ,y1 ,y2 p) p) p) p) p))

(defmacro edwards-assoc-num-x (x1 y1 x2 y2)
  `(add (mul ,x1 ,y2 p) (mul ,y1 ,x2 p) p))

(defmacro edwards-assoc-num-y (x1 y1 x2 y2)
  `(sub (mul ,y1 ,y2 p) (mul a (mul ,x1 ,x2 p) p) p))

;; The intermediate sums, as computed by twisted-edwards-add.

(defmacro edwards-assoc-sums-b* (body)
  `(b* ((x4 (div (edwards-assoc-num-x x1 y1 x2 y2)
                 (edwards-assoc-den+ x1 y1 x2 y2) p))
        (y4 (div (edwards-assoc-num-y x1 y1 x2 y2)
                 (edwards-assoc-den- x1 y1 x2 y2) p))
        (x6 (div (edwards-assoc-num-x x2 y2 x3 y3)
                 (edwards-assoc-den+ x2 y2 x3 y3) p))
        (y6 (div (edwards-assoc-num-y x2 y2 x3 y3)
                 (edwards-assoc-den- x2 y2 x3 y3) p))
        (xl (div (edwards-assoc-num-x x4 y4 x3 y3)
                 (edwards-assoc-den+ x4 y4 x3 y3) p))
        (yl (div (edwards-assoc-num-y x4 y4 x3 y3)
                 (edwards-assoc-den- x4 y4 x3 y3) p))
        (xr (div (edwards-assoc-num-x x1 y1 x6 y6)
                 (edwards-assoc-den+ x1 y1 x6 y6) p))
        (yr (div (edwards-assoc-num-y x1 y1 x6 y6)
                 (edwards-assoc-den- x1 y1 x6 y6) p)))
     ,body))

;; Associativity on the coordinates, with the intermediate sums as variables
;; constrained by the division equations.

(defrule edwards-assoc-abstract
  (implies (and (dm::primep p)
                (< 2 p)
                (fep a p) (fep d p)
                (fep x1 p) (fep y1 p)
                (fep x2 p) (fep y2 p)
                (fep x3 p) (fep y3 p)
                (fep x4 p) (fep y4 p)
                (fep x6 p) (fep y6 p)
                (fep xl p) (fep xr p)
                (fep yl p) (fep yr p)
                (edwards-assoc-oncurvep x1 y1 a d p)
                (edwards-assoc-oncurvep x2 y2 a d p)
                (edwards-assoc-oncurvep x3 y3 a d p)
                (equal (mul (edwards-assoc-den+ x1 y1 x2 y2) x4 p)
                       (edwards-assoc-num-x x1 y1 x2 y2))
                (equal (mul (edwards-assoc-den- x1 y1 x2 y2) y4 p)
                       (edwards-assoc-num-y x1 y1 x2 y2))
                (equal (mul (edwards-assoc-den+ x2 y2 x3 y3) x6 p)
                       (edwards-assoc-num-x x2 y2 x3 y3))
                (equal (mul (edwards-assoc-den- x2 y2 x3 y3) y6 p)
                       (edwards-assoc-num-y x2 y2 x3 y3))
                (equal (mul (edwards-assoc-den+ x4 y4 x3 y3) xl p)
                       (edwards-assoc-num-x x4 y4 x3 y3))
                (equal (mul (edwards-assoc-den- x4 y4 x3 y3) yl p)
                       (edwards-assoc-num-y x4 y4 x3 y3))
                (equal (mul (edwards-assoc-den+ x1 y1 x6 y6) xr p)
                       (edwards-assoc-num-x x1 y1 x6 y6))
                (equal (mul (edwards-assoc-den- x1 y1 x6 y6) yr p)
                       (edwards-assoc-num-y x1 y1 x6 y6))
                (not (equal (edwards-assoc-den+ x1 y1 x2 y2) 0))
                (not (equal (edwards-assoc-den- x1 y1 x2 y2) 0))
                (not (equal (edwards-assoc-den+ x2 y2 x3 y3) 0))
                (not (equal (edwards-assoc-den- x2 y2 x3 y3) 0))
                (not (equal (edwards-assoc-den+ x4 y4 x3 y3) 0))
                (not (equal (edwards-assoc-den- x4 y4 x3 y3) 0))
                (not (equal (edwards-assoc-den+ x1 y1 x6 y6) 0))
                (not (equal (edwards-assoc-den- x1 y1 x6 y6) 0)))
           (and (equal xl xr)
                (equal yl yr)))
  :rule-classes nil
  :use ((:instance certificate-okp-sound
                   (goal *edwards-assoc-goal-x*)
                   (cofs *edwards-assoc-cofactors-x*)
                   (gens *edwards-assoc-gens-x*)
                   (vars *edwards-assoc-vars*)
                   (vals (list a d x1 y1 x2 y2 x3 y3
                               x4 y4 x6 y6 xl xr yl yr)))
        (:instance certificate-okp-sound
                   (goal *edwards-assoc-goal-y*)
                   (cofs *edwards-assoc-cofactors-y*)
                   (gens *edwards-assoc-gens-y*)
                   (vars *edwards-assoc-vars*)
                   (vals (list a d x1 y1 x2 y2 x3 y3
                               x4 y4 x6 y6 xl xr yl yr))))
  :in-theory (union-theories
              (theory 'acl2::ground-zero)
              '(evalf
                gens-zerop
                dm::all-integers
                edwards-assoc-oncurvep
                (:e certificate-okp)
                mod-of-1
                mod-when-fep
                equal-of-sub-and-0
                equal-of-mul-and-0
                integerp-when-fep
                posp-when-primep
                pfield::fep-of-add
                pfield::fep-of-mul
                pfield::fep-of-sub
                pfield::fep-of-neg
                pfield::natp-of-add
                pfield::natp-of-mul
                pfield::natp-of-sub
                pfield::natp-of-neg)))

;; The same, with the intermediate sums computed as in twisted-edwards-add.

(set-ignore-ok t)

(defruled edwards-assoc-components
  (edwards-assoc-sums-b*
    (implies (and (dm::primep p)
                  (< 2 p)
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (fep x3 p)
                  (fep y3 p)
                  (edwards-assoc-oncurvep x1 y1 a d p)
                  (edwards-assoc-oncurvep x2 y2 a d p)
                  (edwards-assoc-oncurvep x3 y3 a d p)
                  (not (equal (edwards-assoc-den+ x1 y1 x2 y2) 0))
                  (not (equal (edwards-assoc-den- x1 y1 x2 y2) 0))
                  (not (equal (edwards-assoc-den+ x2 y2 x3 y3) 0))
                  (not (equal (edwards-assoc-den- x2 y2 x3 y3) 0))
                  (not (equal (edwards-assoc-den+ x4 y4 x3 y3) 0))
                  (not (equal (edwards-assoc-den- x4 y4 x3 y3) 0))
                  (not (equal (edwards-assoc-den+ x1 y1 x6 y6) 0))
                  (not (equal (edwards-assoc-den- x1 y1 x6 y6) 0)))
             (and (equal xl xr)
                  (equal yl yr))))
  :use ((:instance edwards-assoc-abstract
                   (x4 (edwards-assoc-sums-b* x4))
                   (y4 (edwards-assoc-sums-b* y4))
                   (x6 (edwards-assoc-sums-b* x6))
                   (y6 (edwards-assoc-sums-b* y6))
                   (xl (edwards-assoc-sums-b* xl))
                   (yl (edwards-assoc-sums-b* yl))
                   (xr (edwards-assoc-sums-b* xr))
                   (yr (edwards-assoc-sums-b* yr))))
  :in-theory (union-theories
              (theory 'acl2::ground-zero)
              '(mul-of-div-same
                posp-when-primep
                pfield::fep-of-add
                pfield::fep-of-mul
                pfield::fep-of-sub
                pfield::fep-of-div)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl point-on-twisted-edwards-p-components
  (implies (point-on-twisted-edwards-p point curve)
           (b* ((p (twisted-edwards-curve->p curve))
                (a (twisted-edwards-curve->a curve))
                (d (twisted-edwards-curve->d curve))
                (x (point-finite->x point))
                (y (point-finite->y point)))
             (and (fep x p)
                  (fep y p)
                  (edwards-assoc-oncurvep x y a d p))))
  :enable (point-on-twisted-edwards-p edwards-assoc-oncurvep fep))

(defruledl twisted-edwards-curve-components
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve)))
    (and (dm::primep p)
         (< 2 p)
         (fep a p)
         (fep d p)))
  :use (:instance twisted-edwards-curve-requirements (x curve))
  :disable twisted-edwards-curve-requirements)

(defruledl point-on-twisted-edwards-p-of-twisted-edwards-add-unfixed
  (implies (and (twisted-edwards-curve-completep curve)
                (point-on-twisted-edwards-p point1 curve)
                (point-on-twisted-edwards-p point2 curve))
           (point-on-twisted-edwards-p (twisted-edwards-add point1 point2 curve)
                                       curve))
  :use (:instance point-on-twisted-edwards-p-of-twisted-edward-add
                  (point1 (point-fix point1))
                  (point2 (point-fix point2))))

(defrule twisted-edwards-add-associative
  (implies (and (twisted-edwards-curve-completep curve)
                (point-on-twisted-edwards-p point1 curve)
                (point-on-twisted-edwards-p point2 curve)
                (point-on-twisted-edwards-p point3 curve))
           (equal (twisted-edwards-add (twisted-edwards-add point1 point2 curve)
                                       point3
                                       curve)
                  (twisted-edwards-add point1
                                       (twisted-edwards-add point2 point3 curve)
                                       curve)))
  :use ((:instance edwards-assoc-components
                   (p (twisted-edwards-curve->p curve))
                   (a (twisted-edwards-curve->a curve))
                   (d (twisted-edwards-curve->d curve))
                   (x1 (point-finite->x point1))
                   (y1 (point-finite->y point1))
                   (x2 (point-finite->x point2))
                   (y2 (point-finite->y point2))
                   (x3 (point-finite->x point3))
                   (y3 (point-finite->y point3)))
        (:instance twisted-edwards-curve-components)
        (:instance point-on-twisted-edwards-p-components (point point1))
        (:instance point-on-twisted-edwards-p-components (point point2))
        (:instance point-on-twisted-edwards-p-components (point point3))
        (:instance point-on-twisted-edwards-p-of-twisted-edwards-add-unfixed
                   (point1 point1) (point2 point2))
        (:instance point-on-twisted-edwards-p-of-twisted-edwards-add-unfixed
                   (point1 point2) (point2 point3))
        (:instance 1+d.x1.x2.y1.y2-not-0 (point1 point1) (point2 point2))
        (:instance 1-d.x1.x2.y1.y2-not-0 (point1 point1) (point2 point2))
        (:instance 1+d.x1.x2.y1.y2-not-0 (point1 point2) (point2 point3))
        (:instance 1-d.x1.x2.y1.y2-not-0 (point1 point2) (point2 point3))
        (:instance 1+d.x1.x2.y1.y2-not-0
                   (point1 (twisted-edwards-add point1 point2 curve))
                   (point2 point3))
        (:instance 1-d.x1.x2.y1.y2-not-0
                   (point1 (twisted-edwards-add point1 point2 curve))
                   (point2 point3))
        (:instance 1+d.x1.x2.y1.y2-not-0
                   (point1 point1)
                   (point2 (twisted-edwards-add point2 point3 curve)))
        (:instance 1-d.x1.x2.y1.y2-not-0
                   (point1 point1)
                   (point2 (twisted-edwards-add point2 point3 curve))))
  :enable twisted-edwards-add
  :disable (1+d.x1.x2.y1.y2-not-0
            1-d.x1.x2.y1.y2-not-0
            point-on-twisted-edwards-p-of-twisted-edward-add
            twisted-edwards-add-commutative
            twisted-edwards-add-associative-right
            sub))

;; The nullary hypothesis of the Kestrel library is a theorem.

(defrule twisted-edwards-add-associativity-holds
  (twisted-edwards-add-associativity)
  :enable twisted-edwards-add-associativity
  :disable twisted-edwards-add-associative-right)
