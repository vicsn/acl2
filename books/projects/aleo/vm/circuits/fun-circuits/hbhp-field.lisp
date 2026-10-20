; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Small field identities behind the exceptional cases of BHP's incomplete
; Montgomery addition, each proved by an ideal-membership certificate whose
; cofactors are written out by hand and checked with the verified normaliser
; of ../edwards-assoc/field-certificate.lisp.  C(x, y) is the twisted Edwards
; equation a x^2 + y^2 = 1 + d x^2 y^2.
;
;   y = 1 or y = -1 on the curve      =>  (a - d) x^2 = 0
;   a = d y^2 on the curve            =>  a - d = 0
;   C(x1, y), C(x2, y)                =>  (a - d y^2) (x1 - x2) (x1 + x2) = 0
;   (1 - yi) ui = 1 + yi, u1 = u2     =>  2 (y2 - y1) = 0

(in-package "ALEOVM")

(include-book "../edwards-assoc/field-certificate")
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defruledl hbhpf-mod-of-1
  (implies (and (integerp p) (< 1 p))
           (equal (mod 1 p) 1)))

(defruledl hbhpf-equal-of-sub-and-0
  (implies (and (pfield::fep x p) (pfield::fep y p) (integerp p))
           (equal (equal (pfield::sub x y p) 0)
                  (equal x y)))
  :use (:instance pfield::equal-of-0-and-sub
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable (pfield::equal-of-0-and-sub pfield::sub))

(defruledl hbhpf-equal-of-mul-and-0
  (implies (and (pfield::fep x p) (pfield::fep y p) (dm::primep p))
           (equal (equal (pfield::mul x y p) 0)
                  (or (equal x 0) (equal y 0))))
  :use (:instance pfield::equal-of-0-and-mul
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable pfield::equal-of-0-and-mul)

(defruledl hbhpf-integerp-when-fep
  (implies (pfield::fep x p) (integerp x))
  :enable pfield::fep)

(defruledl hbhpf-mod-when-fep
  (implies (pfield::fep x p) (equal (mod x p) x))
  :enable pfield::fep)

(defruledl hbhpf-posp-when-primep
  (implies (dm::primep p) (posp p))
  :rule-classes :forward-chaining
  :enable dm::primep)

(defruledl hbhpf-fep-1
  (implies (and (dm::primep p) (< 2 p)) (pfield::fep 1 p))
  :enable (pfield::fep))

(defconst *hbhpf-theory*
  '(hbhpf-fep-1
    ecurve::evalf
    ecurve::gens-zerop
    dm::all-integers
    hbhpf-mod-of-1
    hbhpf-mod-when-fep
    hbhpf-equal-of-sub-and-0
    hbhpf-equal-of-mul-and-0
    hbhpf-integerp-when-fep
    hbhpf-posp-when-primep
    (:e nfix)
    pfield::fep-of-add
    pfield::fep-of-mul
    pfield::fep-of-sub
    pfield::fep-of-neg
    pfield::natp-of-add
    pfield::natp-of-mul
    pfield::natp-of-sub
    pfield::natp-of-neg))

; (hbhp-defcert name vars gens goal cofs) checks goal = sum cofs * gens and
; proves that goal evaluates to 0 wherever all gens do.
(defmacro hbhp-defcert (name vars gens goal cofs)
  (let ((okp (acl2::packn-pos (list name '-okp) name))
        (sound (acl2::packn-pos (list name '-sound) name)))
    `(progn
       (defthm ,okp
         (ecurve::certificate-okp ',goal ',cofs ',gens ',vars)
         :hints (("Goal" :in-theory '((:e ecurve::certificate-okp)))))
       (defruled ,sound
         (implies (and (dm::all-integers vals)
                       (<= ,(len vars) (len vals))
                       (posp p)
                       (ecurve::gens-zerop ',gens (pairlis$ ',vars vals) p))
                  (equal (ecurve::evalf ',goal (pairlis$ ',vars vals) p) 0))
         :use (,okp
               (:instance ecurve::certificate-okp-sound
                          (goal ',goal) (cofs ',cofs) (gens ',gens)
                          (vars ',vars)
                          (ecurve::vals vals) (ecurve::p p)))
         :in-theory '((:e len))))))

(hbhp-defcert hbhpf-y-one (a d x y)
  ((- (+ (* a (* x x)) (* y y)) (+ 1 (* d (* (* x x) (* y y)))))
   (- y 1))
  (* (- a d) (* x x))
  (1 (- (* (+ y 1) (- 1 (* d (* x x)))))))

(hbhp-defcert hbhpf-y-minus-one (a d x y)
  ((- (+ (* a (* x x)) (* y y)) (+ 1 (* d (* (* x x) (* y y)))))
   (+ y 1))
  (* (- a d) (* x x))
  (1 (- (* (- y 1) (- 1 (* d (* x x)))))))

(hbhp-defcert hbhpf-a-dy2 (a d x y)
  ((- (+ (* a (* x x)) (* y y)) (+ 1 (* d (* (* x x) (* y y)))))
   (- a (* d (* y y))))
  (- a d)
  (d (- 1 (* d (* x x)))))

(hbhp-defcert hbhpf-same-y (a d x1 x2 y)
  ((- (+ (* a (* x1 x1)) (* y y)) (+ 1 (* d (* (* x1 x1) (* y y)))))
   (- (+ (* a (* x2 x2)) (* y y)) (+ 1 (* d (* (* x2 x2) (* y y))))))
  (* (- a (* d (* y y))) (* (- x1 x2) (+ x1 x2)))
  (1 (- 1)))

(hbhp-defcert hbhpf-same-u (y1 y2 u1 u2)
  ((- (* (- 1 y1) u1) (+ 1 y1))
   (- (* (- 1 y2) u2) (+ 1 y2))
   (- u2 u1))
  (* (+ 1 1) (- y2 y1))
  ((- 1 y2) (- (- 1 y1)) (* (- 1 y1) (- 1 y2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro hbhpf-curve (a d x y p)
  `(equal (pfield::add (pfield::mul ,a (pfield::mul ,x ,x ,p) ,p)
                       (pfield::mul ,y ,y ,p) ,p)
          (pfield::add 1 (pfield::mul ,d (pfield::mul (pfield::mul ,x ,x ,p)
                                                      (pfield::mul ,y ,y ,p) ,p)
                                      ,p)
                       ,p)))

(defrule hbhp-x-zero-when-y-one
  :rule-classes nil
  (implies (and (dm::primep p) (< 2 p)
                (pfield::fep a p) (pfield::fep d p)
                (pfield::fep x p)
                (hbhpf-curve a d x 1 p)
                (not (equal a d)))
           (equal x 0))
  :use (:instance hbhpf-y-one-sound (vals (list a d x 1)))
  :in-theory (union-theories (theory 'acl2::ground-zero) *hbhpf-theory*))

(defrule hbhp-x-zero-when-y-minus-one
  :rule-classes nil
  (implies (and (dm::primep p) (< 2 p)
                (pfield::fep a p) (pfield::fep d p)
                (pfield::fep x p)
                (hbhpf-curve a d x (pfield::neg 1 p) p)
                (not (equal a d)))
           (equal x 0))
  :use (:instance hbhpf-y-minus-one-sound (vals (list a d x (pfield::neg 1 p))))
  :in-theory (union-theories (theory 'acl2::ground-zero)
                             (append '(pfield::add-of-neg-same-arg2 pfield::add-of-neg-same-arg1
                                       pfield::fep-of-neg)
                                     *hbhpf-theory*)))

(defruled hbhp-a-not-d-y2
  (implies (and (dm::primep p) (< 2 p)
                (pfield::fep a p) (pfield::fep d p)
                (pfield::fep x p) (pfield::fep y p)
                (hbhpf-curve a d x y p)
                (not (equal a d)))
           (not (equal a (pfield::mul d (pfield::mul y y p) p))))
  :use (:instance hbhpf-a-dy2-sound (vals (list a d x y)))
  :in-theory (union-theories (theory 'acl2::ground-zero) *hbhpf-theory*))

(defrule hbhp-same-y-abstract
  :rule-classes nil
  (implies (and (dm::primep p) (< 2 p)
                (pfield::fep a p) (pfield::fep d p)
                (pfield::fep x1 p) (pfield::fep x2 p) (pfield::fep y p)
                (hbhpf-curve a d x1 y p)
                (hbhpf-curve a d x2 y p)
                (not (equal a d)))
           (or (equal x1 x2)
               (equal (pfield::add x1 x2 p) 0)))
  :use ((:instance hbhpf-same-y-sound (vals (list a d x1 x2 y)))
        hbhp-a-not-d-y2
        (:instance hbhp-a-not-d-y2 (x x1)))
  :in-theory (union-theories (theory 'acl2::ground-zero) *hbhpf-theory*))

(defrule hbhp-same-u-abstract
  :rule-classes nil
  (implies (and (dm::primep p) (< 2 p)
                (pfield::fep y1 p) (pfield::fep y2 p)
                (pfield::fep u1 p) (pfield::fep u2 p)
                (equal (pfield::mul (pfield::sub 1 y1 p) u1 p) (pfield::add 1 y1 p))
                (equal (pfield::mul (pfield::sub 1 y2 p) u2 p) (pfield::add 1 y2 p))
                (equal u1 u2))
           (equal y1 y2))
  :use ((:instance hbhpf-same-u-sound (vals (list y1 y2 u1 u2)))
        (:instance hbhpf-two-nonzero))
  :in-theory (union-theories (theory 'acl2::ground-zero) *hbhpf-theory*)
  :prep-lemmas
  ((defruled hbhpf-two-nonzero
     (implies (and (dm::primep p) (< 2 p))
              (not (equal (pfield::add 1 1 p) 0)))
     :enable (pfield::add)
     :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))))
