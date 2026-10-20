; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Montgomery chord addition (the three constraints of BHPHasher's
; montgomery_add, circuit/algorithms/src/bhp/hasher/hash_uncompressed.rs)
; applied to the Montgomery images of two twisted Edwards points yields the
; Montgomery image of their Edwards sum.  The Montgomery image of (x, y) is
; u = (1 + y) / (1 - y), v = u / x (BHPHasher::Inject::new), and the
; Montgomery coefficients are A = 2 (a + d) / (a - d), B = 4 / (a - d).
;
; Proved by an ideal-membership certificate (hbhp-cert-data.lisp, generated
; by hbhp-sage/hbhp_emit.py with sympy and checked here with the verified
; normaliser of ../edwards-assoc/field-certificate.lisp).  Each division is a
; generator "denominator * quotient - numerator"; the goal is the
; Montgomery-image equation of the sum, times a product of factors that are
; nonzero under the hypotheses.
;
; The generator is only a helper; nothing it computes is trusted.  To
; regenerate the data (Python 3 with sympy), from this directory run
;   python3 hbhp-sage/hbhp_emit.py hbhp-cert-data.lisp

(in-package "ALEOVM")

(include-book "../edwards-assoc/field-certificate")
(include-book "hbhp-cert-data")
(include-book "std/util/defrule" :dir :system)

(defconst *hbhp-gens*
  (list
   '(- (* (- a d) ma) (+ (+ a d) (+ a d)))
   '(- (* (- a d) mb) (+ (+ 1 1) (+ 1 1)))
   '(- (+ (* a (* x1 x1)) (* y1 y1)) (+ 1 (* d (* (* x1 x1) (* y1 y1)))))
   '(- (+ (* a (* x2 x2)) (* y2 y2)) (+ 1 (* d (* (* x2 x2) (* y2 y2)))))
   '(- (* (- 1 y1) u1) (+ 1 y1))
   '(- (* (- 1 y2) u2) (+ 1 y2))
   '(- (* x1 v1) u1)
   '(- (* x2 v2) u2)
   '(- (* (- u2 u1) lam) (- v2 v1))
   '(- (* (* mb lam) lam) (+ (+ (+ ma u1) u2) u3))
   '(- (* (- u1 u3) lam) (+ v1 v3))
   '(- (* (+ 1 (* d (* x1 (* x2 (* y1 y2))))) x3) (+ (* x1 y2) (* y1 x2)))
   '(- (* (- 1 (* d (* x1 (* x2 (* y1 y2))))) y3) (- (* y1 y2) (* a (* x1 x2))))))

(defconst *hbhp-goal-u*
  '(* (* (expt d 2)
         (* (expt x1 2)
            (* (expt x2 2)
               (* (expt (- 1 y1) 3)
                  (* (expt (- 1 y2) 3)
                     (* (expt (- a d) 2)
                        (* (expt (- u2 u1) 2)
                           (- 1 (* d (* x1 (* x2 (* y1 y2))))))))))))
      (- (+ 1 y3) (* (- 1 y3) u3))))

(defconst *hbhp-goal-v*
  '(* (* (expt d 3)
         (* (expt x1 3)
            (* (expt x2 3)
               (* (expt (- 1 y1) 4)
                  (* (expt (- 1 y2) 4)
                     (* (expt (- a d) 2)
                        (* (expt (- u2 u1) 3)
                           (+ 1 (* d (* x1 (* x2 (* y1 y2))))))))))))
      (- (* x3 v3) u3)))

(defthm hbhp-cert-u-okp
  (ecurve::certificate-okp *hbhp-goal-u*
                           *hbhp-cert-cofactors-u*
                           *hbhp-gens*
                           *hbhp-cert-vars*)
  :hints (("Goal" :in-theory '((:e ecurve::certificate-okp)))))

(defthm hbhp-cert-v-okp
  (ecurve::certificate-okp *hbhp-goal-v*
                           *hbhp-cert-cofactors-v*
                           *hbhp-gens*
                           *hbhp-cert-vars*)
  :hints (("Goal" :in-theory '((:e ecurve::certificate-okp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl hbhp-mod-of-1
  (implies (and (integerp p) (< 1 p))
           (equal (mod 1 p) 1))
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruledl hbhp-equal-of-sub-and-0
  (implies (and (pfield::fep x p) (pfield::fep y p) (integerp p))
           (equal (equal (pfield::sub x y p) 0)
                  (equal x y)))
  :use (:instance pfield::equal-of-0-and-sub
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable (pfield::equal-of-0-and-sub pfield::sub))

(defruledl hbhp-equal-of-mul-and-0
  (implies (and (pfield::fep x p) (pfield::fep y p) (dm::primep p))
           (equal (equal (pfield::mul x y p) 0)
                  (or (equal x 0) (equal y 0))))
  :use (:instance pfield::equal-of-0-and-mul
                  (pfield::x x) (pfield::y y) (pfield::p p))
  :disable pfield::equal-of-0-and-mul)

(defruledl hbhp-integerp-when-fep
  (implies (pfield::fep x p) (integerp x))
  :enable pfield::fep)

(defruledl hbhp-mod-when-fep
  (implies (pfield::fep x p) (equal (mod x p) x))
  :enable pfield::fep
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruledl hbhp-posp-when-primep
  (implies (dm::primep p) (posp p))
  :rule-classes :forward-chaining
  :enable dm::primep)

(defruledl hbhp-fep-of-evalf-pow
  (implies (and (posp p) (pfield::fep x p))
           (pfield::fep (ecurve::evalf-pow x k p) p))
  :induct (ecurve::evalf-pow x k p)
  :enable (ecurve::evalf-pow pfield::fep)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruledl hbhp-evalf-pow-nonzero
  (implies (and (dm::primep p) (pfield::fep x p) (not (equal x 0)))
           (not (equal (ecurve::evalf-pow x k p) 0)))
  :induct (ecurve::evalf-pow x k p)
  :enable (ecurve::evalf-pow hbhp-equal-of-mul-and-0 hbhp-mod-of-1
           hbhp-posp-when-primep hbhp-fep-of-evalf-pow)
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defmacro hbhp-den+ () '(pfield::add 1 (pfield::mul d (pfield::mul x1 (pfield::mul x2 (pfield::mul y1 y2 p) p) p) p) p))
(defmacro hbhp-den- () '(pfield::sub 1 (pfield::mul d (pfield::mul x1 (pfield::mul x2 (pfield::mul y1 y2 p) p) p) p) p))

(defmacro hbhp-mont-hyps ()
  '(and (dm::primep p)
        (< 2 p)
        (pfield::fep a p) (pfield::fep d p) (pfield::fep ma p) (pfield::fep mb p)
        (pfield::fep x1 p) (pfield::fep y1 p) (pfield::fep x2 p) (pfield::fep y2 p)
        (pfield::fep u1 p) (pfield::fep v1 p) (pfield::fep u2 p) (pfield::fep v2 p)
        (pfield::fep lam p) (pfield::fep u3 p) (pfield::fep v3 p)
        (pfield::fep x3 p) (pfield::fep y3 p)
        (equal (pfield::mul (pfield::sub a d p) ma p)
               (pfield::add (pfield::add a d p) (pfield::add a d p) p))
        (equal (pfield::mul (pfield::sub a d p) mb p)
               (pfield::add (pfield::add 1 1 p) (pfield::add 1 1 p) p))
        (equal (pfield::add (pfield::mul a (pfield::mul x1 x1 p) p) (pfield::mul y1 y1 p) p)
               (pfield::add 1 (pfield::mul d (pfield::mul (pfield::mul x1 x1 p) (pfield::mul y1 y1 p) p) p) p))
        (equal (pfield::add (pfield::mul a (pfield::mul x2 x2 p) p) (pfield::mul y2 y2 p) p)
               (pfield::add 1 (pfield::mul d (pfield::mul (pfield::mul x2 x2 p) (pfield::mul y2 y2 p) p) p) p))
        (equal (pfield::mul (pfield::sub 1 y1 p) u1 p) (pfield::add 1 y1 p))
        (equal (pfield::mul (pfield::sub 1 y2 p) u2 p) (pfield::add 1 y2 p))
        (equal (pfield::mul x1 v1 p) u1)
        (equal (pfield::mul x2 v2 p) u2)
        (equal (pfield::mul (pfield::sub u2 u1 p) lam p) (pfield::sub v2 v1 p))
        (equal (pfield::mul (pfield::mul mb lam p) lam p)
               (pfield::add (pfield::add (pfield::add ma u1 p) u2 p) u3 p))
        (equal (pfield::mul (pfield::sub u1 u3 p) lam p) (pfield::add v1 v3 p))
        (equal (pfield::mul (hbhp-den+) x3 p)
               (pfield::add (pfield::mul x1 y2 p) (pfield::mul y1 x2 p) p))
        (equal (pfield::mul (hbhp-den-) y3 p)
               (pfield::sub (pfield::mul y1 y2 p) (pfield::mul a (pfield::mul x1 x2 p) p) p))
        (not (equal d 0))
        (not (equal x1 0))
        (not (equal x2 0))
        (not (equal (pfield::sub 1 y1 p) 0))
        (not (equal (pfield::sub 1 y2 p) 0))
        (not (equal (pfield::sub a d p) 0))
        (not (equal (pfield::sub u2 u1 p) 0))
        (not (equal (hbhp-den+) 0))
        (not (equal (hbhp-den-) 0))))

(defruledl hbhp-cert-u-sound
  (implies (and (dm::all-integers vals)
                (<= (len *hbhp-cert-vars*) (len vals))
                (posp p)
                (ecurve::gens-zerop *hbhp-gens* (pairlis$ *hbhp-cert-vars* vals) p))
           (equal (ecurve::evalf *hbhp-goal-u* (pairlis$ *hbhp-cert-vars* vals) p) 0))
  :use (hbhp-cert-u-okp
        (:instance ecurve::certificate-okp-sound
                   (goal *hbhp-goal-u*)
                   (cofs *hbhp-cert-cofactors-u*)
                   (gens *hbhp-gens*)
                   (vars *hbhp-cert-vars*)
                   (ecurve::vals vals) (ecurve::p p)))
  :in-theory nil)

(defruledl hbhp-cert-v-sound
  (implies (and (dm::all-integers vals)
                (<= (len *hbhp-cert-vars*) (len vals))
                (posp p)
                (ecurve::gens-zerop *hbhp-gens* (pairlis$ *hbhp-cert-vars* vals) p))
           (equal (ecurve::evalf *hbhp-goal-v* (pairlis$ *hbhp-cert-vars* vals) p) 0))
  :use (hbhp-cert-v-okp
        (:instance ecurve::certificate-okp-sound
                   (goal *hbhp-goal-v*)
                   (cofs *hbhp-cert-cofactors-v*)
                   (gens *hbhp-gens*)
                   (vars *hbhp-cert-vars*)
                   (ecurve::vals vals) (ecurve::p p)))
  :in-theory nil)

(defruled hbhp-mont-add-abstract
  :short "Montgomery chord addition of Montgomery images is the Montgomery
          image of the Edwards sum, at the level of field equations."
  (implies (hbhp-mont-hyps)
           (and (equal (pfield::mul (pfield::sub 1 y3 p) u3 p)
                       (pfield::add 1 y3 p))
                (equal (pfield::mul x3 v3 p) u3)))
  :use ((:instance hbhp-cert-u-sound
                   (vals (list a d ma mb x1 y1 x2 y2 u1 v1 u2 v2 lam u3 v3 x3 y3)))
        (:instance hbhp-cert-v-sound
                   (vals (list a d ma mb x1 y1 x2 y2 u1 v1 u2 v2 lam u3 v3 x3 y3))))
  :in-theory (union-theories
              (theory 'acl2::ground-zero)
              '(ecurve::evalf
                ecurve::gens-zerop
                dm::all-integers
                hbhp-mod-of-1
                hbhp-mod-when-fep
                hbhp-equal-of-sub-and-0
                hbhp-equal-of-mul-and-0
                hbhp-integerp-when-fep
                hbhp-posp-when-primep
                hbhp-evalf-pow-nonzero
                hbhp-fep-of-evalf-pow
                (:e nfix)
                pfield::fep-of-add
                pfield::fep-of-mul
                pfield::fep-of-sub
                pfield::fep-of-neg
                pfield::natp-of-add
                pfield::natp-of-mul
                pfield::natp-of-sub
                pfield::natp-of-neg)))
