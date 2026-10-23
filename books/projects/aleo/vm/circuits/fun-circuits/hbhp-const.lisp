; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Native evaluation of the BHP gadgets on constant inputs.
;
; snarkVM folds constants: witness! on constant inputs is computed natively
; and E::enforce on three constant linear combinations emits nothing.  So
; on constant chunks the lookup, montgomery_add, the Edwards conversion and
; Group::add are evaluated with the formulas of their witness closures.
; This book defines those formulas and proves that they compute the
; mathematical values.

(in-package "ALEOVM")

(include-book "hbhp-phasher")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constant chunks of a window.

(defruledl hbhp-k-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(define hbhp-cchunk-u (b0 b1 g (j natp))
  :verify-guards nil
  (hbhp-sel4 (hbhp-tab-x g j) b0 b1))

(define hbhp-cchunk-v (b0 b1 b2 g (j natp))
  :verify-guards nil
  (b* ((y (hbhp-sel4 (hbhp-tab-y g j) b0 b1)))
    (if (equal b2 1) (pfield::neg y (base-prime)) y)))

(define hbhp-cwin-acc (bits g (j natp) u v)
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :in-theory (enable hbhp-k-len-of-nthcdr)))
  :short "montgomery_add of the constant chunks @('bits') (bit values) into
          the constant accumulator @('(u, v)'), from chunk position @('j')."
  (if (< (len bits) 3)
      (cons u v)
    (b* ((u2 (hbhp-cchunk-u (nth 0 bits) (nth 1 bits) g j))
         (v2 (hbhp-cchunk-v (nth 0 bits) (nth 1 bits) (nth 2 bits) g j))
         (lam (hbhp-mont-lam u v u2 v2))
         (u3 (hbhp-mont-sum-u u u2 lam))
         (v3 (hbhp-mont-sum-v u v lam u3)))
      (hbhp-cwin-acc (nthcdr 3 bits) g (1+ (lnfix j)) u3 v3))))

(define hbhp-cwin-start (bits g)
  :verify-guards nil
  :short "The accumulator after the constant chunks @('bits') at the start
          of a window: the first chunk initialises it."
  (hbhp-cwin-acc (nthcdr 3 bits) g 1
                 (hbhp-cchunk-u (nth 0 bits) (nth 1 bits) g 0)
                 (hbhp-cchunk-v (nth 0 bits) (nth 1 bits) (nth 2 bits) g 0)))

(defun hbhp-cwin-induct (bits j s)
  (declare (xargs :measure (len bits) :verify-guards nil
                  :hints (("Goal" :in-theory (enable hbhp-k-len-of-nthcdr)))))
  (if (< (len bits) 3)
      (list j s)
    (hbhp-cwin-induct (nthcdr 3 bits) (1+ (nfix j))
                      (+ s (* (hbhp-chunk-scalar (nth 0 bits) (nth 1 bits)
                                                 (nth 2 bits))
                              (expt 16 (nfix j)))))))

(defruled hbhp-k-nth-012
  (and (equal (nth 0 x) (car x))
       (equal (nth 1 x) (cadr x))
       (equal (nth 2 x) (caddr x)))
  :enable nth)

(defruled hbhp-bit-listp-facts
  (implies (and (bit-listp bits) (<= 3 (len bits)))
           (and (bitp (nth 0 bits)) (bitp (nth 1 bits)) (bitp (nth 2 bits))
                (bit-listp (nthcdr 3 bits))))
  :enable (bit-listp nth nthcdr))

(defruled hbhp-cchunk-point
  (implies (and (hbhp-gen-okp g) (natp j) (<= j 62)
                (bitp b0) (bitp b1) (bitp b2))
           (b* ((pt (hbhp-gp (* (hbhp-chunk-scalar b0 b1 b2) (expt 16 j)) g)))
             (and (equal (hbhp-cchunk-u b0 b1 g j) (hbhp-mu pt))
                  (equal (hbhp-cchunk-v b0 b1 b2 g j) (hbhp-mv pt)))))
  :use (:instance hbhp-chunk-point (p (base-prime)))
  :in-theory '(hbhp-cchunk-u hbhp-cchunk-v))

(defruled hbhp-cwin-step
  (implies (and (hbhp-gen-okp g)
                (natp j) (<= 1 j) (<= j 62)
                (hbhp-acc-okp s j)
                (bitp b0) (bitp b1) (bitp b2))
           (b* ((cc (* (hbhp-chunk-scalar b0 b1 b2) (expt 16 j)))
                (s2 (+ s cc))
                (u (hbhp-mu (hbhp-gp s g)))
                (v (hbhp-mv (hbhp-gp s g)))
                (u2 (hbhp-cchunk-u b0 b1 g j))
                (v2 (hbhp-cchunk-v b0 b1 b2 g j))
                (lam (hbhp-mont-lam u v u2 v2)))
             (and (equal (hbhp-mont-sum-u u u2 lam) (hbhp-mu (hbhp-gp s2 g)))
                  (equal (hbhp-mont-sum-v u v lam (hbhp-mu (hbhp-gp s2 g)))
                         (hbhp-mv (hbhp-gp s2 g)))
                  (hbhp-acc-okp s2 (+ 1 j)))))
  :use (hbhp-cchunk-point
        (:instance hbhp-chunk-scalar-range)
        (:instance hbhp-window-step-points (c (hbhp-chunk-scalar b0 b1 b2)))
        (:instance hbhp-mont-add-complete
                   (p (base-prime))
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (* (hbhp-chunk-scalar b0 b1 b2) (expt 16 j)) g))))
  :in-theory nil)

(defruled hbhp-cwin-acc-correct
  (implies (and (hbhp-gen-okp g)
                (natp j) (<= 1 j) (<= (+ j (hbhp-nchunks bits)) 63)
                (hbhp-acc-okp s j)
                (bit-listp bits))
           (b* ((s2 (+ s (hbhp-window-scalar bits j))))
             (and (equal (hbhp-cwin-acc bits g j (hbhp-mu (hbhp-gp s g))
                                        (hbhp-mv (hbhp-gp s g)))
                         (cons (hbhp-mu (hbhp-gp s2 g)) (hbhp-mv (hbhp-gp s2 g))))
                  (hbhp-acc-okp s2 (+ j (hbhp-nchunks bits))))))
  :induct (hbhp-cwin-induct bits j s)
  :in-theory '((:induction hbhp-cwin-induct) natp nfix lnfix
               hbhp-k-plus-assoc hbhp-k-plus-0 hbhp-k-plus-1-comm
               hbhp-k-acc-okp-integerp (:t hbhp-nchunks) (:t hbhp-window-scalar))
  :hints (("Subgoal *1/2"
           :expand ((:free (u v) (hbhp-cwin-acc bits g j u v))
                    (hbhp-nchunks bits)
                    (hbhp-window-scalar bits j))
           :in-theory '(natp nfix lnfix hbhp-cwin-step hbhp-k-plus-assoc
                        hbhp-k-plus-0 hbhp-k-plus-1-comm hbhp-k-acc-okp-integerp
                        (:t hbhp-nchunks) (:t hbhp-window-scalar) (:e <) car-cons cdr-cons
                        hbhp-k-nth-012)
           :use (hbhp-bit-listp-facts
                 (:instance hbhp-k-chunk-int
                            (b0 (nth 0 bits)) (b1 (nth 1 bits)) (b2 (nth 2 bits)))))
          ("Subgoal *1/1"
           :expand ((:free (u v) (hbhp-cwin-acc bits g j u v))
                    (hbhp-nchunks bits)
                    (hbhp-window-scalar bits j))))
  :prep-lemmas
  ((defruled hbhp-k-plus-assoc
     (equal (+ x (+ y z)) (+ (+ x y) z)))
   (defruled hbhp-k-plus-1-comm
     (equal (+ x 1) (+ 1 x)))
   (defruled hbhp-k-plus-0
     (implies (integerp x) (equal (+ x 0) x)))
   (defruled hbhp-k-chunk-int
     (implies (natp j)
              (integerp (* (hbhp-chunk-scalar b0 b1 b2) (expt 16 j)))))
   (defruled hbhp-k-acc-okp-integerp
     (implies (hbhp-acc-okp s j) (integerp s))
     :enable hbhp-acc-okp)))

(defruled hbhp-cwin-start-correct
  (implies (and (hbhp-gen-okp g)
                (bit-listp bits) (<= 3 (len bits))
                (<= (hbhp-nchunks bits) 63))
           (b* ((s (hbhp-window-scalar bits 0)))
             (and (equal (hbhp-cwin-start bits g)
                         (cons (hbhp-mu (hbhp-gp s g)) (hbhp-mv (hbhp-gp s g))))
                  (hbhp-acc-okp s (hbhp-nchunks bits)))))
  :use (hbhp-bit-listp-facts
        (:instance hbhp-cchunk-point (j 0)
                   (b0 (nth 0 bits)) (b1 (nth 1 bits)) (b2 (nth 2 bits)))
        (:instance hbhp-acc-okp-first
                   (b0 (nth 0 bits)) (b1 (nth 1 bits)) (b2 (nth 2 bits)))
        (:instance hbhp-cwin-acc-correct
                   (bits (nthcdr 3 bits)) (j 1)
                   (s (hbhp-chunk-scalar (nth 0 bits) (nth 1 bits) (nth 2 bits))))
        (:instance hbhp-window-scalar (j 0))
        (:instance hbhp-nchunks (bs bits)))
  :in-theory '(hbhp-cwin-start natp (:e expt) (:e <) lnfix nfix hbhp-k-times-1
               (:t hbhp-chunk-scalar) hbhp-k-1-plus hbhp-k-nth-012)
  :prep-lemmas
  ((defruled hbhp-k-times-1
     (implies (integerp x) (equal (* x 1) x)))
   (defruled hbhp-k-1-plus
     (equal (+ 1 x) (+ x 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversion of a constant window sum to Edwards form (div_unchecked on
;; constants is native division).

(define hbhp-nedwards (u v)
  :verify-guards nil
  (b* ((p (base-prime)))
    (ecurve::point-finite (pfield::div u v p)
                          (pfield::div (pfield::sub u 1 p) (pfield::add u 1 p) p))))

(defruledl hbhp-k-mul-div
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p)
                (not (equal x 0)))
           (equal (pfield::mul (pfield::div y x p) x p) y)))

(defruled hbhp-nedwards-correct
  (implies (and (hbhp-gen-okp g)
                (natp j) (< 0 j) (<= j 63)
                (hbhp-acc-okp s j))
           (equal (hbhp-nedwards (hbhp-mu (hbhp-gp s g)) (hbhp-mv (hbhp-gp s g)))
                  (hbhp-gp s g)))
  :use ((:instance hbhp-to-edwards-sound
                   (p (base-prime)) (pt (hbhp-gp s g))
                   (ex (pfield::div (hbhp-mu (hbhp-gp s g)) (hbhp-mv (hbhp-gp s g))
                                    (base-prime)))
                   (ey (pfield::div (pfield::sub (hbhp-mu (hbhp-gp s g)) 1 (base-prime))
                                    (pfield::add (hbhp-mu (hbhp-gp s g)) 1 (base-prime))
                                    (base-prime))))
        (:instance hbhp-mont-image (p (base-prime)) (pt (hbhp-gp s g)))
        (:instance hbhp-k-mul-div (p (base-prime))
                   (x (hbhp-mv (hbhp-gp s g))) (y (hbhp-mu (hbhp-gp s g))))
        (:instance hbhp-k-mul-div (p (base-prime))
                   (x (pfield::add (hbhp-mu (hbhp-gp s g)) 1 (base-prime)))
                   (y (pfield::sub (hbhp-mu (hbhp-gp s g)) 1 (base-prime))))
        (:instance hbhp-x-of-mul-nonzero (n s))
        (:instance hbhp-small-scalar-mod (x s) (k j))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar s) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        hbhp-p-acc-okp-facts)
  :in-theory '(hbhp-nedwards hbhp-base-prime-facts natp pfield::fep-of-div
               pfield::fep-of-sub pfield::fep-of-add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group::add on two constants: the zero shortcuts, then the witness
;; formulas of x3 and y3 on native values.

(define hbhp-nadd (p1 p2)
  :verify-guards nil
  (b* ((p (base-prime))
       ((when (equal p1 (ecurve::twisted-edwards-zero))) p2)
       ((when (equal p2 (ecurve::twisted-edwards-zero))) p1)
       (a (ecurve::edwards-bls12-a))
       (d (ecurve::edwards-bls12-d))
       (x1 (ecurve::point-finite->x p1)) (y1 (ecurve::point-finite->y p1))
       (x2 (ecurve::point-finite->x p2)) (y2 (ecurve::point-finite->y p2))
       (u1 (pfield::add (pfield::mul x1 (pfield::neg a p) p) y1 p))
       (u2 (pfield::add x2 y2 p))
       (u (pfield::mul u1 u2 p))
       (v0 (pfield::mul x1 y2 p))
       (v1 (pfield::mul x2 y1 p))
       (v2 (pfield::mul (pfield::mul v0 v1 p) d p))
       (x3 (pfield::div (pfield::add v0 v1 p) (pfield::add v2 1 p) p))
       (y3 (pfield::div (pfield::sub (pfield::add u (pfield::mul v0 a p) p) v1 p)
                        (pfield::sub 1 v2 p) p)))
    (ecurve::point-finite x3 y3)))

(defruledl hbhp-k-dens
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (b* ((p (base-prime))
                (d (ecurve::edwards-bls12-d))
                (x1 (ecurve::point-finite->x p1)) (y1 (ecurve::point-finite->y p1))
                (x2 (ecurve::point-finite->x p2)) (y2 (ecurve::point-finite->y p2))
                (dv (pfield::mul d (pfield::mul (pfield::mul x1 y2 p)
                                                (pfield::mul x2 y1 p) p) p)))
             (and (not (equal (pfield::add 1 dv p) 0))
                  (not (equal (pfield::sub 1 dv p) 0)))))
  :use (crv-add-dens-nonzero
        (:instance crv-fep-of-edwards-bls12-coords (pt p1) (p (base-prime)))
        (:instance crv-fep-of-edwards-bls12-coords (pt p2) (p (base-prime))))
  :in-theory '(curve-base-prime-is-edwards-bls12-q pfield::mul-associative
               pfield::mul-commutative pfield::mul-commutative-2
               primep-of-base-prime))

(defun hbhp-k-terms ()
  (declare (xargs :guard t :mode :program))
  '((p (base-prime))
    (d (ecurve::edwards-bls12-d))
    (x1 (ecurve::point-finite->x p1)) (y1 (ecurve::point-finite->y p1))
    (x2 (ecurve::point-finite->x p2)) (y2 (ecurve::point-finite->y p2))
    (u (pfield::mul (pfield::add x1 y1 p) (pfield::add x2 y2 p) p))
    (v0 (pfield::mul x1 y2 p))
    (v1 (pfield::mul x2 y1 p))
    (v01 (pfield::mul v0 v1 p))
    (n1 (pfield::add v0 v1 p))
    (d1 (pfield::add 1 (pfield::mul d v01 p) p))
    (n2 (pfield::sub (pfield::sub u v0 p) v1 p))
    (d2 (pfield::sub 1 (pfield::mul d v01 p) p))))

(mutual-recursion
 (defun hbhp-k-subst1 (x binds)
   (declare (xargs :guard t :mode :program))
   (cond ((symbolp x) (let ((b (assoc-eq x binds)))
                        (if b (hbhp-k-subst1 (cadr b) binds) x)))
         ((atom x) x)
         ((eq (car x) 'quote) x)
         (t (cons (car x) (hbhp-k-subst1-lst (cdr x) binds)))))
 (defun hbhp-k-subst1-lst (xs binds)
   (declare (xargs :guard t :mode :program))
   (if (atom xs) nil
     (cons (hbhp-k-subst1 (car xs) binds) (hbhp-k-subst1-lst (cdr xs) binds)))))

(defun hbhp-k-subst (x)
  (declare (xargs :guard t :mode :program))
  (hbhp-k-subst1 x (hbhp-k-terms)))

(defun hbhp-k-inst-binds ()
  (declare (xargs :guard t :mode :program))
  (list (list 'p '(base-prime))
        (list 'x1 (hbhp-k-subst 'x1)) (list 'y1 (hbhp-k-subst 'y1))
        (list 'x2 (hbhp-k-subst 'x2)) (list 'y2 (hbhp-k-subst 'y2))
        (list 'u (hbhp-k-subst 'u)) (list 'v0 (hbhp-k-subst 'v0))
        (list 'v1 (hbhp-k-subst 'v1)) (list 'v01 (hbhp-k-subst 'v01))
        (list 'x3 (hbhp-k-subst '(pfield::div n1 d1 p)))
        (list 'y3 (hbhp-k-subst '(pfield::div n2 d2 p)))))

(defun hbhp-k-mul-div-binds (n d)
  (declare (xargs :guard t :mode :program))
  (list (list 'x (hbhp-k-subst d)) (list 'y (hbhp-k-subst n))))

(make-event
 `(defruledl hbhp-k-nadd-normal
    (implies (and (ecurve::edwards-bls12-pointp p1)
                  (ecurve::edwards-bls12-pointp p2)
                  (not (equal p1 (ecurve::twisted-edwards-zero)))
                  (not (equal p2 (ecurve::twisted-edwards-zero))))
             (b* ,(hbhp-k-terms)
               (equal (hbhp-nadd p1 p2)
                      (ecurve::point-finite (pfield::div n1 d1 p)
                                            (pfield::div n2 d2 p)))))
    :use ((:instance crv-fep-of-edwards-bls12-coords (pt p1) (p (base-prime)))
          (:instance crv-fep-of-edwards-bls12-coords (pt p2) (p (base-prime))))
    :enable (hbhp-nadd crv-edwards-a-is-neg-one pfield::sub
             pfield::mul-commutative pfield::add-commutative)))

(make-event
 `(defruledl hbhp-k-nadd-eqns
    (implies (and (ecurve::edwards-bls12-pointp p1)
                  (ecurve::edwards-bls12-pointp p2))
             (b* ,(hbhp-k-terms)
               (implies (and (not (equal d1 0)) (not (equal d2 0)))
                        (equal (ecurve::point-finite (pfield::div n1 d1 p)
                                                     (pfield::div n2 d2 p))
                               (ecurve::edwards-bls12-add p1 p2)))))
    :use ((:instance crv-fep-of-edwards-bls12-coords (pt p1) (p (base-prime)))
          (:instance crv-fep-of-edwards-bls12-coords (pt p2) (p (base-prime)))
          curve-fep-of-edwards-bls12-d
          (:instance crv-group-add-from-equations
                     ,@(hbhp-k-inst-binds))
          (:instance hbhp-k-mul-div (p (base-prime))
                     ,@(hbhp-k-mul-div-binds 'n1 'd1))
          (:instance hbhp-k-mul-div (p (base-prime))
                     ,@(hbhp-k-mul-div-binds 'n2 'd2)))
    :in-theory '(hbhp-base-prime-facts pfield::fep-of-div pfield::fep-of-add
                 pfield::fep-of-mul pfield::fep-of-sub)))

(defruled hbhp-nadd-correct
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (equal (hbhp-nadd p1 p2) (ecurve::edwards-bls12-add p1 p2)))
  :cases ((equal p1 (ecurve::twisted-edwards-zero))
          (equal p2 (ecurve::twisted-edwards-zero)))
  :hints (("Subgoal 2"
           :use ((:instance hbhp-add-zero-left (pt p2)))
           :in-theory '(hbhp-nadd))
          ("Subgoal 1"
           :use ((:instance hbhp-add-zero-left (pt p1))
                 (:instance hbhp-add-comm (a p1) (b p2)))
           :in-theory '(hbhp-nadd))
          ("Subgoal 3"
           :use (hbhp-k-dens hbhp-k-nadd-normal hbhp-k-nadd-eqns)
           :in-theory nil)))
