; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHP::commit_uncompressed (circuit/algorithms/src/bhp/commit_uncompressed.rs):
;
;   randomizer.to_bits_le().iter().zip_eq(random_base)
;     .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
;     .fold(hash_uncompressed(input), |acc, x| acc + x)
;
; The randomizer bits are those of Scalar::to_bits_le
; (scalar-write-bits-le-gadget, 251 bits).  For a non-empty input the hash
; is held in wires and every add is the variable/variable add with the
; ternary point as `this' (hbhp-commit-fold-gadget).  For the empty input
; the hash is the constant zero: Group::add returns the first ternary point
; itself (linear combinations, no constraint), and the second add has both
; operands as linear combinations (hbhp-lcadd-gadget); the remaining adds
; are again hbhp-commit-fold-gadget.

(in-package "ALEOVM")

(include-book "hbhp-hu")
(include-book "hbhp-commit")
(include-book "scalar-write-bits-r1cs")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The variable/variable Group::add with both operands as linear
;; combinations: `this' = (x1, y1), `that' = (x2, y2).

(define hbhp-lcadd-gadget (x1 y1 x2 y2
                           (u symbolp) (v0 symbolp) (v1 symbolp) (v01 symbolp)
                           (x3 symbolp) (y3 symbolp) (p posp))
  :verify-guards nil
  (b* ((d (ecurve::edwards-bls12-d)))
    (list (r1cs::make-r1cs-constraint
           :a (append x1 y1)
           :b (append x2 y2)
           :c (list (list 1 u)))
          (r1cs::make-r1cs-constraint
           :a x1
           :b y2
           :c (list (list 1 v0)))
          (r1cs::make-r1cs-constraint
           :a x2
           :b y1
           :c (list (list 1 v1)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 v0))
           :b (list (list 1 v1))
           :c (list (list 1 v01)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 x3))
           :b (list (list 1 1) (list d v01))
           :c (list (list 1 v0) (list 1 v1)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 y3))
           :b (list (list 1 1) (list (pfield::neg d p) v01))
           :c (list (list 1 u) (list (1- p) v0) (list (1- p) v1))))))

(defruled hbhp-cadd-is-lcadd
  (equal (hbhp-cadd-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p)
         (hbhp-lcadd-gadget x1 y1 (list (list 1 x2)) (list (list 1 y2))
                            u v0 v1 v01 x3 y3 p))
  :enable (hbhp-cadd-gadget hbhp-lcadd-gadget))

(defruled hbhp-lcadd-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3))
           (b* ((x1$ (hbhp-dot x1)) (y1$ (hbhp-dot y1))
                (x2$ (hbhp-dot x2)) (y2$ (hbhp-dot y2))
                (u$ (hbhp-lk u)) (v0$ (hbhp-lk v0)) (v1$ (hbhp-lk v1))
                (v01$ (hbhp-lk v01)) (x3$ (hbhp-lk x3)) (y3$ (hbhp-lk y3))
                (d (ecurve::edwards-bls12-d)))
             (equal (r1cs::r1cs-constraints-holdp
                     (hbhp-lcadd-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p) asg p)
                    (and (equal u$ (pfield::mul (pfield::add x1$ y1$ p)
                                                (pfield::add x2$ y2$ p) p))
                         (equal v0$ (pfield::mul x1$ y2$ p))
                         (equal v1$ (pfield::mul x2$ y1$ p))
                         (equal v01$ (pfield::mul v0$ v1$ p))
                         (equal (pfield::mul x3$
                                             (pfield::add 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::add v0$ v1$ p))
                         (equal (pfield::mul y3$
                                             (pfield::sub 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::sub (pfield::sub u$ v0$ p) v1$ p))))))
  :use (hbhp-base-prime-facts curve-fep-of-edwards-bls12-d)
  :enable (hbhp-lcadd-gadget r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           hbhp-dot-cons hbhp-dot-nil r1cs::dot-product-of-append
           pfield::sub)
  :disable (r1cs::dot-product))

(defmacro hbhp-lcadd-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (equal (hbhp-dot x1) (ecurve::point-finite->x p1))
        (equal (hbhp-dot y1) (ecurve::point-finite->y p1))
        (equal (hbhp-dot x2) (ecurve::point-finite->x p2))
        (equal (hbhp-dot y2) (ecurve::point-finite->y p2))
        (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
        (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)))

(defruled hbhp-lcadd-sound
  (implies (and (hbhp-lcadd-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-lcadd-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p) asg p))
           (equal (ecurve::point-finite (hbhp-lk x3) (hbhp-lk y3))
                  (ecurve::edwards-bls12-add p2 p1)))
  :use (hbhp-lcadd-gadget-to-eqns
        (:instance crv-group-add-from-equations
                   (x1 (hbhp-dot x1)) (y1 (hbhp-dot y1))
                   (x2 (hbhp-dot x2)) (y2 (hbhp-dot y2))
                   (u (hbhp-lk u)) (v0 (hbhp-lk v0)) (v1 (hbhp-lk v1))
                   (v01 (hbhp-lk v01)) (x3 (hbhp-lk x3)) (y3 (hbhp-lk y3)))
        (:instance hbhp-add-comm (a p2) (b p1))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x3)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y3)
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(hbhp-base-prime-facts pfield::fep nfix natp))

(defmacro hbhp-lcadd-canon (u v0 v1 v01 x3 y3 p1 p2)
  `(b* ((x1$ (ecurve::point-finite->x ,p1)) (y1$ (ecurve::point-finite->y ,p1))
        (x2$ (ecurve::point-finite->x ,p2)) (y2$ (ecurve::point-finite->y ,p2))
        (s (ecurve::edwards-bls12-add ,p2 ,p1)))
     (and (equal (hbhp-lk ,u) (pfield::mul (pfield::add x1$ y1$ p)
                                           (pfield::add x2$ y2$ p) p))
          (equal (hbhp-lk ,v0) (pfield::mul x1$ y2$ p))
          (equal (hbhp-lk ,v1) (pfield::mul x2$ y1$ p))
          (equal (hbhp-lk ,v01) (pfield::mul (hbhp-lk ,v0) (hbhp-lk ,v1) p))
          (equal (hbhp-lk ,x3) (ecurve::point-finite->x s))
          (equal (hbhp-lk ,y3) (ecurve::point-finite->y s)))))

(defruled hbhp-lcadd-complete
  (implies (and (hbhp-lcadd-hyps)
                (hbhp-lcadd-canon u v0 v1 v01 x3 y3 p1 p2))
           (r1cs::r1cs-constraints-holdp
            (hbhp-lcadd-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p) asg p))
  :use (hbhp-lcadd-gadget-to-eqns
        (:instance crv-group-add-equations-complete)
        (:instance hbhp-add-comm (a p2) (b p1)))
  :in-theory '(hbhp-base-prime-facts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness of the randomizer fold on an accumulator held in wires.

(defmacro hbhp-step-canon (b pt x2 y2 st)
  `(hbhp-lcadd-canon (nth 0 ,st) (nth 1 ,st) (nth 2 ,st) (nth 3 ,st)
                     (nth 4 ,st) (nth 5 ,st)
                     (ecurve::edwards-bls12-mul (hbhp-lk ,b) ,pt)
                     (ecurve::point-finite (hbhp-lk ,x2) (hbhp-lk ,y2))))

(defruled hbhp-commit-step-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b) (bitp (hbhp-lk b))
                (ecurve::edwards-bls12-pointp pt)
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp x2) (hbhp-wire-okp y2)
                (equal (ecurve::point-finite (hbhp-lk x2) (hbhp-lk y2)) acc)
                (hbhp-wire-okp (nth 0 st)) (hbhp-wire-okp (nth 1 st))
                (hbhp-wire-okp (nth 2 st)) (hbhp-wire-okp (nth 3 st))
                (hbhp-wire-okp (nth 4 st)) (hbhp-wire-okp (nth 5 st))
                (hbhp-step-canon b pt x2 y2 st))
           (r1cs::r1cs-constraints-holdp
            (hbhp-commit-step-gadget b pt x2 y2 st p) asg p))
  :use (hbhp-tern-values
        hbhp-base-prime-facts
        (:instance hbhp-cadd-is-lcadd
                   (x1 (hbhp-tern-x b pt)) (y1 (hbhp-tern-y b pt p))
                   (u (nth 0 st)) (v0 (nth 1 st)) (v1 (nth 2 st))
                   (v01 (nth 3 st)) (x3 (nth 4 st)) (y3 (nth 5 st)))
        (:instance hbhp-lcadd-complete
                   (x1 (hbhp-tern-x b pt)) (y1 (hbhp-tern-y b pt p))
                   (x2 (list (list 1 x2))) (y2 (list (list 1 y2)))
                   (u (nth 0 st)) (v0 (nth 1 st)) (v1 (nth 2 st))
                   (v01 (nth 3 st)) (x3 (nth 4 st)) (y3 (nth 5 st))
                   (p1 (ecurve::edwards-bls12-mul (hbhp-lk b) pt)) (p2 acc))
        (:instance hbhp-dot-one-wire (w x2))
        (:instance hbhp-dot-one-wire (w y2))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x2)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y2)
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(hbhp-commit-step-gadget
               ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite
               pfield::fep nfix natp))

(define hbhp-commit-fold-canon (rbits sts rgen (i natp) x2 y2 asg)
  :verify-guards nil
  (if (endp rbits)
      t
    (b* ((p (base-prime)))
      (and (hbhp-step-canon (car rbits)
                            (ecurve::edwards-bls12-mul (expt 2 (lnfix i)) rgen)
                            x2 y2 (car sts))
           (hbhp-commit-fold-canon (cdr rbits) (cdr sts) rgen (1+ (lnfix i))
                                   (nth 4 (car sts)) (nth 5 (car sts)) asg)))))

(defruled hbhp-commit-fold-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp rgen)
                (natp i)
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp x2) (hbhp-wire-okp y2)
                (equal (ecurve::point-finite (hbhp-lk x2) (hbhp-lk y2)) acc)
                (hbhp-commit-fold-wires-okp rbits sts asg)
                (hbhp-commit-fold-canon rbits sts rgen i x2 y2 asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-commit-fold-gadget rbits sts rgen i x2 y2 p) asg p))
  :induct (hbhp-fold-induct rbits sts i x2 y2 acc rgen asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               (:induction hbhp-fold-induct) nfix lnfix natp endp)
  :hints (("Subgoal *1/2"
           :expand ((:free (x2 y2 p i)
                     (hbhp-commit-fold-gadget rbits sts rgen i x2 y2 p))
                    (:free (x2 y2 i) (hbhp-commit-fold-canon rbits sts rgen i x2 y2 asg))
                    (hbhp-commit-fold-wires-okp rbits sts asg))
           :use ((:instance hbhp-commit-step-complete
                            (b (car rbits))
                            (pt (ecurve::edwards-bls12-mul (expt 2 i) rgen))
                            (st (car sts)))
                 (:instance hbhp-commit-step-sound
                            (b (car rbits))
                            (pt (ecurve::edwards-bls12-mul (expt 2 i) rgen))
                            (st (car sts)))
                 (:instance hbhp-cu-fold-acc-pointp
                            (b (hbhp-lk (car rbits))) (i i))))
          ("Subgoal *1/1"
           :expand ((:free (x2 y2 p i)
                     (hbhp-commit-fold-gadget rbits sts rgen i x2 y2 p)))
           :use (hbhp-cu-holdp-nil)))
  :prep-lemmas
  ((defruled hbhp-cu-holdp-nil
     (r1cs::r1cs-constraints-holdp nil asg p)
     :enable r1cs::r1cs-constraints-holdp)
   (defruled hbhp-cu-fold-acc-pointp
     (implies (and (bitp b) (natp i)
                   (ecurve::edwards-bls12-pointp rgen)
                   (ecurve::edwards-bls12-pointp acc))
              (and (ecurve::edwards-bls12-pointp
                    (ecurve::edwards-bls12-mul (expt 2 i) rgen))
                   (ecurve::edwards-bls12-pointp
                    (ecurve::edwards-bls12-add
                     acc (ecurve::edwards-bls12-mul
                          b (ecurve::edwards-bls12-mul (expt 2 i) rgen))))
                   (equal (ecurve::edwards-bls12-mul
                           b (ecurve::edwards-bls12-mul (expt 2 i) rgen))
                          (ecurve::edwards-bls12-mul (* b (expt 2 i)) rgen))))
     :use ((:instance hbhp-mul-bit (e (expt 2 i)) (r rgen)))
     :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fold on the constant zero (empty input): zero + T0 = T0 is returned
;; as is, T0 + T1 has T1 as `this' and T0 as `that', both linear
;; combinations; then the fold continues at bit 2 on wires.

(defmacro hbhp-c0-st () '(car sts))

(define hbhp-commit0-fold-gadget (rbits sts rgen (p posp))
  :verify-guards nil
  (b* ((b0 (car rbits)) (b1 (cadr rbits))
       (p0 (ecurve::edwards-bls12-mul 1 rgen))
       (p1 (ecurve::edwards-bls12-mul 2 rgen)))
    (append (hbhp-lcadd-gadget (hbhp-tern-x b1 p1) (hbhp-tern-y b1 p1 p)
                               (hbhp-tern-x b0 p0) (hbhp-tern-y b0 p0 p)
                               (nth 0 (hbhp-c0-st)) (nth 1 (hbhp-c0-st))
                               (nth 2 (hbhp-c0-st)) (nth 3 (hbhp-c0-st))
                               (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st)) p)
            (hbhp-commit-fold-gadget (cddr rbits) (cdr sts) rgen 2
                                     (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st)) p))))

(define hbhp-commit0-fold-out (rbits sts)
  :verify-guards nil
  (hbhp-commit-fold-out (cddr rbits) (cdr sts)
                        (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st))))

(define hbhp-commit0-fold-wires-okp (rbits sts asg)
  :verify-guards nil
  (and (consp rbits) (consp (cdr rbits))
       (hbhp-wire-okp (car rbits)) (bitp (hbhp-lk (car rbits)))
       (hbhp-wire-okp (cadr rbits)) (bitp (hbhp-lk (cadr rbits)))
       (hbhp-wire-okp (nth 0 (hbhp-c0-st))) (hbhp-wire-okp (nth 1 (hbhp-c0-st)))
       (hbhp-wire-okp (nth 2 (hbhp-c0-st))) (hbhp-wire-okp (nth 3 (hbhp-c0-st)))
       (hbhp-wire-okp (nth 4 (hbhp-c0-st))) (hbhp-wire-okp (nth 5 (hbhp-c0-st)))
       (hbhp-commit-fold-wires-okp (cddr rbits) (cdr sts) asg)))

(define hbhp-commit0-fold-canon (rbits sts rgen asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (t0 (ecurve::edwards-bls12-mul (hbhp-lk (car rbits))
                                      (ecurve::edwards-bls12-mul 1 rgen)))
       (t1 (ecurve::edwards-bls12-mul (hbhp-lk (cadr rbits))
                                      (ecurve::edwards-bls12-mul 2 rgen))))
    (and (hbhp-lcadd-canon (nth 0 (hbhp-c0-st)) (nth 1 (hbhp-c0-st))
                           (nth 2 (hbhp-c0-st)) (nth 3 (hbhp-c0-st))
                           (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st)) t1 t0)
         (hbhp-commit-fold-canon (cddr rbits) (cdr sts) rgen 2
                                 (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st)) asg))))

(defmacro hbhp-c0-t0 ()
  '(ecurve::edwards-bls12-mul (hbhp-lk (car rbits)) (ecurve::edwards-bls12-mul 1 rgen)))
(defmacro hbhp-c0-t1 ()
  '(ecurve::edwards-bls12-mul (hbhp-lk (cadr rbits)) (ecurve::edwards-bls12-mul 2 rgen)))

(defruled hbhp-c0-first-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp rgen)
                (hbhp-commit0-fold-wires-okp rbits sts asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-commit0-fold-gadget rbits sts rgen p) asg p))
           (and (equal (ecurve::point-finite (hbhp-lk (nth 4 (hbhp-c0-st)))
                                             (hbhp-lk (nth 5 (hbhp-c0-st))))
                       (ecurve::edwards-bls12-mul
                        (+ (hbhp-lk (car rbits)) (* 2 (hbhp-lk (cadr rbits)))) rgen))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-commit-fold-gadget (cddr rbits) (cdr sts) rgen 2
                                          (nth 4 (hbhp-c0-st)) (nth 5 (hbhp-c0-st)) p)
                 asg p)))
  :use ((:instance hbhp-tern-values (b (car rbits)) (pt (ecurve::edwards-bls12-mul 1 rgen)))
        (:instance hbhp-tern-values (b (cadr rbits)) (pt (ecurve::edwards-bls12-mul 2 rgen)))
        (:instance hbhp-lcadd-sound
                   (x1 (hbhp-tern-x (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen)))
                   (y1 (hbhp-tern-y (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen) p))
                   (x2 (hbhp-tern-x (car rbits) (ecurve::edwards-bls12-mul 1 rgen)))
                   (y2 (hbhp-tern-y (car rbits) (ecurve::edwards-bls12-mul 1 rgen) p))
                   (u (nth 0 (hbhp-c0-st))) (v0 (nth 1 (hbhp-c0-st)))
                   (v1 (nth 2 (hbhp-c0-st))) (v01 (nth 3 (hbhp-c0-st)))
                   (x3 (nth 4 (hbhp-c0-st))) (y3 (nth 5 (hbhp-c0-st)))
                   (p1 (hbhp-c0-t1)) (p2 (hbhp-c0-t0)))
        (:instance hbhp-mul-bit (b (hbhp-lk (car rbits))) (e 1) (r rgen))
        (:instance hbhp-mul-bit (b (hbhp-lk (cadr rbits))) (e 2) (r rgen))
        (:instance hbhp-g-mul-add (g rgen) (m (* (hbhp-lk (car rbits)) 1))
                   (n (* (hbhp-lk (cadr rbits)) 2)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar 1) (point rgen))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar 2) (point rgen)))
  :in-theory '(hbhp-commit0-fold-gadget hbhp-commit0-fold-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               bitp ifix (:e binary-*) (:e binary-+) (:e natp) (:e ifix)
               commutativity-of-* unicity-of-1)
  :do-not-induct t)

(defruledl hbhp-cu-rscalar-int
  (implies (natp i) (integerp (hbhp-rscalar rbits i asg)))
  :induct (hbhp-rscalar rbits i asg)
  :enable hbhp-rscalar
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))

(defruledl hbhp-cu-rscalar-first-two
  (implies (and (consp rbits) (consp (cdr rbits))
                (bitp (hbhp-lk (car rbits))) (bitp (hbhp-lk (cadr rbits))))
           (equal (hbhp-rscalar rbits 0 asg)
                  (+ (hbhp-lk (car rbits)) (* 2 (hbhp-lk (cadr rbits)))
                     (hbhp-rscalar (cddr rbits) 2 asg))))
  :expand ((hbhp-rscalar rbits 0 asg) (hbhp-rscalar (cdr rbits) 1 asg))
  :enable (bitp))

(defruledl hbhp-cu-plus-consts
  (implies (and (syntaxp (quotep a)) (syntaxp (quotep b)))
           (equal (+ a (+ b x)) (+ (+ a b) x))))

(defruled hbhp-commit0-fold-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp rgen)
                (hbhp-commit0-fold-wires-okp rbits sts asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-commit0-fold-gadget rbits sts rgen p) asg p))
           (b* ((out (hbhp-commit0-fold-out rbits sts)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (ecurve::edwards-bls12-mul (hbhp-rscalar rbits 0 asg) rgen))))
  :use (hbhp-c0-first-sound
        hbhp-cu-rscalar-first-two
        (:instance hbhp-commit-fold-sound
                   (rbits (cddr rbits)) (sts (cdr sts)) (i 2)
                   (x2 (nth 4 (hbhp-c0-st))) (y2 (nth 5 (hbhp-c0-st)))
                   (acc (ecurve::edwards-bls12-mul
                         (+ (hbhp-lk (car rbits)) (* 2 (hbhp-lk (cadr rbits)))) rgen)))
        (:instance hbhp-g-mul-add (g rgen)
                   (m (+ (hbhp-lk (car rbits)) (* 2 (hbhp-lk (cadr rbits)))))
                   (n (hbhp-rscalar (cddr rbits) 2 asg)))
        (:instance hbhp-cu-rscalar-int (rbits (cddr rbits)) (i 2))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (+ (hbhp-lk (car rbits)) (* 2 (hbhp-lk (cadr rbits)))))
                   (point rgen)))
  :in-theory '(hbhp-commit0-fold-out hbhp-commit0-fold-wires-okp
               bitp ifix (:e natp) (:e binary-*) (:e binary-+) (:e integerp)
               commutativity-of-+ associativity-of-+ unicity-of-0 fix
               hbhp-cu-plus-consts)
  :do-not-induct t)

(defruled hbhp-commit0-fold-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp rgen)
                (hbhp-commit0-fold-wires-okp rbits sts asg)
                (hbhp-commit0-fold-canon rbits sts rgen asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-commit0-fold-gadget rbits sts rgen p) asg p))
  :use ((:instance hbhp-tern-values (b (car rbits)) (pt (ecurve::edwards-bls12-mul 1 rgen)))
        (:instance hbhp-tern-values (b (cadr rbits)) (pt (ecurve::edwards-bls12-mul 2 rgen)))
        (:instance hbhp-lcadd-complete
                   (x1 (hbhp-tern-x (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen)))
                   (y1 (hbhp-tern-y (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen) p))
                   (x2 (hbhp-tern-x (car rbits) (ecurve::edwards-bls12-mul 1 rgen)))
                   (y2 (hbhp-tern-y (car rbits) (ecurve::edwards-bls12-mul 1 rgen) p))
                   (u (nth 0 (hbhp-c0-st))) (v0 (nth 1 (hbhp-c0-st)))
                   (v1 (nth 2 (hbhp-c0-st))) (v01 (nth 3 (hbhp-c0-st)))
                   (x3 (nth 4 (hbhp-c0-st))) (y3 (nth 5 (hbhp-c0-st)))
                   (p1 (hbhp-c0-t1)) (p2 (hbhp-c0-t0)))
        (:instance hbhp-lcadd-sound
                   (x1 (hbhp-tern-x (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen)))
                   (y1 (hbhp-tern-y (cadr rbits) (ecurve::edwards-bls12-mul 2 rgen) p))
                   (x2 (hbhp-tern-x (car rbits) (ecurve::edwards-bls12-mul 1 rgen)))
                   (y2 (hbhp-tern-y (car rbits) (ecurve::edwards-bls12-mul 1 rgen) p))
                   (u (nth 0 (hbhp-c0-st))) (v0 (nth 1 (hbhp-c0-st)))
                   (v1 (nth 2 (hbhp-c0-st))) (v01 (nth 3 (hbhp-c0-st)))
                   (x3 (nth 4 (hbhp-c0-st))) (y3 (nth 5 (hbhp-c0-st)))
                   (p1 (hbhp-c0-t1)) (p2 (hbhp-c0-t0)))
        (:instance hbhp-commit-fold-complete
                   (rbits (cddr rbits)) (sts (cdr sts)) (i 2)
                   (x2 (nth 4 (hbhp-c0-st))) (y2 (nth 5 (hbhp-c0-st)))
                   (acc (ecurve::edwards-bls12-add (hbhp-c0-t0) (hbhp-c0-t1))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (hbhp-c0-t0)) (ecurve::point2 (hbhp-c0-t1)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar 1) (point rgen))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar 2) (point rgen)))
  :in-theory '(hbhp-commit0-fold-gadget hbhp-commit0-fold-wires-okp
               hbhp-commit0-fold-canon
               r1cs::r1cs-constraints-holdp-of-append (:e natp))
  :do-not-induct t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHP::commit_uncompressed.  s is the randomizer wire, rbits and rs the
;; wires of its Scalar::to_bits_le, sts the wires of the adds.

(defmacro hbhp-cu-hout () '(hbhp-hu-out cbits vb wins0 its gens w m c max))

(define hbhp-cu-gadget (cbits vb wins0 its gens (w posp) m c (max posp) u
                        s rbits rs sts rgen (p posp))
  :verify-guards nil
  (append (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p)
          (scalar-write-bits-le-gadget s rbits rs p)
          (if (consp vb)
              (hbhp-commit-fold-gadget rbits sts rgen 0
                                       (car (hbhp-cu-hout)) (cdr (hbhp-cu-hout)) p)
            (hbhp-commit0-fold-gadget rbits sts rgen p))))

(define hbhp-cu-out (cbits vb wins0 its gens (w posp) m c (max posp) rbits sts)
  :verify-guards nil
  (if (consp vb)
      (hbhp-commit-fold-out rbits sts (car (hbhp-cu-hout)) (cdr (hbhp-cu-hout)))
    (hbhp-commit0-fold-out rbits sts)))

;; As for the digest bits, the booleanity of the randomizer bit wires in
;; the fold's wire conditions is enforced by Scalar::to_bits_le.

(define hbhp-cu-wires-okp (cbits vb wins0 its gens (w posp) m c (max posp)
                           s rbits rs sts asg)
  :verify-guards nil
  (and (symbolp s) (r1cs::valuation-bindsp asg s)
       (symbol-listp rbits) (equal (len rbits) 251)
       (symbol-listp rs) (equal (len rs) 250)
       (r1cs::valuation-binds-allp asg rbits)
       (r1cs::valuation-binds-allp asg rs)
       (if (consp vb)
           (and (hbhp-hu-wires-okp cbits vb wins0 its gens w m c max asg)
                (hbhp-wire-okp (car (hbhp-cu-hout)))
                (hbhp-wire-okp (cdr (hbhp-cu-hout)))
                (implies (bit-listp (lookup-equal-list rbits asg))
                         (hbhp-commit-fold-wires-okp rbits sts asg)))
         (implies (bit-listp (lookup-equal-list rbits asg))
                  (hbhp-commit0-fold-wires-okp rbits sts asg)))))

(define hbhp-cu-canon (cbits vb wins0 its gens (w posp) m c (max posp)
                       s rbits rs sts rgen asg)
  :verify-guards nil
  (and (scalarp (lookup-equal s asg))
       (equal (lookup-equal-list rbits asg) (scalar-bits-le (lookup-equal s asg)))
       (equal (lookup-equal-list rs asg)
              (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                          (scalar-modulus-minus-one-bits)))
       (if (consp vb)
           (and (hbhp-hu-canon cbits vb wins0 its gens w m c max asg)
                (hbhp-commit-fold-canon rbits sts rgen 0 (car (hbhp-cu-hout))
                                        (cdr (hbhp-cu-hout)) asg))
         (hbhp-commit0-fold-canon rbits sts rgen asg))))

(defmacro hbhp-bhp-cu-hyps ()
  '(and (hbhp-sizep size)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal w (hbhp-size-window-size size))
        (equal gens (hbhp-setup-gens size))
        (equal domain (hbhp-size-domain size))
        (equal rgen (hbhp-setup-random-base size))
        (equal m (floor 84 w))
        (equal c (mod 84 w))
        (equal cbits (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)
        (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)))

(defruledl hbhp-cu-rgen-pointp
  (ecurve::edwards-bls12-pointp (hbhp-setup-random-base size))
  :use ((:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (hbhp-setup-random-base size)))
        hbhp-r-pointp-of-setup-random-base)
  :in-theory nil)

(defruled hbhp-cu-scalar-facts
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)
                (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget s rbits rs p) asg p))
           (and (bit-listp (lookup-equal-list rbits asg))
                (equal (hbhp-rscalar rbits 0 asg) (lookup-equal s asg))
                (natp (lookup-equal s asg))))
  :use ((:instance scalar-write-bits-le-gadget-sound (xs rbits) (acc nil))
        (:instance hbhp-rscalar-is-lebits (i 0))
        (:instance hbhp-hu-lk-list-is-lookup-equal-list (bs rbits)))
  :in-theory '(hbhp-cu-wires-okp scalarp pfield::fep (:e expt) (:e bit-listp) (:e natp)
               (:t acl2::lebits=>nat) hbhp-cu-times-1)
  :prep-lemmas
  ((defruled hbhp-cu-times-1
     (implies (acl2-numberp x) (equal (* 1 x) x)))))

(defruledl hbhp-r-pointp-of-hash-uncompressed-ok
  (implies (and (hbhp-r-point-listp gens)
                (equal (hbhp-hash-uncompressed domain gens w bits)
                       (ecurve::point-finite x y)))
           (ecurve::edwards-bls12-pointp (hbhp-hash-uncompressed domain gens w bits)))
  :use ((:instance hbhp-hash-uncompressed-type)
        (:instance hbhp-hu-not-reserrp-point)
        (:instance hbhp-r-pointp-when-okresp
                   (x (hbhp-hash-uncompressed domain gens w bits)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (hbhp-hash-uncompressed domain gens w bits))))
  :in-theory nil)

(defruled hbhp-bhp-cu-sound-nonempty
  (implies (and (hbhp-bhp-cu-hyps)
                (consp vb)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                 asg p))
           (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-bhp-commit-uncompressed size (hbhp-lk-list vb asg)
                                                  (lookup-equal s asg)))))
  :use (hbhp-hu-instance-params hbhp-hu-sound hbhp-cu-scalar-facts
        (:instance hbhp-cu-rgen-pointp)
        (:instance hbhp-commit-fold-sound
                   (i 0) (x2 (car (hbhp-cu-hout))) (y2 (cdr (hbhp-cu-hout)))
                   (acc (hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg))))
        (:instance hbhp-r-pointp-of-hash-uncompressed-ok
                   (bits (hbhp-lk-list vb asg))
                   (x (hbhp-lk (car (hbhp-cu-hout)))) (y (hbhp-lk (cdr (hbhp-cu-hout)))))
        (:instance hbhp-r-point-listp-of-setup-gens)
        (:instance hbhp-hu-not-reserrp-point
                   (x (hbhp-lk (car (hbhp-cu-hout)))) (y (hbhp-lk (cdr (hbhp-cu-hout)))))
        (:instance hbhp-hu-not-reserrp-point
                   (x (hbhp-lk (car (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))
                   (y (hbhp-lk (cdr (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))))
  :in-theory '(hbhp-cu-gadget hbhp-cu-out hbhp-cu-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-bhp-commit-uncompressed hbhp-commit-uncompressed nfix
               (:e natp) natp acl2::lnfix$inline)
  :do-not-induct t)

(defruled hbhp-bhp-cu-sound-empty
  (implies (and (hbhp-bhp-cu-hyps)
                (not (consp vb))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                 asg p))
           (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-bhp-commit-uncompressed size (hbhp-lk-list vb asg)
                                                  (lookup-equal s asg)))))
  :use (hbhp-hu-instance-params hbhp-hu-empty hbhp-cu-scalar-facts
        (:instance hbhp-cu-rgen-pointp)
        (:instance hbhp-commit0-fold-sound)
        (:instance hbhp-add-zero-left
                   (pt (ecurve::edwards-bls12-mul (lookup-equal s asg) rgen)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (lookup-equal s asg)) (point rgen))
        (:instance hbhp-hu-not-reserrp-point
                   (x (hbhp-lk (car (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))
                   (y (hbhp-lk (cdr (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))))
  :in-theory '(hbhp-cu-gadget hbhp-cu-out hbhp-cu-wires-okp
               r1cs::r1cs-constraints-holdp-of-append append
               hbhp-bhp-commit-uncompressed hbhp-commit-uncompressed nfix
               (:e natp) natp acl2::lnfix$inline (:e reserrp)
               (:e ecurve::twisted-edwards-zero))
  :do-not-induct t)

(defruled hbhp-bhp-cu-sound
  (implies (and (hbhp-bhp-cu-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                 asg p))
           (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-bhp-commit-uncompressed size (hbhp-lk-list vb asg)
                                                  (lookup-equal s asg)))))
  :use (hbhp-bhp-cu-sound-nonempty hbhp-bhp-cu-sound-empty)
  :in-theory nil)

(defruled hbhp-bhp-cu-complete-nonempty
  (implies (and (hbhp-bhp-cu-hyps)
                (consp vb)
                (hbhp-cu-canon cbits vb wins0 its gens w m c max s rbits rs sts rgen asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
            asg p))
  :use (hbhp-hu-instance-params hbhp-bhp-hu-complete hbhp-hu-sound
        (:instance hbhp-cu-rgen-pointp)
        (:instance scalar-write-bits-le-gadget-complete (xs rbits) (acc nil))
        (:instance bit-listp-of-scalar-bits-le (a (lookup-equal s asg)))
        (:instance hbhp-commit-fold-complete
                   (i 0) (x2 (car (hbhp-cu-hout))) (y2 (cdr (hbhp-cu-hout)))
                   (acc (hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg))))
        (:instance hbhp-r-pointp-of-hash-uncompressed-ok
                   (bits (hbhp-lk-list vb asg))
                   (x (hbhp-lk (car (hbhp-cu-hout)))) (y (hbhp-lk (cdr (hbhp-cu-hout)))))
        (:instance hbhp-r-point-listp-of-setup-gens))
  :in-theory '(hbhp-cu-gadget hbhp-cu-wires-okp hbhp-cu-canon
               r1cs::r1cs-constraints-holdp-of-append (:e natp))
  :do-not-induct t)

(defruledl hbhp-cu-holdp-of-nil
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(defruled hbhp-bhp-cu-complete-empty
  (implies (and (hbhp-bhp-cu-hyps)
                (not (consp vb))
                (hbhp-cu-canon cbits vb wins0 its gens w m c max s rbits rs sts rgen asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
            asg p))
  :use (hbhp-hu-instance-params hbhp-hu-empty
        (:instance hbhp-cu-rgen-pointp)
        (:instance scalar-write-bits-le-gadget-complete (xs rbits) (acc nil))
        (:instance bit-listp-of-scalar-bits-le (a (lookup-equal s asg)))
        (:instance hbhp-commit0-fold-complete))
  :in-theory '(hbhp-cu-gadget hbhp-cu-wires-okp hbhp-cu-canon
               r1cs::r1cs-constraints-holdp-of-append append
               hbhp-cu-holdp-of-nil)
  :do-not-induct t)

(defruled hbhp-bhp-cu-complete
  (implies (and (hbhp-bhp-cu-hyps)
                (hbhp-cu-canon cbits vb wins0 its gens w m c max s rbits rs sts rgen asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
            asg p))
  :use (hbhp-bhp-cu-complete-nonempty hbhp-bhp-cu-complete-empty)
  :in-theory nil)

;; BHP::commit is commit_uncompressed followed by to_x_coordinate, which
;; emits no constraints: the output is the x wire of commit_uncompressed.

(defruled hbhp-bhp-commit-sound
  (implies (and (hbhp-bhp-cu-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                 asg p))
           (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts)))
             (equal (nfix (hbhp-lk (car out)))
                    (hbhp-bhp-commit size (hbhp-lk-list vb asg) (lookup-equal s asg)))))
  :use (hbhp-bhp-cu-sound
        (:instance ecurve::point-finite->x-of-point-finite
                   (ecurve::x (hbhp-lk (car (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))
                   (ecurve::y (hbhp-lk (cdr (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))))))
  :in-theory '(hbhp-bhp-commit)
  :do-not-induct t)
