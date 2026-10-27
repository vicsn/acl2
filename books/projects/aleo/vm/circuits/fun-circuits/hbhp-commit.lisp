; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The randomizer tail of BHP::commit_uncompressed:
;
;   randomizer.to_bits_le().iter().zip_eq(random_base)
;     .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
;     .fold(hash, |acc, x| acc + x)
;
; The powers 2^i R are constants, so each ternary is constraint-free:
; x = b px and y = b py + (1 - b), as linear combinations.  The ternary
; point is not constant, so Group::add swaps it into `this' and the
; accumulator is `that'; the six constraints are those of the
; variable/variable add, with the coordinates of `this' as linear
; combinations.
;
; Soundness: for Boolean randomizer bit wires and a starting accumulator
; holding the point H, the output is H + (sum_i b_i 2^i) R.  The bit wires
; are those produced by Scalar::to_bits_le (not modelled here).

(in-package "ALEOVM")

(include-book "hbhp-hasher")

(local (include-book "../edwards-assoc/edwards-bls12-associativity"))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group facts.

(defruled hbhp-add-assoc
  (implies (and (ecurve::edwards-bls12-pointp a)
                (ecurve::edwards-bls12-pointp b)
                (ecurve::edwards-bls12-pointp c))
           (equal (ecurve::edwards-bls12-add (ecurve::edwards-bls12-add a b) c)
                  (ecurve::edwards-bls12-add a (ecurve::edwards-bls12-add b c))))
  :use (ecurve::twisted-edwards-add-associativity-holds
        (:instance ecurve::twisted-edwards-add-associative-right
                   (ecurve::point1 a) (ecurve::point2 b) (ecurve::point3 c)
                   (ecurve::curve (ecurve::edwards-bls12-curve))))
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-pointp)
  :disable (ecurve::twisted-edwards-add-associative-right))

(defruled hbhp-mul-0
  (equal (ecurve::edwards-bls12-mul 0 b) (ecurve::twisted-edwards-zero))
  :enable ecurve::edwards-bls12-mul)

(defruled hbhp-mul-1
  (implies (ecurve::edwards-bls12-pointp b)
           (equal (ecurve::edwards-bls12-mul 1 b) b))
  :enable (ecurve::edwards-bls12-mul ecurve::edwards-bls12-pointp))

(defruled hbhp-zero-pointp
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group::add with `this' given by linear combinations.

(define hbhp-cadd-gadget (x1 y1 (x2 symbolp) (y2 symbolp)
                          (u symbolp) (v0 symbolp) (v1 symbolp) (v01 symbolp)
                          (x3 symbolp) (y3 symbolp) (p posp))
  :verify-guards nil
  (b* ((d (ecurve::edwards-bls12-d)))
    (list (r1cs::make-r1cs-constraint
           :a (append x1 y1)
           :b (list (list 1 x2) (list 1 y2))
           :c (list (list 1 u)))
          (r1cs::make-r1cs-constraint
           :a x1
           :b (list (list 1 y2))
           :c (list (list 1 v0)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 x2))
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

(defruled hbhp-cadd-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp x2) (hbhp-wire-okp y2)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3))
           (b* ((x1$ (hbhp-dot x1)) (y1$ (hbhp-dot y1))
                (x2$ (hbhp-lk x2)) (y2$ (hbhp-lk y2))
                (u$ (hbhp-lk u)) (v0$ (hbhp-lk v0)) (v1$ (hbhp-lk v1))
                (v01$ (hbhp-lk v01)) (x3$ (hbhp-lk x3)) (y3$ (hbhp-lk y3))
                (d (ecurve::edwards-bls12-d)))
             (equal (r1cs::r1cs-constraints-holdp
                     (hbhp-cadd-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p) asg p)
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
  :enable (hbhp-cadd-gadget r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           hbhp-dot-cons hbhp-dot-nil r1cs::dot-product-of-append
           pfield::sub)
  :disable (r1cs::dot-product)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One randomizer bit: acc + ternary(b, P, zero), P constant.

(define hbhp-tern-x ((b symbolp) pt)
  :verify-guards nil
  (list (list (ecurve::point-finite->x pt) b)))

(define hbhp-tern-y ((b symbolp) pt (p posp))
  :verify-guards nil
  (list (list 1 1) (list (pfield::sub (ecurve::point-finite->y pt) 1 p) b)))

(define hbhp-commit-step-gadget ((b symbolp) pt (x2 symbolp) (y2 symbolp) st
                                 (p posp))
  :verify-guards nil
  :short "Wires of @('st'): (u v0 v1 v01 x3 y3)."
  (hbhp-cadd-gadget (hbhp-tern-x b pt) (hbhp-tern-y b pt p) x2 y2
                    (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st)
                    (nth 4 st) (nth 5 st) p))

(defruled hbhp-tern-values
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b) (bitp (hbhp-lk b))
                (ecurve::edwards-bls12-pointp pt))
           (b* ((tp (ecurve::edwards-bls12-mul (hbhp-lk b) pt)))
             (and (ecurve::edwards-bls12-pointp tp)
                  (equal (hbhp-dot (hbhp-tern-x b pt)) (ecurve::point-finite->x tp))
                  (equal (hbhp-dot (hbhp-tern-y b pt p)) (ecurve::point-finite->y tp)))))
  :use (hbhp-base-prime-facts
        (:instance hbhp-mul-0 (b pt))
        (:instance hbhp-mul-1 (b pt))
        hbhp-zero-pointp)
  :cases ((equal (hbhp-lk b) 0) (equal (hbhp-lk b) 1))
  :enable (hbhp-tern-x hbhp-tern-y hbhp-dot-cons hbhp-dot-nil bitp
           (:e ecurve::twisted-edwards-zero) hbhp-add-1-sub-1
           crv-fep-of-edwards-bls12-coords)
  :prep-lemmas
  ((defruled hbhp-add-1-sub-1
     (implies (and (pfield::fep y p) (primep p))
              (equal (pfield::add 1 (pfield::add (+ -1 p) y p) p) y))
     :enable (pfield::sub pfield::add pfield::neg pfield::fep)
     :prep-books ((include-book "arithmetic-5/top" :dir :system))))
  :disable (ecurve::edwards-bls12-mul r1cs::dot-product))

(defruled hbhp-commit-step-sound
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
                (r1cs::r1cs-constraints-holdp
                 (hbhp-commit-step-gadget b pt x2 y2 st p) asg p))
           (equal (ecurve::point-finite (hbhp-lk (nth 4 st)) (hbhp-lk (nth 5 st)))
                  (ecurve::edwards-bls12-add
                   acc (ecurve::edwards-bls12-mul (hbhp-lk b) pt))))
  :use (hbhp-tern-values
        (:instance hbhp-cadd-gadget-to-eqns
                   (x1 (hbhp-tern-x b pt)) (y1 (hbhp-tern-y b pt p))
                   (u (nth 0 st)) (v0 (nth 1 st)) (v1 (nth 2 st))
                   (v01 (nth 3 st)) (x3 (nth 4 st)) (y3 (nth 5 st)))
        (:instance crv-group-add-from-equations
                   (p1 (ecurve::edwards-bls12-mul (hbhp-lk b) pt))
                   (p2 acc)
                   (x1 (hbhp-dot (hbhp-tern-x b pt)))
                   (y1 (hbhp-dot (hbhp-tern-y b pt p)))
                   (x2 (hbhp-lk x2)) (y2 (hbhp-lk y2))
                   (u (hbhp-lk (nth 0 st))) (v0 (hbhp-lk (nth 1 st)))
                   (v1 (hbhp-lk (nth 2 st))) (v01 (hbhp-lk (nth 3 st)))
                   (x3 (hbhp-lk (nth 4 st))) (y3 (hbhp-lk (nth 5 st))))
        (:instance hbhp-add-comm
                   (a acc) (b (ecurve::edwards-bls12-mul (hbhp-lk b) pt)))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 4 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 5 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x2)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y2)
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(hbhp-commit-step-gadget hbhp-base-prime-facts
               ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite
               pfield::fep nfix natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fold over the randomizer bits, little-endian, power 2^i R at bit i.

(define hbhp-commit-fold-gadget (rbits sts rgen (i natp) x2 y2 (p posp))
  :verify-guards nil
  (if (endp rbits)
      nil
    (append (hbhp-commit-step-gadget (car rbits)
                                     (ecurve::edwards-bls12-mul (expt 2 (lnfix i)) rgen)
                                     x2 y2 (car sts) p)
            (hbhp-commit-fold-gadget (cdr rbits) (cdr sts) rgen (1+ (lnfix i))
                                     (nth 4 (car sts)) (nth 5 (car sts)) p))))

(define hbhp-commit-fold-out (rbits sts x2 y2)
  :verify-guards nil
  (if (endp rbits)
      (cons x2 y2)
    (hbhp-commit-fold-out (cdr rbits) (cdr sts)
                          (nth 4 (car sts)) (nth 5 (car sts)))))

(define hbhp-commit-fold-wires-okp (rbits sts asg)
  :verify-guards nil
  (if (endp rbits)
      t
    (b* ((st (car sts)))
      (and (hbhp-wire-okp (car rbits)) (bitp (hbhp-lk (car rbits)))
           (hbhp-wire-okp (nth 0 st)) (hbhp-wire-okp (nth 1 st))
           (hbhp-wire-okp (nth 2 st)) (hbhp-wire-okp (nth 3 st))
           (hbhp-wire-okp (nth 4 st)) (hbhp-wire-okp (nth 5 st))
           (hbhp-commit-fold-wires-okp (cdr rbits) (cdr sts) asg)))))

(define hbhp-rscalar (rbits (i natp) asg)
  :verify-guards nil
  (if (endp rbits)
      0
    (+ (* (acl2::bfix (hbhp-lk (car rbits))) (expt 2 (lnfix i)))
       (hbhp-rscalar (cdr rbits) (1+ (lnfix i)) asg))))

(defruled hbhp-mul-bit
  (implies (and (bitp b) (ecurve::edwards-bls12-pointp r) (natp e))
           (equal (ecurve::edwards-bls12-mul b (ecurve::edwards-bls12-mul e r))
                  (ecurve::edwards-bls12-mul (* b e) r)))
  :cases ((equal b 0) (equal b 1))
  :use ((:instance hbhp-mul-0 (b (ecurve::edwards-bls12-mul e r)))
        (:instance hbhp-mul-0 (b r))
        (:instance hbhp-mul-1 (b (ecurve::edwards-bls12-mul e r)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar e) (point r)))
  :in-theory '(bitp (:t ecurve::edwards-bls12-mul) (:e binary-*) hbhp-times-0
               hbhp-times-1 natp)
  :prep-lemmas
  ((defruled hbhp-times-0 (equal (* 0 x) 0))
   (defruled hbhp-times-1 (implies (natp x) (equal (* 1 x) x)))))

(defruled hbhp-add-zero-right
  (implies (ecurve::edwards-bls12-pointp pt)
           (equal (ecurve::edwards-bls12-add pt (ecurve::twisted-edwards-zero))
                  pt))
  :use (hbhp-add-zero-left
        (:instance hbhp-add-comm (a pt) (b (ecurve::twisted-edwards-zero)))))

(defun hbhp-fold-induct (rbits sts i x2 y2 acc rgen asg)
  (declare (xargs :verify-guards nil))
  (if (endp rbits)
      (list sts i x2 y2 acc rgen asg)
    (hbhp-fold-induct (cdr rbits) (cdr sts) (1+ (nfix i))
                      (nth 4 (car sts)) (nth 5 (car sts))
                      (ecurve::edwards-bls12-add
                       acc (ecurve::edwards-bls12-mul
                            (* (hbhp-lk (car rbits)) (expt 2 (nfix i))) rgen))
                      rgen asg)))

(defruled hbhp-commit-fold-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp rgen)
                (natp i)
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp x2) (hbhp-wire-okp y2)
                (equal (ecurve::point-finite (hbhp-lk x2) (hbhp-lk y2)) acc)
                (hbhp-commit-fold-wires-okp rbits sts asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-commit-fold-gadget rbits sts rgen i x2 y2 p) asg p))
           (b* ((out (hbhp-commit-fold-out rbits sts x2 y2)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (ecurve::edwards-bls12-add
                     acc (ecurve::edwards-bls12-mul (hbhp-rscalar rbits i asg)
                                                    rgen)))))
  :induct (hbhp-fold-induct rbits sts i x2 y2 acc rgen asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               (:induction hbhp-fold-induct) nfix lnfix natp endp
               hbhp-bfix-bit ifix car-cons cdr-cons)
  :hints (("Subgoal *1/2"
           :expand ((:free (x2 y2 p i)
                     (hbhp-commit-fold-gadget rbits sts rgen i x2 y2 p))
                    (:free (x2 y2) (hbhp-commit-fold-out rbits sts x2 y2))
                    (hbhp-commit-fold-wires-okp rbits sts asg)
                    (:free (i) (hbhp-rscalar rbits i asg)))
           :use ((:instance hbhp-commit-step-sound
                            (b (car rbits))
                            (pt (ecurve::edwards-bls12-mul (expt 2 i) rgen))
                            (st (car sts)))
                 (:instance hbhp-mul-bit (b (hbhp-lk (car rbits)))
                            (e (expt 2 i)) (r rgen))
                 (:instance hbhp-add-assoc
                            (a acc)
                            (b (ecurve::edwards-bls12-mul
                                (* (hbhp-lk (car rbits)) (expt 2 i)) rgen))
                            (c (ecurve::edwards-bls12-mul
                                (hbhp-rscalar (cdr rbits) (+ 1 i) asg) rgen)))
                 (:instance hbhp-g-mul-add (g rgen)
                            (m (* (hbhp-lk (car rbits)) (expt 2 i)))
                            (n (hbhp-rscalar (cdr rbits) (+ 1 i) asg)))
                 (:instance hbhp-rscalar-int (rbits (cdr rbits)) (i (+ 1 i)))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar (expt 2 i)) (point rgen))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar (* (hbhp-lk (car rbits)) (expt 2 i)))
                            (point rgen))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar (hbhp-rscalar (cdr rbits) (+ 1 i) asg))
                            (point rgen))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                            (ecurve::point1 acc)
                            (ecurve::point2
                             (ecurve::edwards-bls12-mul
                              (* (hbhp-lk (car rbits)) (expt 2 i)) rgen)))
                 (:instance hbhp-bit-times-expt (b (hbhp-lk (car rbits))))))
          ("Subgoal *1/1"
           :expand ((:free (x2 y2) (hbhp-commit-fold-out rbits sts x2 y2))
                    (:free (i) (hbhp-rscalar rbits i asg)))
           :use ((:instance hbhp-mul-0 (b rgen))
                 (:instance hbhp-add-zero-right (pt acc)))))
  :prep-lemmas
  ((defruled hbhp-bfix-bit
     (implies (bitp b) (equal (acl2::bfix b) b)))
   (defruled hbhp-rscalar-int
     (implies (natp i) (integerp (hbhp-rscalar rbits i asg)))
     :induct (hbhp-rscalar rbits i asg)
     :enable hbhp-rscalar
     :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))
   (defruled hbhp-bit-times-expt
     (implies (and (bitp b) (natp i))
              (and (natp (expt 2 i))
                   (integerp (* b (expt 2 i)))
                   (equal (ifix (* b (expt 2 i))) (* b (expt 2 i)))))
     :enable bitp)))

(defruled hbhp-rscalar-is-lebits
  (implies (natp i)
           (equal (hbhp-rscalar rbits i asg)
                  (* (expt 2 i) (acl2::lebits=>nat (hbhp-lk-list rbits asg)))))
  :induct (hbhp-rscalar rbits i asg)
  :enable (hbhp-rscalar hbhp-lk-list acl2::lendian=>nat-of-cons hbhp-digit-fix-2
           acl2::lebits=>nat)
  :prep-lemmas
  ((defruled hbhp-digit-fix-2
     (equal (acl2::dab-digit-fix 2 x) (acl2::bfix x))
     :enable (acl2::dab-digit-fix acl2::dab-digitp acl2::bfix)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHPHasher followed by the randomizer tail.

(define hbhp-hasher-commit-gadget (bits wins gens w rbits sts rgen (p posp))
  :verify-guards nil
  :short "@('commit_uncompressed') with @('hash_uncompressed') replaced by
          the BHPHasher on variable bits."
  (b* ((out (hbhp-hasher-out bits wins gens w)))
    (append (hbhp-hasher-gadget bits wins gens w p)
            (hbhp-commit-fold-gadget rbits sts rgen 0 (car out) (cdr out) p))))

(define hbhp-hasher-commit-out (bits wins gens w rbits sts)
  :verify-guards nil
  (b* ((out (hbhp-hasher-out bits wins gens w)))
    (hbhp-commit-fold-out rbits sts (car out) (cdr out))))

(defruled hbhp-hasher-out-wires
  (implies (and (hbhp-hasher-wires-okp bits wins gens w asg)
                (consp bits) (consp gens) (posp w))
           (b* ((out (hbhp-hasher-out bits wins gens w)))
             (and (hbhp-wire-okp (car out)) (hbhp-wire-okp (cdr out)))))
  :use ((:instance hbhp-rest-out-wires
                   (bits (nthcdr (hbhp-win-n bits w) bits))
                   (wins (cdr wins)) (gens (cdr gens))
                   (xacc (nth 1 (car wins))) (yacc (nth 2 (car wins)))))
  :enable (hbhp-hasher-out hbhp-hasher-wires-okp hbhp-wwires-okp)
  :prep-lemmas
  ((defruled hbhp-rest-out-wires
     (implies (and (hbhp-hasher-rest-wires-okp bits wins gens w asg)
                   (hbhp-wire-okp xacc) (hbhp-wire-okp yacc))
              (b* ((out (hbhp-hasher-rest-out bits wins gens w xacc yacc)))
                (and (hbhp-wire-okp (car out)) (hbhp-wire-okp (cdr out)))))
     :induct (hbhp-hasher-rest-out bits wins gens w xacc yacc)
     :enable (hbhp-hasher-rest-out hbhp-hasher-rest-wires-okp))))

(defruled hbhp-pointp-of-hasher-hash-ok
  (implies (and (hbhp-gens-okp gens)
                (posp w)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens))))
           (ecurve::edwards-bls12-pointp
            (hbhp-hasher-hash-uncompressed gens w bits)))
  :use ((:instance hbhp-r-pointp-of-hasher-sum
                   (bits (hbhp-pad bits)) (acc (ecurve::twisted-edwards-zero)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (hbhp-hasher-sum (hbhp-pad bits) gens w
                                               (ecurve::twisted-edwards-zero)))))
  :enable (hbhp-hasher-hash-uncompressed hbhp-gens-okp)
  :disable (hbhp-r-pointp-of-hasher-sum
            ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp))

(defruled hbhp-hasher-commit-gadget-sound
  :short "Soundness of the hasher followed by the randomizer tail."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-hasher-wires-okp bits wins gens w asg)
                (ecurve::edwards-bls12-pointp rgen)
                (hbhp-commit-fold-wires-okp rbits sts asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-commit-gadget bits wins gens w rbits sts rgen p)
                 asg p))
           (b* ((out (hbhp-hasher-commit-out bits wins gens w rbits sts)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (ecurve::edwards-bls12-add
                     (hbhp-hasher-hash-uncompressed gens w (hbhp-lk-list bits asg))
                     (ecurve::edwards-bls12-mul
                      (acl2::lebits=>nat (hbhp-lk-list rbits asg)) rgen)))))
  :use (hbhp-hasher-gadget-sound
        hbhp-hasher-out-wires
        (:instance hbhp-commit-fold-sound
                   (i 0)
                   (x2 (car (hbhp-hasher-out bits wins gens w)))
                   (y2 (cdr (hbhp-hasher-out bits wins gens w)))
                   (acc (hbhp-hasher-hash-uncompressed
                         gens w (hbhp-lk-list bits asg))))
        (:instance hbhp-rscalar-is-lebits (i 0))
        (:instance hbhp-pointp-of-hasher-hash-ok
                   (bits (hbhp-lk-list bits asg))))
  :in-theory '(hbhp-hasher-commit-gadget hbhp-hasher-commit-out
               r1cs::r1cs-constraints-holdp-of-append
               (:e expt) natp hbhp-times-1-left hbhp-lebits-natp
               hbhp-len-of-lk-list hbhp-len-atom-2 hbhp-gens-okp-consp posp)
  :prep-lemmas
  ((defruled hbhp-len-atom-2
     (implies (not (consp x)) (equal (len x) 0)))
   (defruled hbhp-gens-okp-consp
     (implies (hbhp-gens-okp gens) (consp gens))
     :enable hbhp-gens-okp)
   (defruled hbhp-times-1-left
     (implies (natp x) (equal (* 1 x) x)))
   (defruled hbhp-lebits-natp
     (natp (acl2::lebits=>nat x)))))
