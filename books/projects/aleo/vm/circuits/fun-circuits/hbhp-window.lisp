; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One window of BHPHasher::hash_uncompressed on variable bits.
;
; Chunk j of the window with generator G looks up the Montgomery image of
; (k + 1) 16^j G, k < 4 (the constant tables of BHPHasher::Inject::new).  The
; first chunk initialises the accumulator; every further chunk adds into it
; with montgomery_add (3 constraints); the window ends with the two
; div_unchecked constraints converting back to Edwards coordinates.
;
; Soundness: for a nonzero subgroup point G and 1 <= chunks <= 63, the
; output wires are the window scalar times G (hbhp-window-scalar).  The
; non-exceptional conditions are discharged by hbhp-bounds.lisp.

(in-package "ALEOVM")

(include-book "hbhp-chunk")
(include-book "hbhp-bounds")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lookup tables (BHPHasher::Inject::new).

(define hbhp-tab-x (g (j natp))
  :verify-guards nil
  :short "Montgomery abscissas of @($(k+1) 16^j G$), @($k < 4$)."
  (b* ((e (expt 16 (lnfix j))))
    (list (hbhp-mu (hbhp-gp (* 1 e) g)) (hbhp-mu (hbhp-gp (* 2 e) g))
          (hbhp-mu (hbhp-gp (* 3 e) g)) (hbhp-mu (hbhp-gp (* 4 e) g)))))

(define hbhp-tab-y (g (j natp))
  :verify-guards nil
  :short "Montgomery ordinates of @($(k+1) 16^j G$), @($k < 4$)."
  (b* ((e (expt 16 (lnfix j))))
    (list (hbhp-mv (hbhp-gp (* 1 e) g)) (hbhp-mv (hbhp-gp (* 2 e) g))
          (hbhp-mv (hbhp-gp (* 3 e) g)) (hbhp-mv (hbhp-gp (* 4 e) g)))))

(defruled hbhp-mult-point-ok
  :short "@($c 16^j G$) with @($1 \\le |c| \\le 4$), @($j \\le 62$) has a
          nonzero abscissa, so its Montgomery image exists."
  (implies (and (hbhp-gen-okp g)
                (natp j) (<= j 62)
                (integerp c) (<= 1 (abs c)) (<= (abs c) 4))
           (b* ((pt (hbhp-gp (* c (expt 16 j)) g)))
             (and (ecurve::edwards-bls12-pointp pt)
                  (not (equal (hbhp-x pt) 0)))))
  :use (hbhp-chunk-mult-bound
        (:instance hbhp-small-scalar-mod (x (* c (expt 16 j))) (k (+ 1 j)))
        (:instance hbhp-x-of-mul-nonzero (n (* c (expt 16 j)))))
  :in-theory '(ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
               ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
               natp (:t expt) (:e <) (:t abs)))

(defruled hbhp-tab-fep4p
  (implies (and (hbhp-gen-okp g) (natp j) (<= j 62)
                (equal p (base-prime)))
           (and (hbhp-fep4p (hbhp-tab-x g j) p)
                (hbhp-fep4p (hbhp-tab-y g j) p)))
  :use ((:instance hbhp-mult-point-ok (c 1))
        (:instance hbhp-mult-point-ok (c 2))
        (:instance hbhp-mult-point-ok (c 3))
        (:instance hbhp-mult-point-ok (c 4))
        (:instance hbhp-mont-image (pt (hbhp-gp (* 1 (expt 16 j)) g)))
        (:instance hbhp-mont-image (pt (hbhp-gp (* 2 (expt 16 j)) g)))
        (:instance hbhp-mont-image (pt (hbhp-gp (* 3 (expt 16 j)) g)))
        (:instance hbhp-mont-image (pt (hbhp-gp (* 4 (expt 16 j)) g))))
  :in-theory '(hbhp-fep4p hbhp-tab-x hbhp-tab-y hbhp-nth-of-cons
               (:e abs) (:e <) (:e integerp) lnfix nfix natp)
  :prep-lemmas
  ((defruled hbhp-nth-of-cons
     (and (equal (nth 0 (cons a x)) a)
          (equal (nth 1 (cons a x)) (nth 0 x))
          (equal (nth 2 (cons a x)) (nth 1 x))
          (equal (nth 3 (cons a x)) (nth 2 x))))))

(defruledl hbhp-expt16-int
  (implies (natp j) (and (integerp (expt 16 j)) (< 0 (expt 16 j))
                         (integerp (* 2 (expt 16 j)))
                         (integerp (* 3 (expt 16 j)))
                         (integerp (* 4 (expt 16 j))))))

(defruledl hbhp-times-minus
  (and (equal (* -1 x) (- x))
       (equal (* (- a) b) (- (* a b))))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled hbhp-chunk-point
  :short "The chunk outputs are the Montgomery image of
          @($c \\cdot 16^j G$), @($c$) the signed chunk multiplier."
  (implies (and (hbhp-gen-okp g) (natp j) (<= j 62)
                (equal p (base-prime))
                (bitp b0) (bitp b1) (bitp b2))
           (b* ((pt (hbhp-gp (* (hbhp-chunk-scalar b0 b1 b2) (expt 16 j)) g)))
             (and (ecurve::edwards-bls12-pointp pt)
                  (not (equal (hbhp-x pt) 0))
                  (equal (hbhp-sel4 (hbhp-tab-x g j) b0 b1) (hbhp-mu pt))
                  (equal (if (equal b2 1)
                             (pfield::neg (hbhp-sel4 (hbhp-tab-y g j) b0 b1) p)
                           (hbhp-sel4 (hbhp-tab-y g j) b0 b1))
                         (hbhp-mv pt)))))
  :use ((:instance hbhp-mult-point-ok (c (+ 1 b0 (* 2 b1))))
        (:instance hbhp-mult-point-ok (c (hbhp-chunk-scalar b0 b1 b2)))
        (:instance hbhp-mont-of-neg
                   (pt (hbhp-gp (* (+ 1 b0 (* 2 b1)) (expt 16 j)) g)))
        (:instance hbhp-g-neg-mul (n (* (+ 1 b0 (* 2 b1)) (expt 16 j))))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g)))
  :do-not-induct t
  :in-theory (e/d (hbhp-chunk-scalar hbhp-sel4 hbhp-tab-x hbhp-tab-y bitp
                   hbhp-times-minus hbhp-expt16-int)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-neg
                   hbhp-mu hbhp-mv))
  :cases ((and (equal b0 0) (equal b1 0))
          (and (equal b0 1) (equal b1 0))
          (and (equal b0 0) (equal b1 1))
          (and (equal b0 1) (equal b1 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; montgomery_add and the conversion back, over linear combinations.

(define hbhp-sv-neg (vec (p posp))
  :verify-guards nil
  (hbhp-sv-scale (pfield::neg 1 p) vec p))

(defrule hbhp-dot-product-of-sv-neg
  (implies (posp p)
           (equal (r1cs::dot-product (hbhp-sv-neg vec p) asg p)
                  (pfield::neg (r1cs::dot-product vec asg p) p)))
  :enable hbhp-sv-neg)

(define hbhp-mont-add-gadget (u1 v1 u2 v2
                              (lam symbolp) (u3 symbolp) (v3 symbolp)
                              (p posp))
  :verify-guards nil
  :short "@('montgomery_add((u1, v1), (u2, v2))'): the accumulator
          @('(u1, v1)') (this) and the chunk point @('(u2, v2)') (that) are
          linear combinations; @('lam'), @('u3'), @('v3') are new wires."
  (list (r1cs::make-r1cs-constraint
         :a (append u2 (hbhp-sv-neg u1 p))
         :b (list (list 1 lam))
         :c (append v2 (hbhp-sv-neg v1 p)))
        (r1cs::make-r1cs-constraint
         :a (list (list (hbhp-mont-b) lam))
         :b (list (list 1 lam))
         :c (append (list (list (hbhp-mont-a) 1)) u1 u2 (list (list 1 u3))))
        (r1cs::make-r1cs-constraint
         :a (append u1 (list (list (pfield::neg 1 p) u3)))
         :b (list (list 1 lam))
         :c (append v1 (list (list 1 v3))))))

(defmacro hbhp-dot (v) `(r1cs::dot-product ,v asg p))

(defmacro hbhp-wire-okp (w)
  `(and (symbolp ,w) (not (equal ,w 1)) (r1cs::valuation-bindsp asg ,w)))

(defruled hbhp-mont-add-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp lam) (hbhp-wire-okp u3) (hbhp-wire-okp v3))
           (equal (r1cs::r1cs-constraints-holdp
                   (hbhp-mont-add-gadget u1 v1 u2 v2 lam u3 v3 p) asg p)
                  (hbhp-mont-add-eqns (hbhp-dot u1) (hbhp-dot v1)
                                      (hbhp-dot u2) (hbhp-dot v2)
                                      (hbhp-lk lam) (hbhp-lk u3) (hbhp-lk v3) p)))
  :use hbhp-mont-coeffs
  :in-theory '(hbhp-mont-add-gadget r1cs::r1cs-constraint-holdsp
               r1cs::r1cs-constraints-holdp
               r1cs::r1cs-constraint->a-of-r1cs-constraint
               r1cs::r1cs-constraint->b-of-r1cs-constraint
               r1cs::r1cs-constraint->c-of-r1cs-constraint
               hbhp-base-prime-facts r1cs::fep-of-lookup-equal
               hbhp-dot-cons hbhp-dot-nil hbhp-simple-field-2
               hbhp-dot-product-of-sv-neg r1cs::dot-product-of-append
               hbhp-append-to-nil
               pfield::fep-of-neg pfield::fep-of-mul pfield::fep-of-add
               car-cons cdr-cons (:e equal) endp atom
               pfield::sub r1cs::fep-of-dot-product
               pfield::add-associative pfield::mul-commutative)
  :prep-lemmas
  ((defruled hbhp-append-to-nil
     (and (equal (append (list a) x) (cons a x))
          (equal (append (cons a x) y) (cons a (append x y)))))
   (defruled hbhp-simple-field-2
     (implies (and (primep p) (< 2 p))
              (and (equal (mod 1 p) 1)
                   (implies (pfield::fep x p)
                            (and (equal (pfield::mul 1 x p) x)
                                 (equal (pfield::mul x 1 p) x)
                                 (equal (pfield::add x 0 p) x)
                                 (equal (pfield::add 0 x p) x)
                                 (equal (pfield::mul (pfield::neg 1 p) x p)
                                        (pfield::neg x p))
                                 (equal (mod x p) x))))))))

(define hbhp-to-edwards-gadget (u v (ex symbolp) (ey symbolp) (p posp))
  :verify-guards nil
  :short "@('sum_x.div_unchecked(sum_y)') and
          @('(sum_x - 1).div_unchecked(sum_x + 1)')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 ex))
         :b v
         :c u)
        (r1cs::make-r1cs-constraint
         :a (list (list 1 ey))
         :b (append u (list (list 1 1)))
         :c (append u (list (list (pfield::neg 1 p) 1))))))

(defruled hbhp-to-edwards-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp ex) (hbhp-wire-okp ey))
           (equal (r1cs::r1cs-constraints-holdp
                   (hbhp-to-edwards-gadget u v ex ey p) asg p)
                  (hbhp-to-edwards-eqns (hbhp-dot u) (hbhp-dot v)
                                        (hbhp-lk ex) (hbhp-lk ey) p)))
  :in-theory '(hbhp-to-edwards-gadget r1cs::r1cs-constraint-holdsp
               r1cs::r1cs-constraints-holdp
               r1cs::r1cs-constraint->a-of-r1cs-constraint
               r1cs::r1cs-constraint->b-of-r1cs-constraint
               r1cs::r1cs-constraint->c-of-r1cs-constraint
               hbhp-base-prime-facts r1cs::fep-of-lookup-equal
               hbhp-dot-cons hbhp-dot-nil hbhp-simple-field-3
               r1cs::dot-product-of-append r1cs::fep-of-dot-product
               pfield::fep-of-neg pfield::fep-of-mul pfield::fep-of-add
               car-cons cdr-cons (:e equal) endp atom pfield::sub
               pfield::mul-commutative)
  :prep-lemmas
  ((defruled hbhp-simple-field-3
     (implies (and (primep p) (< 2 p))
              (and (equal (mod 1 p) 1)
                   (equal (mod (pfield::neg 1 p) p) (pfield::neg 1 p))
                   (equal (pfield::mul 1 1 p) 1)
                   (equal (pfield::add 1 0 p) 1)
                   (implies (pfield::fep x p)
                            (and (equal (pfield::mul 1 x p) x)
                                 (equal (pfield::mul x 1 p) x)
                                 (equal (pfield::add x 0 p) x)
                                 (equal (mod x p) x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One accumulation step.

(defruled hbhp-window-step-points
  :short "The accumulator @($s G$) and the chunk point @($c 16^j G$) satisfy
          the non-exceptional conditions of montgomery_add."
  (implies (and (hbhp-gen-okp g)
                (natp j) (<= 1 j) (<= j 62)
                (hbhp-acc-okp s j)
                (integerp c) (<= 1 (abs c)) (<= (abs c) 4))
           (b* ((cc (* c (expt 16 j)))
                (p1 (hbhp-gp s g))
                (p2 (hbhp-gp cc g)))
             (and (ecurve::edwards-bls12-pointp p1)
                  (ecurve::edwards-bls12-pointp p2)
                  (hbhp-mont-add-ok p1 p2)
                  (equal (ecurve::edwards-bls12-add p1 p2) (hbhp-gp (+ s cc) g))
                  (hbhp-acc-okp (+ s cc) (+ 1 j)))))
  :do-not-induct t
  :cases ((integerp s))
  :use (hbhp-acc-step
        hbhp-acc-okp-int
        (:instance hbhp-expt16-int)
        (:instance hbhp-small-scalar-mod (x s) (k j))
        (:instance hbhp-small-scalar-mod (x (* c (expt 16 j))) (k (+ 1 j)))
        (:instance hbhp-small-scalar-mod (x (+ s (* c (expt 16 j)))) (k (+ 1 j)))
        (:instance hbhp-small-scalar-mod (x (- s (* c (expt 16 j)))) (k (+ 1 j)))
        (:instance hbhp-x-of-mul-nonzero (n s))
        (:instance hbhp-x-of-mul-nonzero (n (* c (expt 16 j))))
        (:instance hbhp-x-of-mul-nonzero (n (+ s (* c (expt 16 j)))))
        (:instance hbhp-y-of-muls-differ (m s) (n (* c (expt 16 j))))
        (:instance hbhp-g-mul-add (m s) (n (* c (expt 16 j))))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g)))
  :in-theory (e/d (hbhp-acc-okp-int hbhp-expt16-int)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                   hbhp-acc-okp hbhp-wbound hbhp-mu hbhp-mv abs))
  :prep-lemmas
  ((defruled hbhp-acc-okp-int
     (implies (hbhp-acc-okp s j)
              (and (integerp s)
                   (<= (abs s) (hbhp-wbound j))
                   (implies (< 0 (nfix j)) (not (equal s 0)))))
     :enable hbhp-acc-okp)))

(defruled hbhp-dot-one-wire
  (implies (and (primep p) (< 2 p)
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp w))
           (equal (r1cs::dot-product (list (list 1 w)) asg p) (hbhp-lk w)))
  :in-theory '(hbhp-dot-cons hbhp-dot-nil r1cs::fep-of-lookup-equal
               pfield::mul-of-1-arg1 pfield::add-of-0-arg2 hbhp-mod-1
               hbhp-int-of-primep car-cons cdr-cons)
  :prep-lemmas
  ((defruled hbhp-mod-1
     (implies (and (integerp p) (< 2 p)) (equal (mod 1 p) 1)))
   (defruled hbhp-int-of-primep
     (implies (primep p) (integerp p))
     :enable primep)))

(defmacro hbhp-step-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (natp j) (<= 1 j) (<= j 62)
        (hbhp-acc-okp s j)
        (hbhp-wire-okp b0) (hbhp-wire-okp b1) (hbhp-wire-okp b2)
        (bitp (hbhp-lk b0)) (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
        (hbhp-wire-okp b01) (hbhp-wire-okp my)
        (hbhp-wire-okp lam) (hbhp-wire-okp u3) (hbhp-wire-okp v3)
        (equal (hbhp-dot u1) (hbhp-mu (hbhp-gp s g)))
        (equal (hbhp-dot v1) (hbhp-mv (hbhp-gp s g)))))

(defmacro hbhp-step-cc ()
  '(* (hbhp-chunk-scalar (hbhp-lk b0) (hbhp-lk b1) (hbhp-lk b2)) (expt 16 j)))

(defruled hbhp-window-step-sound
  (implies (and (hbhp-step-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-chunk-gadget b0 b1 b2 b01 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1
                                       (hbhp-lookup-lc b0 b1 b01 (hbhp-tab-x g j) p)
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p))
           (b* ((s2 (+ s (hbhp-step-cc))))
             (and (equal (hbhp-mu (hbhp-gp s2 g)) (hbhp-lk u3))
                  (equal (hbhp-mv (hbhp-gp s2 g)) (hbhp-lk v3))
                  (hbhp-acc-okp s2 (+ 1 j)))))
  :use ((:instance hbhp-chunk-gadget-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
        (:instance hbhp-tab-fep4p)
        (:instance hbhp-chunk-point (b0 (hbhp-lk b0)) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-chunk-scalar-range
                   (b0 (hbhp-lk b0)) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-window-step-points
                   (c (hbhp-chunk-scalar (hbhp-lk b0) (hbhp-lk b1) (hbhp-lk b2))))
        (:instance hbhp-mont-add-gadget-to-eqns
                   (u2 (hbhp-lookup-lc b0 b1 b01 (hbhp-tab-x g j) p))
                   (v2 (list (list 1 my))))
        (:instance hbhp-dot-one-wire (w my))
        (:instance hbhp-mont-add-sound
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (hbhp-step-cc) g))
                   (lam (hbhp-lk lam)) (u3 (hbhp-lk u3)) (v3 (hbhp-lk v3))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The chunks after the first: lookup, then montgomery_add into the
;; accumulator.  Each chunk has new wires (b01 my lam u3 v3).

(defrulel hbhp-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(define hbhp-window-steps (bs ws g (j natp) u1 v1 (p posp))
  :verify-guards nil
  :measure (len bs)
  (if (< (len bs) 3)
      nil
    (b* ((b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs)) (w (car ws))
         (b01 (nth 0 w)) (my (nth 1 w)) (lam (nth 2 w))
         (u3 (nth 3 w)) (v3 (nth 4 w)))
      (append (hbhp-chunk-gadget b0 b1 b2 b01 my (hbhp-tab-y g j) p)
              (hbhp-mont-add-gadget u1 v1
                                    (hbhp-lookup-lc b0 b1 b01 (hbhp-tab-x g j) p)
                                    (list (list 1 my))
                                    lam u3 v3 p)
              (hbhp-window-steps (nthcdr 3 bs) (cdr ws) g (1+ (lnfix j))
                                 (list (list 1 u3)) (list (list 1 v3)) p)))))

(define hbhp-window-steps-out (bs ws u1 v1)
  :verify-guards nil
  :measure (len bs)
  :short "The accumulator after the steps, as a pair of linear combinations."
  (if (< (len bs) 3)
      (cons u1 v1)
    (b* ((w (car ws)))
      (hbhp-window-steps-out (nthcdr 3 bs) (cdr ws)
                             (list (list 1 (nth 3 w))) (list (list 1 (nth 4 w)))))))

(define hbhp-nchunks (bs)
  :verify-guards nil
  :measure (len bs)
  (if (< (len bs) 3) 0 (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))

(define hbhp-steps-wires-okp (bs ws asg)
  :verify-guards nil
  :measure (len bs)
  (if (< (len bs) 3)
      t
    (b* ((b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs)) (w (car ws)))
      (and (hbhp-wire-okp b0) (hbhp-wire-okp b1) (hbhp-wire-okp b2)
           (bitp (hbhp-lk b0)) (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
           (hbhp-wire-okp (nth 0 w)) (hbhp-wire-okp (nth 1 w))
           (hbhp-wire-okp (nth 2 w)) (hbhp-wire-okp (nth 3 w))
           (hbhp-wire-okp (nth 4 w))
           (hbhp-steps-wires-okp (nthcdr 3 bs) (cdr ws) asg)))))

(define hbhp-steps-scalar (bs (j natp) asg)
  :verify-guards nil
  :measure (len bs)
  (if (< (len bs) 3)
      0
    (+ (* (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                             (hbhp-lk (nth 2 bs)))
          (expt 16 (lnfix j)))
       (hbhp-steps-scalar (nthcdr 3 bs) (1+ (lnfix j)) asg))))

(defun hbhp-steps-induct (bs ws j s u1 v1 asg)
  (declare (xargs :measure (len bs) :verify-guards nil))
  (if (< (len bs) 3)
      (list ws j s u1 v1 asg)
    (b* ((w (car ws)))
      (hbhp-steps-induct (nthcdr 3 bs) (cdr ws) (1+ (nfix j))
                         (+ s (* (hbhp-chunk-scalar (hbhp-lk (nth 0 bs))
                                                    (hbhp-lk (nth 1 bs))
                                                    (hbhp-lk (nth 2 bs)))
                                 (expt 16 (nfix j))))
                         (list (list 1 (nth 3 w))) (list (list 1 (nth 4 w)))
                         asg))))

(defruled hbhp-window-steps-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (natp j) (<= 1 j) (<= (+ j (hbhp-nchunks bs)) 63)
                (hbhp-acc-okp s j)
                (hbhp-steps-wires-okp bs ws asg)
                (equal (hbhp-dot u1) (hbhp-mu (hbhp-gp s g)))
                (equal (hbhp-dot v1) (hbhp-mv (hbhp-gp s g)))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-steps bs ws g j u1 v1 p) asg p))
           (b* ((s2 (+ s (hbhp-steps-scalar bs j asg)))
                (out (hbhp-window-steps-out bs ws u1 v1)))
             (and (equal (hbhp-dot (car out)) (hbhp-mu (hbhp-gp s2 g)))
                  (equal (hbhp-dot (cdr out)) (hbhp-mv (hbhp-gp s2 g)))
                  (hbhp-acc-okp s2 (+ j (hbhp-nchunks bs))))))
  :induct (hbhp-steps-induct bs ws j s u1 v1 asg)
  :in-theory '(hbhp-base-prime-facts r1cs::r1cs-constraints-holdp-of-append
               hbhp-holdp-nil hbhp-plus-assoc hbhp-plus-0 hbhp-acc-okp-integerp
               nfix lnfix car-cons cdr-cons (:induction hbhp-steps-induct)
               natp not (:t hbhp-nchunks) hbhp-plus-1-comm)
  :hints (("Subgoal *1/2"
           :expand ((hbhp-window-steps bs ws g j u1 v1 p)
                    (hbhp-window-steps bs ws g j u1 v1 (base-prime))
                    (hbhp-window-steps-out bs ws u1 v1)
                    (hbhp-nchunks bs)
                    (hbhp-steps-wires-okp bs ws asg)
                    (hbhp-steps-scalar bs j asg))
           :use ((:instance hbhp-window-step-sound
                            (b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs))
                            (b01 (nth 0 (car ws))) (my (nth 1 (car ws)))
                            (lam (nth 2 (car ws))) (u3 (nth 3 (car ws)))
                            (v3 (nth 4 (car ws))))
                 (:instance hbhp-dot-one-wire (w (nth 3 (car ws))))
                 (:instance hbhp-dot-one-wire (w (nth 4 (car ws))))))
          ("Subgoal *1/1"
           :expand ((hbhp-window-steps bs ws g j u1 v1 p)
                    (hbhp-window-steps bs ws g j u1 v1 (base-prime))
                    (hbhp-window-steps-out bs ws u1 v1)
                    (hbhp-nchunks bs)
                    (hbhp-steps-scalar bs j asg))))
  :prep-lemmas
  ((defruled hbhp-holdp-nil
     (r1cs::r1cs-constraints-holdp nil asg p)
     :enable r1cs::r1cs-constraints-holdp)
   (defruled hbhp-plus-assoc
     (equal (+ x (+ y z)) (+ (+ x y) z)))
   (defruled hbhp-plus-1-comm
     (equal (+ x 1) (+ 1 x)))
   (defruled hbhp-plus-0
     (implies (integerp x) (equal (+ x 0) x)))
   (defruled hbhp-acc-okp-integerp
     (implies (hbhp-acc-okp s j) (integerp s))
     :enable hbhp-acc-okp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A whole window: the first chunk initialises the accumulator, the remaining
;; chunks are added in, and the result is converted back to Edwards form.
;; The wires of the first chunk are (b01 my), the first element of ws.

(define hbhp-window-acc0 (bs ws g (p posp))
  :verify-guards nil
  (cons (hbhp-lookup-lc (nth 0 bs) (nth 1 bs) (nth 0 (car ws)) (hbhp-tab-x g 0) p)
        (list (list 1 (nth 1 (car ws))))))

(define hbhp-window-gadget (bs ws g (ex symbolp) (ey symbolp) (p posp))
  :verify-guards nil
  :short "The constraints of one window of variable bits @('bs')."
  (b* ((acc0 (hbhp-window-acc0 bs ws g p))
       (out (hbhp-window-steps-out (nthcdr 3 bs) (cdr ws) (car acc0) (cdr acc0))))
    (append (hbhp-chunk-gadget (nth 0 bs) (nth 1 bs) (nth 2 bs)
                               (nth 0 (car ws)) (nth 1 (car ws))
                               (hbhp-tab-y g 0) p)
            (hbhp-window-steps (nthcdr 3 bs) (cdr ws) g 1 (car acc0) (cdr acc0) p)
            (hbhp-to-edwards-gadget (car out) (cdr out) ex ey p))))

(define hbhp-window-wires-okp (bs ws ex ey asg)
  :verify-guards nil
  (and (<= 3 (len bs))
       (hbhp-wire-okp (nth 0 bs)) (hbhp-wire-okp (nth 1 bs))
       (hbhp-wire-okp (nth 2 bs))
       (bitp (hbhp-lk (nth 0 bs))) (bitp (hbhp-lk (nth 1 bs)))
       (bitp (hbhp-lk (nth 2 bs)))
       (hbhp-wire-okp (nth 0 (car ws))) (hbhp-wire-okp (nth 1 (car ws)))
       (hbhp-steps-wires-okp (nthcdr 3 bs) (cdr ws) asg)
       (hbhp-wire-okp ex) (hbhp-wire-okp ey)))

(defruled hbhp-window-first-chunk
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-window-wires-okp bs ws ex ey asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-chunk-gadget (nth 0 bs) (nth 1 bs) (nth 2 bs)
                                    (nth 0 (car ws)) (nth 1 (car ws))
                                    (hbhp-tab-y g 0) p)
                 asg p))
           (b* ((c (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                      (hbhp-lk (nth 2 bs))))
                (acc0 (hbhp-window-acc0 bs ws g p)))
             (and (equal (hbhp-dot (car acc0)) (hbhp-mu (hbhp-gp c g)))
                  (equal (hbhp-dot (cdr acc0)) (hbhp-mv (hbhp-gp c g)))
                  (hbhp-acc-okp c 1))))
  :use ((:instance hbhp-chunk-gadget-sound
                   (b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs))
                   (b01 (nth 0 (car ws))) (my (nth 1 (car ws)))
                   (tx (hbhp-tab-x g 0)) (ty (hbhp-tab-y g 0)))
        (:instance hbhp-tab-fep4p (j 0))
        (:instance hbhp-chunk-point (j 0)
                   (b0 (hbhp-lk (nth 0 bs))) (b1 (hbhp-lk (nth 1 bs)))
                   (b2 (hbhp-lk (nth 2 bs))))
        (:instance hbhp-dot-one-wire (w (nth 1 (car ws))))
        (:instance hbhp-acc-okp-first
                   (b0 (hbhp-lk (nth 0 bs))) (b1 (hbhp-lk (nth 1 bs)))
                   (b2 (hbhp-lk (nth 2 bs)))))
  :in-theory '(hbhp-window-wires-okp hbhp-window-acc0 car-cons cdr-cons
               hbhp-base-prime-facts hbhp-times-1 (:e expt) natp (:e <)
               (:t hbhp-chunk-scalar))
  :prep-lemmas
  ((defruled hbhp-times-1
     (implies (integerp x) (equal (* x 1) x)))))

(defruled hbhp-window-gadget-sound
  :short "Soundness of one window: the output wires are the Edwards
          coordinates of the window scalar times @($G$)."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-window-wires-okp bs ws ex ey asg)
                (<= (hbhp-nchunks bs) 63)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-gadget bs ws g ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-steps-scalar bs 0 asg) g)))
  :use (hbhp-window-first-chunk
        (:instance hbhp-window-steps-sound
                   (bs (nthcdr 3 bs)) (ws (cdr ws)) (j 1)
                   (s (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                         (hbhp-lk (nth 2 bs))))
                   (u1 (car (hbhp-window-acc0 bs ws g p)))
                   (v1 (cdr (hbhp-window-acc0 bs ws g p))))
        (:instance hbhp-to-edwards-gadget-to-eqns
                   (u (car (hbhp-window-steps-out
                            (nthcdr 3 bs) (cdr ws)
                            (car (hbhp-window-acc0 bs ws g p))
                            (cdr (hbhp-window-acc0 bs ws g p)))))
                   (v (cdr (hbhp-window-steps-out
                            (nthcdr 3 bs) (cdr ws)
                            (car (hbhp-window-acc0 bs ws g p))
                            (cdr (hbhp-window-acc0 bs ws g p))))))
        (:instance hbhp-to-edwards-sound
                   (pt (hbhp-gp (hbhp-steps-scalar bs 0 asg) g))
                   (ex (hbhp-lk ex)) (ey (hbhp-lk ey)))
        (:instance hbhp-x-of-mul-nonzero (n (hbhp-steps-scalar bs 0 asg)))
        (:instance hbhp-small-scalar-mod
                   (x (hbhp-steps-scalar bs 0 asg))
                   (k (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-steps-scalar bs 0 asg)) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        hbhp-steps-scalar-first
        (:instance hbhp-acc-okp-facts
                   (s (hbhp-steps-scalar bs 0 asg))
                   (j (+ 1 (hbhp-nchunks (nthcdr 3 bs))))))
  :in-theory '(hbhp-window-gadget r1cs::r1cs-constraints-holdp-of-append
               hbhp-window-wires-okp hbhp-nchunks-first
               hbhp-base-prime-facts natp (:t hbhp-nchunks))
  :prep-lemmas
  ((defruled hbhp-steps-scalar-first
     (implies (<= 3 (len bs))
              (equal (hbhp-steps-scalar bs 0 asg)
                     (+ (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                           (hbhp-lk (nth 2 bs)))
                        (hbhp-steps-scalar (nthcdr 3 bs) 1 asg))))
     :expand (hbhp-steps-scalar bs 0 asg))
   (defruled hbhp-nchunks-first
     (implies (<= 3 (len bs))
              (equal (hbhp-nchunks bs) (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))
     :expand (hbhp-nchunks bs))
   (defruled hbhp-acc-okp-facts
     (implies (and (hbhp-acc-okp s j) (natp j) (< 0 j))
              (and (integerp s) (not (equal s 0))
                   (<= (abs s) (hbhp-wbound j))))
     :enable hbhp-acc-okp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Relation to the specification.

(define hbhp-lk-list (bs asg)
  :verify-guards nil
  :short "The values of the bit wires @('bs')."
  (if (consp bs)
      (cons (hbhp-lk (car bs)) (hbhp-lk-list (cdr bs) asg))
    nil))

(defrule hbhp-len-of-lk-list
  (equal (len (hbhp-lk-list bs asg)) (len bs))
  :enable hbhp-lk-list)

(defruled hbhp-nthcdr-of-lk-list
  (equal (nthcdr n (hbhp-lk-list bs asg)) (hbhp-lk-list (nthcdr n bs) asg))
  :enable (hbhp-lk-list nthcdr))

(defruled hbhp-nth-of-lk-list
  (implies (< (nfix n) (len bs))
           (equal (nth n (hbhp-lk-list bs asg)) (hbhp-lk (nth n bs))))
  :enable (hbhp-lk-list nth))

(defruled hbhp-steps-scalar-is-window-scalar
  (equal (hbhp-steps-scalar bs j asg)
         (hbhp-window-scalar (hbhp-lk-list bs asg) j))
  :induct (hbhp-steps-scalar bs j asg)
  :enable (hbhp-steps-scalar hbhp-window-scalar hbhp-nthcdr-of-lk-list nth)
  :expand ((hbhp-lk-list bs asg) (hbhp-lk-list (cdr bs) asg)
           (hbhp-lk-list (cddr bs) asg)))

(defruled hbhp-window-gadget-sound-spec
  :short "Soundness of one window against @('hbhp-window-scalar')."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-window-wires-okp bs ws ex ey asg)
                (<= (hbhp-nchunks bs) 63)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-gadget bs ws g ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-window-scalar (hbhp-lk-list bs asg) 0) g)))
  :use (hbhp-window-gadget-sound
        (:instance hbhp-steps-scalar-is-window-scalar (j 0)))
  :in-theory nil)
