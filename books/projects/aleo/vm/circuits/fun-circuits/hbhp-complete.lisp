; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness of BHPHasher::hash_uncompressed on variable bits: the witness
; values snarkVM computes (the AND of the two low chunk bits, the signed
; table ordinate, the Montgomery slope and sum, the Edwards coordinates of
; each window sum, and the Group::add products and sum) satisfy every
; constraint.  The canonical values are stated by the -canon predicates
; below, which follow the same recursions as the gadgets.

(in-package "ALEOVM")

(include-book "hbhp-hasher")
(include-book "crv-add-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A chunk.

(defmacro hbhp-chunk-canon (b0 b1 b2 b01 my ty)
  `(and (equal (hbhp-lk ,b01) (pfield::mul (hbhp-lk ,b0) (hbhp-lk ,b1) p))
        (equal (hbhp-lk ,my)
               (if (equal (hbhp-lk ,b2) 1)
                   (pfield::neg (hbhp-sel4 ,ty (hbhp-lk ,b0) (hbhp-lk ,b1)) p)
                 (hbhp-sel4 ,ty (hbhp-lk ,b0) (hbhp-lk ,b1))))))

(defruled hbhp-chunk-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b0) (hbhp-wire-okp b1) (hbhp-wire-okp b2)
                (hbhp-wire-okp b01) (hbhp-wire-okp my)
                (bitp (hbhp-lk b0)) (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
                (hbhp-fep4p ty p)
                (hbhp-chunk-canon b0 b1 b2 b01 my ty))
           (r1cs::r1cs-constraints-holdp
            (hbhp-chunk-gadget b0 b1 b2 b01 my ty p) asg p))
  :use (hbhp-chunk-gadget-to-eqns
        (:instance hbhp-lookup-lc-value (tab ty)
                   (b0$ (hbhp-lk b0)) (b1$ (hbhp-lk b1)))
        (:instance hbhp-c-fep-of-sel4 (tab ty) (b0 (hbhp-lk b0)) (b1 (hbhp-lk b1)))
        (:instance hbhp-c-sign-lemma
                   (y (hbhp-sel4 ty (hbhp-lk b0) (hbhp-lk b1)))
                   (b (hbhp-lk b2))))
  :in-theory '(hbhp-base-prime-facts)
  :prep-lemmas
  ((defruled hbhp-c-two-half-y
     (implies (and (equal p (base-prime)) (pfield::fep y p))
              (equal (pfield::mul 2 (pfield::mul (hbhp-half) y p) p) y))
     :use (hbhp-half-facts
           (:instance pfield::mul-associative
                      (pfield::x 2) (pfield::y (hbhp-half)) (pfield::z y)
                      (pfield::p p)))
     :in-theory '(hbhp-base-prime-facts pfield::mul-of-1-arg1))
   (defruled hbhp-c-fep-of-sel4
     (implies (hbhp-fep4p tab p)
              (pfield::fep (hbhp-sel4 tab b0 b1) p))
     :enable (hbhp-sel4 hbhp-fep4p acl2::bfix))
   (defruled hbhp-c-sign-lemma
     (implies (and (equal p (base-prime))
                   (pfield::fep y p) (bitp b))
              (equal (pfield::mul (pfield::mul (pfield::neg 2 p) y p)
                                  (pfield::add b (pfield::neg (hbhp-half) p) p)
                                  p)
                     (if (equal b 1) (pfield::neg y p) y)))
     :use (hbhp-half-facts hbhp-c-two-half-y)
     :enable (bitp hbhp-base-prime-facts)
     :disable ((:e hbhp-half)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A step: chunk j added into the accumulator s G.

(defmacro hbhp-mont-canon (pa pb lam u3 v3)
  `(and (equal (hbhp-lk ,lam)
               (hbhp-mont-lam (hbhp-mu ,pa) (hbhp-mv ,pa) (hbhp-mu ,pb) (hbhp-mv ,pb)))
        (equal (hbhp-lk ,u3) (hbhp-mu (ecurve::edwards-bls12-add ,pa ,pb)))
        (equal (hbhp-lk ,v3) (hbhp-mv (ecurve::edwards-bls12-add ,pa ,pb)))))

(defruled hbhp-window-step-complete
  (implies (and (hbhp-step-hyps)
                (hbhp-chunk-canon b0 b1 b2 b01 my (hbhp-tab-y g j))
                (hbhp-mont-canon (hbhp-gp s g) (hbhp-gp (hbhp-step-cc) g)
                                 lam u3 v3))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-chunk-gadget b0 b1 b2 b01 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1
                                       (hbhp-lookup-lc b0 b1 b01 (hbhp-tab-x g j) p)
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p)))
  :use ((:instance hbhp-chunk-gadget-complete (ty (hbhp-tab-y g j)))
        (:instance hbhp-chunk-gadget-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
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
        (:instance hbhp-mont-add-complete
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (hbhp-step-cc) g))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The steps of a window.

(defruledl hbhp-c-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(define hbhp-steps-canon (bs ws g (j natp) s asg)
  :verify-guards nil
  :measure (len bs)
  :hints (("Goal" :in-theory (enable hbhp-c-len-of-nthcdr)))
  (if (< (len bs) 3)
      t
    (b* ((p (base-prime))
         (j (lnfix j))
         (b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs)) (w (car ws))
         (cc (* (hbhp-chunk-scalar (hbhp-lk b0) (hbhp-lk b1) (hbhp-lk b2))
                (expt 16 j))))
      (and (hbhp-chunk-canon b0 b1 b2 (nth 0 w) (nth 1 w) (hbhp-tab-y g j))
           (hbhp-mont-canon (hbhp-gp s g) (hbhp-gp cc g)
                            (nth 2 w) (nth 3 w) (nth 4 w))
           (hbhp-steps-canon (nthcdr 3 bs) (cdr ws) g (1+ j) (+ s cc) asg)))))

(defruled hbhp-window-steps-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (natp j) (<= 1 j) (<= (+ j (hbhp-nchunks bs)) 63)
                (hbhp-acc-okp s j)
                (hbhp-steps-wires-okp bs ws asg)
                (equal (hbhp-dot u1) (hbhp-mu (hbhp-gp s g)))
                (equal (hbhp-dot v1) (hbhp-mv (hbhp-gp s g)))
                (hbhp-steps-canon bs ws g j s asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-window-steps bs ws g j u1 v1 p) asg p))
  :induct (hbhp-steps-induct bs ws j s u1 v1 asg)
  :in-theory '(hbhp-base-prime-facts r1cs::r1cs-constraints-holdp-of-append
               hbhp-c-holdp-nil hbhp-c-plus-1-comm
               nfix lnfix car-cons cdr-cons (:induction hbhp-steps-induct)
               natp not (:t hbhp-nchunks))
  :hints (("Subgoal *1/2"
           :expand ((hbhp-window-steps bs ws g j u1 v1 p)
                    (hbhp-window-steps bs ws g j u1 v1 (base-prime))
                    (hbhp-nchunks bs)
                    (hbhp-steps-wires-okp bs ws asg)
                    (hbhp-steps-canon bs ws g j s asg))
           :use ((:instance hbhp-window-step-complete
                            (b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs))
                            (b01 (nth 0 (car ws))) (my (nth 1 (car ws)))
                            (lam (nth 2 (car ws))) (u3 (nth 3 (car ws)))
                            (v3 (nth 4 (car ws))))
                 (:instance hbhp-window-step-points
                            (c (hbhp-chunk-scalar (hbhp-lk (nth 0 bs))
                                                  (hbhp-lk (nth 1 bs))
                                                  (hbhp-lk (nth 2 bs)))))
                 (:instance hbhp-chunk-scalar-range
                            (b0 (hbhp-lk (nth 0 bs))) (b1 (hbhp-lk (nth 1 bs)))
                            (b2 (hbhp-lk (nth 2 bs))))
                 (:instance hbhp-dot-one-wire (w (nth 3 (car ws))))
                 (:instance hbhp-dot-one-wire (w (nth 4 (car ws))))))
          ("Subgoal *1/1"
           :expand ((hbhp-window-steps bs ws g j u1 v1 p)
                    (hbhp-window-steps bs ws g j u1 v1 (base-prime)))))
  :prep-lemmas
  ((defruled hbhp-c-holdp-nil
     (r1cs::r1cs-constraints-holdp nil asg p)
     :enable r1cs::r1cs-constraints-holdp)
   (defruled hbhp-c-plus-1-comm
     (equal (+ x 1) (+ 1 x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A window.

(define hbhp-window-canon (bs ws g ex ey asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (c (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                             (hbhp-lk (nth 2 bs))))
       (pt (hbhp-gp (hbhp-steps-scalar bs 0 asg) g)))
    (and (hbhp-chunk-canon (nth 0 bs) (nth 1 bs) (nth 2 bs)
                           (nth 0 (car ws)) (nth 1 (car ws)) (hbhp-tab-y g 0))
         (hbhp-steps-canon (nthcdr 3 bs) (cdr ws) g 1 c asg)
         (equal (hbhp-lk ex) (hbhp-x pt))
         (equal (hbhp-lk ey) (hbhp-y pt)))))

(defruled hbhp-window-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-window-wires-okp bs ws ex ey asg)
                (<= (hbhp-nchunks bs) 63)
                (hbhp-window-canon bs ws g ex ey asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-window-gadget bs ws g ex ey p) asg p))
  :use ((:instance hbhp-chunk-gadget-complete
                   (b0 (nth 0 bs)) (b1 (nth 1 bs)) (b2 (nth 2 bs))
                   (b01 (nth 0 (car ws))) (my (nth 1 (car ws)))
                   (ty (hbhp-tab-y g 0)))
        (:instance hbhp-tab-fep4p (j 0))
        hbhp-window-first-chunk
        (:instance hbhp-window-steps-complete
                   (bs (nthcdr 3 bs)) (ws (cdr ws)) (j 1)
                   (s (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                         (hbhp-lk (nth 2 bs))))
                   (u1 (car (hbhp-window-acc0 bs ws g p)))
                   (v1 (cdr (hbhp-window-acc0 bs ws g p))))
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
        (:instance hbhp-to-edwards-complete
                   (pt (hbhp-gp (hbhp-steps-scalar bs 0 asg) g)))
        (:instance hbhp-x-of-mul-nonzero (n (hbhp-steps-scalar bs 0 asg)))
        (:instance hbhp-small-scalar-mod
                   (x (hbhp-steps-scalar bs 0 asg))
                   (k (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-steps-scalar bs 0 asg)) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        hbhp-c-steps-scalar-first
        (:instance hbhp-c-acc-okp-facts
                   (s (hbhp-steps-scalar bs 0 asg))
                   (j (+ 1 (hbhp-nchunks (nthcdr 3 bs))))))
  :in-theory '(hbhp-window-gadget hbhp-window-canon
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-window-wires-okp hbhp-c-nchunks-first
               hbhp-base-prime-facts natp (:t hbhp-nchunks))
  :prep-lemmas
  ((defruled hbhp-c-steps-scalar-first
     (implies (<= 3 (len bs))
              (equal (hbhp-steps-scalar bs 0 asg)
                     (+ (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                           (hbhp-lk (nth 2 bs)))
                        (hbhp-steps-scalar (nthcdr 3 bs) 1 asg))))
     :expand (hbhp-steps-scalar bs 0 asg))
   (defruled hbhp-c-nchunks-first
     (implies (<= 3 (len bs))
              (equal (hbhp-nchunks bs) (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))
     :expand (hbhp-nchunks bs))
   (defruled hbhp-c-acc-okp-facts
     (implies (and (hbhp-acc-okp s j) (natp j) (< 0 j))
              (and (integerp s) (not (equal s 0))
                   (<= (abs s) (hbhp-wbound j))))
     :enable hbhp-acc-okp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fold.

(defmacro hbhp-add-canon (x1 y1 x2 y2 u v0 v1 v01 x3 y3 sum)
  `(and (equal (hbhp-lk ,u)
               (pfield::mul (pfield::add (hbhp-lk ,x1) (hbhp-lk ,y1) p)
                            (pfield::add (hbhp-lk ,x2) (hbhp-lk ,y2) p) p))
        (equal (hbhp-lk ,v0) (pfield::mul (hbhp-lk ,x1) (hbhp-lk ,y2) p))
        (equal (hbhp-lk ,v1) (pfield::mul (hbhp-lk ,x2) (hbhp-lk ,y1) p))
        (equal (hbhp-lk ,v01) (pfield::mul (hbhp-lk ,v0) (hbhp-lk ,v1) p))
        (equal (hbhp-lk ,x3) (ecurve::point-finite->x ,sum))
        (equal (hbhp-lk ,y3) (ecurve::point-finite->y ,sum))))

(defruled hbhp-hasher-window-step-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (posp w) (<= w 63)
                (natp n) (<= 3 n) (<= n (* 3 w)) (<= n (len bits))
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-wwires-okp (take n bits) ws ex ey asg)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (hbhp-window-canon (take n bits) ws g ex ey asg)
                (hbhp-add-canon ex ey xacc yacc u v0 v1 v01 x3 y3
                                (ecurve::edwards-bls12-add
                                 (hbhp-gp (hbhp-window-scalar
                                           (take n (hbhp-lk-list bits asg)) 0)
                                          g)
                                 acc)))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-window-gadget (take n bits) ws g ex ey p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-add-gadget ex ey xacc yacc u v0 v1 v01 x3 y3 p)
                 asg p)))
  :use ((:instance hbhp-window-gadget-complete (bs (take n bits)))
        (:instance hbhp-window-gadget-sound-spec (bs (take n bits)))
        (:instance hbhp-window-wires-okp-from-wwires (bs (take n bits)))
        (:instance hbhp-window-nchunks-ok)
        (:instance hbhp-take-of-lk-list (bs bits))
        (:instance crv-group-add-gadget-complete
                   (x1 ex) (y1 ey) (x2 xacc) (y2 yacc)
                   (p1 (hbhp-gp (hbhp-window-scalar
                                 (hbhp-lk-list (take n bits) asg) 0)
                                g))
                   (p2 acc))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (hbhp-lk-list (take n bits) asg) 0))
                   (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var xacc) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var yacc) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :in-theory (e/d (group-add-funspec hbhp-wwires-okp hbhp-base-prime-facts
                   pfield::fep)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                   hbhp-window-gadget crv-group-add-gadget hbhp-window-canon
                   hbhp-window-wires-okp hbhp-steps-wires-okp
                   hbhp-window-scalar hbhp-lk-list hbhp-nchunks
                   ecurve::edwards-bls12-r-pointp
                   ecurve::edwards-bls12-pointp)))

(defruledl hbhp-c-len-pos
  (implies (consp x) (< 0 (len x))))

(defruledl hbhp-c-win-measure
  (implies (consp bits)
           (< (len (nthcdr (hbhp-win-n bits w) bits)) (len bits)))
  :enable (acl2::pos-fix hbhp-c-len-of-nthcdr))

(define hbhp-hasher-rest-canon (bits wins gens w xacc yacc acc asg)
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :use hbhp-c-win-measure
           :in-theory '(o< o-finp o-p natp (:t len) endp atom not)))
  (b* (((when (or (endp bits) (endp gens))) t)
       (p (base-prime))
       (n (hbhp-win-n bits w))
       (r (car wins))
       (pw (hbhp-gp (hbhp-window-scalar (take n (hbhp-lk-list bits asg)) 0)
                    (car gens))))
    (and (hbhp-window-canon (take n bits) (nth 0 r) (car gens)
                            (nth 1 r) (nth 2 r) asg)
         (hbhp-add-canon (nth 1 r) (nth 2 r) xacc yacc
                         (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r) (nth 7 r) (nth 8 r)
                         (ecurve::edwards-bls12-add pw acc))
         (hbhp-hasher-rest-canon (nthcdr n bits) (cdr wins) (cdr gens) w
                                 (nth 7 r) (nth 8 r)
                                 (ecurve::edwards-bls12-add acc pw) asg))))

(defruledl hbhp-c-holdp
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(defruled hbhp-hasher-rest-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-hasher-rest-wires-okp bits wins gens w asg)
                (hbhp-hasher-rest-canon bits wins gens w xacc yacc acc asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hasher-rest bits wins gens w xacc yacc p) asg p))
  :induct (hbhp-rest-induct bits wins gens w xacc yacc acc asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               hbhp-nthcdr-of-lk-list hbhp-consp-of-lk-list hbhp-len-of-lk-list
               hbhp-r-point-listp hbhp-nonzero-listp acl2::pos-fix posp natp
               hbhp-c-len-of-nthcdr nfix hbhp-c-len-pos (:induction hbhp-rest-induct)
               endp atom not car-cons cdr-cons (:t min) (:t len)
               hbhp-c-holdp)
  :hints (("Subgoal *1/2"
           :expand ((:free (gens xacc yacc p)
                     (hbhp-hasher-rest bits wins gens w xacc yacc p))
                    (:free (gens) (hbhp-hasher-rest-wires-okp bits wins gens w asg))
                    (:free (gens acc xacc yacc)
                     (hbhp-hasher-rest-canon bits wins gens w xacc yacc acc asg)))
           :use ((:instance hbhp-hasher-window-step-complete
                            (g (car gens)) (n (hbhp-win-n bits w))
                            (ws (nth 0 (car wins)))
                            (ex (nth 1 (car wins))) (ey (nth 2 (car wins)))
                            (u (nth 3 (car wins))) (v0 (nth 4 (car wins)))
                            (v1 (nth 5 (car wins))) (v01 (nth 6 (car wins)))
                            (x3 (nth 7 (car wins))) (y3 (nth 8 (car wins))))
                 (:instance hbhp-hasher-window-step
                            (g (car gens)) (n (hbhp-win-n bits w))
                            (ws (nth 0 (car wins)))
                            (ex (nth 1 (car wins))) (ey (nth 2 (car wins)))
                            (u (nth 3 (car wins))) (v0 (nth 4 (car wins)))
                            (v1 (nth 5 (car wins))) (v01 (nth 6 (car wins)))
                            (x3 (nth 7 (car wins))) (y3 (nth 8 (car wins))))
                 (:instance hbhp-add-comm
                            (a acc)
                            (b (hbhp-gp (hbhp-window-scalar
                                         (take (hbhp-win-n bits w)
                                               (hbhp-lk-list bits asg)) 0)
                                        (car gens))))
                 (:instance hbhp-win-n-facts (len (len bits)))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                            (ecurve::point1 acc)
                            (ecurve::point2
                             (hbhp-gp (hbhp-window-scalar
                                       (take (hbhp-win-n bits w)
                                             (hbhp-lk-list bits asg)) 0)
                                      (car gens))))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar
                             (hbhp-window-scalar
                              (take (hbhp-win-n bits w) (hbhp-lk-list bits asg)) 0))
                            (point (car gens)))
                 (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                            (ecurve::x (car gens)))))
          ("Subgoal *1/1"
           :expand ((:free (gens xacc yacc p)
                     (hbhp-hasher-rest bits wins gens w xacc yacc p))))))

(define hbhp-hasher-canon (bits wins gens w asg)
  :verify-guards nil
  :short "The canonical witness of the hasher gadget."
  (b* ((n (hbhp-win-n bits w))
       (r (car wins)))
    (and (hbhp-window-canon (take n bits) (nth 0 r) (car gens) (nth 1 r) (nth 2 r) asg)
         (hbhp-hasher-rest-canon (nthcdr n bits) (cdr wins) (cdr gens) w
                                 (nth 1 r) (nth 2 r)
                                 (hbhp-gp (hbhp-window-scalar
                                           (take n (hbhp-lk-list bits asg)) 0)
                                          (car gens))
                                 asg))))

(defruledl hbhp-c-len-atom
  (implies (not (consp x)) (equal (len x) 0)))

(defruledl hbhp-c-len-of-take
  (equal (len (take n x)) (nfix n)))

(defruled hbhp-hasher-gadget-complete
  :short "Completeness of @('BHPHasher::hash_uncompressed') on variable bits:
          the canonical witness satisfies the constraints."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-hasher-wires-okp bits wins gens w asg)
                (hbhp-hasher-canon bits wins gens w asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hasher-gadget bits wins gens w p) asg p))
  :use ((:instance hbhp-window-gadget-complete
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-gadget-sound-spec
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-wires-okp-from-wwires
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins)))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-nchunks-ok (n (hbhp-win-n bits w)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (hbhp-win-n bits w)))
        (:instance hbhp-win-n-facts (len (len bits)))
        (:instance hbhp-hasher-rest-complete
                   (bits (nthcdr (hbhp-win-n bits w) bits))
                   (wins (cdr wins)) (gens (cdr gens))
                   (xacc (nth 1 (car wins))) (yacc (nth 2 (car wins)))
                   (acc (hbhp-gp (hbhp-window-scalar
                                  (take (hbhp-win-n bits w)
                                        (hbhp-lk-list bits asg)) 0)
                                 (car gens))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (take (hbhp-win-n bits w)
                                          (hbhp-lk-list bits asg)) 0))
                   (point (car gens)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (car gens))))
  :in-theory '(hbhp-hasher-gadget hbhp-hasher-canon
               hbhp-hasher-wires-okp hbhp-gens-okp hbhp-r-point-listp
               hbhp-nonzero-listp r1cs::r1cs-constraints-holdp-of-append
               hbhp-len-of-lk-list acl2::pos-fix posp natp
               hbhp-c-len-of-nthcdr nfix hbhp-c-len-pos
               endp atom not car-cons cdr-cons (:t min) (:t len)
               hbhp-c-len-of-take hbhp-wwires-okp hbhp-c-len-atom))
