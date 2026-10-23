; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHPHasher::hash_uncompressed when the input length is not a multiple of 3.
;
; snarkVM pads the input with Boolean::constant(false), so the last chunk is
; [v0, v1, false] or [v0, false, false].  Constant folding then gives:
;
;   [v0, v1, false]:  b01 = v0 AND v1                  1 constraint
;                     (-2 y) * (-1/2) = montgomery_y   1 constraint
;                     (bit_2 - 1/2 is the constant -1/2)
;   [v0, false, false]: v0 AND false is the constant false (no constraint);
;                     montgomery_x = x0 + v0 (x1 - x0)  (the b1 and b01 terms
;                     are constant zero and fold away), likewise y;
;                     (-2 y) * (-1/2) = montgomery_y   1 constraint
;
; montgomery_y is still a witness (its inputs include v0), so the sign
; constraint is emitted.  The padded chunk is the last chunk of the last
; window; it is either the first chunk of that window or is added into the
; accumulator by montgomery_add as usual.  All earlier windows are full and
; are emitted exactly as by hbhp-hasher-gadget.

(in-package "ALEOVM")

(include-book "hbhp-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The padded chunk.  `tl' is the list of the one or two variable bits.

(define hbhp-lookup-lc1 (b0 tab (p posp))
  :verify-guards nil
  :short "@('t0 + b0 (t1 - t0)'): the lookup with @('b1') constant false."
  (list (list (nth 0 tab) 1)
        (list (pfield::sub (nth 1 tab) (nth 0 tab) p) b0)))

(define hbhp-plc (tl b01 tab (p posp))
  :verify-guards nil
  (if (consp (cdr tl))
      (hbhp-lookup-lc (nth 0 tl) (nth 1 tl) b01 tab p)
    (hbhp-lookup-lc1 (nth 0 tl) tab p)))

(define hbhp-pchunk-gadget (tl (b01 symbolp) (my symbolp) ty (p posp))
  :verify-guards nil
  :short "The constraints of the padded last chunk."
  (b* ((sign (r1cs::make-r1cs-constraint
              :a (hbhp-sv-scale (pfield::neg 2 p) (hbhp-plc tl b01 ty p) p)
              :b (list (list (pfield::neg (hbhp-half) p) 1))
              :c (list (list 1 my)))))
    (if (consp (cdr tl))
        (list (r1cs::make-r1cs-constraint
               :a (list (list 1 (nth 0 tl)))
               :b (list (list 1 (nth 1 tl)))
               :c (list (list 1 b01)))
              sign)
      (list sign))))

(define hbhp-pb1 (tl asg)
  :verify-guards nil
  :short "The value of the second chunk bit (0 when it is padding)."
  (if (consp (cdr tl)) (hbhp-lk (nth 1 tl)) 0))

(define hbhp-ptl-okp (tl b01 asg)
  :verify-guards nil
  (and (consp tl)
       (< (len tl) 3)
       (hbhp-wire-okp (nth 0 tl)) (bitp (hbhp-lk (nth 0 tl)))
       (implies (consp (cdr tl))
                (and (hbhp-wire-okp (nth 1 tl)) (bitp (hbhp-lk (nth 1 tl)))
                     (hbhp-wire-okp b01)))))

(defruledl hbhp-p-simple-field
  (implies (equal p (base-prime))
           (and (equal (mod 1 p) 1)
                (implies (pfield::fep x p)
                         (and (equal (pfield::mul 1 x p) x)
                              (equal (pfield::mul x 1 p) x)
                              (equal (pfield::add x 0 p) x)
                              (equal (pfield::add 0 x p) x)
                              (equal (mod x p) x)))))
  :enable hbhp-base-prime-facts)

(defruled hbhp-lookup-lc1-value
  (implies (and (equal p (base-prime))
                (hbhp-fep4p tab p)
                (bitp (hbhp-lk b0)) (hbhp-wire-okp b0)
                (r1cs::r1cs-valuationp asg p))
           (equal (r1cs::dot-product (hbhp-lookup-lc1 b0 tab p) asg p)
                  (hbhp-sel4 tab (hbhp-lk b0) 0)))
  :use ((:instance hbhp-p-simple-field (x (nth 0 tab))))
  :enable (hbhp-lookup-lc1 hbhp-sel4 hbhp-fep4p hbhp-dot-cons hbhp-dot-nil bitp
           hbhp-base-prime-facts)
  :cases ((equal (hbhp-lk b0) 0) (equal (hbhp-lk b0) 1)))

(defruled hbhp-pchunk-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-ptl-okp tl b01 asg)
                (hbhp-wire-okp my))
           (equal (r1cs::r1cs-constraints-holdp
                   (hbhp-pchunk-gadget tl b01 my ty p) asg p)
                  (and (implies (consp (cdr tl))
                                (equal (pfield::mul (hbhp-lk (nth 0 tl))
                                                    (hbhp-lk (nth 1 tl)) p)
                                       (hbhp-lk b01)))
                       (equal (pfield::mul
                               (pfield::mul (pfield::neg 2 p)
                                            (r1cs::dot-product
                                             (hbhp-plc tl b01 ty p) asg p)
                                            p)
                               (pfield::neg (hbhp-half) p)
                               p)
                              (hbhp-lk my)))))
  :in-theory '(hbhp-pchunk-gadget hbhp-ptl-okp r1cs::r1cs-constraint-holdsp
               r1cs::r1cs-constraints-holdp
               r1cs::r1cs-constraint->a-of-r1cs-constraint
               r1cs::r1cs-constraint->b-of-r1cs-constraint
               r1cs::r1cs-constraint->c-of-r1cs-constraint
               hbhp-base-prime-facts r1cs::fep-of-lookup-equal
               hbhp-dot-cons hbhp-dot-nil hbhp-p-simple-field
               hbhp-dot-product-of-sv-scale
               pfield::fep-of-neg pfield::fep-of-mul pfield::fep-of-add
               r1cs::fep-of-dot-product
               car-cons cdr-cons (:e equal) endp atom))

(defruled hbhp-p-fep-of-sel4
  (implies (hbhp-fep4p tab p)
           (pfield::fep (hbhp-sel4 tab b0 b1) p))
  :enable (hbhp-sel4 hbhp-fep4p acl2::bfix))

(defruled hbhp-p-sign0
  (implies (and (equal p (base-prime)) (pfield::fep y p))
           (equal (pfield::mul (pfield::mul (pfield::neg 2 p) y p)
                               (pfield::neg (hbhp-half) p)
                               p)
                  y))
  :use ((:instance hbhp-p-sign0-aux))
  :in-theory '(hbhp-base-prime-facts pfield::add-of-0-arg1 pfield::fep-of-neg
               pfield::fep-of-mul)
  :prep-lemmas
  ((defruled hbhp-p-two-half-y
     (implies (and (equal p (base-prime)) (pfield::fep y p))
              (equal (pfield::mul 2 (pfield::mul (hbhp-half) y p) p) y))
     :use (hbhp-half-facts
           (:instance pfield::mul-associative
                      (pfield::x 2) (pfield::y (hbhp-half)) (pfield::z y)
                      (pfield::p p)))
     :in-theory '(hbhp-base-prime-facts pfield::mul-of-1-arg1))
   (defruled hbhp-p-sign0-aux
     (implies (and (equal p (base-prime)) (pfield::fep y p))
              (equal (pfield::mul (pfield::mul (pfield::neg 2 p) y p)
                                  (pfield::add 0 (pfield::neg (hbhp-half) p) p)
                                  p)
                     y))
     :use (hbhp-half-facts hbhp-p-two-half-y)
     :enable (hbhp-base-prime-facts)
     :disable ((:e hbhp-half)))))

(defruled hbhp-plc-value
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-ptl-okp tl b01 asg)
                (hbhp-fep4p tab p)
                (implies (consp (cdr tl))
                         (equal (hbhp-lk b01)
                                (pfield::mul (hbhp-lk (nth 0 tl))
                                             (hbhp-lk (nth 1 tl)) p))))
           (equal (r1cs::dot-product (hbhp-plc tl b01 tab p) asg p)
                  (hbhp-sel4 tab (hbhp-lk (nth 0 tl)) (hbhp-pb1 tl asg))))
  :use ((:instance hbhp-lookup-lc-value
                   (b0 (nth 0 tl)) (b1 (nth 1 tl))
                   (b0$ (hbhp-lk (nth 0 tl))) (b1$ (hbhp-lk (nth 1 tl))))
        (:instance hbhp-lookup-lc1-value (b0 (nth 0 tl))))
  :in-theory '(hbhp-plc hbhp-pb1 hbhp-ptl-okp hbhp-base-prime-facts))

(defruled hbhp-pchunk-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-ptl-okp tl b01 asg)
                (hbhp-wire-okp my)
                (hbhp-fep4p tx p) (hbhp-fep4p ty p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pchunk-gadget tl b01 my ty p) asg p))
           (and (equal (r1cs::dot-product (hbhp-plc tl b01 tx p) asg p)
                       (hbhp-sel4 tx (hbhp-lk (nth 0 tl)) (hbhp-pb1 tl asg)))
                (equal (hbhp-lk my)
                       (hbhp-sel4 ty (hbhp-lk (nth 0 tl)) (hbhp-pb1 tl asg)))))
  :use (hbhp-pchunk-to-eqns
        (:instance hbhp-plc-value (tab tx))
        (:instance hbhp-plc-value (tab ty))
        (:instance hbhp-p-fep-of-sel4 (tab ty) (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)))
        (:instance hbhp-p-sign0
                   (y (hbhp-sel4 ty (hbhp-lk (nth 0 tl)) (hbhp-pb1 tl asg)))))
  :in-theory '(hbhp-base-prime-facts))

(defmacro hbhp-pchunk-canon (tl b01 my ty)
  `(and (implies (consp (cdr ,tl))
                 (equal (hbhp-lk ,b01)
                        (pfield::mul (hbhp-lk (nth 0 ,tl)) (hbhp-lk (nth 1 ,tl)) p)))
        (equal (hbhp-lk ,my)
               (hbhp-sel4 ,ty (hbhp-lk (nth 0 ,tl)) (hbhp-pb1 ,tl asg)))))

(defruled hbhp-pchunk-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-ptl-okp tl b01 asg)
                (hbhp-wire-okp my)
                (hbhp-fep4p ty p)
                (hbhp-pchunk-canon tl b01 my ty))
           (r1cs::r1cs-constraints-holdp
            (hbhp-pchunk-gadget tl b01 my ty p) asg p))
  :use (hbhp-pchunk-to-eqns
        (:instance hbhp-plc-value (tab ty))
        (:instance hbhp-p-fep-of-sel4 (tab ty) (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)))
        (:instance hbhp-p-sign0
                   (y (hbhp-sel4 ty (hbhp-lk (nth 0 tl)) (hbhp-pb1 tl asg)))))
  :in-theory '(hbhp-base-prime-facts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The conversion to Edwards form of an accumulator s G.

(defruled hbhp-p-acc-okp-facts
  (implies (and (hbhp-acc-okp s j) (natp j) (< 0 j))
           (and (integerp s) (not (equal s 0))
                (<= (abs s) (hbhp-wbound j))))
  :enable hbhp-acc-okp)

(defruled hbhp-edwards-final-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (natp j) (< 0 j) (<= j 63)
                (hbhp-acc-okp s j)
                (hbhp-wire-okp ex) (hbhp-wire-okp ey)
                (equal (hbhp-dot u) (hbhp-mu (hbhp-gp s g)))
                (equal (hbhp-dot v) (hbhp-mv (hbhp-gp s g)))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-to-edwards-gadget u v ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp s g)))
  :use (hbhp-to-edwards-gadget-to-eqns
        (:instance hbhp-to-edwards-sound
                   (pt (hbhp-gp s g)) (ex (hbhp-lk ex)) (ey (hbhp-lk ey)))
        (:instance hbhp-x-of-mul-nonzero (n s))
        (:instance hbhp-small-scalar-mod (x s) (k j))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar s) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        hbhp-p-acc-okp-facts)
  :in-theory '(hbhp-base-prime-facts natp))

(defruled hbhp-edwards-final-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (natp j) (< 0 j) (<= j 63)
                (hbhp-acc-okp s j)
                (hbhp-wire-okp ex) (hbhp-wire-okp ey)
                (equal (hbhp-dot u) (hbhp-mu (hbhp-gp s g)))
                (equal (hbhp-dot v) (hbhp-mv (hbhp-gp s g)))
                (equal (hbhp-lk ex) (hbhp-x (hbhp-gp s g)))
                (equal (hbhp-lk ey) (hbhp-y (hbhp-gp s g))))
           (r1cs::r1cs-constraints-holdp
            (hbhp-to-edwards-gadget u v ex ey p) asg p))
  :use (hbhp-to-edwards-gadget-to-eqns
        (:instance hbhp-to-edwards-complete (pt (hbhp-gp s g)))
        (:instance hbhp-x-of-mul-nonzero (n s))
        (:instance hbhp-small-scalar-mod (x s) (k j))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar s) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        hbhp-p-acc-okp-facts)
  :in-theory '(hbhp-base-prime-facts natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The padded chunk added into the accumulator s G at position j.

(defruled hbhp-bitp-of-pb1
  (implies (hbhp-ptl-okp tl b01 asg)
           (bitp (hbhp-pb1 tl asg)))
  :enable (hbhp-ptl-okp hbhp-pb1))

(defmacro hbhp-pc (tl)
  `(hbhp-chunk-scalar (hbhp-lk (nth 0 ,tl)) (hbhp-pb1 ,tl asg) 0))

(defmacro hbhp-pstep-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (natp j) (<= 1 j) (<= j 62)
        (hbhp-acc-okp s j)
        (hbhp-ptl-okp tl b01 asg)
        (hbhp-wire-okp my)
        (hbhp-wire-okp lam) (hbhp-wire-okp u3) (hbhp-wire-okp v3)
        (equal (hbhp-dot u1) (hbhp-mu (hbhp-gp s g)))
        (equal (hbhp-dot v1) (hbhp-mv (hbhp-gp s g)))))

(defruled hbhp-pstep-sound
  (implies (and (hbhp-pstep-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pchunk-gadget tl b01 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1
                                       (hbhp-plc tl b01 (hbhp-tab-x g j) p)
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p))
           (b* ((s2 (+ s (* (hbhp-pc tl) (expt 16 j)))))
             (and (equal (hbhp-mu (hbhp-gp s2 g)) (hbhp-lk u3))
                  (equal (hbhp-mv (hbhp-gp s2 g)) (hbhp-lk v3))
                  (hbhp-acc-okp s2 (+ 1 j)))))
  :use ((:instance hbhp-pchunk-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
        (:instance hbhp-tab-fep4p)
        hbhp-bitp-of-pb1
        (:instance hbhp-chunk-point (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-chunk-scalar-range
                   (b0 (hbhp-lk (nth 0 tl))) (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-window-step-points (c (hbhp-pc tl)))
        (:instance hbhp-mont-add-gadget-to-eqns
                   (u2 (hbhp-plc tl b01 (hbhp-tab-x g j) p))
                   (v2 (list (list 1 my))))
        (:instance hbhp-dot-one-wire (w my))
        (:instance hbhp-mont-add-sound
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (* (hbhp-pc tl) (expt 16 j)) g))
                   (lam (hbhp-lk lam)) (u3 (hbhp-lk u3)) (v3 (hbhp-lk v3))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal hbhp-ptl-okp
               (:e equal) (:e bitp)))

(defruled hbhp-pstep-complete
  (implies (and (hbhp-pstep-hyps)
                (hbhp-pchunk-canon tl b01 my (hbhp-tab-y g j))
                (hbhp-mont-canon (hbhp-gp s g)
                                 (hbhp-gp (* (hbhp-pc tl) (expt 16 j)) g)
                                 lam u3 v3))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-pchunk-gadget tl b01 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1
                                       (hbhp-plc tl b01 (hbhp-tab-x g j) p)
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p)))
  :use ((:instance hbhp-pchunk-complete (ty (hbhp-tab-y g j)))
        (:instance hbhp-pchunk-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
        (:instance hbhp-tab-fep4p)
        hbhp-bitp-of-pb1
        (:instance hbhp-chunk-point (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-chunk-scalar-range
                   (b0 (hbhp-lk (nth 0 tl))) (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-window-step-points (c (hbhp-pc tl)))
        (:instance hbhp-mont-add-gadget-to-eqns
                   (u2 (hbhp-plc tl b01 (hbhp-tab-x g j) p))
                   (v2 (list (list 1 my))))
        (:instance hbhp-dot-one-wire (w my))
        (:instance hbhp-mont-add-complete
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (* (hbhp-pc tl) (expt 16 j)) g))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal hbhp-ptl-okp
               (:e equal) (:e bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The padded last window.  With k full chunks before the padded one, the
;; window is: first chunk, k - 1 steps, the padded step (wires (nth k ws)),
;; and the conversion.  With k = 0 the padded chunk initialises the
;; accumulator directly.

(define hbhp-pwin0-gadget (tl r g (ex symbolp) (ey symbolp) (p posp))
  :verify-guards nil
  (append (hbhp-pchunk-gadget tl (nth 0 r) (nth 1 r) (hbhp-tab-y g 0) p)
          (hbhp-to-edwards-gadget (hbhp-plc tl (nth 0 r) (hbhp-tab-x g 0) p)
                                  (list (list 1 (nth 1 r)))
                                  ex ey p)))

(define hbhp-pwink-gadget (full tl ws g (ex symbolp) (ey symbolp) (k natp)
                           (p posp))
  :verify-guards nil
  (b* ((acc0 (hbhp-window-acc0 full ws g p))
       (out (hbhp-window-steps-out (nthcdr 3 full) (cdr ws) (car acc0) (cdr acc0)))
       (r (nth k ws)))
    (append (hbhp-chunk-gadget (nth 0 full) (nth 1 full) (nth 2 full)
                               (nth 0 (car ws)) (nth 1 (car ws))
                               (hbhp-tab-y g 0) p)
            (hbhp-window-steps (nthcdr 3 full) (cdr ws) g 1 (car acc0) (cdr acc0) p)
            (hbhp-pchunk-gadget tl (nth 0 r) (nth 1 r) (hbhp-tab-y g k) p)
            (hbhp-mont-add-gadget (car out) (cdr out)
                                  (hbhp-plc tl (nth 0 r) (hbhp-tab-x g k) p)
                                  (list (list 1 (nth 1 r)))
                                  (nth 2 r) (nth 3 r) (nth 4 r) p)
            (hbhp-to-edwards-gadget (list (list 1 (nth 3 r)))
                                    (list (list 1 (nth 4 r)))
                                    ex ey p))))

(defruledl hbhp-p-times-1
  (implies (integerp x) (equal (* x 1) x)))

(defruled hbhp-pwin0-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-ptl-okp tl (nth 0 r) asg)
                (hbhp-wire-okp (nth 1 r))
                (hbhp-wire-okp ex) (hbhp-wire-okp ey)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pwin0-gadget tl r g ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-pc tl) g)))
  :use ((:instance hbhp-pchunk-sound (b01 (nth 0 r)) (my (nth 1 r))
                   (tx (hbhp-tab-x g 0)) (ty (hbhp-tab-y g 0)))
        (:instance hbhp-tab-fep4p (j 0))
        (:instance hbhp-bitp-of-pb1 (b01 (nth 0 r)))
        (:instance hbhp-chunk-point (j 0) (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-acc-okp-first (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-dot-one-wire (w (nth 1 r)))
        (:instance hbhp-edwards-final-sound
                   (s (hbhp-pc tl)) (j 1)
                   (u (hbhp-plc tl (nth 0 r) (hbhp-tab-x g 0) p))
                   (v (list (list 1 (nth 1 r))))))
  :in-theory '(hbhp-pwin0-gadget r1cs::r1cs-constraints-holdp-of-append hbhp-ptl-okp
               hbhp-base-prime-facts hbhp-p-times-1 (:e expt) natp (:e <)
               (:t hbhp-chunk-scalar) (:e equal) (:e bitp)))

(defruled hbhp-pwin0-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (hbhp-ptl-okp tl (nth 0 r) asg)
                (hbhp-wire-okp (nth 1 r))
                (hbhp-wire-okp ex) (hbhp-wire-okp ey)
                (hbhp-pchunk-canon tl (nth 0 r) (nth 1 r) (hbhp-tab-y g 0))
                (equal (hbhp-lk ex) (hbhp-x (hbhp-gp (hbhp-pc tl) g)))
                (equal (hbhp-lk ey) (hbhp-y (hbhp-gp (hbhp-pc tl) g))))
           (r1cs::r1cs-constraints-holdp
            (hbhp-pwin0-gadget tl r g ex ey p) asg p))
  :use ((:instance hbhp-pchunk-complete (b01 (nth 0 r)) (my (nth 1 r))
                   (ty (hbhp-tab-y g 0)))
        (:instance hbhp-pchunk-sound (b01 (nth 0 r)) (my (nth 1 r))
                   (tx (hbhp-tab-x g 0)) (ty (hbhp-tab-y g 0)))
        (:instance hbhp-tab-fep4p (j 0))
        (:instance hbhp-bitp-of-pb1 (b01 (nth 0 r)))
        (:instance hbhp-chunk-point (j 0) (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-acc-okp-first (b0 (hbhp-lk (nth 0 tl)))
                   (b1 (hbhp-pb1 tl asg)) (b2 0))
        (:instance hbhp-dot-one-wire (w (nth 1 r)))
        (:instance hbhp-edwards-final-complete
                   (s (hbhp-pc tl)) (j 1)
                   (u (hbhp-plc tl (nth 0 r) (hbhp-tab-x g 0) p))
                   (v (list (list 1 (nth 1 r))))))
  :in-theory '(hbhp-pwin0-gadget r1cs::r1cs-constraints-holdp-of-append hbhp-ptl-okp
               hbhp-base-prime-facts hbhp-p-times-1 (:e expt) natp (:e <)
               (:t hbhp-chunk-scalar) (:e equal) (:e bitp)))

(defruledl hbhp-p-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(defun hbhp-p-nchunks-induct (x k)
  (declare (xargs :measure (len x)
                  :hints (("Goal" :in-theory (enable hbhp-p-len-of-nthcdr)))))
  (if (< (len x) 3) k (hbhp-p-nchunks-induct (nthcdr 3 x) (- k 1))))

(defruled hbhp-nchunks-of-3k
  (implies (and (natp k) (equal (len x) (* 3 k)))
           (equal (hbhp-nchunks x) k))
  :induct (hbhp-p-nchunks-induct x k)
  :enable (hbhp-nchunks hbhp-p-len-of-nthcdr))

(defruled hbhp-p-steps-scalar-first
  (implies (<= 3 (len bs))
           (equal (hbhp-steps-scalar bs 0 asg)
                  (+ (hbhp-chunk-scalar (hbhp-lk (nth 0 bs)) (hbhp-lk (nth 1 bs))
                                        (hbhp-lk (nth 2 bs)))
                     (hbhp-steps-scalar (nthcdr 3 bs) 1 asg))))
  :expand (hbhp-steps-scalar bs 0 asg))

(defruled hbhp-p-nchunks-first
  (implies (<= 3 (len bs))
           (equal (hbhp-nchunks bs) (+ 1 (hbhp-nchunks (nthcdr 3 bs)))))
  :expand (hbhp-nchunks bs))

(defmacro hbhp-pwink-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (posp k) (<= k 62)
        (equal (len full) (* 3 k))
        (hbhp-window-wires-okp full ws ex ey asg)
        (hbhp-ptl-okp tl (nth 0 (nth k ws)) asg)
        (hbhp-wire-okp (nth 1 (nth k ws))) (hbhp-wire-okp (nth 2 (nth k ws)))
        (hbhp-wire-okp (nth 3 (nth k ws))) (hbhp-wire-okp (nth 4 (nth k ws)))))

(defmacro hbhp-pwink-scalar ()
  '(+ (hbhp-steps-scalar full 0 asg) (* (hbhp-pc tl) (expt 16 k))))

(defruled hbhp-pwink-sound
  (implies (and (hbhp-pwink-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pwink-gadget full tl ws g ex ey k p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-pwink-scalar) g)))
  :use ((:instance hbhp-window-first-chunk (bs full))
        (:instance hbhp-window-steps-sound
                   (bs (nthcdr 3 full)) (ws (cdr ws)) (j 1)
                   (s (hbhp-chunk-scalar (hbhp-lk (nth 0 full)) (hbhp-lk (nth 1 full))
                                         (hbhp-lk (nth 2 full))))
                   (u1 (car (hbhp-window-acc0 full ws g p)))
                   (v1 (cdr (hbhp-window-acc0 full ws g p))))
        (:instance hbhp-nchunks-of-3k (x full))
        (:instance hbhp-p-nchunks-first (bs full))
        (:instance hbhp-p-steps-scalar-first (bs full))
        (:instance hbhp-pstep-sound
                   (j k) (s (hbhp-steps-scalar full 0 asg))
                   (u1 (car (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (v1 (cdr (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (b01 (nth 0 (nth k ws))) (my (nth 1 (nth k ws)))
                   (lam (nth 2 (nth k ws))) (u3 (nth 3 (nth k ws)))
                   (v3 (nth 4 (nth k ws))))
        (:instance hbhp-dot-one-wire (w (nth 3 (nth k ws))))
        (:instance hbhp-dot-one-wire (w (nth 4 (nth k ws))))
        (:instance hbhp-edwards-final-sound
                   (s (hbhp-pwink-scalar)) (j (+ 1 k))
                   (u (list (list 1 (nth 3 (nth k ws)))))
                   (v (list (list 1 (nth 4 (nth k ws)))))))
  :in-theory '(hbhp-pwink-gadget r1cs::r1cs-constraints-holdp-of-append
               hbhp-window-wires-okp hbhp-base-prime-facts natp posp
               (:t hbhp-nchunks) (:t hbhp-steps-scalar)))

(defruled hbhp-pwink-complete
  (implies (and (hbhp-pwink-hyps)
                (hbhp-window-canon full ws g ex ey asg)
                (hbhp-pchunk-canon tl (nth 0 (nth k ws)) (nth 1 (nth k ws))
                                   (hbhp-tab-y g k))
                (hbhp-mont-canon (hbhp-gp (hbhp-steps-scalar full 0 asg) g)
                                 (hbhp-gp (* (hbhp-pc tl) (expt 16 k)) g)
                                 (nth 2 (nth k ws)) (nth 3 (nth k ws))
                                 (nth 4 (nth k ws)))
                (equal (hbhp-lk ex) (hbhp-x (hbhp-gp (hbhp-pwink-scalar) g)))
                (equal (hbhp-lk ey) (hbhp-y (hbhp-gp (hbhp-pwink-scalar) g))))
           (r1cs::r1cs-constraints-holdp
            (hbhp-pwink-gadget full tl ws g ex ey k p) asg p))
  :use ((:instance hbhp-chunk-gadget-complete
                   (b0 (nth 0 full)) (b1 (nth 1 full)) (b2 (nth 2 full))
                   (b01 (nth 0 (car ws))) (my (nth 1 (car ws)))
                   (ty (hbhp-tab-y g 0)))
        (:instance hbhp-tab-fep4p (j 0))
        (:instance hbhp-window-first-chunk (bs full))
        (:instance hbhp-window-steps-complete
                   (bs (nthcdr 3 full)) (ws (cdr ws)) (j 1)
                   (s (hbhp-chunk-scalar (hbhp-lk (nth 0 full)) (hbhp-lk (nth 1 full))
                                         (hbhp-lk (nth 2 full))))
                   (u1 (car (hbhp-window-acc0 full ws g p)))
                   (v1 (cdr (hbhp-window-acc0 full ws g p))))
        (:instance hbhp-window-steps-sound
                   (bs (nthcdr 3 full)) (ws (cdr ws)) (j 1)
                   (s (hbhp-chunk-scalar (hbhp-lk (nth 0 full)) (hbhp-lk (nth 1 full))
                                         (hbhp-lk (nth 2 full))))
                   (u1 (car (hbhp-window-acc0 full ws g p)))
                   (v1 (cdr (hbhp-window-acc0 full ws g p))))
        (:instance hbhp-nchunks-of-3k (x full))
        (:instance hbhp-p-nchunks-first (bs full))
        (:instance hbhp-p-steps-scalar-first (bs full))
        (:instance hbhp-pstep-complete
                   (j k) (s (hbhp-steps-scalar full 0 asg))
                   (u1 (car (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (v1 (cdr (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (b01 (nth 0 (nth k ws))) (my (nth 1 (nth k ws)))
                   (lam (nth 2 (nth k ws))) (u3 (nth 3 (nth k ws)))
                   (v3 (nth 4 (nth k ws))))
        (:instance hbhp-pstep-sound
                   (j k) (s (hbhp-steps-scalar full 0 asg))
                   (u1 (car (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (v1 (cdr (hbhp-window-steps-out
                             (nthcdr 3 full) (cdr ws)
                             (car (hbhp-window-acc0 full ws g p))
                             (cdr (hbhp-window-acc0 full ws g p)))))
                   (b01 (nth 0 (nth k ws))) (my (nth 1 (nth k ws)))
                   (lam (nth 2 (nth k ws))) (u3 (nth 3 (nth k ws)))
                   (v3 (nth 4 (nth k ws))))
        (:instance hbhp-dot-one-wire (w (nth 3 (nth k ws))))
        (:instance hbhp-dot-one-wire (w (nth 4 (nth k ws))))
        (:instance hbhp-edwards-final-complete
                   (s (hbhp-pwink-scalar)) (j (+ 1 k))
                   (u (list (list 1 (nth 3 (nth k ws)))))
                   (v (list (list 1 (nth 4 (nth k ws)))))))
  :in-theory '(hbhp-pwink-gadget hbhp-window-canon
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-window-wires-okp hbhp-base-prime-facts natp posp
               (:t hbhp-nchunks) (:t hbhp-steps-scalar)))

(define hbhp-pwindow-k (bs)
  :verify-guards nil
  :short "The number of full chunks of the padded window."
  (floor (len bs) 3))

(define hbhp-pwindow-gadget (bs ws g (ex symbolp) (ey symbolp) (p posp))
  :verify-guards nil
  :short "The constraints of a last window whose length is not a multiple
          of 3."
  (b* ((k (hbhp-pwindow-k bs))
       (tl (nthcdr (* 3 k) bs)))
    (if (zp k)
        (hbhp-pwin0-gadget tl (car ws) g ex ey p)
      (hbhp-pwink-gadget (take (* 3 k) bs) tl ws g ex ey k p))))

(define hbhp-pwindow-wires-okp (bs ws ex ey asg)
  :verify-guards nil
  (b* ((k (hbhp-pwindow-k bs))
       (tl (nthcdr (* 3 k) bs))
       (r (nth k ws)))
    (and (hbhp-ptl-okp tl (nth 0 r) asg)
         (hbhp-wire-okp (nth 1 r))
         (if (zp k)
             (and (hbhp-wire-okp ex) (hbhp-wire-okp ey))
           (and (hbhp-window-wires-okp (take (* 3 k) bs) ws ex ey asg)
                (hbhp-wire-okp (nth 2 r)) (hbhp-wire-okp (nth 3 r))
                (hbhp-wire-okp (nth 4 r)))))))

(define hbhp-pwindow-scalar (bs asg)
  :verify-guards nil
  (b* ((k (hbhp-pwindow-k bs))
       (tl (nthcdr (* 3 k) bs))
       (c (* (hbhp-pc tl) (expt 16 k))))
    (if (zp k) c (+ (hbhp-steps-scalar (take (* 3 k) bs) 0 asg) c))))

(defruled hbhp-pwindow-k-facts
  (implies (< (len bs) 189)
           (and (natp (hbhp-pwindow-k bs))
                (<= (hbhp-pwindow-k bs) 62)
                (<= (* 3 (hbhp-pwindow-k bs)) (len bs))
                (equal (len (take (* 3 (hbhp-pwindow-k bs)) bs))
                       (* 3 (hbhp-pwindow-k bs)))))
  :enable hbhp-pwindow-k
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-pwindow-gadget-sound
  :short "Soundness of the padded last window."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (< (len bs) 189)
                (hbhp-pwindow-wires-okp bs ws ex ey asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pwindow-gadget bs ws g ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-pwindow-scalar bs asg) g)))
  :use (hbhp-pwindow-k-facts
        (:instance hbhp-pwin0-sound
                   (tl (nthcdr (* 3 (hbhp-pwindow-k bs)) bs)) (r (car ws)))
        (:instance hbhp-pwink-sound
                   (full (take (* 3 (hbhp-pwindow-k bs)) bs))
                   (tl (nthcdr (* 3 (hbhp-pwindow-k bs)) bs))
                   (k (hbhp-pwindow-k bs))))
  :in-theory '(hbhp-pwindow-gadget hbhp-pwindow-wires-okp hbhp-pwindow-scalar
               zp natp posp (:e expt) hbhp-p-times-1 (:t hbhp-chunk-scalar)
               nth (:e zp) (:e nfix) car-cons))

(defruled hbhp-pwindow-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (< (len bs) 189)
                (hbhp-pwindow-wires-okp bs ws ex ey asg)
                (b* ((k (hbhp-pwindow-k bs))
                     (tl (nthcdr (* 3 k) bs))
                     (full (take (* 3 k) bs))
                     (r (nth k ws))
                     (pt (hbhp-gp (hbhp-pwindow-scalar bs asg) g)))
                  (and (implies (not (zp k))
                                (and (hbhp-window-canon full ws g ex ey asg)
                                     (hbhp-mont-canon
                                      (hbhp-gp (hbhp-steps-scalar full 0 asg) g)
                                      (hbhp-gp (* (hbhp-pc tl) (expt 16 k)) g)
                                      (nth 2 r) (nth 3 r) (nth 4 r))))
                       (hbhp-pchunk-canon tl (nth 0 r) (nth 1 r) (hbhp-tab-y g k))
                       (equal (hbhp-lk ex) (hbhp-x pt))
                       (equal (hbhp-lk ey) (hbhp-y pt)))))
           (r1cs::r1cs-constraints-holdp
            (hbhp-pwindow-gadget bs ws g ex ey p) asg p))
  :use (hbhp-pwindow-k-facts
        (:instance hbhp-pwin0-complete
                   (tl (nthcdr (* 3 (hbhp-pwindow-k bs)) bs)) (r (car ws)))
        (:instance hbhp-pwink-complete
                   (full (take (* 3 (hbhp-pwindow-k bs)) bs))
                   (tl (nthcdr (* 3 (hbhp-pwindow-k bs)) bs))
                   (k (hbhp-pwindow-k bs))))
  :in-theory '(hbhp-pwindow-gadget hbhp-pwindow-wires-okp hbhp-pwindow-scalar
               zp natp posp (:e expt) hbhp-p-times-1 (:t hbhp-chunk-scalar)
               nth (:e zp) (:e nfix) car-cons))
