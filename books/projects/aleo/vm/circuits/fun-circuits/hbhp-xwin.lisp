; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first iteration of BHP::hash_uncompressed when the input starts with
; one constant true bit followed by variable bits (PathHash::hash_children).
; The 252 constant domain/length bits end on a chunk boundary, so the chunk
; at position c of window m is [true, v0, v1].  snarkVM folds it:
;
;   bit_0 is the constant 1 and true AND v0 is v0 itself (no constraint), so
;   montgomery_x = x0 + (x1 - x0) + v0 (x2 - x0) + v0 (x3 - x2 - x1 + x0),
;   the lookup linear combination with b0 = the constant 1 and b01 = v0;
;   the sign constraint (-2 y) * (v1 - 1/2) = montgomery_y remains.
;
; The accumulator entering it is the constant (Cu, Cv) of the constant
; chunks of window m, so montgomery_add takes Cu, Cv as `this'.  The rest
; of window m is ordinary variable chunks starting from that sum.  Here the
; variable part of window m is always full (hash_children has 506 variable
; bits), so no padding arises in it.

(in-package "ALEOVM")

(include-book "hbhp-iter0")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The mixed chunk [true, b1, b2].

(defmacro hbhp-xlc (b1 tab)
  `(hbhp-lookup-lc 1 ,b1 ,b1 ,tab p))

(define hbhp-xchunk-gadget ((b1 symbolp) (b2 symbolp) (my symbolp) ty (p posp))
  :verify-guards nil
  :short "The constraint of the mixed chunk: only the sign constraint."
  (list (r1cs::make-r1cs-constraint
         :a (hbhp-sv-scale (pfield::neg 2 p) (hbhp-lookup-lc 1 b1 b1 ty p) p)
         :b (list (list 1 b2) (list (pfield::neg (hbhp-half) p) 1))
         :c (list (list 1 my)))))

(defruled hbhp-xlc-value
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-fep4p tab p)
                (hbhp-wire-okp b1) (bitp (hbhp-lk b1)))
           (equal (r1cs::dot-product (hbhp-xlc b1 tab) asg p)
                  (hbhp-sel4 tab 1 (hbhp-lk b1))))
  :enable (hbhp-lookup-lc hbhp-sel4 hbhp-fep4p hbhp-dot-cons hbhp-dot-nil bitp
           hbhp-base-prime-facts)
  :cases ((equal (hbhp-lk b1) 0) (equal (hbhp-lk b1) 1)))

(defruled hbhp-xchunk-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b1) (hbhp-wire-okp b2) (hbhp-wire-okp my))
           (equal (r1cs::r1cs-constraints-holdp
                   (hbhp-xchunk-gadget b1 b2 my ty p) asg p)
                  (equal (pfield::mul
                          (pfield::mul (pfield::neg 2 p)
                                       (r1cs::dot-product (hbhp-xlc b1 ty) asg p)
                                       p)
                          (pfield::add (hbhp-lk b2) (pfield::neg (hbhp-half) p) p)
                          p)
                         (hbhp-lk my))))
  :in-theory '(hbhp-xchunk-gadget r1cs::r1cs-constraint-holdsp
               r1cs::r1cs-constraints-holdp
               r1cs::r1cs-constraint->a-of-r1cs-constraint
               r1cs::r1cs-constraint->b-of-r1cs-constraint
               r1cs::r1cs-constraint->c-of-r1cs-constraint
               hbhp-base-prime-facts r1cs::fep-of-lookup-equal
               hbhp-dot-cons hbhp-dot-nil hbhp-x-simple-field
               hbhp-dot-product-of-sv-scale
               pfield::fep-of-neg pfield::fep-of-mul pfield::fep-of-add
               r1cs::fep-of-dot-product
               car-cons cdr-cons (:e equal) endp atom)
  :prep-lemmas
  ((defruled hbhp-x-simple-field
     (implies (equal p (base-prime))
              (and (equal (mod 1 p) 1)
                   (implies (pfield::fep x p)
                            (and (equal (pfield::mul 1 x p) x)
                                 (equal (pfield::mul x 1 p) x)
                                 (equal (pfield::add x 0 p) x)
                                 (equal (mod x p) x)))))
     :enable hbhp-base-prime-facts)))

(defruled hbhp-x-fep-of-sel4
  (implies (hbhp-fep4p tab p)
           (pfield::fep (hbhp-sel4 tab b0 b1) p))
  :enable (hbhp-sel4 hbhp-fep4p acl2::bfix))

(defruled hbhp-x-sign-lemma
  (implies (and (equal p (base-prime))
                (pfield::fep y p) (bitp b))
           (equal (pfield::mul (pfield::mul (pfield::neg 2 p) y p)
                               (pfield::add b (pfield::neg (hbhp-half) p) p)
                               p)
                  (if (equal b 1) (pfield::neg y p) y)))
  :use (hbhp-half-facts hbhp-x-two-half-y)
  :enable (bitp hbhp-base-prime-facts)
  :disable ((:e hbhp-half))
  :prep-lemmas
  ((defruled hbhp-x-two-half-y
     (implies (and (equal p (base-prime)) (pfield::fep y p))
              (equal (pfield::mul 2 (pfield::mul (hbhp-half) y p) p) y))
     :use (hbhp-half-facts
           (:instance pfield::mul-associative
                      (pfield::x 2) (pfield::y (hbhp-half)) (pfield::z y)
                      (pfield::p p)))
     :in-theory '(hbhp-base-prime-facts pfield::mul-of-1-arg1))))

(defmacro hbhp-xmy (b1 b2 ty)
  `(if (equal (hbhp-lk ,b2) 1)
       (pfield::neg (hbhp-sel4 ,ty 1 (hbhp-lk ,b1)) p)
     (hbhp-sel4 ,ty 1 (hbhp-lk ,b1))))

(defruled hbhp-xchunk-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b1) (hbhp-wire-okp b2) (hbhp-wire-okp my)
                (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
                (hbhp-fep4p tx p) (hbhp-fep4p ty p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-xchunk-gadget b1 b2 my ty p) asg p))
           (and (equal (r1cs::dot-product (hbhp-xlc b1 tx) asg p)
                       (hbhp-sel4 tx 1 (hbhp-lk b1)))
                (equal (hbhp-lk my) (hbhp-xmy b1 b2 ty))))
  :use (hbhp-xchunk-to-eqns
        (:instance hbhp-xlc-value (tab tx))
        (:instance hbhp-xlc-value (tab ty))
        (:instance hbhp-x-fep-of-sel4 (tab ty) (b0 1) (b1 (hbhp-lk b1)))
        (:instance hbhp-x-sign-lemma
                   (y (hbhp-sel4 ty 1 (hbhp-lk b1))) (b (hbhp-lk b2))))
  :in-theory '(hbhp-base-prime-facts))

(defruled hbhp-xchunk-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp b1) (hbhp-wire-okp b2) (hbhp-wire-okp my)
                (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
                (hbhp-fep4p ty p)
                (equal (hbhp-lk my) (hbhp-xmy b1 b2 ty)))
           (r1cs::r1cs-constraints-holdp
            (hbhp-xchunk-gadget b1 b2 my ty p) asg p))
  :use (hbhp-xchunk-to-eqns
        (:instance hbhp-xlc-value (tab ty))
        (:instance hbhp-x-fep-of-sel4 (tab ty) (b0 1) (b1 (hbhp-lk b1)))
        (:instance hbhp-x-sign-lemma
                   (y (hbhp-sel4 ty 1 (hbhp-lk b1))) (b (hbhp-lk b2))))
  :in-theory '(hbhp-base-prime-facts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The mixed chunk added into the accumulator s G at position j.

(defmacro hbhp-xstep-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (natp j) (<= 1 j) (<= j 62)
        (hbhp-acc-okp s j)
        (hbhp-wire-okp b1) (hbhp-wire-okp b2)
        (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
        (hbhp-wire-okp my)
        (hbhp-wire-okp lam) (hbhp-wire-okp u3) (hbhp-wire-okp v3)
        (equal (hbhp-dot u1) (hbhp-mu (hbhp-gp s g)))
        (equal (hbhp-dot v1) (hbhp-mv (hbhp-gp s g)))))

(defmacro hbhp-xstep-cc ()
  '(* (hbhp-chunk-scalar 1 (hbhp-lk b1) (hbhp-lk b2)) (expt 16 j)))

(defruled hbhp-xstep-sound
  (implies (and (hbhp-xstep-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-xchunk-gadget b1 b2 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1 (hbhp-xlc b1 (hbhp-tab-x g j))
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p))
           (b* ((s2 (+ s (hbhp-xstep-cc))))
             (and (equal (hbhp-mu (hbhp-gp s2 g)) (hbhp-lk u3))
                  (equal (hbhp-mv (hbhp-gp s2 g)) (hbhp-lk v3))
                  (hbhp-acc-okp s2 (+ 1 j)))))
  :use ((:instance hbhp-xchunk-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
        (:instance hbhp-tab-fep4p)
        (:instance hbhp-chunk-point (b0 1) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-chunk-scalar-range
                   (b0 1) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-window-step-points
                   (c (hbhp-chunk-scalar 1 (hbhp-lk b1) (hbhp-lk b2))))
        (:instance hbhp-mont-add-gadget-to-eqns
                   (u2 (hbhp-xlc b1 (hbhp-tab-x g j)))
                   (v2 (list (list 1 my))))
        (:instance hbhp-dot-one-wire (w my))
        (:instance hbhp-mont-add-sound
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (hbhp-xstep-cc) g))
                   (lam (hbhp-lk lam)) (u3 (hbhp-lk u3)) (v3 (hbhp-lk v3))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal (:e bitp)))

(defruled hbhp-xstep-complete
  (implies (and (hbhp-xstep-hyps)
                (equal (hbhp-lk my) (hbhp-xmy b1 b2 (hbhp-tab-y g j)))
                (hbhp-mont-canon (hbhp-gp s g) (hbhp-gp (hbhp-xstep-cc) g)
                                 lam u3 v3))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-xchunk-gadget b1 b2 my (hbhp-tab-y g j) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget u1 v1 (hbhp-xlc b1 (hbhp-tab-x g j))
                                       (list (list 1 my))
                                       lam u3 v3 p)
                 asg p)))
  :use ((:instance hbhp-xchunk-complete (ty (hbhp-tab-y g j)))
        (:instance hbhp-xchunk-sound (tx (hbhp-tab-x g j)) (ty (hbhp-tab-y g j)))
        (:instance hbhp-tab-fep4p)
        (:instance hbhp-chunk-point (b0 1) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-chunk-scalar-range
                   (b0 1) (b1 (hbhp-lk b1)) (b2 (hbhp-lk b2)))
        (:instance hbhp-window-step-points
                   (c (hbhp-chunk-scalar 1 (hbhp-lk b1) (hbhp-lk b2))))
        (:instance hbhp-mont-add-gadget-to-eqns
                   (u2 (hbhp-xlc b1 (hbhp-tab-x g j)))
                   (v2 (list (list 1 my))))
        (:instance hbhp-dot-one-wire (w my))
        (:instance hbhp-mont-add-complete
                   (p1 (hbhp-gp s g))
                   (p2 (hbhp-gp (hbhp-xstep-cc) g))))
  :in-theory '(hbhp-base-prime-facts r1cs::fep-of-lookup-equal (:e bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The variable part of the straddling window: vb = (b1 b2 . full), with
;; full a whole number of chunks.  (car ws) = (- my lam u3 v3) are the wires
;; of the mixed chunk, (cdr ws) those of the chunks of full.

(define hbhp-xwindow-gadget (vb ws g (c natp) cu cv (ex symbolp) (ey symbolp)
                                (p posp))
  :verify-guards nil
  (b* ((r (car ws))
       (j (lnfix c))
       (u1 (list (list 1 (nth 3 r))))
       (v1 (list (list 1 (nth 4 r))))
       (out (hbhp-window-steps-out (nthcdr 2 vb) (cdr ws) u1 v1)))
    (append (hbhp-xchunk-gadget (nth 0 vb) (nth 1 vb) (nth 1 r) (hbhp-tab-y g j) p)
            (hbhp-mont-add-gadget (list (list cu 1)) (list (list cv 1))
                                  (hbhp-lookup-lc 1 (nth 0 vb) (nth 0 vb)
                                                  (hbhp-tab-x g j) p)
                                  (list (list 1 (nth 1 r)))
                                  (nth 2 r) (nth 3 r) (nth 4 r) p)
            (hbhp-window-steps (nthcdr 2 vb) (cdr ws) g (+ 1 j) u1 v1 p)
            (hbhp-to-edwards-gadget (car out) (cdr out) ex ey p))))

(define hbhp-xwindow-wires-okp (vb ws ex ey asg)
  :verify-guards nil
  (b* ((r (car ws)))
    (and (hbhp-wire-okp (nth 0 vb)) (hbhp-wire-okp (nth 1 vb))
         (bitp (hbhp-lk (nth 0 vb))) (bitp (hbhp-lk (nth 1 vb)))
         (hbhp-wire-okp (nth 1 r)) (hbhp-wire-okp (nth 2 r))
         (hbhp-wire-okp (nth 3 r)) (hbhp-wire-okp (nth 4 r))
         (hbhp-steps-wires-okp (nthcdr 2 vb) (cdr ws) asg)
         (hbhp-wire-okp ex) (hbhp-wire-okp ey))))

(define hbhp-xwindow-scalar (vb (c natp) asg)
  :verify-guards nil
  (+ (* (hbhp-chunk-scalar 1 (hbhp-lk (nth 0 vb)) (hbhp-lk (nth 1 vb)))
        (expt 16 (lnfix c)))
     (hbhp-steps-scalar (nthcdr 2 vb) (+ 1 (lnfix c)) asg)))

(defmacro hbhp-xwindow-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (natp c) (<= 1 c) (<= c 62)
        (<= (+ c 1 (hbhp-nchunks (nthcdr 2 vb))) 63)
        (hbhp-acc-okp sc c)
        (equal cu (hbhp-mu (hbhp-gp sc g)))
        (equal cv (hbhp-mv (hbhp-gp sc g)))
        (hbhp-xwindow-wires-okp vb ws ex ey asg)))

(defruledl hbhp-x-fep-mu-mv
  (and (pfield::fep (hbhp-mu pt) (base-prime))
       (pfield::fep (hbhp-mv pt) (base-prime)))
  :use hbhp-base-prime-facts
  :in-theory '(hbhp-mu hbhp-mv pfield::fep-of-div))

(defmacro hbhp-x-r () '(car ws))
(defmacro hbhp-x-cc ()
  '(* (hbhp-chunk-scalar 1 (hbhp-lk (nth 0 vb)) (hbhp-lk (nth 1 vb))) (expt 16 c)))
(defmacro hbhp-x-s1 () '(+ sc (hbhp-x-cc)))
(defmacro hbhp-x-u1 () '(list (list 1 (nth 3 (hbhp-x-r)))))
(defmacro hbhp-x-v1 () '(list (list 1 (nth 4 (hbhp-x-r)))))
(defmacro hbhp-x-out ()
  '(hbhp-window-steps-out (nthcdr 2 vb) (cdr ws) (hbhp-x-u1) (hbhp-x-v1)))
(defmacro hbhp-x-s2 () '(+ (hbhp-x-s1) (hbhp-steps-scalar (nthcdr 2 vb) (+ 1 c) asg)))

(defun hbhp-x-step-uses (thm)
  (declare (xargs :guard t :mode :program))
  `((:instance ,thm
               (b1 (nth 0 vb)) (b2 (nth 1 vb)) (j c) (s sc)
               (u1 (list (list cu 1))) (v1 (list (list cv 1)))
               (my (nth 1 (hbhp-x-r))) (lam (nth 2 (hbhp-x-r)))
               (u3 (nth 3 (hbhp-x-r))) (v3 (nth 4 (hbhp-x-r))))
    (:instance hbhp-x-fep-mu-mv (pt (hbhp-gp sc g)))
    (:instance hbhp-dot-const (x cu))
    (:instance hbhp-dot-const (x cv))
    (:instance hbhp-dot-one-wire (w (nth 3 (hbhp-x-r))))
    (:instance hbhp-dot-one-wire (w (nth 4 (hbhp-x-r))))))

(make-event
 `(defruled hbhp-xwindow-sound
    (implies (and (hbhp-xwindow-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-xwindow-gadget vb ws g c cu cv ex ey p) asg p))
             (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                    (hbhp-gp (+ sc (hbhp-xwindow-scalar vb c asg)) g)))
    :use (,@(hbhp-x-step-uses 'hbhp-xstep-sound)
          (:instance hbhp-window-steps-sound
                     (bs (nthcdr 2 vb)) (ws (cdr ws)) (j (+ 1 c)) (s (hbhp-x-s1))
                     (u1 (hbhp-x-u1)) (v1 (hbhp-x-v1)))
          (:instance hbhp-edwards-final-sound
                     (s (hbhp-x-s2)) (j (+ 1 c (hbhp-nchunks (nthcdr 2 vb))))
                     (u (car (hbhp-x-out))) (v (cdr (hbhp-x-out)))))
    :in-theory '(hbhp-xwindow-gadget hbhp-xwindow-wires-okp hbhp-xwindow-scalar
                 r1cs::r1cs-constraints-holdp-of-append
                 hbhp-base-prime-facts hbhp-m-plus-assoc
                 natp lnfix nfix (:t hbhp-nchunks))))

(define hbhp-xwindow-canon (vb ws g (c natp) sc ex ey asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (r (car ws))
       (j (lnfix c))
       (cc (* (hbhp-chunk-scalar 1 (hbhp-lk (nth 0 vb)) (hbhp-lk (nth 1 vb)))
              (expt 16 j)))
       (pt (hbhp-gp (+ sc (hbhp-xwindow-scalar vb c asg)) g)))
    (and (equal (hbhp-lk (nth 1 r)) (hbhp-xmy (nth 0 vb) (nth 1 vb) (hbhp-tab-y g j)))
         (hbhp-mont-canon (hbhp-gp sc g) (hbhp-gp cc g) (nth 2 r) (nth 3 r) (nth 4 r))
         (hbhp-steps-canon (nthcdr 2 vb) (cdr ws) g (+ 1 j) (+ sc cc) asg)
         (equal (hbhp-lk ex) (hbhp-x pt))
         (equal (hbhp-lk ey) (hbhp-y pt)))))

(make-event
 `(defruled hbhp-xwindow-complete
    (implies (and (hbhp-xwindow-hyps)
                  (hbhp-xwindow-canon vb ws g c sc ex ey asg))
             (r1cs::r1cs-constraints-holdp
              (hbhp-xwindow-gadget vb ws g c cu cv ex ey p) asg p))
    :use (,@(hbhp-x-step-uses 'hbhp-xstep-sound)
          ,@(hbhp-x-step-uses 'hbhp-xstep-complete)
          (:instance hbhp-window-steps-sound
                     (bs (nthcdr 2 vb)) (ws (cdr ws)) (j (+ 1 c)) (s (hbhp-x-s1))
                     (u1 (hbhp-x-u1)) (v1 (hbhp-x-v1)))
          (:instance hbhp-window-steps-complete
                     (bs (nthcdr 2 vb)) (ws (cdr ws)) (j (+ 1 c)) (s (hbhp-x-s1))
                     (u1 (hbhp-x-u1)) (v1 (hbhp-x-v1)))
          (:instance hbhp-edwards-final-complete
                     (s (hbhp-x-s2)) (j (+ 1 c (hbhp-nchunks (nthcdr 2 vb))))
                     (u (car (hbhp-x-out))) (v (cdr (hbhp-x-out)))))
    :in-theory '(hbhp-xwindow-gadget hbhp-xwindow-wires-okp hbhp-xwindow-scalar
                 hbhp-xwindow-canon
                 r1cs::r1cs-constraints-holdp-of-append
                 hbhp-base-prime-facts hbhp-m-plus-assoc
                 natp lnfix nfix (:t hbhp-nchunks))))

(defruled hbhp-xwindow-scalar-is-spec
  (implies (and (natp c) (consp (cdr vb)))
           (equal (hbhp-window-scalar (cons 1 (hbhp-lk-list vb asg)) c)
                  (hbhp-xwindow-scalar vb c asg)))
  :expand ((:free (a b l) (hbhp-window-scalar (list* 1 a b l) c))
           (hbhp-lk-list vb asg) (hbhp-lk-list (cdr vb) asg))
  :use ((:instance hbhp-steps-scalar-is-window-scalar (bs (nthcdr 2 vb)) (j (+ 1 c)))
        (:instance hbhp-nthcdr-of-lk-list (bs vb) (n 2)))
  :in-theory '(hbhp-xwindow-scalar natp lnfix nfix len nthcdr nth car-cons cdr-cons
               (:e nfix) (:e zp) (:e binary-+) (:e <) hbhp-x-nthcdr-2
               hbhp-x-len-ge-3 (:t len))
  :prep-lemmas
  ((defruled hbhp-x-nthcdr-2
     (equal (nthcdr 2 x) (cddr x)))
   (defruled hbhp-x-len-ge-3
     (not (< (len (list* a b c l)) 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The first iteration on cbits ++ [true] ++ vb.  As in hbhp-iter0, the m
;; constant windows fold natively into A and the straddling window m is
;; added to A by Group::add (or replaces it when A is zero), but window m
;; now begins with the mixed chunk: its variable part is the first
;; 3(w - c) - 1 wires of vb.  The rest of vb is non-empty (always so for
;; hash_children) and is hashed by hbhp-rest-full-gadget.

(defmacro hbhp-x0-nv () '(- (* 3 (- w c)) 1))
(defmacro hbhp-x0-vm () '(take (hbhp-x0-nv) vb))
(defmacro hbhp-x0-vr () '(nthcdr (hbhp-x0-nv) vb))
(defmacro hbhp-x0-x ()
  '(hbhp-gp (+ (hbhp-window-scalar (hbhp-i0-cm) 0)
               (hbhp-window-scalar (cons 1 (hbhp-lk-list (hbhp-x0-vm) asg)) c))
            (hbhp-i0-g)))

(define hbhp-iterx-gadget (cbits vb wins gens w m c (p posp))
  :verify-guards nil
  (append (hbhp-xwindow-gadget (hbhp-x0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                               (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                               (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p)
          (if (hbhp-i0-zp)
              nil
            (hbhp-kadd-gadget (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r))
                              (ecurve::point-finite->x (hbhp-i0-a))
                              (ecurve::point-finite->y (hbhp-i0-a))
                              (nth 3 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))
                              (nth 5 (hbhp-i0-r)) p))
          (hbhp-rest-full-gadget (hbhp-x0-vr) (cdr wins) (nthcdr (+ 1 m) gens)
                                 w (hbhp-i0-xacc) (hbhp-i0-yacc) p)))

(define hbhp-iterx-out (cbits vb wins gens w m c)
  :verify-guards nil
  (hbhp-rest-full-out (hbhp-x0-vr) (cdr wins) (nthcdr (+ 1 m) gens)
                      w (hbhp-i0-xacc) (hbhp-i0-yacc)))

(define hbhp-iterx-wires-okp (cbits vb wins gens w m c asg)
  :verify-guards nil
  (and (hbhp-xwindow-wires-okp (hbhp-x0-vm) (nth 0 (hbhp-i0-r))
                               (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) asg)
       (or (hbhp-i0-zp)
           (and (hbhp-wire-okp (nth 3 (hbhp-i0-r)))
                (hbhp-wire-okp (nth 4 (hbhp-i0-r)))
                (hbhp-wire-okp (nth 5 (hbhp-i0-r)))))
       (hbhp-rest-full-wires-okp (hbhp-x0-vr) (cdr wins)
                                 (nthcdr (+ 1 m) gens) w
                                 (hbhp-i0-xacc) (hbhp-i0-yacc) asg)))

(define hbhp-iterx-canon (cbits vb wins gens w m c asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
       (s (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x))))
    (and (hbhp-xwindow-canon (hbhp-x0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c sc
                             (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) asg)
         (or (hbhp-i0-zp)
             (hbhp-kadd-canon (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r))
                              (ecurve::point-finite->x (hbhp-i0-a))
                              (ecurve::point-finite->y (hbhp-i0-a))
                              (nth 3 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))
                              (nth 5 (hbhp-i0-r)) s))
         (hbhp-rest-full-canon (hbhp-x0-vr) (cdr wins)
                               (nthcdr (+ 1 m) gens) w
                               (hbhp-i0-xacc) (hbhp-i0-yacc) s asg))))

(defmacro hbhp-iterx-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
        (posp w) (<= w 63) (natp m) (natp c) (<= 1 c) (< c w)
        (bit-listp cbits) (equal (len cbits) (+ (* 3 w m) (* 3 c)))
        (< (hbhp-x0-nv) (len vb)) (< m (len gens))
        (<= (+ (len cbits) 1 (len vb)) (* 3 w (len gens)))
        (hbhp-iterx-wires-okp cbits vb wins gens w m c asg)))

(defruledl hbhp-x0-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(defruledl hbhp-x0-nums
  (implies (and (posp w) (<= w 63) (natp m) (natp c) (<= 1 c) (< c w))
           (and (natp (* 3 w m)) (natp (- (* 3 (- w c)) 1))
                (natp (- (- w c) 1))
                (<= 2 (- (* 3 (- w c)) 1))
                (equal (- (- (* 3 (- w c)) 1) 2) (* 3 (- (- w c) 1)))
                (equal (+ c 1 (- (- w c) 1)) w)
                (equal (+ 1 (- (* 3 (- w c)) 1)) (* 3 (- w c)))
                (<= c 62) (<= 3 (* 3 c))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-x0-consp-cdr
  (implies (<= 2 (len x)) (consp (cdr x))))

(defruled hbhp-x0-window-sound
  (implies (and (hbhp-iterx-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-xwindow-gadget (hbhp-x0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                                      (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                                      (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p)
                 asg p))
           (and (equal (ecurve::point-finite (hbhp-lk (nth 1 (hbhp-i0-r)))
                                             (hbhp-lk (nth 2 (hbhp-i0-r))))
                       (hbhp-x0-x))
                (ecurve::edwards-bls12-pointp (hbhp-x0-x))))
  :use ((:instance hbhp-gen-okp-of-nth (q m))
        (:instance hbhp-cwin-start-correct (bits (hbhp-i0-cm)) (g (hbhp-i0-g)))
        (:instance hbhp-nchunks-of-3k (x (hbhp-i0-cm)) (k c))
        (:instance hbhp-nchunks-of-3k (x (nthcdr 2 (hbhp-x0-vm))) (k (- (- w c) 1)))
        (:instance hbhp-x0-len-of-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-x0-len-of-nthcdr (x (hbhp-x0-vm)) (n 2))
        (:instance hbhp-i-bit-listp-nthcdr (x cbits) (n (* 3 w m)))
        hbhp-x0-nums
        (:instance hbhp-ph-len-of-take (n (hbhp-x0-nv)) (x vb))
        (:instance hbhp-x0-consp-cdr (x (hbhp-x0-vm)))
        (:instance hbhp-xwindow-sound
                   (vb (hbhp-x0-vm)) (ws (nth 0 (hbhp-i0-r))) (g (hbhp-i0-g))
                   (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
                   (cu (car (hbhp-i0-cuv))) (cv (cdr (hbhp-i0-cuv)))
                   (ex (nth 1 (hbhp-i0-r))) (ey (nth 2 (hbhp-i0-r))))
        (:instance hbhp-xwindow-scalar-is-spec (vb (hbhp-x0-vm)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar
                    (+ (hbhp-window-scalar (hbhp-i0-cm) 0)
                       (hbhp-window-scalar (cons 1 (hbhp-lk-list (hbhp-x0-vm) asg)) c)))
                   (point (hbhp-i0-g)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (hbhp-i0-g))))
  :in-theory '(hbhp-iterx-wires-okp natp posp nfix car-cons cdr-cons (:t len)))

(defruledl hbhp-x0-pointp-zero
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero))
  :use hbhp-pointp-of-zero
  :in-theory '((:e ecurve::twisted-edwards-zero)))

(defruled hbhp-x0-a-is-spec
  (implies (hbhp-iterx-hyps)
           (and (equal (hbhp-i0-a)
                       (hbhp-hasher-sum (take (* 3 w m) cbits) gens w
                                        (ecurve::twisted-edwards-zero)))
                (ecurve::edwards-bls12-pointp (hbhp-i0-a))))
  :use ((:instance hbhp-cfold-correct
                   (bits (take (* 3 w m) cbits)) (q m)
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-i-bit-listp-take (x cbits) (n (* 3 w m)))
        (:instance hbhp-ph-len-of-take (x cbits) (n (* 3 w m)))
        (:instance hbhp-pointp-of-hasher-sum
                   (bits (take (* 3 w m) cbits))
                   (acc (ecurve::twisted-edwards-zero)))
        hbhp-x0-nums
        hbhp-x0-pointp-zero)
  :in-theory '(natp posp nfix))

(defmacro hbhp-x0-xw-gadget ()
  '(hbhp-xwindow-gadget (hbhp-x0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                        (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                        (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p))

(defruled hbhp-x0-acc-point
  (implies (and (hbhp-iterx-hyps)
                (r1cs::r1cs-constraints-holdp (hbhp-x0-xw-gadget) asg p)
                (or (hbhp-i0-zp)
                    (r1cs::r1cs-constraints-holdp (hbhp-i0-k-gadget) asg p)))
           (and (equal (ecurve::point-finite (hbhp-lk (hbhp-i0-xacc))
                                             (hbhp-lk (hbhp-i0-yacc)))
                       (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x)))
                (ecurve::edwards-bls12-pointp
                 (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x)))
                (hbhp-wire-okp (hbhp-i0-xacc)) (hbhp-wire-okp (hbhp-i0-yacc))))
  :use (hbhp-x0-window-sound hbhp-x0-a-is-spec
        (:instance hbhp-add-zero-left (pt (hbhp-x0-x)))
        (:instance hbhp-kadd-sound
                   (acc (hbhp-i0-a)) (pt (hbhp-x0-x))
                   (cx (ecurve::point-finite->x (hbhp-i0-a)))
                   (cy (ecurve::point-finite->y (hbhp-i0-a)))
                   (x1 (nth 1 (hbhp-i0-r))) (y1 (nth 2 (hbhp-i0-r)))
                   (v01 (nth 3 (hbhp-i0-r))) (x3 (nth 4 (hbhp-i0-r)))
                   (y3 (nth 5 (hbhp-i0-r))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (hbhp-i0-a)) (ecurve::point2 (hbhp-x0-x))))
  :in-theory '(hbhp-iterx-wires-okp hbhp-xwindow-wires-okp))

(defruled hbhp-x0-acc-sound
  (implies (and (hbhp-iterx-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-iterx-gadget cbits vb wins gens w m c p) asg p))
           (and (equal (ecurve::point-finite (hbhp-lk (hbhp-i0-xacc))
                                             (hbhp-lk (hbhp-i0-yacc)))
                       (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x)))
                (ecurve::edwards-bls12-pointp
                 (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x)))
                (hbhp-wire-okp (hbhp-i0-xacc)) (hbhp-wire-okp (hbhp-i0-yacc))))
  :use hbhp-x0-acc-point
  :in-theory '(hbhp-iterx-gadget r1cs::r1cs-constraints-holdp-of-append))

;; The specification side: cbits = c0 ++ cm, then the true bit and l.

(defruledl hbhp-x0-take-cons
  (implies (posp n)
           (equal (take n (cons a x)) (cons a (take (- n 1) x))))
  :enable take)

(defruledl hbhp-x0-nthcdr-cons
  (implies (posp n)
           (equal (nthcdr n (cons a x)) (nthcdr (- n 1) x)))
  :enable nthcdr)

(defruledl hbhp-x0-spec-nums
  (implies (and (posp w) (natp c) (< c w) (natp ll) (< (- (* 3 (- w c)) 1) ll))
           (and (posp (* 3 (- w c)))
                (equal (min (* 3 (- w c)) (+ 1 ll)) (* 3 (- w c)))
                (equal (mod (+ 1 (- (* 3 (- w c)) 1)) 3) 0)
                (equal (nfix (- (* 3 (- w c)) 1)) (- (* 3 (- w c)) 1))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-x0-spec
  (implies (and (posp w) (natp m) (natp c) (<= 1 c) (< c w)
                (equal (len c0) (* 3 w m)) (equal (len cm) (* 3 c))
                (true-listp cm) (true-listp l)
                (< (- (* 3 (- w c)) 1) (len l))
                (< m (len gens)))
           (equal (hbhp-hasher-sum (hbhp-pad (append c0 cm (cons 1 l))) gens w acc)
                  (hbhp-hasher-sum
                   (hbhp-pad (nthcdr (- (* 3 (- w c)) 1) l)) (nthcdr (+ 1 m) gens) w
                   (ecurve::edwards-bls12-add
                    (hbhp-hasher-sum c0 gens w acc)
                    (ecurve::edwards-bls12-mul
                     (+ (hbhp-window-scalar cm 0)
                        (hbhp-window-scalar (cons 1 (take (- (* 3 (- w c)) 1) l)) c))
                     (nth m gens))))))
  :use ((:instance hbhp-iter0-spec (v (cons 1 l)))
        (:instance hbhp-pad-when-mod-3 (x (cons 1 (take (- (* 3 (- w c)) 1) l))))
        (:instance hbhp-x0-take-cons (n (* 3 (- w c))) (a 1) (x l))
        (:instance hbhp-x0-nthcdr-cons (n (* 3 (- w c))) (a 1) (x l))
        (:instance hbhp-x0-spec-nums (ll (len l)))
        (:instance hbhp-ph-len-of-take (n (- (* 3 (- w c)) 1)) (x l)))
  :in-theory '(len true-listp car-cons cdr-cons (:t len) natp posp
               hbhp-x0-true-listp-take)
  :prep-lemmas
  ((defruled hbhp-x0-true-listp-take
     (true-listp (take n x)))))

(defruledl hbhp-x0-nonzero-listp-of-nthcdr
  (implies (hbhp-nonzero-listp gens)
           (hbhp-nonzero-listp (nthcdr q gens)))
  :enable (nthcdr hbhp-nonzero-listp))

(defruledl hbhp-x0-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defruledl hbhp-x0-split-append
  (implies (<= (nfix f) (len x))
           (equal (append x l) (append (take f x) (nthcdr f x) l)))
  :use ((:instance hbhp-append-take-nthcdr (n f)))
  :in-theory '(hbhp-x0-append-assoc))

(defruledl hbhp-x0-true-listp-nthcdr
  (implies (true-listp x) (true-listp (nthcdr n x)))
  :enable nthcdr)

(defruledl hbhp-x0-true-listp-when-bit-listp
  (implies (bit-listp x) (true-listp x))
  :enable bit-listp)

(defruledl hbhp-x0-len-arith
  (implies (and (posp w) (natp m) (natp c) (< c w) (natp lg) (natp lv)
                (<= (+ (* 3 w m) (* 3 c) 1 lv) (* 3 w lg))
                (< (- (* 3 (- w c)) 1) lv))
           (<= (- lv (- (* 3 (- w c)) 1)) (* 3 w (- lg (+ 1 m)))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defun hbhp-x0-rest-uses ()
  (declare (xargs :guard t :mode :program))
  '((:instance hbhp-r-point-listp-of-nthcdr (q (+ 1 m)))
    (:instance hbhp-x0-nonzero-listp-of-nthcdr (q (+ 1 m)))
    (:instance hbhp-x0-len-of-nthcdr (x vb) (n (hbhp-x0-nv)))
    (:instance hbhp-x0-len-of-nthcdr (x gens) (n (+ 1 m)))
    (:instance hbhp-x0-len-arith (lg (len gens)) (lv (len vb)))
    hbhp-x0-nums))

(make-event
 `(defruled hbhp-iterx-sound
    (implies (and (hbhp-iterx-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-iterx-gadget cbits vb wins gens w m c p) asg p))
             (b* ((out (hbhp-iterx-out cbits vb wins gens w m c)))
               (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                      (hbhp-hasher-sum
                       (hbhp-pad (append cbits (cons 1 (hbhp-lk-list vb asg))))
                       gens w (ecurve::twisted-edwards-zero)))))
    :use ((:instance hbhp-x0-split-append (f (* 3 w m)) (x cbits)
                     (l (cons 1 (hbhp-lk-list vb asg))))
          (:instance hbhp-x0-spec
                     (c0 (take (* 3 w m) cbits)) (cm (hbhp-i0-cm))
                     (l (hbhp-lk-list vb asg)) (acc (ecurve::twisted-edwards-zero)))
          (:instance hbhp-ph-len-of-take (x cbits) (n (* 3 w m)))
          (:instance hbhp-x0-len-of-nthcdr (x cbits) (n (* 3 w m)))
          (:instance hbhp-x0-true-listp-nthcdr (x cbits) (n (* 3 w m)))
          (:instance hbhp-true-listp-of-lk-list (bs vb))
          (:instance hbhp-take-of-lk-list (bs vb) (n (hbhp-x0-nv)))
          (:instance hbhp-nthcdr-of-lk-list (bs vb) (n (hbhp-x0-nv)))
          hbhp-x0-a-is-spec hbhp-x0-acc-sound
          (:instance hbhp-rest-full-sound
                     (bits (hbhp-x0-vr)) (wins (cdr wins))
                     (gens (nthcdr (+ 1 m) gens))
                     (xacc (hbhp-i0-xacc)) (yacc (hbhp-i0-yacc))
                     (acc (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x))))
          ,@(hbhp-x0-rest-uses))
    :in-theory '(hbhp-iterx-out hbhp-iterx-wires-okp hbhp-iterx-gadget
                 r1cs::r1cs-constraints-holdp-of-append
                 natp posp nfix car-cons cdr-cons
                 hbhp-len-of-lk-list hbhp-x0-true-listp-when-bit-listp (:t len))))

(defruled hbhp-x0-window-complete
  (implies (and (hbhp-iterx-hyps)
                (hbhp-iterx-canon cbits vb wins gens w m c asg))
           (r1cs::r1cs-constraints-holdp (hbhp-x0-xw-gadget) asg p))
  :use ((:instance hbhp-gen-okp-of-nth (q m))
        (:instance hbhp-cwin-start-correct (bits (hbhp-i0-cm)) (g (hbhp-i0-g)))
        (:instance hbhp-nchunks-of-3k (x (hbhp-i0-cm)) (k c))
        (:instance hbhp-nchunks-of-3k (x (nthcdr 2 (hbhp-x0-vm))) (k (- (- w c) 1)))
        (:instance hbhp-x0-len-of-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-x0-len-of-nthcdr (x (hbhp-x0-vm)) (n 2))
        (:instance hbhp-i-bit-listp-nthcdr (x cbits) (n (* 3 w m)))
        hbhp-x0-nums
        (:instance hbhp-ph-len-of-take (n (hbhp-x0-nv)) (x vb))
        (:instance hbhp-xwindow-complete
                   (vb (hbhp-x0-vm)) (ws (nth 0 (hbhp-i0-r))) (g (hbhp-i0-g))
                   (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
                   (cu (car (hbhp-i0-cuv))) (cv (cdr (hbhp-i0-cuv)))
                   (ex (nth 1 (hbhp-i0-r))) (ey (nth 2 (hbhp-i0-r)))))
  :in-theory '(hbhp-iterx-wires-okp hbhp-iterx-canon natp posp nfix
               car-cons cdr-cons (:t len)))

(defruled hbhp-x0-kadd-complete
  (implies (and (hbhp-iterx-hyps)
                (hbhp-iterx-canon cbits vb wins gens w m c asg)
                (not (hbhp-i0-zp)))
           (r1cs::r1cs-constraints-holdp (hbhp-i0-k-gadget) asg p))
  :use (hbhp-x0-window-complete hbhp-x0-window-sound hbhp-x0-a-is-spec
        (:instance hbhp-kadd-complete
                   (acc (hbhp-i0-a)) (pt (hbhp-x0-x))
                   (cx (ecurve::point-finite->x (hbhp-i0-a)))
                   (cy (ecurve::point-finite->y (hbhp-i0-a)))
                   (x1 (nth 1 (hbhp-i0-r))) (y1 (nth 2 (hbhp-i0-r)))
                   (v01 (nth 3 (hbhp-i0-r))) (x3 (nth 4 (hbhp-i0-r)))
                   (y3 (nth 5 (hbhp-i0-r)))))
  :in-theory '(hbhp-iterx-wires-okp hbhp-xwindow-wires-okp hbhp-iterx-canon))

(defruledl hbhp-x0-holdp-nil
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(make-event
 `(defruled hbhp-iterx-complete
    (implies (and (hbhp-iterx-hyps)
                  (hbhp-iterx-canon cbits vb wins gens w m c asg))
             (r1cs::r1cs-constraints-holdp
              (hbhp-iterx-gadget cbits vb wins gens w m c p) asg p))
    :use (hbhp-x0-window-complete hbhp-x0-kadd-complete hbhp-x0-acc-point
          (:instance hbhp-rest-full-complete
                     (bits (hbhp-x0-vr)) (wins (cdr wins))
                     (gens (nthcdr (+ 1 m) gens))
                     (xacc (hbhp-i0-xacc)) (yacc (hbhp-i0-yacc))
                     (acc (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-x0-x))))
          ,@(hbhp-x0-rest-uses))
    :in-theory '(hbhp-iterx-gadget r1cs::r1cs-constraints-holdp-of-append
                 hbhp-iterx-canon hbhp-iterx-wires-okp hbhp-x0-holdp-nil
                 natp posp nfix (:t len))))
