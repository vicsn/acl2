; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Poseidon::hash_to_group (circuit/algorithms/src/poseidon/hash_to_group.rs):
; [h0, h1] = hash_many(input, 2); Elligator2::encode(h1) + Elligator2::encode(h0).
;
; The Poseidon part is hpos-c-poseidon-hash-many (hpos-aleo.lisp), the
; Elligator2 encodings are hpos-c-ell2 (hped-elligator2-gadget on a linear
; combination, hpos-ell2.lisp) and the addition is hpos-c-gadd
; (crv-group-add-gadget, hpos-gadd.lisp).  A point is a cons of two
; variables (x . y).  Elligator2 is synthesized on h1 before h0, as Rust
; evaluates the left operand of + first.  Empty input halts in snarkVM; the
; theorems assume (consp xs).
;
; Completeness of an Elligator2 instance holds in every valuation extending
; its witness (hpos-c-ell2-complete-frame), so the stages are composed with
; hpos-fwit-okp, which records that the constraints hold in all such
; extensions, instead of hpos-wit-okp.

(in-package "ALEOVM")

(include-book "hpos-gadd")

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund hpos-hash-to-group-spec (rate inputs)
  (declare (xargs :verify-guards nil))
  (b* ((fs (hpos-hash-to-group-fields rate inputs)))
    (if (eq fs :halt)
        :halt
      (group-add-funspec (hped-elligator2-encode (first fs))
                         (hped-elligator2-encode (second fs))))))

(defund hpos-hash-to-group-validp (rate inputs)
  (declare (xargs :verify-guards nil))
  (b* ((fs (hpos-hash-to-group-fields rate inputs)))
    (and (not (eq fs :halt))
         (hped-elligator2-encode-validp (first fs))
         (hped-elligator2-encode-validp (second fs)))))

;; The circuit, staged so that each proof sees one gadget call at a time.

(defund hpos-c-h2g-add (p1 h0 u vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv p0 cs3 vs asg) (hpos-c-ell2 h0 u vs asg))
       ((mv g cs4 vs asg) (hpos-c-gadd p1 p0 vs asg)))
    (mv g (append cs3 cs4) vs asg)))

(defund hpos-c-h2g-encode (h1 h0 u vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv p1 cs2 vs asg) (hpos-c-ell2 h1 u vs asg))
       ((mv g cs34 vs asg) (hpos-c-h2g-add p1 h0 u vs asg)))
    (mv g (append cs2 cs34) vs asg)))

(defund hpos-c-hash-to-group (rate xs u vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv outs cs1 vs asg) (hpos-c-poseidon-hash-many rate xs 2 vs asg))
       ((mv g cs2 vs asg) (hpos-c-h2g-encode (cadr outs) (car outs) u vs asg)))
    (mv g (append cs1 cs2) vs asg)))

;; Soundness hypotheses: the wires of each gadget instance are distinct
;; symbols bound in the valuation, and the unit wire is 1.

(defund hpos-gadd-wire-hyps (vs asgx)
  (declare (xargs :verify-guards nil))
  (and (symbol-listp (take 6 vs))
       (<= 6 (len vs))
       (r1cs::r1cs-valuationp asgx primes::*bls12-377-scalar-field-prime*)
       (r1cs::valuation-binds-allp asgx (take 6 vs))))

(defund hpos-h2g-add-hyps (u vs asgx)
  (declare (xargs :verify-guards nil))
  (and (hpos-ell2-sound-hyps u vs asgx)
       (hpos-gadd-wire-hyps (nthcdr *hpos-ell2-nblock* vs) asgx)))

(defund hpos-h2g-encode-hyps (u vs asgx)
  (declare (xargs :verify-guards nil))
  (and (hpos-ell2-sound-hyps u vs asgx)
       (hpos-h2g-add-hyps u (nthcdr *hpos-ell2-nblock* vs) asgx)))

(defund hpos-h2g-sound-hyps (rate xs u vs asg asgx)
  (declare (xargs :verify-guards nil))
  (b* (((mv & & vs1 &) (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
    (hpos-h2g-encode-hyps u vs1 asgx)))

(defund hpos-h2g-bound (rate nin)
  (declare (xargs :verify-guards nil))
  (+ (hpos-poseidon-bound rate nin 2)
     (* 2 *hpos-ell2-nblock*)
     6))

;; Synthesis-time intermediates, named for the hypotheses below.
(defrulel hpos-lc-eval-of-car-and-cadr
  (and (implies (consp l)
                (equal (hpos-lc-eval (car l) asg p)
                       (car (hpos-lc-eval-list l asg p))))
       (implies (consp (cdr l))
                (equal (hpos-lc-eval (cadr l) asg p)
                       (cadr (hpos-lc-eval-list l asg p)))))
  :enable hpos-lc-eval-list)

(defrulel hpos-len-of-hpos-poseidon-hash-many-2
  (equal (len (hpos-poseidon-hash-many rate inputs 2)) 2)
  :use (:instance hpos-len-of-hpos-poseidon-hash-many (num-outputs 2))
  :disable hpos-len-of-hpos-poseidon-hash-many)

(defrulel hpos-c-poseidon-hash-many-2-outs
  (b* (((mv outs cs & &) (hpos-c-poseidon-hash-many rate xs 2 vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (hs (hpos-poseidon-hash-many rate (hpos-lc-eval-list xs asgx p) 2)))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (consp outs)
                  (consp (cdr outs))
                  (equal (hpos-lc-eval (car outs) asgx p) (car hs))
                  (equal (hpos-lc-eval (cadr outs) asgx p) (cadr hs)))))
  :do-not-induct t
  :disable (hpos-c-poseidon-hash-many-sound hpos-len-of-hpos-lc-eval-list)
  :use ((:instance hpos-c-poseidon-hash-many-sound (nout 2))
        (:instance hpos-len-of-hpos-lc-eval-list
                   (lcs (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (asg asgx)
                   (p primes::*bls12-377-scalar-field-prime*))))

(defrulel hpos-c-h2g-add-sound
  (b* (((mv g cs & &) (hpos-c-h2g-add p1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (r0 (hpos-lc-eval h0 asgx p)))
    (implies (and (hpos-h2g-add-hyps u vs asgx)
                  (hpos-pt-boundp p1 asgx)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval p1 asgx))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hped-elligator2-encode-validp r0)
                  (equal (hpos-pt-eval g asgx)
                         (group-add-funspec (hpos-pt-eval p1 asgx)
                                            (hped-elligator2-encode r0))))))
  :do-not-induct t
  :enable (hpos-c-h2g-add hpos-h2g-add-hyps hpos-gadd-wire-hyps hpos-gadd-sound-hyps
           hpos-ell2-sound-hyps)
  :disable (hpos-c-ell2-sound hpos-c-gadd-sound hped-elligator2-encode
            hped-elligator2-encode-validp group-add-funspec)
  :use ((:instance hpos-c-ell2-sound (h h0))
        (:instance hpos-c-gadd-sound
                   (a p1) (b (hpos-ell2-pt vs))
                   (vs (nthcdr *hpos-ell2-nblock* vs))
                   (asg (mv-nth 3 (hpos-c-ell2 h0 u vs asg))))
        (:instance hpos-pt-boundp-of-hpos-ell2-pt (a asgx))
        (:instance hpos-edwards-bls12-pointp-of-hped-elligator2-encode
                   (r (hpos-lc-eval h0 asgx primes::*bls12-377-scalar-field-prime*)))))

(defrulel hpos-c-h2g-encode-sound
  (b* (((mv g cs & &) (hpos-c-h2g-encode h1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (r1 (hpos-lc-eval h1 asgx p))
       (r0 (hpos-lc-eval h0 asgx p)))
    (implies (and (hpos-h2g-encode-hyps u vs asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hped-elligator2-encode-validp r1)
                  (hped-elligator2-encode-validp r0)
                  (equal (hpos-pt-eval g asgx)
                         (group-add-funspec (hped-elligator2-encode r1)
                                            (hped-elligator2-encode r0))))))
  :do-not-induct t
  :enable (hpos-c-h2g-encode hpos-h2g-encode-hyps hpos-ell2-sound-hyps)
  :disable (hpos-c-h2g-add-sound hpos-c-ell2-sound hped-elligator2-encode
            hped-elligator2-encode-validp group-add-funspec)
  :use ((:instance hpos-c-ell2-sound (h h1))
        (:instance hpos-c-h2g-add-sound
                   (p1 (hpos-ell2-pt vs))
                   (vs (nthcdr *hpos-ell2-nblock* vs))
                   (asg (mv-nth 3 (hpos-c-ell2 h1 u vs asg))))
        (:instance hpos-pt-boundp-of-hpos-ell2-pt (a asgx))
        (:instance hpos-edwards-bls12-pointp-of-hped-elligator2-encode
                   (r (hpos-lc-eval h1 asgx primes::*bls12-377-scalar-field-prime*)))))

(defrule hpos-c-hash-to-group-sound
  (b* (((mv g cs & &) (hpos-c-hash-to-group rate xs u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (in (hpos-lc-eval-list xs asgx p)))
    (implies (and (hpos-aleo-rate-p rate)
                  (consp xs)
                  (hpos-h2g-sound-hyps rate xs u vs asg asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hpos-hash-to-group-validp rate in)
                  (equal (hpos-pt-eval g asgx)
                         (hpos-hash-to-group-spec rate in)))))
  :do-not-induct t
  :enable (hpos-c-hash-to-group hpos-h2g-sound-hyps hpos-hash-to-group-spec
           hpos-hash-to-group-validp hpos-hash-to-group-fields)
  :disable (hpos-c-poseidon-hash-many-2-outs hpos-c-h2g-encode-sound
            hpos-lc-eval-of-car-and-cadr hpos-lc-eval-decomp hped-elligator2-encode
            hped-elligator2-encode-validp group-add-funspec)
  :use ((:instance hpos-c-poseidon-hash-many-2-outs)
        (:instance hpos-c-h2g-encode-sound
                   (h1 (cadr (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
                   (h0 (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
                   (vs (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))))

(defrulel hpos-u-when-ext-p
  (implies (and (hpos-ext-p old new)
                (r1cs::r1cs-valuationp new p)
                (r1cs::valuation-bindsp old u)
                (equal (lookup-equal u old) 1))
           (and (r1cs::valuation-bindsp new u)
                (equal (lookup-equal u new) 1)))
  :use ((:instance hpos-lookup-when-ext-p (v u))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp (asg new)))
  :enable r1cs::valuation-bindsp
  :disable hpos-lookup-when-ext-p)

(defrulel hpos-lc-eval-when-ext-p-valuationp
  (implies (and (hpos-ext-p old new)
                (r1cs::r1cs-valuationp new p)
                (hpos-lc-boundp lc old))
           (equal (hpos-lc-eval lc new p)
                  (hpos-lc-eval lc old p)))
  :use (:instance hpos-no-duplicatesp-strip-cars-when-valuationp (asg new)))

(defrulel hpos-lc-eval-list-when-ext-p-valuationp
  (implies (and (hpos-ext-p old new)
                (r1cs::r1cs-valuationp new p)
                (hpos-lc-list-boundp lcs old))
           (equal (hpos-lc-eval-list lcs new p)
                  (hpos-lc-eval-list lcs old p)))
  :use (:instance hpos-no-duplicatesp-strip-cars-when-valuationp (asg new)))

(defrulel hpos-lc-boundp-of-cadr
  (implies (hpos-lc-list-boundp x asg)
           (hpos-lc-boundp (cadr x) asg))
  :use (:instance hpos-lc-boundp-of-car (x (cdr x))))

;; Stage 1: hash_many(input, 2).
(defrulel hpos-h2g-stage1
  (b* ((p primes::*bls12-377-scalar-field-prime*)
       ((mv outs cs1 vs1 asg1) (hpos-c-poseidon-hash-many rate xs 2 vs asg))
       (hs (hpos-poseidon-hash-many rate (hpos-lc-eval-list xs asg p) 2)))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound rate (len xs) 2) (len vs))
                  (hpos-lc-list-boundp xs asg))
             (and (hpos-wit-okp asg vs asg1 vs1 cs1 p)
                  (hpos-lc-boundp (car outs) asg1)
                  (hpos-lc-boundp (cadr outs) asg1)
                  (equal (hpos-lc-eval (car outs) asg1 p) (car hs))
                  (equal (hpos-lc-eval (cadr outs) asg1 p) (cadr hs))
                  (<= (- (len vs) (hpos-poseidon-bound rate (len xs) 2)) (len vs1)))))
  :do-not-induct t
  :enable hpos-wit-okp
  :disable (hpos-c-poseidon-hash-many-complete hpos-c-poseidon-hash-many-2-outs
            hpos-lc-eval-list-when-ext-p-valuationp hpos-lc-eval-list-when-ext-p
            hpos-lc-eval-decomp)
  :use ((:instance hpos-c-poseidon-hash-many-complete (nout 2))
        (:instance hpos-c-poseidon-hash-many-vs-len (nout 2))
        (:instance hpos-c-poseidon-hash-many-2-outs
                   (asgx (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
        (:instance hpos-lc-eval-list-when-ext-p-valuationp
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (lcs xs)
                   (p primes::*bls12-377-scalar-field-prime*))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness invariant: the constraints hold in every valuation that
;; extends the witness.

(defun-sk hpos-holds-ext (cs a)
  (forall f (implies (and (hpos-ext-p a f)
                          (r1cs::r1cs-valuationp f primes::*bls12-377-scalar-field-prime*))
                     (r1cs::r1cs-constraints-holdp
                      cs f primes::*bls12-377-scalar-field-prime*))))

(in-theory (disable hpos-holds-ext hpos-holds-ext-necc))

(defund hpos-fwit-okp (asg vs asg2 vs2 cs)
  (declare (xargs :verify-guards nil))
  (b* ((p primes::*bls12-377-scalar-field-prime*))
    (and (r1cs::r1cs-valuationp asg2 p)
         (hpos-ext-p asg asg2)
         (hpos-ext-p vs2 vs)
         (hpos-supply-okp vs2 asg2)
         (hpos-holds-ext cs asg2))))

(defrule hpos-fwit-okp-forward
  (implies (hpos-fwit-okp asg vs asg2 vs2 cs)
           (and (r1cs::r1cs-valuationp asg2 primes::*bls12-377-scalar-field-prime*)
                (hpos-ext-p asg asg2)
                (hpos-ext-p vs2 vs)
                (hpos-supply-okp vs2 asg2)))
  :rule-classes :forward-chaining
  :enable hpos-fwit-okp)

(defrule hpos-fwit-okp-holdp
  (implies (hpos-fwit-okp asg vs asg2 vs2 cs)
           (r1cs::r1cs-constraints-holdp cs asg2 primes::*bls12-377-scalar-field-prime*))
  :enable hpos-fwit-okp
  :use (:instance hpos-holds-ext-necc (a asg2) (f asg2)))

(defrule hpos-fwit-okp-when-wit-okp
  (implies (hpos-wit-okp asg vs asg2 vs2 cs primes::*bls12-377-scalar-field-prime*)
           (hpos-fwit-okp asg vs asg2 vs2 cs))
  :enable (hpos-fwit-okp hpos-wit-okp hpos-holds-ext)
  :use (:instance hpos-holdp-when-ext-p
                  (old asg2) (new (hpos-holds-ext-witness cs asg2))
                  (p primes::*bls12-377-scalar-field-prime*)))

(defrulel hpos-holds-ext-when-ext-p
  (implies (and (hpos-holds-ext cs a1)
                (hpos-ext-p a1 a2))
           (hpos-holds-ext cs a2))
  :expand ((hpos-holds-ext cs a2))
  :use (:instance hpos-holds-ext-necc (a a1) (f (hpos-holds-ext-witness cs a2))))

(defrulel hpos-holds-ext-of-append
  (implies (and (hpos-holds-ext cs1 a)
                (hpos-holds-ext cs2 a))
           (hpos-holds-ext (append cs1 cs2) a))
  :expand ((hpos-holds-ext (append cs1 cs2) a))
  :use ((:instance hpos-holds-ext-necc (cs cs1) (f (hpos-holds-ext-witness (append cs1 cs2) a)))
        (:instance hpos-holds-ext-necc (cs cs2) (f (hpos-holds-ext-witness (append cs1 cs2) a)))))

(defrule hpos-fwit-okp-append
  (implies (and (hpos-fwit-okp asg vs asg1 vs1 cs1)
                (hpos-fwit-okp asg1 vs1 asg2 vs2 cs2))
           (hpos-fwit-okp asg vs asg2 vs2 (append cs1 cs2)))
  :enable hpos-fwit-okp
  :use (:instance hpos-holds-ext-when-ext-p (cs cs1) (a1 asg1) (a2 asg2)))

(defrulel hpos-holds-ext-of-hpos-c-ell2
  (b* (((mv & cs & a2) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hped-elligator2-encode-validp (hpos-lc-eval h asg p)))
             (hpos-holds-ext cs a2)))
  :enable hpos-holds-ext
  :disable hpos-c-ell2-complete-frame
  :use (:instance hpos-c-ell2-complete-frame
                  (f (hpos-holds-ext-witness (mv-nth 1 (hpos-c-ell2 h u vs asg))
                                             (mv-nth 3 (hpos-c-ell2 h u vs asg))))))


;; Stages 2 and 3: Elligator2::encode, with the unit wire carried from ASG0.
(defrulel hpos-h2g-ell2-stage
  (b* ((p primes::*bls12-377-scalar-field-prime*)
       ((mv pt cs vs2 asg2) (hpos-c-ell2 h u vs asg)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (hpos-ext-p asg0 asg)
                  (r1cs::valuation-bindsp asg0 u)
                  (equal (lookup-equal u asg0) 1)
                  (hped-elligator2-encode-validp (hpos-lc-eval h asg p)))
             (and (hpos-fwit-okp asg vs asg2 vs2 cs)
                  (hpos-pt-boundp pt asg2)
                  (equal (hpos-pt-eval pt asg2)
                         (hped-elligator2-encode (hpos-lc-eval h asg p)))
                  (hpos-ext-p asg0 asg2))))
  :do-not-induct t
  :enable hpos-fwit-okp
  :disable (hpos-c-ell2-complete hpos-u-when-ext-p hpos-holds-ext-of-hpos-c-ell2
            hped-elligator2-encode hped-elligator2-encode-validp)
  :use (hpos-c-ell2-complete
        hpos-holds-ext-of-hpos-c-ell2
        (:instance hpos-u-when-ext-p (old asg0) (new asg)
                   (p primes::*bls12-377-scalar-field-prime*))))

(defrulel hpos-c-h2g-add-complete
  (b* (((mv g cs vs2 asg2) (hpos-c-h2g-add p1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (+ *hpos-ell2-nblock* 6) (len vs))
                  (hpos-pt-boundp p1 asg)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval p1 asg))
                  (hpos-lc-boundp h0 asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hped-elligator2-encode-validp (hpos-lc-eval h0 asg p)))
             (and (hpos-fwit-okp asg vs asg2 vs2 cs)
                  (hpos-pt-boundp g asg2))))
  :do-not-induct t
  :enable hpos-c-h2g-add
  :disable (hpos-h2g-ell2-stage hpos-c-gadd-complete hpos-fwit-okp-append
            hpos-pt-boundp-when-ext-p hpos-pt-eval-when-ext-p hpos-fwit-okp-when-wit-okp
            hped-elligator2-encode hped-elligator2-encode-validp group-add-funspec)
  :use ((:instance hpos-h2g-ell2-stage (h h0) (asg0 asg))
        (:instance hpos-pt-boundp-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h0 u vs asg))) (pt p1))
        (:instance hpos-pt-eval-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h0 u vs asg))) (pt p1))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                   (asg (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-edwards-bls12-pointp-of-hped-elligator2-encode
                   (r (hpos-lc-eval h0 asg primes::*bls12-377-scalar-field-prime*)))
        (:instance hpos-c-gadd-complete
                   (a p1) (b (mv-nth 0 (hpos-c-ell2 h0 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h0 u vs asg)))
                   (asg (mv-nth 3 (hpos-c-ell2 h0 u vs asg))))
        (:instance hpos-fwit-okp-when-wit-okp
                   (asg (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h0 u vs asg)))
                   (asg2 (mv-nth 3 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                                (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                                (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))))
                   (vs2 (mv-nth 2 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))))
                   (cs (mv-nth 1 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                              (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                              (mv-nth 3 (hpos-c-ell2 h0 u vs asg))))))
        (:instance hpos-fwit-okp-append
                   (asg1 (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))
                   (vs1 (mv-nth 2 (hpos-c-ell2 h0 u vs asg)))
                   (cs1 (mv-nth 1 (hpos-c-ell2 h0 u vs asg)))
                   (asg2 (mv-nth 3 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                                (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                                (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))))
                   (vs2 (mv-nth 2 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))))
                   (cs2 (mv-nth 1 (hpos-c-gadd p1 (mv-nth 0 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 2 (hpos-c-ell2 h0 u vs asg))
                                               (mv-nth 3 (hpos-c-ell2 h0 u vs asg))))))))

(defrulel hpos-c-h2g-encode-complete
  (b* (((mv g cs vs2 asg2) (hpos-c-h2g-encode h1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (+ (* 2 *hpos-ell2-nblock*) 6) (len vs))
                  (hpos-lc-boundp h1 asg)
                  (hpos-lc-boundp h0 asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hped-elligator2-encode-validp (hpos-lc-eval h1 asg p))
                  (hped-elligator2-encode-validp (hpos-lc-eval h0 asg p)))
             (and (hpos-fwit-okp asg vs asg2 vs2 cs)
                  (hpos-pt-boundp g asg2))))
  :do-not-induct t
  :enable hpos-c-h2g-encode
  :disable (hpos-h2g-ell2-stage hpos-c-h2g-add-complete hpos-fwit-okp-append
            hpos-u-when-ext-p hpos-lc-eval-when-ext-p-valuationp
            hpos-lc-boundp-when-ext-p hpos-lc-eval-decomp
            hped-elligator2-encode hped-elligator2-encode-validp group-add-funspec)
  :use ((:instance hpos-h2g-ell2-stage (h h1) (asg0 asg))
        (:instance hpos-u-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-lc-boundp-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg))) (lc h0))
        (:instance hpos-lc-eval-when-ext-p-valuationp
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg))) (lc h0)
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-edwards-bls12-pointp-of-hped-elligator2-encode
                   (r (hpos-lc-eval h1 asg primes::*bls12-377-scalar-field-prime*)))
        (:instance hpos-c-h2g-add-complete
                   (p1 (mv-nth 0 (hpos-c-ell2 h1 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h1 u vs asg)))
                   (asg (mv-nth 3 (hpos-c-ell2 h1 u vs asg))))
        (:instance hpos-fwit-okp-append
                   (asg1 (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))
                   (vs1 (mv-nth 2 (hpos-c-ell2 h1 u vs asg)))
                   (cs1 (mv-nth 1 (hpos-c-ell2 h1 u vs asg)))
                   (asg2 (mv-nth 3 (hpos-c-h2g-add (mv-nth 0 (hpos-c-ell2 h1 u vs asg)) h0 u
                                                   (mv-nth 2 (hpos-c-ell2 h1 u vs asg))
                                                   (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))))
                   (vs2 (mv-nth 2 (hpos-c-h2g-add (mv-nth 0 (hpos-c-ell2 h1 u vs asg)) h0 u
                                                  (mv-nth 2 (hpos-c-ell2 h1 u vs asg))
                                                  (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))))
                   (cs2 (mv-nth 1 (hpos-c-h2g-add (mv-nth 0 (hpos-c-ell2 h1 u vs asg)) h0 u
                                                  (mv-nth 2 (hpos-c-ell2 h1 u vs asg))
                                                  (mv-nth 3 (hpos-c-ell2 h1 u vs asg))))))))

(defrule hpos-c-hash-to-group-complete
  (b* (((mv g cs & asg2) (hpos-c-hash-to-group rate xs u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-h2g-bound rate (len xs)) (len vs))
                  (hpos-lc-list-boundp xs asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hpos-hash-to-group-validp rate (hpos-lc-eval-list xs asg p)))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (hpos-pt-boundp g asg2))))
  :do-not-induct t
  :enable (hpos-c-hash-to-group hpos-h2g-bound hpos-hash-to-group-validp
           hpos-hash-to-group-fields)
  :disable (hpos-h2g-stage1 hpos-c-h2g-encode-complete hpos-fwit-okp-append
            hpos-u-when-ext-p hpos-lc-eval-decomp hpos-fwit-okp-when-wit-okp
            hped-elligator2-encode-validp)
  :use (hpos-h2g-stage1
        (:instance hpos-fwit-okp-when-wit-okp
                   (asg2 (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (cs (mv-nth 1 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (cs (mv-nth 1 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-u-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-c-h2g-encode-complete
                   (h1 (cadr (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
                   (h0 (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
                   (vs (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))
        (:instance hpos-fwit-okp-append
                   (asg1 (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (vs1 (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (cs1 (mv-nth 1 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                   (asg2 (mv-nth 3 (hpos-c-hash-to-group rate xs u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-hash-to-group rate xs u vs asg)))
                   (cs2 (mv-nth 1 (hpos-c-h2g-encode
                                   (cadr (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                                   (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
                                   u
                                   (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 2 vs asg))
                                   (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg))))))
        (:instance hpos-fwit-okp-holdp
                   (asg2 (mv-nth 3 (hpos-c-hash-to-group rate xs u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-hash-to-group rate xs u vs asg)))
                   (cs (mv-nth 1 (hpos-c-hash-to-group rate xs u vs asg))))
        (:instance hpos-fwit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-hash-to-group rate xs u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-hash-to-group rate xs u vs asg)))
                   (cs (mv-nth 1 (hpos-c-hash-to-group rate xs u vs asg))))))
