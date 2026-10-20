; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Poseidon::hash_to_group (circuit/algorithms/src/poseidon/hash_to_group.rs):
; [h0, h1] = hash_many(input, 2); Elligator2::encode(h1) + Elligator2::encode(h0).
;
; The Poseidon part is the certified hpos-c-poseidon-hash-many.  The
; Elligator2 encoding and the group addition are constrained gadgets
; (hpos-c-ell2, hpos-c-gadd) whose soundness and completeness are the
; contracts below; the theorems here are conditional on them.  A point is a
; cons of two linear combinations (x . y).  The Elligator2 contract has the
; shape of hped-elligator2-gadget-sound / hped-elligator2-gadget-complete
; (fun-circuits/hped-elligator2.lisp): soundness yields validity of the
; input and the encoded point; completeness requires a valid input.
; Elligator2 is synthesized on h1 before h0, as Rust evaluates the left
; operand of + first.  Empty input halts in snarkVM; the theorems assume
; (consp xs).

(in-package "ALEOVM")

(include-book "hpos-aleo")

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund hpos-pt-eval (pt asg p)
  (declare (xargs :verify-guards nil))
  (cons (hpos-lc-eval (car pt) asg p) (hpos-lc-eval (cdr pt) asg p)))

(defund hpos-pt-boundp (pt asg)
  (declare (xargs :verify-guards nil))
  (and (hpos-lc-boundp (car pt) asg)
       (hpos-lc-boundp (cdr pt) asg)))

(defrule hpos-lc-boundp-of-const-zero-one
  (and (hpos-lc-boundp '(0) asg)
       (hpos-lc-boundp '(1) asg))
  :enable (hpos-lc-boundp hpos-lc-sv hpos-sv-boundp))

(encapsulate
  (((hpos-ell2-spec *) => *)
   ((hpos-ell2-validp *) => *)
   ((hpos-ell2-bound) => *)
   ((hpos-ell2-sound-hyps * * * * *) => *)
   ((hpos-c-ell2 * * * *) => (mv * * * *))
   ((hpos-gadd-spec * *) => *)
   ((hpos-gadd-bound) => *)
   ((hpos-gadd-sound-hyps * * * * *) => *)
   ((hpos-c-gadd * * * *) => (mv * * * *)))

  (local (defun hpos-ell2-spec (r) (declare (ignore r)) nil))
  (local (defun hpos-ell2-validp (r) (declare (ignore r)) t))
  (local (defun hpos-ell2-bound () 0))
  (local (defun hpos-ell2-sound-hyps (h u vs asg asgx)
           (declare (ignore h u vs asg asgx))
           nil))
  (local (defun hpos-c-ell2 (h u vs asg)
           (declare (ignore h u))
           (mv (cons '(0) '(1)) nil vs asg)))
  (local (defun hpos-gadd-spec (a b) (declare (ignore a b)) nil))
  (local (defun hpos-gadd-bound () 0))
  (local (defun hpos-gadd-sound-hyps (a b vs asg asgx)
           (declare (ignore a b vs asg asgx))
           nil))
  (local (defun hpos-c-gadd (a b vs asg)
           (declare (ignore a b))
           (mv (cons '(0) '(1)) nil vs asg)))

  (defrule hpos-natp-of-hpos-ell2-bound
    (natp (hpos-ell2-bound))
    :rule-classes :type-prescription)

  (defrule hpos-natp-of-hpos-gadd-bound
    (natp (hpos-gadd-bound))
    :rule-classes :type-prescription)

  ;; Elligator2::encode on a linear combination H; U is the public unit wire.
  (defrule hpos-c-ell2-sound
    (b* (((mv pt cs & &) (hpos-c-ell2 h u vs asg))
         (p primes::*bls12-377-scalar-field-prime*))
      (implies (and (hpos-ell2-sound-hyps h u vs asg asgx)
                    (r1cs::r1cs-constraints-holdp cs asgx p))
               (and (hpos-ell2-validp (hpos-lc-eval h asgx p))
                    (equal (hpos-pt-eval pt asgx p)
                           (hpos-ell2-spec (hpos-lc-eval h asgx p)))))))

  (defrule hpos-c-ell2-vs-len
    (b* (((mv & & vs2 &) (hpos-c-ell2 h u vs asg)))
      (<= (- (len vs) (hpos-ell2-bound)) (len vs2)))
    :rule-classes :linear)

  (defrule hpos-c-ell2-complete
    (b* (((mv pt cs vs2 asg2) (hpos-c-ell2 h u vs asg))
         (p primes::*bls12-377-scalar-field-prime*))
      (implies (and (r1cs::r1cs-valuationp asg p)
                    (hpos-supply-okp vs asg)
                    (<= (hpos-ell2-bound) (len vs))
                    (hpos-lc-boundp h asg)
                    (symbolp u)
                    (r1cs::valuation-bindsp asg u)
                    (equal (lookup-equal u asg) 1)
                    (hpos-ell2-validp (hpos-lc-eval h asg p)))
               (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                    (hpos-pt-boundp pt asg2))))
    :enable hpos-pt-boundp)

  ;; Group addition of two points.
  (defrule hpos-c-gadd-sound
    (b* (((mv pt cs & &) (hpos-c-gadd a b vs asg))
         (p primes::*bls12-377-scalar-field-prime*))
      (implies (and (hpos-gadd-sound-hyps a b vs asg asgx)
                    (r1cs::r1cs-constraints-holdp cs asgx p))
               (equal (hpos-pt-eval pt asgx p)
                      (hpos-gadd-spec (hpos-pt-eval a asgx p)
                                      (hpos-pt-eval b asgx p))))))

  (defrule hpos-c-gadd-vs-len
    (b* (((mv & & vs2 &) (hpos-c-gadd a b vs asg)))
      (<= (- (len vs) (hpos-gadd-bound)) (len vs2)))
    :rule-classes :linear)

  (defrule hpos-c-gadd-complete
    (b* (((mv pt cs vs2 asg2) (hpos-c-gadd a b vs asg))
         (p primes::*bls12-377-scalar-field-prime*))
      (implies (and (r1cs::r1cs-valuationp asg p)
                    (hpos-supply-okp vs asg)
                    (<= (hpos-gadd-bound) (len vs))
                    (hpos-pt-boundp a asg)
                    (hpos-pt-boundp b asg))
               (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                    (hpos-pt-boundp pt asg2))))
    :enable hpos-pt-boundp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund hpos-hash-to-group-spec (rate inputs)
  (declare (xargs :verify-guards nil))
  (b* ((fs (hpos-hash-to-group-fields rate inputs)))
    (if (eq fs :halt)
        :halt
      (hpos-gadd-spec (hpos-ell2-spec (first fs))
                      (hpos-ell2-spec (second fs))))))

(defund hpos-hash-to-group-validp (rate inputs)
  (declare (xargs :verify-guards nil))
  (b* ((fs (hpos-hash-to-group-fields rate inputs)))
    (and (not (eq fs :halt))
         (hpos-ell2-validp (first fs))
         (hpos-ell2-validp (second fs)))))

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

;; The contract hypotheses of the three gadget instances, at their synthesis
;; inputs.

(defund hpos-h2g-add-hyps (p1 h0 u vs asg asgx)
  (declare (xargs :verify-guards nil))
  (b* (((mv p0 & vs3 asg3) (hpos-c-ell2 h0 u vs asg)))
    (and (hpos-ell2-sound-hyps h0 u vs asg asgx)
         (hpos-gadd-sound-hyps p1 p0 vs3 asg3 asgx))))

(defund hpos-h2g-encode-hyps (h1 h0 u vs asg asgx)
  (declare (xargs :verify-guards nil))
  (b* (((mv p1 & vs2 asg2) (hpos-c-ell2 h1 u vs asg)))
    (and (hpos-ell2-sound-hyps h1 u vs asg asgx)
         (hpos-h2g-add-hyps p1 h0 u vs2 asg2 asgx))))

(defund hpos-h2g-sound-hyps (rate xs u vs asg asgx)
  (declare (xargs :verify-guards nil))
  (b* (((mv outs & vs1 asg1) (hpos-c-poseidon-hash-many rate xs 2 vs asg)))
    (hpos-h2g-encode-hyps (cadr outs) (car outs) u vs1 asg1 asgx)))

(defund hpos-h2g-bound (rate nin)
  (declare (xargs :verify-guards nil))
  (+ (hpos-poseidon-bound rate nin 2)
     (* 2 (hpos-ell2-bound))
     (hpos-gadd-bound)))

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
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-h2g-add-hyps p1 h0 u vs asg asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hpos-ell2-validp (hpos-lc-eval h0 asgx p))
                  (equal (hpos-pt-eval g asgx p)
                         (hpos-gadd-spec (hpos-pt-eval p1 asgx p)
                                         (hpos-ell2-spec (hpos-lc-eval h0 asgx p)))))))
  :do-not-induct t
  :enable (hpos-c-h2g-add hpos-h2g-add-hyps))

(defrulel hpos-c-h2g-encode-sound
  (b* (((mv g cs & &) (hpos-c-h2g-encode h1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-h2g-encode-hyps h1 h0 u vs asg asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hpos-ell2-validp (hpos-lc-eval h1 asgx p))
                  (hpos-ell2-validp (hpos-lc-eval h0 asgx p))
                  (equal (hpos-pt-eval g asgx p)
                         (hpos-gadd-spec (hpos-ell2-spec (hpos-lc-eval h1 asgx p))
                                         (hpos-ell2-spec (hpos-lc-eval h0 asgx p)))))))
  :do-not-induct t
  :enable (hpos-c-h2g-encode hpos-h2g-encode-hyps)
  :disable (hpos-c-h2g-add-sound hpos-c-ell2-sound)
  :use ((:instance hpos-c-ell2-sound (h h1))
        (:instance hpos-c-h2g-add-sound
                   (p1 (mv-nth 0 (hpos-c-ell2 h1 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h1 u vs asg)))
                   (asg (mv-nth 3 (hpos-c-ell2 h1 u vs asg))))))

(defrule hpos-c-hash-to-group-sound
  (b* (((mv g cs & &) (hpos-c-hash-to-group rate xs u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (in (hpos-lc-eval-list xs asgx p)))
    (implies (and (hpos-aleo-rate-p rate)
                  (consp xs)
                  (hpos-h2g-sound-hyps rate xs u vs asg asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hpos-hash-to-group-validp rate in)
                  (equal (hpos-pt-eval g asgx p)
                         (hpos-hash-to-group-spec rate in)))))
  :do-not-induct t
  :enable (hpos-c-hash-to-group hpos-h2g-sound-hyps hpos-hash-to-group-spec
           hpos-hash-to-group-validp hpos-hash-to-group-fields)
  :disable (hpos-c-poseidon-hash-many-2-outs hpos-c-h2g-encode-sound
            hpos-lc-eval-of-car-and-cadr hpos-lc-eval-decomp)
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

(defrule hpos-pt-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-pt-boundp pt old))
           (hpos-pt-boundp pt new))
  :enable hpos-pt-boundp)

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

;; Stages 2 and 3: Elligator2::encode, with the unit wire carried from ASG0.
(defrulel hpos-h2g-ell2-stage
  (b* ((p primes::*bls12-377-scalar-field-prime*)
       ((mv pt cs vs2 asg2) (hpos-c-ell2 h u vs asg)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-ell2-bound) (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (hpos-ext-p asg0 asg)
                  (r1cs::valuation-bindsp asg0 u)
                  (equal (lookup-equal u asg0) 1)
                  (hpos-ell2-validp (hpos-lc-eval h asg p)))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-pt-boundp pt asg2)
                  (hpos-ext-p asg0 asg2))))
  :do-not-induct t
  :disable (hpos-c-ell2-complete hpos-u-when-ext-p)
  :use (hpos-c-ell2-complete
        (:instance hpos-u-when-ext-p (old asg0) (new asg)
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-ell2 h u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-ell2 h u vs asg)))
                   (cs (mv-nth 1 (hpos-c-ell2 h u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))))

(defrulel hpos-wit-okp-len
  (implies (hpos-wit-okp asg vs asg2 vs2 cs p)
           (<= (len vs2) (len vs)))
  :rule-classes :linear
  :enable (hpos-wit-okp hpos-ext-p)
  :induct (hpos-ext-p vs2 vs))

(defrulel hpos-c-h2g-add-complete
  (b* (((mv g cs vs2 asg2) (hpos-c-h2g-add p1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (+ (hpos-ell2-bound) (hpos-gadd-bound)) (len vs))
                  (hpos-pt-boundp p1 asg)
                  (hpos-lc-boundp h0 asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hpos-ell2-validp (hpos-lc-eval h0 asg p)))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-pt-boundp g asg2))))
  :do-not-induct t
  :enable hpos-c-h2g-add
  :disable (hpos-h2g-ell2-stage hpos-c-gadd-complete hpos-wit-okp-append
            hpos-pt-boundp-when-ext-p)
  :use ((:instance hpos-h2g-ell2-stage (h h0) (asg0 asg))
        (:instance hpos-pt-boundp-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h0 u vs asg))) (pt p1))
        (:instance hpos-c-gadd-complete
                   (a p1) (b (mv-nth 0 (hpos-c-ell2 h0 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h0 u vs asg)))
                   (asg (mv-nth 3 (hpos-c-ell2 h0 u vs asg))))
        (:instance hpos-wit-okp-append
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
                                               (mv-nth 3 (hpos-c-ell2 h0 u vs asg)))))
                   (p primes::*bls12-377-scalar-field-prime*))))

(defrulel hpos-c-h2g-encode-complete
  (b* (((mv g cs vs2 asg2) (hpos-c-h2g-encode h1 h0 u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (+ (* 2 (hpos-ell2-bound)) (hpos-gadd-bound)) (len vs))
                  (hpos-lc-boundp h1 asg)
                  (hpos-lc-boundp h0 asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hpos-ell2-validp (hpos-lc-eval h1 asg p))
                  (hpos-ell2-validp (hpos-lc-eval h0 asg p)))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-pt-boundp g asg2))))
  :do-not-induct t
  :enable hpos-c-h2g-encode
  :disable (hpos-h2g-ell2-stage hpos-c-h2g-add-complete hpos-wit-okp-append
            hpos-u-when-ext-p hpos-lc-eval-when-ext-p-valuationp
            hpos-lc-boundp-when-ext-p hpos-lc-eval-decomp)
  :use ((:instance hpos-h2g-ell2-stage (h h1) (asg0 asg))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-ell2 h1 u vs asg)))
                   (cs (mv-nth 1 (hpos-c-ell2 h1 u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-u-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-lc-boundp-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg))) (lc h0))
        (:instance hpos-lc-eval-when-ext-p-valuationp
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h1 u vs asg))) (lc h0)
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-c-h2g-add-complete
                   (p1 (mv-nth 0 (hpos-c-ell2 h1 u vs asg)))
                   (vs (mv-nth 2 (hpos-c-ell2 h1 u vs asg)))
                   (asg (mv-nth 3 (hpos-c-ell2 h1 u vs asg))))
        (:instance hpos-wit-okp-append
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
                                                  (mv-nth 3 (hpos-c-ell2 h1 u vs asg)))))
                   (p primes::*bls12-377-scalar-field-prime*))))

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
           hpos-hash-to-group-fields hpos-wit-okp)
  :disable (hpos-h2g-stage1 hpos-c-h2g-encode-complete hpos-wit-okp-append
            hpos-u-when-ext-p hpos-lc-eval-decomp)
  :use (hpos-h2g-stage1
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
        (:instance hpos-wit-okp-append
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
                                   (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 2 vs asg)))))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-hash-to-group rate xs u vs asg)))
                   (vs2 (mv-nth 2 (hpos-c-hash-to-group rate xs u vs asg)))
                   (cs (mv-nth 1 (hpos-c-hash-to-group rate xs u vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))))
