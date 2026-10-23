; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Poseidon permutation circuit (circuit/algorithms/src/poseidon/
; hash_many.rs: apply_ark, apply_s_box, apply_mds, permute), generic over the
; prime, the round counts, the round constants, the MDS matrix and the bits
; of alpha.
;
; apply_ark and apply_mds only add constants and multiply by constants, so
; they emit no constraints: the state elements become new linear
; combinations.  apply_s_box raises every element (full round) or state[0]
; only (partial round) to alpha with Field::pow on the constant alpha, i.e.
; square-and-multiply over the 253 big-endian bits of alpha, where a
; multiplication emits a constraint only when both sides are non-constant.
;
; Soundness: for every assignment satisfying the constraints, the values of
; the output linear combinations are the hpos-* spec functions of
; fun-specs/hash-poseidon.lisp applied to the values of the inputs.
; Completeness: the assignment extended with snarkVM's witnesses satisfies
; the constraints (given enough fresh variable names).

(in-package "ALEOVM")

(include-book "hpos-lc")
(include-book "../fun-specs/hash-poseidon")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule hpos-lc-list-boundp-of-cons
  (equal (hpos-lc-list-boundp (cons a b) asg)
         (and (hpos-lc-boundp a asg) (hpos-lc-list-boundp b asg)))
  :enable hpos-lc-list-boundp)

(defrule hpos-lc-list-boundp-of-atom
  (implies (atom x) (hpos-lc-list-boundp x asg))
  :enable hpos-lc-list-boundp)

(defrule hpos-lc-eval-list-of-cons
  (equal (hpos-lc-eval-list (cons a b) asg p)
         (cons (hpos-lc-eval a asg p) (hpos-lc-eval-list b asg p)))
  :enable hpos-lc-eval-list)

(defrule hpos-lc-eval-list-of-atom
  (implies (atom x) (equal (hpos-lc-eval-list x asg p) nil))
  :enable hpos-lc-eval-list)

(defrule hpos-lc-boundp-of-car
  (implies (hpos-lc-list-boundp x asg)
           (hpos-lc-boundp (car x) asg))
  :enable (hpos-lc-list-boundp hpos-lc-boundp-alt hpos-terms-boundp))

(defrule hpos-lc-list-boundp-of-cdr
  (implies (hpos-lc-list-boundp x asg)
           (hpos-lc-list-boundp (cdr x) asg))
  :enable hpos-lc-list-boundp)

;; Every synthesis function only conses witness bindings onto asg, so
;; anything bound in asg stays bound, with the same value.

(defmacro hpos-def-mono (name call)
  (let ((ext (acl2::packn-pos (list name '-ext) name))
        (lcb (acl2::packn-pos (list name '-lc-boundp) name))
        (lcl (acl2::packn-pos (list name '-lc-list-boundp) name))
        (csb (acl2::packn-pos (list name '-cs-boundp) name)))
    `(progn
       (defrule ,lcb
         (implies (hpos-lc-boundp y asg)
                  (hpos-lc-boundp y (mv-nth 3 ,call)))
         :use ((:instance ,ext (a asg))
               (:instance hpos-lc-boundp-when-ext-p (lc y) (old asg)
                          (new (mv-nth 3 ,call))))
         :disable (,ext hpos-lc-boundp-when-ext-p))
       (defrule ,lcl
         (implies (hpos-lc-list-boundp y asg)
                  (hpos-lc-list-boundp y (mv-nth 3 ,call)))
         :use ((:instance ,ext (a asg))
               (:instance hpos-lc-list-boundp-when-ext-p (lcs y) (old asg)
                          (new (mv-nth 3 ,call))))
         :disable (,ext hpos-lc-list-boundp-when-ext-p))
       (defrule ,csb
         (implies (hpos-cs-boundp y asg)
                  (hpos-cs-boundp y (mv-nth 3 ,call)))
         :use ((:instance ,ext (a asg))
               (:instance hpos-cs-boundp-when-ext-p (cs y) (old asg)
                          (new (mv-nth 3 ,call))))
         :disable (,ext hpos-cs-boundp-when-ext-p)))))

(defrule hpos-mul-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-mul x y vs asg p))))
  :enable hpos-mul)

(hpos-def-mono hpos-mul (hpos-mul x y vs asg p))

(defrule hpos-c-pow-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-pow x out bits vs asg p))))
  :induct (hpos-c-pow x out bits vs asg p)
  :enable hpos-c-pow)

(hpos-def-mono hpos-c-pow (hpos-c-pow x out bits vs asg p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; apply_ark: state[i] += ark[round][i].  No constraints.

(defund hpos-c-ark (st row p)
  (declare (xargs :verify-guards nil))
  (if (atom st)
      nil
    (cons (hpos-lc-add (car st) (hpos-lc-const (ifix (car row))) p)
          (hpos-c-ark (cdr st) (cdr row) p))))

(defrule hpos-len-of-hpos-c-ark
  (equal (len (hpos-c-ark st row p)) (len st))
  :enable hpos-c-ark)

(defrule hpos-c-ark-sound
  (implies (posp p)
           (equal (hpos-lc-eval-list (hpos-c-ark st row p) asg p)
                  (hpos-apply-ark (hpos-lc-eval-list st asg p) row p)))
  :enable (hpos-c-ark hpos-apply-ark))

(defrule hpos-c-ark-bound
  (implies (hpos-lc-list-boundp st asg)
           (hpos-lc-list-boundp (hpos-c-ark st row p) asg))
  :enable hpos-c-ark)

;; apply_mds: new_state[i] = sum_j state[j] * mds[i][j].  No constraints.

(defund hpos-c-mds-row (st row p)
  (declare (xargs :verify-guards nil))
  (if (atom st)
      (hpos-lc-const 0)
    (hpos-lc-add (hpos-lc-scale (car st) (ifix (car row)) p)
                 (hpos-c-mds-row (cdr st) (cdr row) p)
                 p)))

(defrule hpos-c-mds-row-sound
  (implies (posp p)
           (equal (hpos-lc-eval (hpos-c-mds-row st row p) asg p)
                  (hpos-mds-row (hpos-lc-eval-list st asg p) row p)))
  :enable (hpos-c-mds-row hpos-mds-row)
  :disable hpos-lc-eval-decomp)

(defrule hpos-c-mds-row-bound
  (implies (hpos-lc-list-boundp st asg)
           (hpos-lc-boundp (hpos-c-mds-row st row p) asg))
  :enable hpos-c-mds-row)

(defund hpos-c-mds-rows (st rows p)
  (declare (xargs :verify-guards nil))
  (if (atom rows)
      nil
    (cons (hpos-c-mds-row st (car rows) p)
          (hpos-c-mds-rows st (cdr rows) p))))

(defrule hpos-len-of-hpos-c-mds-rows
  (equal (len (hpos-c-mds-rows st rows p)) (len rows))
  :enable hpos-c-mds-rows)

(defrule hpos-c-mds-rows-sound
  (implies (posp p)
           (equal (hpos-lc-eval-list (hpos-c-mds-rows st rows p) asg p)
                  (hpos-apply-mds-rows (hpos-lc-eval-list st asg p) rows p)))
  :enable (hpos-c-mds-rows hpos-apply-mds-rows))

(defrule hpos-c-mds-rows-bound
  (implies (hpos-lc-list-boundp st asg)
           (hpos-lc-list-boundp (hpos-c-mds-rows st rows p) asg))
  :enable hpos-c-mds-rows)

(defund hpos-c-mds (st mds p)
  (declare (xargs :verify-guards nil))
  (hpos-c-mds-rows st (take (len st) mds) p))

(defrule hpos-len-of-hpos-c-mds
  (equal (len (hpos-c-mds st mds p)) (len st))
  :enable hpos-c-mds)

(defrule hpos-c-mds-sound
  (implies (posp p)
           (equal (hpos-lc-eval-list (hpos-c-mds st mds p) asg p)
                  (hpos-apply-mds (hpos-lc-eval-list st asg p) mds p)))
  :enable (hpos-c-mds hpos-apply-mds))

(defrule hpos-c-mds-bound
  (implies (hpos-lc-list-boundp st asg)
           (hpos-lc-list-boundp (hpos-c-mds st mds p) asg))
  :enable hpos-c-mds)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; apply_s_box.

(defund hpos-sbox-bound (n bits)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      0
    (+ (* 2 (len bits)) (hpos-sbox-bound (1- n) bits))))

(defrule hpos-natp-of-hpos-sbox-bound
  (natp (hpos-sbox-bound n bits))
  :rule-classes :type-prescription
  :enable hpos-sbox-bound)

(defrule hpos-sbox-bound-of-len-cons
  (equal (hpos-sbox-bound (len (cons a st)) bits)
         (+ (* 2 (len bits)) (hpos-sbox-bound (len st) bits)))
  :enable hpos-sbox-bound)

(defrule hpos-sbox-bound-of-len-when-consp
  (implies (consp st)
           (equal (hpos-sbox-bound (len st) bits)
                  (+ (* 2 (len bits)) (hpos-sbox-bound (len (cdr st)) bits))))
  :enable hpos-sbox-bound)

(defrule hpos-sbox-bound-when-posp
  (implies (posp n)
           (<= (* 2 (len bits)) (hpos-sbox-bound n bits)))
  :rule-classes :linear
  :enable hpos-sbox-bound)

(defrule hpos-c-pow-1-complete
  (b* (((mv o cs vs2 asg2) (hpos-c-pow x (hpos-lc-const 1) bits vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (* 2 (len bits)) (len vs))
                  (hpos-lc-boundp x asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-boundp o asg2))))
  :use (:instance hpos-c-pow-complete (out (hpos-lc-const 1)))
  :disable hpos-c-pow-complete)

(defund hpos-c-s-box-all (st bits vs asg p)
  (declare (xargs :verify-guards nil))
  (if (atom st)
      (mv nil nil vs asg)
    (b* (((mv o cs1 vs asg) (hpos-c-pow (car st) (hpos-lc-const 1) bits vs asg p))
         ((mv os cs2 vs asg) (hpos-c-s-box-all (cdr st) bits vs asg p)))
      (mv (cons o os) (append cs1 cs2) vs asg))))

(defrule hpos-c-s-box-all-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-s-box-all st bits vs asg p))))
  :induct (hpos-c-s-box-all st bits vs asg p)
  :enable hpos-c-s-box-all)

(hpos-def-mono hpos-c-s-box-all (hpos-c-s-box-all st bits vs asg p))

(defrule hpos-len-of-hpos-c-s-box-all
  (equal (len (mv-nth 0 (hpos-c-s-box-all st bits vs asg p))) (len st))
  :enable hpos-c-s-box-all)

(defrule hpos-c-pow-1-sound
  (b* (((mv o cs & &) (hpos-c-pow x (hpos-lc-const 1) bits vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval o asgx p)
                    (pfield::pow (hpos-lc-eval x asgx p) (hpos-bits-val 0 bits) p))))
  :use (:instance hpos-c-pow-sound (out (hpos-lc-const 1)))
  :disable (hpos-c-pow-sound hpos-lc-eval-decomp))

(defrule hpos-c-s-box-all-sound
  (b* (((mv os cs & &) (hpos-c-s-box-all st bits vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list os asgx p)
                    (hpos-s-box-all (hpos-lc-eval-list st asgx p) (hpos-bits-val 0 bits) p))))
  :induct (hpos-c-s-box-all st bits vs asg p)
  :enable (hpos-c-s-box-all hpos-s-box-all)
  :disable hpos-lc-eval-decomp)

(defrule hpos-c-s-box-all-vs-len
  (b* (((mv & & vs2 &) (hpos-c-s-box-all st bits vs asg p)))
    (and (<= (- (len vs) (hpos-sbox-bound (len st) bits)) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :induct (hpos-c-s-box-all st bits vs asg p)
  :enable (hpos-c-s-box-all hpos-sbox-bound))

(defrule hpos-c-s-box-all-complete
  (b* (((mv os cs vs2 asg2) (hpos-c-s-box-all st bits vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-sbox-bound (len st) bits) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp os asg2))))
  :induct (hpos-c-s-box-all st bits vs asg p)
  :enable hpos-c-s-box-all
  :disable hpos-c-pow-1-complete
  :hints (("Subgoal *1/2"
           :use ((:instance hpos-c-pow-vs-len (x (car st)) (out (hpos-lc-const 1)))
                 (:instance hpos-c-pow-1-complete (x (car st)))))))

(defund hpos-c-s-box (st bits full-p vs asg p)
  (declare (xargs :verify-guards nil))
  (if full-p
      (hpos-c-s-box-all st bits vs asg p)
    (if (consp st)
        (b* (((mv o cs vs asg)
              (hpos-c-pow (car st) (hpos-lc-const 1) bits vs asg p)))
          (mv (cons o (cdr st)) cs vs asg))
      (mv st nil vs asg))))

(defrule hpos-c-s-box-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-s-box st bits full-p vs asg p))))
  :enable hpos-c-s-box)

(hpos-def-mono hpos-c-s-box (hpos-c-s-box st bits full-p vs asg p))

(defrule hpos-len-of-hpos-c-s-box
  (equal (len (mv-nth 0 (hpos-c-s-box st bits full-p vs asg p))) (len st))
  :enable hpos-c-s-box)

(defrule hpos-c-s-box-sound
  (b* (((mv os cs & &) (hpos-c-s-box st bits full-p vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list os asgx p)
                    (hpos-apply-s-box (hpos-lc-eval-list st asgx p)
                                      (hpos-bits-val 0 bits) full-p p))))
  :enable (hpos-c-s-box hpos-apply-s-box)
  :disable hpos-lc-eval-decomp)

(defrule hpos-c-s-box-vs-len
  (b* (((mv & & vs2 &) (hpos-c-s-box st bits full-p vs asg p)))
    (and (<= (- (len vs) (hpos-sbox-bound (len st) bits)) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable hpos-c-s-box
  :hints (("Goal" :use (:instance hpos-c-pow-vs-len (x (car st))
                                  (out (hpos-lc-const 1))))))

(defrule hpos-c-s-box-complete
  (b* (((mv os cs vs2 asg2) (hpos-c-s-box st bits full-p vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-sbox-bound (len st) bits) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp os asg2))))
  :enable hpos-c-s-box
  :hints (("Goal" :use (:instance hpos-c-pow-1-complete (x (car st))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One round and permute.

(defund hpos-c-round (st i ark mds bits full partial vs asg p)
  (declare (xargs :verify-guards nil))
  (b* ((st (hpos-c-ark st (nth i ark) p))
       ((mv st cs vs asg)
        (hpos-c-s-box st bits (hpos-full-round-p i full partial) vs asg p))
       (st (hpos-c-mds st mds p)))
    (mv st cs vs asg)))

(defrule hpos-c-round-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-round st i ark mds bits full partial vs asg p))))
  :enable hpos-c-round)

(hpos-def-mono hpos-c-round (hpos-c-round st i ark mds bits full partial vs asg p))

(defrule hpos-len-of-hpos-c-round
  (equal (len (mv-nth 0 (hpos-c-round st i ark mds bits full partial vs asg p)))
         (len st))
  :enable hpos-c-round)

(defrule hpos-c-round-sound
  (b* (((mv os cs & &) (hpos-c-round st i ark mds bits full partial vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list os asgx p)
                    (hpos-round (hpos-lc-eval-list st asgx p)
                                i ark mds (hpos-bits-val 0 bits) full partial p))))
  :enable (hpos-c-round hpos-round))

(defrule hpos-c-round-vs-len
  (b* (((mv & & vs2 &) (hpos-c-round st i ark mds bits full partial vs asg p)))
    (and (<= (- (len vs) (hpos-sbox-bound (len st) bits)) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable hpos-c-round
  :hints (("Goal" :use (:instance hpos-c-s-box-vs-len
                                  (st (hpos-c-ark st (nth i ark) p))
                                  (full-p (hpos-full-round-p i full partial))))))

(defrule hpos-c-round-complete
  (b* (((mv os cs vs2 asg2) (hpos-c-round st i ark mds bits full partial vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-sbox-bound (len st) bits) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp os asg2))))
  :enable hpos-c-round
  :hints (("Goal" :use (:instance hpos-c-s-box-complete
                                  (st (hpos-c-ark st (nth i ark) p))
                                  (full-p (hpos-full-round-p i full partial))))))

(defund hpos-c-rounds (st i ark mds bits full partial vs asg p)
  (declare (xargs :verify-guards nil
                  :measure (nfix (- (+ (nfix full) (nfix partial)) (nfix i)))))
  (if (< (nfix i) (+ (nfix full) (nfix partial)))
      (b* (((mv st cs1 vs asg)
            (hpos-c-round st (nfix i) ark mds bits full partial vs asg p))
           ((mv st cs2 vs asg)
            (hpos-c-rounds st (1+ (nfix i)) ark mds bits full partial vs asg p)))
        (mv st (append cs1 cs2) vs asg))
    (mv st nil vs asg)))

(defund hpos-rounds-bound (i full partial n bits)
  (declare (xargs :verify-guards nil
                  :measure (nfix (- (+ (nfix full) (nfix partial)) (nfix i)))))
  (if (< (nfix i) (+ (nfix full) (nfix partial)))
      (+ (hpos-sbox-bound n bits)
         (hpos-rounds-bound (1+ (nfix i)) full partial n bits))
    0))

(defrule hpos-natp-of-hpos-rounds-bound
  (natp (hpos-rounds-bound i full partial n bits))
  :rule-classes :type-prescription
  :enable hpos-rounds-bound)

(defrule hpos-c-rounds-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-rounds st i ark mds bits full partial vs asg p))))
  :induct (hpos-c-rounds st i ark mds bits full partial vs asg p)
  :enable hpos-c-rounds)

(hpos-def-mono hpos-c-rounds (hpos-c-rounds st i ark mds bits full partial vs asg p))

(defrule hpos-len-of-hpos-c-rounds
  (equal (len (mv-nth 0 (hpos-c-rounds st i ark mds bits full partial vs asg p)))
         (len st))
  :enable hpos-c-rounds)

(defrule hpos-c-rounds-sound
  (b* (((mv os cs & &) (hpos-c-rounds st i ark mds bits full partial vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list os asgx p)
                    (hpos-rounds (hpos-lc-eval-list st asgx p)
                                 i ark mds (hpos-bits-val 0 bits) full partial p))))
  :induct (hpos-c-rounds st i ark mds bits full partial vs asg p)
  :enable (hpos-c-rounds hpos-rounds))

(defrule hpos-c-rounds-vs-len
  (b* (((mv & & vs2 &) (hpos-c-rounds st i ark mds bits full partial vs asg p)))
    (and (<= (- (len vs) (hpos-rounds-bound i full partial (len st) bits))
             (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :induct (hpos-c-rounds st i ark mds bits full partial vs asg p)
  :enable hpos-c-rounds
  :expand ((hpos-rounds-bound i full partial (len st) bits)))

(defrule hpos-c-rounds-complete
  (b* (((mv os cs vs2 asg2) (hpos-c-rounds st i ark mds bits full partial vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-rounds-bound i full partial (len st) bits) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp os asg2))))
  :induct (hpos-c-rounds st i ark mds bits full partial vs asg p)
  :enable hpos-c-rounds
  :disable hpos-c-round-complete
  :expand ((hpos-rounds-bound i full partial (len st) bits))
  :hints (("Subgoal *1/1"
           :use ((:instance hpos-c-round-vs-len (i (nfix i)))
                 (:instance hpos-c-round-complete (i (nfix i)))))))

;; Poseidon::permute.  BITS are the big-endian bits of alpha that
;; Field::pow walks (253 for the BLS12-377 scalar field).

(defund hpos-c-permute (st params bits vs asg)
  (declare (xargs :verify-guards nil))
  (hpos-c-rounds st 0
                 (hpos-params->ark params)
                 (hpos-params->mds params)
                 bits
                 (hpos-params->full params)
                 (hpos-params->partial params)
                 vs asg
                 (hpos-params->prime params)))

(defund hpos-perm-bound (n params bits)
  (declare (xargs :verify-guards nil))
  (hpos-rounds-bound 0 (hpos-params->full params) (hpos-params->partial params)
                     n bits))

(defrule hpos-natp-of-hpos-perm-bound
  (natp (hpos-perm-bound n params bits))
  :rule-classes :type-prescription
  :enable hpos-perm-bound)

(defrule hpos-c-permute-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-permute st params bits vs asg))))
  :enable hpos-c-permute)

(hpos-def-mono hpos-c-permute (hpos-c-permute st params bits vs asg))

(defrule hpos-len-of-hpos-c-permute
  (equal (len (mv-nth 0 (hpos-c-permute st params bits vs asg)))
         (len st))
  :enable hpos-c-permute)

(defrule hpos-c-permute-sound
  (b* (((mv os cs & &) (hpos-c-permute st params bits vs asg))
       (p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits)
                         (hpos-params->alpha params))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list os asgx p)
                    (hpos-permute (hpos-lc-eval-list st asgx p) params))))
  :enable (hpos-c-permute hpos-permute))

(defrule hpos-c-permute-vs-len
  (b* (((mv & & vs2 &) (hpos-c-permute st params bits vs asg)))
    (and (<= (- (len vs) (hpos-perm-bound (len st) params bits)) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable (hpos-c-permute hpos-perm-bound))

(defrule hpos-c-permute-complete
  (b* (((mv os cs vs2 asg2) (hpos-c-permute st params bits vs asg))
       (p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-perm-bound (len st) params bits) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp os asg2))))
  :enable (hpos-c-permute hpos-perm-bound))
