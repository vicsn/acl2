; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete Poseidon, as snarkVM 7dc117d45 computes it
; (console/algorithms/src/poseidon: hash_many.rs, helpers/sponge.rs).
;
; The definitions follow snarkVM's structure, generic over the prime, the
; round counts, alpha, the round constants (ark) and the MDS matrix:
;
;   - the state has RATE + 1 elements; index 0 is the capacity element,
;     indices 1..RATE are the rate elements;
;   - round i (0 <= i < full + partial) adds ark[i], applies the S-box, and
;     multiplies by the MDS matrix; it is a partial round when
;     full/2 <= i < full/2 + partial, and a partial round applies x^alpha to
;     state[0] only;
;   - the duplex sponge starts in Absorbing{0} with an all-zero state;
;   - hash_many absorbs [DOMAIN, LEN(INPUT), 0 ... 0 (to RATE), INPUT]
;     and squeezes num_outputs elements.
;
; The Aleo instances (rate 2, 4, 8, alpha 17, 8 full and 31 partial rounds)
; take their ark and MDS constants from projects/poseidon, which checks them
; against snarkVM test vectors.  The domain is snarkVM's
; Field::new_domain_separator of "AleoPoseidon2/4/8" (console/network
; mainnet_v0.rs), i.e. the little-endian bytes of the string.
;
; hpos-hash-many is checked below against poseidon::hash2/4/8-many (which
; use the older domains "Poseidon2/4/8") on sample inputs.

(in-package "ALEOVM")

(include-book "projects/poseidon/rate-2-alpha-17" :dir :system)
(include-book "projects/poseidon/rate-4-alpha-17" :dir :system)
(include-book "projects/poseidon/rate-8-alpha-17" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Permutation layers.

; Poseidon::apply_ark: state[i] += ark[round][i].
(defund hpos-apply-ark (st row p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom st)
      nil
    (cons (pfield::add (car st) (ifix (car row)) p)
          (hpos-apply-ark (cdr st) (cdr row) p))))

; Poseidon::apply_s_box: x^alpha on every element (full) or on state[0].
(defund hpos-s-box-all (st alpha p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom st)
      nil
    (cons (pfield::pow (car st) (nfix alpha) p)
          (hpos-s-box-all (cdr st) alpha p))))

(defund hpos-apply-s-box (st alpha full-p p)
  (declare (xargs :guard t :verify-guards nil))
  (if full-p
      (hpos-s-box-all st alpha p)
    (if (consp st)
        (cons (pfield::pow (car st) (nfix alpha) p) (cdr st))
      st)))

; One row of Poseidon::apply_mds: sum over j of state[j] * mds[i][j].
(defund hpos-mds-row (st row p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom st)
      0
    (pfield::add (pfield::mul (car st) (ifix (car row)) p)
                 (hpos-mds-row (cdr st) (cdr row) p)
                 p)))

(defund hpos-apply-mds-rows (st rows p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rows)
      nil
    (cons (hpos-mds-row st (car rows) p)
          (hpos-apply-mds-rows st (cdr rows) p))))

; Poseidon::apply_mds: new_state[i] for i in 0..state.len().
(defund hpos-apply-mds (st mds p)
  (declare (xargs :guard t :verify-guards nil))
  (hpos-apply-mds-rows st (take (len st) mds) p))

(defund hpos-full-round-p (i full partial)
  (declare (xargs :guard t))
  (let ((half (floor (nfix full) 2)))
    (not (and (<= half (nfix i))
              (< (nfix i) (+ half (nfix partial)))))))

(defund hpos-round (st i ark mds alpha full partial p)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((st (hpos-apply-ark st (nth i ark) p))
         (st (hpos-apply-s-box st alpha
                                  (hpos-full-round-p i full partial) p)))
    (hpos-apply-mds st mds p)))

; Rounds i .. full + partial - 1.
(defund hpos-rounds (st i ark mds alpha full partial p)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (+ (nfix full) (nfix partial)) (nfix i)))))
  (if (< (nfix i) (+ (nfix full) (nfix partial)))
      (hpos-rounds (hpos-round st (nfix i) ark mds alpha full partial p)
                   (1+ (nfix i)) ark mds alpha full partial p)
    st))

;; Parameters: (list ark mds alpha full partial p), in snarkVM's
;; Poseidon {full_rounds, partial_rounds, alpha, ark, mds} order of use.

(defund hpos-params (ark mds alpha full partial p)
  (declare (xargs :guard t))
  (list ark mds alpha full partial p))

(defund hpos-params->ark (params) (declare (xargs :verify-guards nil)) (nth 0 params))
(defund hpos-params->mds (params) (declare (xargs :verify-guards nil)) (nth 1 params))
(defund hpos-params->alpha (params) (declare (xargs :verify-guards nil)) (nth 2 params))
(defund hpos-params->full (params) (declare (xargs :verify-guards nil)) (nth 3 params))
(defund hpos-params->partial (params) (declare (xargs :verify-guards nil)) (nth 4 params))
(defund hpos-params->prime (params) (declare (xargs :verify-guards nil)) (nth 5 params))

; Poseidon::permute.
(defund hpos-permute (st params)
  (declare (xargs :guard t :verify-guards nil))
  (hpos-rounds st 0
               (hpos-params->ark params)
               (hpos-params->mds params)
               (hpos-params->alpha params)
               (hpos-params->full params)
               (hpos-params->partial params)
               (hpos-params->prime params)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Duplex sponge.  A mode is (:absorbing . next_absorb_index) or
;; (:squeezing . next_squeeze_index).

; state[pos + i] += elems[i].
(defund hpos-add-into (st pos elems p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom elems)
      st
    (hpos-add-into (update-nth (nfix pos)
                               (pfield::add (nth (nfix pos) st) (car elems) p)
                               st)
                   (1+ (nfix pos)) (cdr elems) p)))

; The loop of Poseidon::absorb, from absorb_index; returns (mv state mode).
(defund hpos-absorb-loop (st idx remaining rate params)
  (declare (xargs :guard t :verify-guards nil
                  :measure (len remaining)))
  (let ((idx (nfix idx))
        (rate (nfix rate))
        (p (hpos-params->prime params)))
    (cond
     ((<= (+ idx (len remaining)) rate)
      (mv (hpos-add-into st (+ 1 idx) remaining p)
          (cons :absorbing (+ idx (len remaining)))))
     ;; Unreachable: absorb never starts the loop at idx = RATE.
     ((<= rate idx) (mv st (cons :absorbing idx)))
     (t
      (let* ((k (- rate idx))
             (st (hpos-add-into st (+ 1 idx) (take k remaining) p))
             (st (hpos-permute st params)))
        (hpos-absorb-loop st 0 (nthcdr k remaining) rate params))))))

; Poseidon::absorb.
(defund hpos-absorb (st mode input rate params)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom input)
      (mv st mode)
    (b* (((mv idx should-permute)
          (if (eq (car mode) :absorbing)
              (if (equal (cdr mode) (nfix rate))
                  (mv 0 t)
                (mv (cdr mode) nil))
            (mv 0 t)))
         (st (if should-permute (hpos-permute st params) st)))
      (hpos-absorb-loop st idx input rate params))))

; The loop of Poseidon::squeeze_internal; returns (mv outputs state mode).
(defund hpos-squeeze-loop (st idx n rate params)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix n)))
  (let ((idx (nfix idx))
        (n (nfix n))
        (rate (nfix rate)))
    (cond
     ((<= (+ idx n) rate)
      (mv (take n (nthcdr (+ 1 idx) st))
          st
          (cons :squeezing (+ idx n))))
     ;; Unreachable: squeeze_internal never starts the loop at idx = RATE.
     ((<= rate idx) (mv (repeat n 0) st (cons :squeezing idx)))
     (t
      (b* ((k (- rate idx))
           (out1 (take k (nthcdr (+ 1 idx) st)))
           (st (hpos-permute st params))
           ((mv out2 st mode)
            (hpos-squeeze-loop st 0 (- n k) rate params)))
        (mv (append out1 out2) st mode))))))

; Poseidon::squeeze_internal.
(defund hpos-squeeze-internal (st mode n rate params)
  (declare (xargs :guard t :verify-guards nil))
  (b* (((mv idx should-permute)
        (if (eq (car mode) :absorbing)
            (mv 0 t)
          (if (equal (cdr mode) (nfix rate))
              (mv 0 t)
            (mv (cdr mode) nil))))
       (st (if should-permute (hpos-permute st params) st)))
    (hpos-squeeze-loop st idx n rate params)))

; Poseidon::squeeze.
(defund hpos-squeeze (st mode n rate params)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n)
      (mv nil st mode)
    (hpos-squeeze-internal st mode n rate params)))

; The preimage [DOMAIN, LEN, 0 ... 0] resized to RATE, then INPUT.
(defund hpos-preimage (domain inputs rate p)
  (declare (xargs :guard t :verify-guards nil))
  (append (take (nfix rate)
                (list* domain (mod (len inputs) p) (repeat (nfix rate) 0)))
          inputs))

; HashMany::hash_many for Poseidon<RATE> with the given domain and parameters.
(defund hpos-hash-many (domain inputs num-outputs rate params)
  (declare (xargs :guard t :verify-guards nil))
  (b* ((st (repeat (+ 1 (nfix rate)) 0))
       (mode (cons :absorbing 0))
       ((mv st mode)
        (hpos-absorb st mode
                     (hpos-preimage domain inputs rate
                                    (hpos-params->prime params))
                     rate params))
       ((mv outs & &) (hpos-squeeze st mode num-outputs rate params)))
    outs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Result type and length.

(local
 (defthm hpos-fe-listp-of-take
   (implies (and (pfield::fe-listp x p) (<= (nfix n) (len x)))
            (pfield::fe-listp (take n x) p))
   :hints (("Goal" :in-theory (enable take pfield::fe-listp)))))

(local
 (defthm hpos-fe-listp-of-nthcdr
   (implies (pfield::fe-listp x p)
            (pfield::fe-listp (nthcdr n x) p))
   :hints (("Goal" :in-theory (enable nthcdr pfield::fe-listp)))))

(defrule hpos-len-of-hpos-apply-ark
  (equal (len (hpos-apply-ark st row p)) (len st))
  :enable hpos-apply-ark)

(defrule hpos-fe-listp-of-hpos-apply-ark
  (implies (dm::primep p)
           (pfield::fe-listp (hpos-apply-ark st row p) p))
  :enable (hpos-apply-ark pfield::fe-listp))

(defrule hpos-len-of-hpos-apply-s-box
  (equal (len (hpos-apply-s-box st alpha full-p p)) (len st))
  :enable (hpos-apply-s-box hpos-s-box-all))

(defrule hpos-fe-listp-of-hpos-s-box-all
  (implies (and (dm::primep p) (pfield::fe-listp st p))
           (pfield::fe-listp (hpos-s-box-all st alpha p) p))
  :enable (hpos-s-box-all pfield::fe-listp))

(defrule hpos-fe-listp-of-hpos-apply-s-box
  (implies (and (dm::primep p) (pfield::fe-listp st p))
           (pfield::fe-listp (hpos-apply-s-box st alpha full-p p) p))
  :enable (hpos-apply-s-box pfield::fe-listp))

(defrule hpos-len-of-hpos-apply-mds-rows
  (equal (len (hpos-apply-mds-rows st rows p)) (len rows))
  :enable hpos-apply-mds-rows)

(defrule hpos-fe-listp-of-hpos-apply-mds-rows
  (implies (dm::primep p)
           (pfield::fe-listp (hpos-apply-mds-rows st rows p) p))
  :enable (hpos-apply-mds-rows hpos-mds-row pfield::fe-listp))

(defrule hpos-len-of-hpos-apply-mds
  (implies (<= (len st) (len mds))
           (equal (len (hpos-apply-mds st mds p)) (len st)))
  :enable hpos-apply-mds)

(defrule hpos-fe-listp-of-hpos-apply-mds
  (implies (dm::primep p)
           (pfield::fe-listp (hpos-apply-mds st mds p) p))
  :enable hpos-apply-mds)

(defrule hpos-fe-listp-of-hpos-round
  (implies (dm::primep p)
           (pfield::fe-listp (hpos-round st i ark mds alpha full partial p) p))
  :enable hpos-round)

(defrule hpos-len-of-hpos-round
  (implies (<= (len st) (len mds))
           (equal (len (hpos-round st i ark mds alpha full partial p))
                  (len st)))
  :enable hpos-round)

(defrule hpos-len-of-hpos-rounds
  (implies (<= (len st) (len mds))
           (equal (len (hpos-rounds st i ark mds alpha full partial p))
                  (len st)))
  :enable hpos-rounds)

(defrule hpos-len-of-hpos-permute
  (implies (<= (len st) (len (hpos-params->mds params)))
           (equal (len (hpos-permute st params)) (len st)))
  :enable hpos-permute)

(defrule hpos-len-of-hpos-squeeze-loop
  (implies (and (<= (+ 1 (nfix rate)) (len st))
                (<= (len st) (len (hpos-params->mds params))))
           (equal (len (mv-nth 0 (hpos-squeeze-loop st idx n rate params)))
                  (nfix n)))
  :induct (hpos-squeeze-loop st idx n rate params)
  :enable hpos-squeeze-loop)

(defrule hpos-len-of-hpos-squeeze
  (implies (and (<= (+ 1 (nfix rate)) (len st))
                (<= (len st) (len (hpos-params->mds params))))
           (equal (len (mv-nth 0 (hpos-squeeze st mode n rate params)))
                  (nfix n)))
  :enable (hpos-squeeze hpos-squeeze-internal))

(defrule hpos-len-of-hpos-add-into
  (implies (<= (+ (nfix pos) (len elems)) (len st))
           (equal (len (hpos-add-into st pos elems p)) (len st)))
  :enable hpos-add-into)

(defrule hpos-len-of-hpos-absorb-loop
  (implies (and (equal (len st) (+ 1 (nfix rate)))
                (<= (len st) (len (hpos-params->mds params)))
                (<= (nfix idx) (nfix rate)))
           (equal (len (mv-nth 0 (hpos-absorb-loop st idx remaining rate params)))
                  (len st)))
  :induct (hpos-absorb-loop st idx remaining rate params)
  :enable hpos-absorb-loop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Aleo instances.

(define hpos-domain-fe ((domain stringp))
  :verify-guards nil
  :short "snarkVM @('Field::new_domain_separator'): the string's bytes, little endian."
  (mod (acl2::lendian=>nat 256 (acl2::chars=>nats (acl2::explode domain)))
       primes::*bls12-377-scalar-field-prime*))

(define hpos-param-instance ((param poseidon::paramp))
  :verify-guards nil
  :short "The generic parameters of a @('projects/poseidon') instance."
  (hpos-params (poseidon::param->constants param)
               (poseidon::param->mds param)
               (poseidon::param->alpha param)
               (* 2 (poseidon::param->full-rounds-half param))
               (poseidon::param->partial-rounds param)
               (poseidon::param->prime param)))

(define hpos-aleo-params (rate)
  :verify-guards nil
  :short "Parameters of snarkVM's @('Poseidon2/4/8') (rate 2, 4, 8; alpha 17)."
  (case rate
    (2 (hpos-param-instance (poseidon::rate-2-alpha-17-parameters)))
    (4 (hpos-param-instance (poseidon::rate-4-alpha-17-parameters)))
    (t (hpos-param-instance (poseidon::rate-8-alpha-17-parameters)))))

(define hpos-aleo-rate-p (rate)
  :verify-guards nil
  (and (member-equal rate '(2 4 8)) t))

(define hpos-aleo-domain (rate)
  :verify-guards nil
  :short "The network domain separators AleoPoseidon2/4/8 (mainnet_v0.rs)."
  (case rate
    (2 (hpos-domain-fe "AleoPoseidon2"))
    (4 (hpos-domain-fe "AleoPoseidon4"))
    (t (hpos-domain-fe "AleoPoseidon8"))))

(define hpos-zeros ((n natp))
  (if (zp n) nil (cons 0 (hpos-zeros (1- n))))
  ///
  (defrule hpos-len-of-hpos-zeros
    (equal (len (hpos-zeros n)) (nfix n)))
  (defrule hpos-fe-listp-of-hpos-zeros
    (implies (dm::primep p) (pfield::fe-listp (hpos-zeros n) p))
    :enable pfield::fe-listp))

(define hpos-poseidon-hash-many (rate inputs num-outputs)
  :short "Concrete @('poseidon-hash-many') of @('fun-specs/base.lisp')."
  :long "<p>For rate 2, 4 and 8 this is snarkVM's network instance
  @('Poseidon{rate}::setup(\"AleoPoseidon{rate}\").hash_many(inputs, num_outputs)').
  Other values of the first argument name no network Poseidon instance;
  the result is then @('num_outputs') zeros so that the type and length
  constraints of the stub hold for every argument.  Inputs that are not
  field elements are not reachable from the circuits.</p>"
  :verify-guards nil
  (if (hpos-aleo-rate-p rate)
      (hpos-hash-many (hpos-aleo-domain rate)
                      inputs num-outputs rate (hpos-aleo-params rate))
    (hpos-zeros num-outputs)))

(define hpos-poseidon-hash (rate inputs)
  :short "Concrete @('poseidon-hash'): @('Poseidon::hash'), the first output
          of @('hash_many(inputs, 1)')."
  :verify-guards nil
  (car (hpos-poseidon-hash-many rate inputs 1)))

(define hpos-hash-to-scalar (rate inputs)
  :short "@('Poseidon::hash_to_scalar'): @('Scalar::from_field_lossy') of
          @('hash(inputs)'), i.e. its low 250 bits."
  :verify-guards nil
  (mod (nfix (hpos-poseidon-hash rate inputs)) (expt 2 250)))

(define hpos-hash-to-group-fields (rate inputs)
  :short "The field elements that @('Poseidon::hash_to_group') encodes."
  :long "<p>@('hash_to_group') halts on empty input (result @(':halt'));
  otherwise it computes @('[h0, h1] = hash_many(inputs, 2)') and returns
  @('Elligator2::encode(h1) + Elligator2::encode(h0)').  This function
  returns @('(h1 h0)'); the group part is @('crypto-hash-to-group-psd') of
  @('crypto-model.lisp').</p>"
  :verify-guards nil
  (if (endp inputs)
      :halt
    (let ((hs (hpos-poseidon-hash-many rate inputs 2)))
      (list (second hs) (first hs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cross-check against projects/poseidon (domains "Poseidon2/4/8").

(defmacro hpos-check (rate hash-many domain-fn inputs count)
  `(assert-event
    (equal (hpos-hash-many (,domain-fn) ',inputs ,count ,rate (hpos-aleo-params ,rate))
           (,hash-many ',inputs ,count))))

(hpos-check 2 poseidon::hash2-many poseidon::rate-2-domain-fe () 1)
(hpos-check 2 poseidon::hash2-many poseidon::rate-2-domain-fe (1 2 3) 5)
(hpos-check 4 poseidon::hash4-many poseidon::rate-4-domain-fe (0 1) 1)
(hpos-check 4 poseidon::hash4-many poseidon::rate-4-domain-fe (7 6 5 4 3) 9)
(hpos-check 8 poseidon::hash8-many poseidon::rate-8-domain-fe (1) 2)
(hpos-check 8 poseidon::hash8-many poseidon::rate-8-domain-fe
            (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17) 17)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The constraints that fun-specs/base.lisp states for poseidon-hash-many.

(defruled hpos-aleo-params-shape
  (implies (hpos-aleo-rate-p rate)
           (and (natp rate)
                (equal (len (hpos-params->mds (hpos-aleo-params rate)))
                       (+ 1 rate))
                (equal (hpos-params->prime (hpos-aleo-params rate))
                       primes::*bls12-377-scalar-field-prime*)))
  :enable (hpos-aleo-rate-p hpos-aleo-params hpos-param-instance hpos-params
           hpos-params->mds hpos-params->prime))

(defrule hpos-len-of-hpos-absorb
  (implies (and (equal (len st) (+ 1 (nfix rate)))
                (<= (len st) (len (hpos-params->mds params)))
                (or (not (eq (car mode) :absorbing))
                    (<= (nfix (cdr mode)) (nfix rate))))
           (equal (len (mv-nth 0 (hpos-absorb st mode input rate params)))
                  (len st)))
  :do-not-induct t
  :enable hpos-absorb
  :disable hpos-len-of-hpos-absorb-loop
  :use ((:instance hpos-len-of-hpos-absorb-loop (idx (cdr mode)) (remaining input))
        (:instance hpos-len-of-hpos-absorb-loop (idx 0) (remaining input)
                   (st (hpos-permute st params)))))

(defrule hpos-len-of-hpos-hash-many
  (implies (<= (+ 1 (nfix rate)) (len (hpos-params->mds params)))
           (equal (len (hpos-hash-many domain inputs num-outputs rate params))
                  (nfix num-outputs)))
  :enable hpos-hash-many)

(local
 (defthm hpos-fe-listp-of-append
   (equal (pfield::fe-listp (append x y) p)
          (and (pfield::fe-listp (true-list-fix x) p) (pfield::fe-listp y p)))
   :hints (("Goal" :in-theory (enable pfield::fe-listp append)))))

(defrule hpos-fe-listp-of-hpos-rounds
  (implies (and (dm::primep p) (pfield::fe-listp st p))
           (pfield::fe-listp (hpos-rounds st i ark mds alpha full partial p) p))
  :enable hpos-rounds)

(defrule hpos-fe-listp-of-hpos-permute
  (implies (and (dm::primep (hpos-params->prime params))
                (pfield::fe-listp st (hpos-params->prime params)))
           (pfield::fe-listp (hpos-permute st params)
                             (hpos-params->prime params)))
  :enable hpos-permute)

(defrule hpos-fe-listp-of-update-nth
  (implies (and (pfield::fe-listp l p) (pfield::fep v p) (< (nfix n) (len l)))
           (pfield::fe-listp (update-nth n v l) p))
  :enable (pfield::fe-listp update-nth))

(defrule hpos-fe-listp-of-hpos-add-into
  (implies (and (dm::primep p) (pfield::fe-listp st p)
                (<= (+ (nfix pos) (len elems)) (len st)))
           (pfield::fe-listp (hpos-add-into st pos elems p) p))
  :enable hpos-add-into)

(defrule hpos-fe-listp-of-hpos-absorb-loop
  (b* ((p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (pfield::fe-listp st p)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (len st) (len (hpos-params->mds params)))
                  (<= (nfix idx) (nfix rate)))
             (pfield::fe-listp
              (mv-nth 0 (hpos-absorb-loop st idx remaining rate params)) p)))
  :induct (hpos-absorb-loop st idx remaining rate params)
  :enable hpos-absorb-loop)

(defrule hpos-fe-listp-of-hpos-absorb
  (b* ((p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (pfield::fe-listp st p)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (len st) (len (hpos-params->mds params)))
                  (or (not (eq (car mode) :absorbing))
                      (<= (nfix (cdr mode)) (nfix rate))))
             (pfield::fe-listp
              (mv-nth 0 (hpos-absorb st mode input rate params)) p)))
  :do-not-induct t
  :enable hpos-absorb
  :disable hpos-fe-listp-of-hpos-absorb-loop
  :use ((:instance hpos-fe-listp-of-hpos-absorb-loop (idx (cdr mode)) (remaining input))
        (:instance hpos-fe-listp-of-hpos-absorb-loop (idx 0) (remaining input)
                   (st (hpos-permute st params)))))

(defrule hpos-fe-listp-of-hpos-squeeze-loop
  (b* ((p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (pfield::fe-listp st p)
                  (<= (+ 1 (nfix rate)) (len st))
                  (<= (len st) (len (hpos-params->mds params))))
             (pfield::fe-listp
              (mv-nth 0 (hpos-squeeze-loop st idx n rate params)) p)))
  :induct (hpos-squeeze-loop st idx n rate params)
  :enable (hpos-squeeze-loop pfield::fe-listp-of-repeat))

(defrule hpos-fe-listp-of-hpos-squeeze
  (b* ((p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (pfield::fe-listp st p)
                  (<= (+ 1 (nfix rate)) (len st))
                  (<= (len st) (len (hpos-params->mds params))))
             (pfield::fe-listp
              (mv-nth 0 (hpos-squeeze st mode n rate params)) p)))
  :enable (hpos-squeeze hpos-squeeze-internal))

(defrule hpos-fe-listp-of-hpos-hash-many
  (b* ((p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (<= (+ 1 (nfix rate)) (len (hpos-params->mds params))))
             (pfield::fe-listp
              (hpos-hash-many domain inputs num-outputs rate params) p)))
  :enable (hpos-hash-many pfield::fe-listp-of-repeat)
  :disable (hpos-fe-listp-of-hpos-absorb)
  :use (:instance hpos-fe-listp-of-hpos-absorb
        (st (repeat (+ 1 (nfix rate)) 0))
        (mode (cons :absorbing 0))
        (input (hpos-preimage domain inputs rate (hpos-params->prime params)))))

(defrule hpos-fe-listp-of-hpos-poseidon-hash-many
  (pfield::fe-listp (hpos-poseidon-hash-many rate inputs num-outputs)
                    primes::*bls12-377-scalar-field-prime*)
  :enable (hpos-poseidon-hash-many)
  :use (hpos-aleo-params-shape
        (:instance hpos-fe-listp-of-hpos-hash-many
                   (domain (hpos-aleo-domain rate))
                   (params (hpos-aleo-params rate)))))

(defrule hpos-true-listp-of-hpos-poseidon-hash-many
  (true-listp (hpos-poseidon-hash-many rate inputs num-outputs))
  :rule-classes (:rewrite :type-prescription)
  :use hpos-fe-listp-of-hpos-poseidon-hash-many
  :disable hpos-fe-listp-of-hpos-poseidon-hash-many
  :enable pfield::true-listp-when-fe-listp)

(local
 (defthm hpos-nfix-when-natp
   (implies (natp x) (equal (nfix x) x))))

(defrule hpos-len-of-hpos-poseidon-hash-many
  (equal (len (hpos-poseidon-hash-many rate inputs num-outputs))
         (nfix num-outputs))
  :enable (hpos-poseidon-hash-many)
  :disable (nfix hpos-len-of-hpos-hash-many)
  :use (hpos-aleo-params-shape
        (:instance hpos-len-of-hpos-hash-many
                   (domain (hpos-aleo-domain rate))
                   (params (hpos-aleo-params rate)))))
