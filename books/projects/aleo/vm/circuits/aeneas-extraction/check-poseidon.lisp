; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for the Poseidon permutation and sponge against the
; hpos-c- circuit generators, which are generic over the rate, the rounds and
; the constants. Both sides use the test parameters of pos_test in
; src/circuits.rs: ark[i][j] = 7i + j + 3, mds[i][j] = i + 2j + 1, domain 5,
; alpha 17. The generators are run on the input wires with fresh variables
; V0, V1, ... and an empty assignment.

(include-book "check-lib")
(include-book "../fun-circuits/hpos-hash-to-scalar")
(include-book "../fun-circuits/enc-record-enc")
(include-book "../fun-circuits/dec-record-decrypt")
(include-book "../edwards-order/bls12-points")

(local (include-book "arithmetic-3/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pos-row (f i j n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix j)))))
  (if (zp (- (nfix n) (nfix j)))
      nil
    (cons (if (eq f :ark) (+ (* 7 i) j 3) (+ i (* 2 j) 1))
          (pos-row f i (1+ (nfix j)) n))))

(defun pos-rows (f i m n)
  (declare (xargs :measure (nfix (- (nfix m) (nfix i)))))
  (if (zp (- (nfix m) (nfix i)))
      nil
    (cons (pos-row f i 0 n) (pos-rows f (1+ (nfix i)) m n))))

(defun pos-params (rate full partial)
  (hpos-params (pos-rows :ark 0 (+ full partial) (1+ rate))
               (pos-rows :mds 0 (1+ rate) (1+ rate))
               17 full partial (base-prime)))

(defun pos-bits-be (k n)
  (if (zp n) nil (cons (if (logbitp (1- n) k) 1 0) (pos-bits-be k (1- n)))))

(defconst *pos-bits* (pos-bits-be 17 253))

(defun pos-vars (lo n)
  (if (zp n) nil (cons (hpos-lc-var (wv lo)) (pos-vars (1+ (nfix lo)) (1- n)))))

(defconst *pos-vs* (gs "V" 8000))

(defun pos-permute-check (rate full partial)
  (b* (((mv & cs & &)
        (hpos-c-permute (pos-vars 1 (1+ rate)) (pos-params rate full partial)
                        *pos-bits* *pos-vs* nil)))
    (same-circuit-renamed
     (ext-run (acl2::circuits-h-poseidon *fuel* 0 rate full partial 0 0 nil 0))
     cs (wvs 1 (1+ rate)) nil)))

; permute covers apply_ark, apply_s_box (full and partial rounds) and
; apply_mds.
(defcheck poseidon-permute-extraction
  (and (pos-permute-check 2 2 1) (pos-permute-check 2 4 3) (pos-permute-check 4 2 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The network instances (hpos-aleo-params, hpos-aleo-domain): the model's
; pos_named takes every ark, mds and domain constant by name, numbered as
; in pos_named, and the checks give their values.

(defun pos-named-row (row k)
  (if (atom row) nil (cons (cons k (car row)) (pos-named-row (cdr row) (1+ k)))))

(defun pos-named-rows (rows k n)
  (if (atom rows)
      nil
    (append (pos-named-row (car rows) k) (pos-named-rows (cdr rows) (+ k n) n))))

(defun pos-aleo-syms (rate)
  (b* ((params (hpos-aleo-params rate))
       (n (1+ rate))
       (rounds (+ (hpos-params->full params) (hpos-params->partial params))))
    (append (pos-named-rows (hpos-params->ark params) 1 n)
            (pos-named-rows (hpos-params->mds params) (+ 1 (* rounds n)) n)
            (list (cons (+ 1 (* (+ rounds n) n)) (hpos-aleo-domain rate))))))

(defun pos-aleo-run (op rate nin nout)
  (b* ((params (hpos-aleo-params rate)))
    (ext-run-syms (acl2::circuits-h-poseidon *fuel* op rate (hpos-params->full params)
                                             (hpos-params->partial params) nin nout nil 0)
                  (pos-aleo-syms rate))))

(defun pos-hash-many-check (rate nin nout)
  (b* (((mv & cs & &) (hpos-c-poseidon-hash-many rate (pos-vars 1 nin) nout *pos-vs* nil)))
    (same-circuit-renamed (pos-aleo-run 5 rate nin nout) cs (wvs 1 nin) nil)))

; The first RATE preimage elements are constants, so the first permutation
; folds constants, which the model keeps as expressions in Cs::ks.
(defcheck poseidon-hash-many-extraction
  (and (pos-hash-many-check 2 1 1) (pos-hash-many-check 2 3 1)
       (pos-hash-many-check 2 5 3) (pos-hash-many-check 4 2 0)
       (pos-hash-many-check 4 6 5) (pos-hash-many-check 8 2 1)
       (pos-hash-many-check 8 9 2)))

; A state W1..W(rate+1) in mode (sq, idx), nin inputs absorbed, then nout
; squeezed.
(defun pos-sponge-check (rate nin nout sq idx)
  (b* (((mv & cs & &)
        (hpos-c-absorb-squeeze (pos-vars 1 (1+ rate))
                               (cons (if sq :squeezing :absorbing) idx)
                               (pos-vars (+ 2 rate) nin) nout rate
                               (pos-params rate 2 1) *pos-bits* *pos-vs* nil)))
    (same-circuit-renamed
     (ext-run (acl2::circuits-h-poseidon *fuel* 2 rate 2 1 nin nout sq idx))
     cs (wvs 1 (+ 1 rate nin)) nil)))

; absorb, squeeze and squeeze_internal from each mode, including a full
; absorbing index, a full squeezing index and empty inputs and outputs.
(defcheck poseidon-sponge-extraction
  (and (pos-sponge-check 2 0 0 nil 0) (pos-sponge-check 2 1 1 nil 0)
       (pos-sponge-check 2 3 2 nil 1) (pos-sponge-check 2 2 1 nil 2)
       (pos-sponge-check 2 1 3 t 0) (pos-sponge-check 2 4 2 t 2)
       (pos-sponge-check 2 0 3 t 1) (pos-sponge-check 2 0 1 t 2)
       (pos-sponge-check 4 5 4 nil 3)))

; hash_to_scalar: hash_many to one output and then Scalar::from_field_lossy
; on it, on the network instances.
(defun pos-hash-to-scalar-check (rate nin)
  (b* (((mv outs cs1 vs asg)
        (hpos-c-poseidon-hash-many rate (pos-vars 1 nin) 1 *pos-vs* nil))
       ((mv & cs2 & &) (hpos-c-lc-to-scalar-bits (car outs) 'u vs asg)))
    (same-circuit-renamed (pos-aleo-run 6 rate nin 0)
                          (append cs1 cs2) (wvs 1 nin) '((u . 1)))))

(defcheck poseidon-hash-to-scalar-extraction
  (and (pos-hash-to-scalar-check 2 1) (pos-hash-to-scalar-check 2 3)
       (pos-hash-to-scalar-check 4 2) (pos-hash-to-scalar-check 8 1)))

(defun pos-new-constraints (rate)
  (mv-let (domain params cs) (hpos-c-new rate)
    (declare (ignore domain params))
    cs))

(defcheck poseidon-new-extraction
  (and (equal (ext-run (acl2::circuits-h-poseidon *fuel* 4 2 2 1 0 0 nil 0))
              (pos-new-constraints 2))
       (equal (pos-new-constraints 4) nil)
       (equal (pos-new-constraints 8) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; net-gbase is 2^i G by edwards-bls12-mul, which adds G 2^i times, so the
; gadgets that fold the generator powers cannot be evaluated. The fast-
; copies use double-and-add (te-mul-fast-exec) and are proved equal; the
; record checks rewrite the gadgets to them before evaluating.

(defun fast-gbase (i)
  (ecurve::te-mul-fast-exec (expt 2 (nfix i)) (curve-generator-g)
                            (ecurve::edwards-bls12-curve)))

(defruled curve-generator-g-on-curve
  (ecurve::point-on-twisted-edwards-p (curve-generator-g)
                                      (ecurve::edwards-bls12-curve))
  :use edwards-bls12-pointp-of-curve-generator-g
  :in-theory '(ecurve::edwards-bls12-pointp))

(defruled net-gbase-is-fast
  (equal (net-gbase i) (fast-gbase i))
  :use (curve-generator-g-on-curve
        (:instance ecurve::twisted-edwards-mul-is-exec
                   (scalar (expt 2 (nfix i)))
                   (ecurve::point (curve-generator-g))
                   (ecurve::curve (ecurve::edwards-bls12-curve))))
  :in-theory (e/d (net-gbase fast-gbase ecurve::edwards-bls12-mul)
                  (ecurve::te-mul-fast-exec)))

(defun fast-gfold (bits sts i ax ay p)
  (if (endp bits)
      nil
    (append (net-gstep-gadget ax ay (car bits) (fast-gbase i) (car sts) p)
            (fast-gfold (cdr bits) (cdr sts) (1+ (lnfix i))
                        (list (list 1 (nth 3 (car sts))))
                        (list (list 1 (nth 4 (car sts))))
                        p))))

(defruled net-gfold-is-fast
  (equal (net-gfold-gadget bits sts i ax ay p) (fast-gfold bits sts i ax ay p))
  :induct (fast-gfold bits sts i ax ay p)
  :in-theory (enable net-gfold-gadget net-gbase-is-fast))

(defun fast-gmul (s rbits rs sts p)
  (append (scalar-write-bits-le-gadget s rbits rs p)
          (fast-gfold (cdr rbits) sts 1
                      (hbhp-tern-x (car rbits) (curve-generator-g))
                      (hbhp-tern-y (car rbits) (curve-generator-g) p)
                      p)))

(defruled net-gmul-is-fast
  (equal (net-gmul-gadget s rbits rs sts p) (fast-gmul s rbits rs sts p))
  :in-theory (enable net-gmul-gadget net-gfold-is-fast))

(defruled enc-c-rec-sym-is-fast
  (equal (mv-nth 2 (enc-c-rec-sym pubp og data ng s rbits rs sts steps ox oy vs asg))
         (append (append (fast-gmul s rbits rs sts (base-prime))
                         (enc-nonce-gadget (net-gmul-out rbits sts (base-prime)) ng)
                         (grp-mul-gadget (rev rbits) ox oy steps (nth 0 og) (nth 1 og)
                                         (base-prime)))
                 (mv-nth 1 (enc-c-rec-sym-unchecked
                            pubp data (enc-rec-sym-key rbits ox oy steps) vs asg))))
  :in-theory (e/d (enc-c-rec-sym enc-rec-sym-prefix net-gmul-is-fast)
                  ((:e base-prime))))

(defruled dec-c-rdec-is-fast
  (equal (mv-nth 2 (dec-c-rdec pubp og oc ow data ng s rbits rs sts steps ox oy vs asg))
         (append (append (fast-gmul s rbits rs sts (base-prime))
                         (grp-mul-gadget (rev rbits) ox oy steps (nth 0 ng) (nth 1 ng)
                                         (base-prime)))
                 (mv-nth 2 (dec-c-crec-sym pubp oc ow data
                                           (enc-rec-sym-key rbits ox oy steps) vs asg))
                 (enc-nonce-gadget (net-gmul-out rbits sts (base-prime))
                                   (if pubp og ow))))
  :in-theory (e/d (dec-c-rdec dec-rdec-prefix net-gmul-is-fast)
                  ((:e base-prime))))

; The theory for a record check: evaluation, except of the gadgets that fold
; the generator powers, which are rewritten to their fast copies.
(defmacro rec-check-theory (check)
  `(union-theories
    '(,check net-gfold-is-fast enc-c-rec-sym-is-fast dec-c-rdec-is-fast)
    (set-difference-theories
     (executable-counterpart-theory :here)
     '((:e ,check) (:e net-gbase) (:e net-gfold-gadget) (:e net-gmul-gadget)
       (:e enc-c-rec-sym) (:e enc-rec-sym-prefix) (:e dec-c-rdec)
       (:e dec-rdec-prefix)))))

; Record::encrypt_symmetric of a record with no entries, with a private or a
; public owner: owner W1, W2, nonce W3, W4 and randomizer W5. The named
; constants are the Poseidon8 parameters, the encryption domain (5000) and
; the generator powers 2^i G (10000 + 2i and 10001 + 2i).

(defun gen-power-syms (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (list* (cons (+ 10000 (* 2 i)) (ecurve::point-finite->x (fast-gbase i)))
           (cons (+ 10001 (* 2 i)) (ecurve::point-finite->y (fast-gbase i)))
           (gen-power-syms (1+ (nfix i)) n))))

(defun gsteps2 (prefix k n)
  (if (zp k)
      nil
    (append (gsteps2 prefix (1- k) n)
            (list (gs (acl2::packn-pos (list prefix (1- k) "-") 'wv) n)))))

(defun record-encrypt-check (pubp)
  (b* ((params (hpos-aleo-params 8))
       (syms (append (pos-aleo-syms 8)
                     (list (cons 5000 (values-encryption-domain)))
                     (gen-power-syms 0 251)))
       (ext (ext-run-syms (acl2::circuits-h-rec-encrypt-symmetric
                           *fuel* (not pubp) (hpos-params->full params)
                           (hpos-params->partial params))
                          syms))
       ((mv & & cs & &)
        (enc-c-rec-sym pubp (list (wv 1) (wv 2)) nil
                       (append (list (wv 3) (wv 4)) (gs "NG" 12))
                       (wv 5) (gs "B" 251) (gs "RS" 250) (gsteps2 "N" 250 5)
                       (gsteps2 "M" 250 13) 'ox 'oy *pos-vs* nil)))
    (same-circuit-renamed ext cs (wvs 1 5) nil)))

(defthm record-encrypt-symmetric-extraction
  (and (record-encrypt-check nil)
       (record-encrypt-check t))
  :hints (("Goal" :in-theory (rec-check-theory record-encrypt-check)))
  :rule-classes nil)

; Record::decrypt for a public owner W1, W2, nonce W3, W4 and view key W5,
; with no entries. snarkVM emits Scalar::to_bits_le, the nonce times the view
; key, hash_many_psd8 of the encryption domain and the record view key, and
; then to_address, which reuses the cached bits, against the owner.
; dec-c-rdec emits the to_address fold before the multiplication, so the
; extraction is compared with the gadgets in snarkVM's order, and that list
; with dec-c-rdec up to constraint order.
(defun record-decrypt-public-check ()
  (b* ((p (base-prime))
       (params (hpos-aleo-params 8))
       (syms (append (pos-aleo-syms 8)
                     (list (cons 5000 (values-encryption-domain)))
                     (gen-power-syms 0 251)))
       (ext (ext-run-syms (acl2::circuits-h-rec-decrypt-public
                           *fuel* (hpos-params->full params) (hpos-params->partial params))
                          syms))
       (bits (gs "B" 251))
       (steps (gsteps2 "M" 250 13))
       (sts (gsteps2 "N" 250 5))
       (key (car (grp-mul-out (rev bits) 'ox 'oy steps)))
       ((mv & hcs & &)
        (hpos-c-poseidon-hash-many 8 (enc-randomizer-inputs key) 0 *pos-vs* nil))
       (g (curve-generator-g))
       (ordered
        (append (scalar-write-bits-le-gadget (wv 5) bits (gs "RS" 250) p)
             (grp-mul-gadget (rev bits) 'ox 'oy steps (wv 3) (wv 4) p)
             hcs
             (net-gfold-gadget (cdr bits) sts 1
                               (hbhp-tern-x (car bits) g) (hbhp-tern-y (car bits) g p) p)
             (enc-nonce-gadget (net-gmul-out bits sts p) (list (wv 1) (wv 2)))))
       ((mv & & dcs & &)
        (dec-c-rdec t (list (wv 1) (wv 2)) nil nil nil
                    (append (list (wv 3) (wv 4)) (gs "NG" 12))
                    (wv 5) bits (gs "RS" 250) sts steps 'ox 'oy *pos-vs* nil)))
    (and (same-circuit-renamed ext ordered (wvs 1 5) nil)
         (same-circuit-unordered ordered dcs nil))))

(defthm record-decrypt-public-extraction
  (record-decrypt-public-check)
  :hints (("Goal" :in-theory (rec-check-theory record-decrypt-public-check)))
  :rule-classes nil)
