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

(defconst *pos-vs* (gs "V" 4000))

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

(defun pos-hash-many-check (rate full partial nin nout)
  (b* (((mv & cs & &)
        (hpos-c-hash-many 5 (pos-vars 1 nin) nout rate (pos-params rate full partial)
                          *pos-bits* *pos-vs* nil)))
    (same-circuit-renamed
     (ext-run (acl2::circuits-h-poseidon *fuel* 1 rate full partial nin nout nil 0))
     cs (wvs 1 nin) nil)))

;
; The first RATE preimage elements are constants, so hash_many's first
; permutation runs on constants; snarkVM folds them mod p, which the model's
; i128 constants cannot. hash_many and hash_to_scalar are therefore checked
; with zero rounds, and the rounds by the permute and sponge checks.
(defcheck poseidon-hash-many-extraction
  (and (pos-hash-many-check 2 0 0 1 1) (pos-hash-many-check 2 0 0 3 1)
       (pos-hash-many-check 2 0 0 5 3) (pos-hash-many-check 4 0 0 2 0)
       (pos-hash-many-check 4 0 0 6 5)))

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

; hash_to_scalar: hpos-c-hash-to-scalar with the test parameters (zero
; rounds, as for hash_many) in place of the network instance, that is
; hash_many to one output and then Scalar::from_field_lossy on it.
(defun pos-hash-to-scalar-check (rate nin)
  (b* (((mv outs cs1 vs asg)
        (hpos-c-hash-many 5 (pos-vars 1 nin) 1 rate (pos-params rate 0 0)
                          *pos-bits* *pos-vs* nil))
       ((mv & cs2 & &) (hpos-c-lc-to-scalar-bits (car outs) 'u vs asg)))
    (same-circuit-renamed
     (ext-run (acl2::circuits-h-poseidon *fuel* 3 rate 0 0 nin 0 nil 0))
     (append cs1 cs2) (wvs 1 nin) '((u . 1)))))

(defcheck poseidon-hash-to-scalar-extraction
  (and (pos-hash-to-scalar-check 2 1) (pos-hash-to-scalar-check 2 3)))

(defun pos-new-constraints (rate)
  (mv-let (domain params cs) (hpos-c-new rate)
    (declare (ignore domain params))
    cs))

(defcheck poseidon-new-extraction
  (and (equal (ext-run (acl2::circuits-h-poseidon *fuel* 4 2 2 1 0 0 nil 0))
              (pos-new-constraints 2))
       (equal (pos-new-constraints 4) nil)
       (equal (pos-new-constraints 8) nil)))
