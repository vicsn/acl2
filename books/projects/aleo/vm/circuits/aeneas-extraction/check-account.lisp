; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for ComputeKey::to_fields and Signature::to_fields, which
; add no constraints, for BooleanHash::new, which checks each bit W1..Wn, and
; for the ComputeKey, Signature and BooleanHash equality, the Signature and
; BooleanHash ternary, Signature::write_bits_le and _be, and
; KaryMerklePath::new.

(include-book "check-lib")
(include-book "../fun-circuits/crv-project")
(include-book "../fun-circuits/val-collections")
(include-book "../fun-circuits/crv-account")
(include-book "../fun-circuits/crv-ternary")
(include-book "../fun-circuits/lit-signature")
(include-book "../fun-circuits/gap-boolean-hash")
(include-book "../fun-circuits/gap-kary-path-new")

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcheck compute-key-to-fields-extraction
  (same-circuit (ext-run (acl2::circuits-h-account-to-fields *fuel* 0))
                (crv-compute-key-to-fields-gadget)
                nil))

(defcheck signature-to-fields-extraction
  (same-circuit (ext-run (acl2::circuits-h-account-to-fields *fuel* 1))
                (crv-signature-to-fields-gadget)
                nil))

(defun boolean-hash-new-check (n)
  (same-circuit (ext-run (acl2::circuits-h-bh-new *fuel* n))
                (boolean-hash-new-gadget (wvs 1 n) (base-prime))
                nil))

(defcheck boolean-hash-new-extraction
  (and (boolean-hash-new-check 1)
       (boolean-hash-new-check 2)
       (boolean-hash-new-check 8)))

; ComputeKey (W1..W5) against (W6..W10): the multiplier and result wires of
; the pk_sig (W11..W15) and pr_sig (W16..W20) comparisons, their AND W21, the
; sk_prf comparison W22, W23 and the result W24. snarkVM evaluates
; (pk_sig == pk_sig') & (pr_sig == pr_sig') before sk_prf == sk_prf', so the
; AND W21 precedes the sk_prf constraint.
(defun compute-key-equal-check (op)
  (same-circuit-unordered
   (ext-run (acl2::circuits-h-account-equal *fuel* op))
   (crv-compute-key-is-equal-gadget
    (wv 1) (wv 2) (wv 6) (wv 7) (wv 12) (wv 11) (wv 14) (wv 13) (wv 15)
    (wv 3) (wv 4) (wv 8) (wv 9) (wv 17) (wv 16) (wv 19) (wv 18) (wv 20)
    (wv 5) (wv 10) (wv 23) (wv 22)
    (wv 21) (wv 24) (base-prime))
   nil))

(defcheck compute-key-is-equal-extraction (compute-key-equal-check 0))

(defcheck compute-key-is-not-equal-extraction (compute-key-equal-check 1))

; Signature (W1..W7) against (W8..W14): challenge W15, W16, response W17,
; W18, their AND W19, the compute key comparison W20..W33 and the result W34.
(defun signature-equal-check (op)
  (same-circuit-unordered
   (ext-run (acl2::circuits-h-account-equal *fuel* op))
   (crv-signature-is-equal-gadget
    (wv 1) (wv 8) (wv 16) (wv 15)
    (wv 2) (wv 9) (wv 18) (wv 17)
    (wv 3) (wv 4) (wv 10) (wv 11) (wv 21) (wv 20) (wv 23) (wv 22) (wv 24)
    (wv 5) (wv 6) (wv 12) (wv 13) (wv 26) (wv 25) (wv 28) (wv 27) (wv 29)
    (wv 7) (wv 14) (wv 32) (wv 31)
    (wv 30) (wv 33)
    (wv 19) (wv 34) (base-prime))
   nil))

(defcheck signature-is-equal-extraction (signature-equal-check 2))

(defcheck signature-is-not-equal-extraction (signature-equal-check 3))

(defcheck signature-ternary-extraction
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-sig-ternary *fuel*))
   (crv-signature-ternary-gadget
    (wv 1) (wv 2) (wv 9) (wv 3) (wv 10)
    (wv 4) (wv 5) (wv 11) (wv 12) (wv 6) (wv 7) (wv 13) (wv 14) (wv 8) (wv 15)
    'ch 'rsp 'pkx 'pky 'prx 'pry 's (base-prime))
   (wvs 1 15) nil))

; Signature (W1..W7); write_bits_be adds the same constraints.
(defcheck signature-write-bits-extraction
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-sig-write-bits *fuel*))
   (lit-signature-write-bits-le-gadget
    (wv 1) (gs "CB" 251) (gs "CR" 250)
    (wv 2) (gs "RB" 251) (gs "RR" 250)
    (wv 3) (gs "PKB" 253) (gs "PKR" *r*)
    (wv 5) (gs "PRB" 253) (gs "PRR" *r*)
    'u (base-prime))
   (wvs 1 7) *u*))

; BooleanHash of n bits W1..Wn against Wn+1..W2n. The lazy map interleaves
; each XOR z_i with the AND w_i of the fold: z_0 is W(2n+1), z_i is W(2n+2i)
; and w_i is W(2n+2i+1); the gadget has all XORs first.
(defun bh-is-equal-check (n op)
  (same-circuit-unordered
   (ext-run (acl2::circuits-h-bh-op *fuel* n op))
   (gap-bh-is-equal-gadget (wvs 1 n) (wvs (1+ n) n)
                           (cons (wv (1+ (* 2 n))) (wvs-stride (+ 2 (* 2 n)) (1- n) 2))
                           (wvs-stride (+ 3 (* 2 n)) (1- n) 2)
                           (base-prime))
   nil))

(defcheck boolean-hash-is-equal-extraction
  (and (bh-is-equal-check 1 0) (bh-is-equal-check 2 0) (bh-is-equal-check 8 0)))

(defcheck boolean-hash-is-not-equal-extraction
  (and (bh-is-equal-check 1 1) (bh-is-equal-check 2 1) (bh-is-equal-check 8 1)))

(defun bh-ternary-check (n)
  (same-circuit-renamed (ext-run (acl2::circuits-h-bh-op *fuel* n 2))
                        (gap-bh-ternary-gadget (wv 1) (wvs 2 n) (wvs (+ 2 n) n)
                                               (gs "T" n) (base-prime))
                        (wvs 1 (1+ (* 2 n))) nil))

(defcheck boolean-hash-ternary-extraction
  (and (bh-ternary-check 1) (bh-ternary-check 2) (bh-ternary-check 8)))

; KaryMerklePath::new: the leaf index bits W1..W64, then depth levels of
; arity - 1 siblings, each a field wire or a BooleanHash of variant bits.
(defun kary-sibling-wires (lo variant)
  (if (zp variant) (wv lo) (wvs lo variant)))

(defun kary-level-wires (lo k variant)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (cons (kary-sibling-wires lo variant)
          (kary-level-wires (+ (nfix lo) (max 1 (nfix variant))) (1- k) variant))))

(defun kary-path-wires (lo depth arity variant)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      nil
    (cons (kary-level-wires lo (1- (nfix arity)) variant)
          (kary-path-wires (+ (nfix lo) (* (1- (nfix arity)) (max 1 (nfix variant))))
                           (1- depth) arity variant))))

(defun kary-path-new-check (depth arity variant)
  (same-circuit (ext-run (acl2::circuits-h-kary-path-new *fuel* depth arity variant))
                (gap-kary-path-new-gadget (if (zp variant) '(:poseidon) (list* :keccak 0 variant))
                                          (wvs 1 64)
                                          (kary-path-wires 65 depth arity variant)
                                          (base-prime))
                nil))

(defcheck kary-merkle-path-new-extraction
  (and (kary-path-new-check 1 2 0) (kary-path-new-check 3 4 0)
       (kary-path-new-check 1 2 8) (kary-path-new-check 2 3 4)))
