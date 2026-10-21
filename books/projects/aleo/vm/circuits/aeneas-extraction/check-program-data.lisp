; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for Ciphertext, the state-path leaves, Identifier and
; ProgramID bits, Owner<Plaintext>, DynamicFuture, DynamicRecord, and the
; Literal rows with no constraints.

(include-book "check-lib")
(include-book "../fun-circuits/rec-ciphertext")
(include-book "../fun-circuits/rec-leaves")
(include-book "../fun-circuits/lit-identifier-bits")
(include-book "../fun-circuits/rec-owner")
(include-book "../fun-circuits/rec-dynamic-future")
(include-book "../fun-circuits/rec-dynamic-record")
(include-book "../fun-circuits/rec-dynamic-record-eq")
(include-book "../fun-circuits/lit-literal-to-fields")
(include-book "../fun-circuits/lit-literal-equal")

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ciphertexts W1..Wn and Wn+1..Wn+m; different lengths add no constraint.
(defun ct-check (n m op)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-ct-op *fuel* n m op))
   (if (equal op 0)
       (rec-fields-is-equal-gadget (wvs 1 n) (wvs (1+ n) m)
                                   (gs "M" n) (gs "R" n) (gs "Z" n))
     (rec-fields-is-not-equal-gadget (wvs 1 n) (wvs (1+ n) m)
                                     (gs "M" n) (gs "R" n) (gs "Z" n)))
   (wvs 1 (+ n m)) nil))

(defcheck ciphertext-is-equal-extraction
  (and (ct-check 1 1 0) (ct-check 2 2 0) (ct-check 5 5 0) (ct-check 2 3 0)))

(defcheck ciphertext-is-not-equal-extraction
  (and (ct-check 1 1 1) (ct-check 2 2 1) (ct-check 5 5 1) (ct-check 2 3 1)))

(defcheck ciphertext-new-extraction
  (and (same-circuit (ext-run (acl2::circuits-h-ct-op *fuel* 1 0 2))
                     (rec-ciphertext-new-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-ct-op *fuel* 4 0 2))
                     (rec-ciphertext-new-gadget) nil)))

(defun ct-bits-names (prefix i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i)))
      nil
    (cons (gs (acl2::packn-pos (list prefix "X" i "Y") 'wv)
              (if (equal prefix "B") (integer-length (base-prime)) *r*))
          (ct-bits-names prefix (1+ (nfix i)) n))))

; write_bits_be adds the same constraints.
(defun ct-bits-check (n)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-ct-op *fuel* n 0 3))
   (rec-fields-write-bits-gadget (wvs 1 n) (ct-bits-names "B" 0 n)
                                 (ct-bits-names "R" 0 n) 'u)
   (wvs 1 n) *u*))

(defcheck ciphertext-write-bits-extraction
  (and (ct-bits-check 1) (ct-bits-check 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The integer bit wires come first (8 for HeaderLeaf, 24 for the others),
; then the id; write_bits_be adds the same constraints.
(defun leaf-check (kind ints gadget)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-leaf-write-bits *fuel* kind))
   gadget (wvs 1 (1+ ints)) *u*))

(defcheck header-leaf-write-bits-extraction
  (leaf-check 0 8 (rec-header-leaf-write-bits-gadget
                   (wv 9) (gs "B" 253) (gs "R" *r*) 'u)))

(defcheck transaction-leaf-write-bits-extraction
  (leaf-check 1 24 (rec-transaction-leaf-write-bits-gadget
                    (wv 25) (gs "B" 253) (gs "R" *r*) 'u)))

(defcheck transition-leaf-write-bits-extraction
  (leaf-check 2 24 (rec-transition-leaf-write-bits-gadget
                    (wv 25) (gs "B" 253) (gs "R" *r*) 'u)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier W1 of size n bytes; the truncation adds no constraint, and
; write_bits_be reverses the truncated bits.
(defun identifier-bits-check (n)
  (same-circuit (ext-run (acl2::circuits-h-id-write-bits *fuel* 0 n 0))
                (lit-identifier-write-bits-le-gadget (wv 1) (wvs 2 253) (wvs 255 *r*)
                                                     'u (base-prime))
                *u*))

(defcheck identifier-write-bits-extraction
  (and (identifier-bits-check 1) (identifier-bits-check 8) (identifier-bits-check 31)))

(defun program-id-bits-check (n m)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-id-write-bits *fuel* 1 n m))
   (lit-program-id-write-bits-le-gadget (wv 1) (gs "NB" 253) (gs "NR" *r*)
                                        (wv 2) (gs "WB" 253) (gs "WR" *r*)
                                        'u (base-prime))
   (wvs 1 2) *u*))

(defcheck program-id-write-bits-extraction
  (and (program-id-bits-check 5 5) (program-id-bits-check 31 4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Owners (W1, W2) and (W3, W4): the multipliers and results W5..W8 and the
; AND W9 when the variants agree, no constraint otherwise.
(defun owner-equal-check (op pa pb)
  (same-circuit (ext-run (acl2::circuits-h-owner *fuel* op pa pb))
                (rec-owner-is-equal-gadget pa pb (wv 1) (wv 2) (wv 3) (wv 4)
                                           (wv 6) (wv 5) (wv 8) (wv 7) (wv 9))
                nil))

(defcheck owner-is-equal-extraction
  (and (owner-equal-check 0 t t) (owner-equal-check 0 nil nil)
       (owner-equal-check 0 t nil) (owner-equal-check 0 nil t)))

(defcheck owner-is-not-equal-extraction
  (and (owner-equal-check 1 t t) (owner-equal-check 1 nil nil)
       (owner-equal-check 1 t nil) (owner-equal-check 1 nil t)))

(defcheck owner-new-extraction
  (same-circuit (ext-run (acl2::circuits-h-owner *fuel* 2 t t))
                (rec-owner-new-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6)
                                      (wv 7) (wv 8) (wv 9) (wv 10) (wv 11) (wv 12)
                                      (wv 13) (wv 14))
                nil))

(defcheck owner-to-entry-extraction
  (same-circuit (ext-run (acl2::circuits-h-owner *fuel* 3 t t))
                (rec-owner-to-entry-gadget)
                nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcheck dynamic-future-new-extraction
  (same-circuit (ext-run (acl2::circuits-h-dynamic-future *fuel* 0))
                (rec-dynamic-future-new-gadget) nil))

; program_name, program_network, function_name and checksum W1..W4;
; write_bits_be adds the same constraints, and to_fields packs the bits into
; 252-bit chunks, which are linear combinations.
(defun dynamic-future-bits-check (op)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-dynamic-future *fuel* op))
   (rec-dynamic-future-write-bits-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                         (ct-bits-names "B" 0 4)
                                         (ct-bits-names "R" 0 4) 'u)
   (wvs 1 4) *u*))

(defcheck dynamic-future-write-bits-extraction (dynamic-future-bits-check 1))

(defcheck dynamic-future-to-fields-extraction (dynamic-future-bits-check 2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcheck dynamic-record-new-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-dynamic-record *fuel* 0))
                        (rec-dynamic-record-new-gadget (gs "O" 14) (gs "N" 14) (gs "V" 8))
                        nil nil))

; Owner (W1, W2), root W3, nonce (W4, W5) and version bits W6..W13.
(defun dynamic-record-bits-check (op)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-dynamic-record *fuel* op))
   (rec-dynamic-record-write-bits-gadget (wv 1) (wv 3) (wv 4)
                                         (ct-bits-names "B" 0 3)
                                         (ct-bits-names "R" 0 3) 'u)
   (wvs 1 13) *u*))

(defcheck dynamic-record-write-bits-extraction (dynamic-record-bits-check 1))

(defcheck dynamic-record-to-fields-extraction (dynamic-record-bits-check 2))

; Against W14..W26.
(defun dynamic-record-equal-check (op)
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-dynamic-record *fuel* op))
   (rec-dynamic-record-is-equal-gadget
    (wv 1) (wv 2) (wv 14) (wv 15) 'omx 'orx 'omy 'ory 'oout
    (wv 3) (wv 16) 'rm 'rr 'z1
    (wv 4) (wv 5) (wv 17) (wv 18) 'nmx 'nrx 'nmy 'nry 'nout
    'z2
    (wvs 6 8) (wvs 19 8) 'vm 'vr
    'z3)
   (wvs 1 26) nil))

(defcheck dynamic-record-is-equal-extraction (dynamic-record-equal-check 3))

(defcheck dynamic-record-is-not-equal-extraction (dynamic-record-equal-check 4))

(defcheck dynamic-record-find-extraction
  (same-circuit (ext-run (acl2::circuits-h-dynamic-record *fuel* 5))
                (rec-dynamic-record-find-gadget) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Every arm of Literal::to_fields (the StringType arm is deprecated).
(defcheck literal-to-fields-extraction
  (and (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 0 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 1 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 2 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 3 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 4 8))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 4 128))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 5 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 6 0))
                     (lit-literal-to-fields-gadget) nil)
       (same-circuit (ext-run (acl2::circuits-h-lit-to-fields *fuel* 7 0))
                     (lit-literal-to-fields-gadget) nil)))

(defcheck literal-is-equal-mismatch-extraction
  (same-circuit (ext-run (acl2::circuits-h-lit-equal-mismatch *fuel* nil))
                (lit-literal-equal-mismatch-gadget) nil))

(defcheck literal-is-not-equal-mismatch-extraction
  (same-circuit (ext-run (acl2::circuits-h-lit-equal-mismatch *fuel* t))
                (lit-literal-equal-mismatch-gadget) nil))
