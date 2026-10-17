; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/types/scalar. A scalar is its field wire.
; The gadgets are called on fresh internal symbols, and the checks are up to
; a renaming of internal wires (same-circuit-renamed).

(include-book "check-lib")
(include-book "../fun-circuits/crv-equal")
(include-book "../fun-circuits/crv-ternary")
(include-book "../fun-circuits/crv-scalar")
(include-book "../fun-circuits/fsa-scalar-add")
(include-book "../fun-circuits/scalar-from-bits-r1cs")
(include-book "../fun-circuits/scalar-write-bits-r1cs")
(include-book "../fun-circuits/scalar-from-field-lossy-r1cs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

; The model's r and r - 1 limbs are the ACL2 scalar prime.
(defcheck scalar-modulus-extraction
  (equal (scalar-prime)
         2111115437357092606062206234695386632838870926408408195193685246394721360383))

(defun scalar-ext (op) (ext-run (acl2::circuits-h-s-binop *fuel* op)))

(defcheck scalar-is-equal-extraction
  (same-circuit-renamed (scalar-ext 0)
                        (crv-scalar-is-equal-gadget (wv 1) (wv 2) 'm 'r (base-prime))
                        (wvs 1 2) nil))

(defcheck scalar-is-not-equal-extraction
  (same-circuit-renamed (scalar-ext 1)
                        (crv-scalar-is-not-equal-gadget (wv 1) (wv 2) 'm 'r (base-prime))
                        (wvs 1 2) nil))

(defcheck scalar-is-zero-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-unop *fuel* 0))
                        (crv-scalar-is-zero-gadget (wv 1) 'm 'r (base-prime))
                        (wvs 1 1) nil))

(defcheck scalar-is-one-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-unop *fuel* 1))
                        (crv-scalar-is-one-gadget (wv 1) 'm 'r (base-prime))
                        (wvs 1 1) nil))

(defcheck scalar-ternary-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-ternary *fuel*))
                        (crv-scalar-ternary-gadget (wv 1) (wv 2) (wv 3) 'r (base-prime))
                        (wvs 1 3) nil))

(defun scalar-compare-check (op gadget)
  (same-circuit-renamed (scalar-ext op) gadget (wvs 1 2) *u*))

(defcheck scalar-compare-extraction
  (b* ((p (base-prime)) (bits (gs "B" 253)) (rs (gs "RS" *r*)))
    (and (scalar-compare-check 2 (crv-scalar-is-less-than-gadget (wv 1) (wv 2) bits rs 'u p))
         (scalar-compare-check 3 (crv-scalar-is-greater-than-gadget (wv 1) (wv 2) bits rs 'u p))
         (scalar-compare-check 4 (crv-scalar-is-less-than-or-equal-gadget (wv 1) (wv 2) bits rs 'u p))
         (scalar-compare-check 5 (crv-scalar-is-greater-than-or-equal-gadget (wv 1) (wv 2) bits rs
                                                                             'u p)))))

; The fold of Field::is_less_than against the constant r has one gate per
; step that constant folding does not remove. Their number is the extracted
; circuit's internal wires less the 252 sum bits, the ternary result, and the
; 251 result bits.
(defun scalar-add-gates ()
  (- (len (first-occurrences (constraints-vars (scalar-ext 6)) (list 1 (wv 1) (wv 2)) nil))
     504))

(defcheck scalar-add-extraction
  (same-circuit-renamed (scalar-ext 6)
                        (fsa-scalar-add-gadget (wv 1) (wv 2) (gs "B" 252) (gs "Z" (scalar-add-gates))
                                               'w (gs "C" 251) (base-prime))
                        (wvs 1 2) nil))

(defcheck scalar-write-bits-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-unop *fuel* 2))
                        (scalar-write-bits-le-gadget (wv 1) (gs "B" 251) (gs "RS" 250) (base-prime))
                        (wvs 1 1) nil))

(defcheck scalar-from-field-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-unop *fuel* 3))
                        (scalar-from-field-gadget (wv 1) (gs "B" 253) (gs "FRS" *r*) 'u
                                                  (gs "SRS" 250) (base-prime))
                        (wvs 1 1) *u*))

(defcheck scalar-from-field-lossy-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-unop *fuel* 4))
                        (scalar-from-field-lossy-gadget (wv 1) (gs "B" 253) (gs "RS" *r*) 'u
                                                        (base-prime))
                        (wvs 1 1) *u*))

; from_bits with 250 (nothing), 251 (the r - 1 comparison), and 253 (also the
; two excess bits) input bits. from_bits_be is from_bits_le of the reversal.
(defun scalar-from-bits-check (n)
  (same-circuit-renamed (ext-run (acl2::circuits-h-s-from-bits *fuel* n))
                        (scalar-from-bits-le-gadget (wvs 1 n) (gs "RS" 250) (base-prime))
                        (wvs 1 n) nil))

(defcheck scalar-from-bits-extraction
  (and (scalar-from-bits-check 250)
       (scalar-from-bits-check 251)
       (scalar-from-bits-check 253)
       (equal (scalar-from-bits-be-gadget (wvs 1 253) (gs "RS" 250) (base-prime))
              (scalar-from-bits-le-gadget (rev (wvs 1 253)) (gs "RS" 250) (base-prime)))))
