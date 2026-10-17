; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/types/field.

(include-book "check-lib")
(include-book "../r1cs/field-mul")
(include-book "../r1cs/field-square")
(include-book "../r1cs/field-inverse")
(include-book "../r1cs/field-div")
(include-book "../r1cs/field-neq-opt")
(include-book "../r1cs/field-ternary")
(include-book "../r1cs/field-to-bits")
(include-book "../r1cs/field-lt")
(include-book "../r1cs/field-pow")
(include-book "../r1cs/field-square-root")
(include-book "../fun-circuits/fb-field-eq")
(include-book "../fun-circuits/field-zero-r1cs")
(include-book "../fun-circuits/fb-field-bits")
(include-book "../fun-circuits/fb-field-compare")
(include-book "../fun-circuits/field-compare-r1cs")
(include-book "../fun-circuits/fb-field-pow")
(include-book "../fun-circuits/fb-field-sqrt")
(include-book "../fun-circuits/fb-boolean-bits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inputs: x is W1 and y is W2. The unit wire U of the bits gadgets is the
; constant 1.

(defconst *u* '((u . 1)))

; R, the number of wires the fold of Boolean::assert_less_than_or_equal_constant
; against p - 1 allocates (bits-lt-prime-rlen).
(defconst *r* (bits-lt-prime-rlen (base-prime)))

(defcheck field-mul-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 0))
                (field-mul-gadget (wv 1) (wv 2) (wv 3))
                nil))

(defcheck field-square-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 0))
                (field-square-gadget (wv 1) (wv 2))
                nil))

(defcheck field-inverse-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 1))
                (field-inverse-gadget (wv 1) (wv 2))
                nil))

; The inverse of y is W3 and the product W4.
(defcheck field-div-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 1))
                (field-div-gadget (wv 1) (wv 2) (wv 4) (wv 3))
                nil))

; is_neq is W3 and the multiplier W4.
(defcheck field-is-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 2))
                (field-is-equal-gadget (wv 1) (wv 2) (wv 4) (wv 3) (base-prime))
                nil))

; field-neq-gadget, named in ACL2_MODELS, adds a boolean check on the result
; that snarkVM does not emit; field-neq-opt-gadget is the two snarkVM
; constraints. B is the constant 1.
(defcheck field-is-not-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 3))
                (field-neq-opt-gadget (wv 1) (wv 2) (wv 4) (wv 3) 'b (base-prime))
                '((b . 1))))

(defcheck field-is-zero-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 2))
                (field-is-zero-gadget (wv 1) (wv 3) (wv 2) (base-prime))
                nil))

(defcheck field-is-one-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 3))
                (field-is-one-gadget (wv 1) (wv 3) (wv 2) (base-prime))
                nil))

; Condition W1, first W2, second W3, output W4.
(defcheck field-ternary-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-ternary *fuel*))
                (field-ternary-gadget (wv 1) (wv 2) (wv 3) (wv 4) (base-prime))
                nil))

(defcheck field-from-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-from *fuel*))
                (field-from-gadget)
                nil))

(defcheck field-from-boolean-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-from-boolean *fuel*))
                (field-from-boolean-gadget)
                nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write_bits_le: the 253 bits are W2..W254, then the R fold wires.

(defcheck field-write-bits-le-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 4))
                (fb-field-write-bits-le-gadget (wv 1) (wvs 2 253) (wvs 255 *r*) 'u (base-prime))
                *u*))

; The gadget takes the little-endian wires; the written bits are their reverse.
(defcheck field-write-bits-be-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 5))
                (fb-field-write-bits-be-gadget (wv 1) (wvs 2 253) (wvs 255 *r*) 'u (base-prime))
                *u*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Comparisons: the bits of x, its fold wires, the bits of y, its fold wires,
; then one XOR wire and one ternary wire per bit.

(defconst *x-bits* (wvs 3 253))
(defconst *x-rs* (wvs 256 *r*))
(defconst *y-bits* (wvs (+ 256 *r*) 253))
(defconst *y-rs* (wvs (+ 509 *r*) *r*))
(defconst *ds* (wvs-stride (+ 509 (* 2 *r*)) 253 2))
(defconst *lt-rs* (wvs-stride (+ 510 (* 2 *r*)) 253 2))

(defcheck field-is-less-than-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 4))
                (fb-field-is-less-than-gadget (wv 1) *x-bits* *x-rs* (wv 2) *y-bits* *y-rs*
                                              *ds* *lt-rs* 'u (base-prime))
                *u*))

; is_greater_than is y < x, so the bits of y (W2) are converted first.
(defcheck field-is-greater-than-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 5))
                (field-is-greater-than-gadget (wv 1) *y-bits* *y-rs* (wv 2) *x-bits* *x-rs*
                                              *ds* *lt-rs* 'u (base-prime))
                *u*))

; is_less_than_or_equal is !(y < x).
(defcheck field-is-less-than-or-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 6))
                (field-is-less-than-or-equal-gadget (wv 1) *y-bits* *y-rs* (wv 2) *x-bits* *x-rs*
                                                    *ds* *lt-rs* 'u (base-prime))
                *u*))

(defcheck field-is-greater-than-or-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 7))
                (field-is-greater-than-or-equal-gadget (wv 1) *x-bits* *x-rs* (wv 2) *y-bits* *y-rs*
                                                       *ds* *lt-rs* 'u (base-prime))
                *u*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; pow: the bits of the exponent W2 are W3..W255 and its fold wires follow.
; The MSB step allocates one result wire; every later step a square, a
; product, and a result. The gadget lists are little-endian, so they are the
; reverse of the allocation order.

(defconst *pow-base* (+ 256 *r*))

(defcheck field-pow-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-binop *fuel* 8))
                (fb-field-pow-gadget (wv 1) (wv 2) (wvs 3 253) (wvs 256 *r*)
                                     (rev (wvs-stride (+ *pow-base* 1) 252 3))
                                     (rev (wvs-stride (+ *pow-base* 2) 252 3))
                                     (rev (cons (wv *pow-base*)
                                                (wvs-stride (+ *pow-base* 3) 252 3)))
                                     'u (base-prime))
                *u*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; from_bits_le and from_bits_be of n input bits W1..Wn: below 253 bits there
; is no constraint, at 253 the range check against p - 1, and past 253 the
; excess bits are asserted zero first. The fold wires follow the inputs.

(defconst *rc* (bits-lte-const-check-rlen (nat=>lebits* (1- (base-prime)))))

(defun from-bits-check (n be)
  (same-circuit (ext-run (acl2::circuits-h-f-from-bits *fuel* n be))
                (if be
                    (fb-field-from-bits-be-gadget (wvs 1 n) (wvs (1+ n) *rc*) (base-prime))
                  (fb-field-from-bits-le-gadget (wvs 1 n) (wvs (1+ n) *rc*) (base-prime)))
                nil))

(defcheck field-from-bits-le-extraction
  (and (from-bits-check 8 nil)
       (from-bits-check 252 nil)
       (from-bits-check 253 nil)
       (from-bits-check 256 nil)))

(defcheck field-from-bits-be-extraction
  (and (from-bits-check 8 t)
       (from-bits-check 252 t)
       (from-bits-check 253 t)
       (from-bits-check 256 t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Square roots of x (W1). The root is W2, its bits W3..W255, and the fold
; wires of the bits' range check follow.

(defcheck field-even-square-root-extraction
  (same-circuit (ext-run (acl2::circuits-h-f-unop *fuel* 7))
                (fb-field-even-square-root-gadget (wv 1) (wv 2) (wvs 3 253) (wvs 256 *r*) 'u (base-prime))
                *u*))

; square_root does not match. snarkVM emits 761 constraints:
; the square, field-to-bits-gadget on the root (its boolean checks, the
; weighted sum, and the range check against p - 1), and !((p-1)/2 < root)
; as a fold over all 253 bits of (p-1)/2. field-square-root-gadget has 508:
; it leaves out the range check against p - 1, and its bound check asserts
; the top bit of the root is zero and then folds the other 252 bits.

(defconst *sqrt-rs* (wvs 256 (field-square-root-rlen (base-prime))))

(defcheck field-square-root-differs
  (b* ((ext (ext-run (acl2::circuits-h-f-unop *fuel* 6)))
       (gadget (field-square-root-gadget (wv 1) (wv 2) (wvs 3 253) *sqrt-rs* (base-prime))))
    (and (equal (len ext) 761)
         (equal (len gadget) 508)
         (equal (canon-constraints (take 508 ext) nil (base-prime))
                (canon-constraints
                 (append (field-square-gadget (wv 2) (wv 1))
                         (field-to-bits-gadget (wv 2) (wvs 3 253) (wvs 256 *r*) 'u (base-prime)))
                 *u* (base-prime)))
         (not (same-circuit-unordered ext gadget nil))
         (not (contains-circuit ext gadget nil)))))
