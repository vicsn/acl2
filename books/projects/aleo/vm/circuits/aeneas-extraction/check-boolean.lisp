; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for the environment primitives and circuit/types/boolean.

(include-book "check-lib")
(include-book "../fun-circuits/environment-r1cs")
(include-book "../fun-circuits/boolean-adder-r1cs")
(include-book "../fun-circuits/fb-boolean-bits")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-nand")
(include-book "../r1cs/boolean-nor")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/if")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; circuit/environment/src: enforce (Circuit, CanaryCircuit, TestnetCircuit,
; and AleoV0, which all call the same R1CS::enforce), assert, assert_eq,
; assert_neq.

(defcheck env-enforce-extraction
  (same-circuit (ext-run (acl2::circuits-h-enforce *fuel*))
                (enforce-gadget (wv 1) (wv 2) (wv 3))
                nil))

(defcheck env-assert-extraction
  (same-circuit (ext-run (acl2::circuits-h-assert *fuel*))
                (assert-gadget (wv 1))
                nil))

(defcheck env-assert-eq-extraction
  (same-circuit (ext-run (acl2::circuits-h-assert-eq *fuel*))
                (assert-eq-gadget (wv 1) (wv 2))
                nil))

(defcheck env-assert-neq-extraction
  (same-circuit (ext-run (acl2::circuits-h-assert-neq *fuel*))
                (assert-neq-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; circuit/types/boolean. Inputs are W1 (self) and W2 (other); the output
; wire is W3.

(defcheck boolean-new-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-new *fuel*))
                (boolean-check-gadget (wv 1) (base-prime))
                nil))

(defcheck boolean-and-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 0))
                (boolean-and-gadget (wv 1) (wv 2) (wv 3))
                nil))

(defcheck boolean-or-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 1))
                (boolean-or-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

(defcheck boolean-xor-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 2))
                (boolean-xor-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

(defcheck boolean-nand-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 3))
                (boolean-nand-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

(defcheck boolean-nor-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 4))
                (boolean-nor-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

; is_equal and is_not_equal are XOR; is_equal returns 1 - W3.
(defcheck boolean-is-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 5))
                (boolean-xor-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

(defcheck boolean-is-not-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-binop *fuel* 6))
                (boolean-xor-gadget (wv 1) (wv 2) (wv 3) (base-prime))
                nil))

; Condition W1, first W2, second W3, output W4.
(defcheck boolean-ternary-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-ternary *fuel*))
                (if-gadget (wv 1) (wv 2) (wv 3) (wv 4) (base-prime))
                nil))

; a W1, b W2, carry W3; then c0, sum, c1, c2, carry-out.
(defcheck boolean-adder-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-adder *fuel* nil))
                (boolean-adder-gadget (wv 1) (wv 2) (wv 3)
                                      (wv 4) (wv 5) (wv 6) (wv 7) (wv 8)
                                      (base-prime))
                nil))

(defcheck boolean-subtractor-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-adder *fuel* t))
                (boolean-subtractor-gadget (wv 1) (wv 2) (wv 3)
                                           (wv 4) (wv 5) (wv 6) (wv 7) (wv 8)
                                           'one (base-prime))
                '((one . 1))))

(defcheck boolean-assert-bits-are-zero-extraction
  (same-circuit (ext-run (acl2::circuits-h-b-assert-bits-are-zero *fuel* 8))
                (fb-boolean-assert-bits-are-zero-gadget (wvs 1 8))
                nil))
