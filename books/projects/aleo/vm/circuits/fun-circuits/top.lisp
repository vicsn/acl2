; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top book for circuit specifications of snarkVM functions.
; Each included book is a formal R1CS (and, where present, PFCS)
; for one family of snarkVM circuit functions.

(in-package "ALEOVM")

(include-book "environment-r1cs")
(include-book "environment-pfcs")
(include-book "boolean-adder-r1cs")
(include-book "field-zero-r1cs")
(include-book "field-compare-r1cs")
(include-book "group-inject-r1cs")
(include-book "group-inject-sound")
(include-book "scalar-new-r1cs")
(include-book "identifier-new-r1cs")
(include-book "literal-new-r1cs")
(include-book "identifier-list-sound")
(include-book "literal-new-pfcs")
