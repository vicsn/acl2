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
(include-book "identifier-new-complete")
(include-book "group-enforce-in-group-complete")
(include-book "literal-new-group-complete")
(include-book "literal-new-pfcs")
(include-book "fb-top")
(include-book "prog-top")
(include-book "val-top")
(include-book "int-top")
(include-book "crv-top")
(include-book "scalar-range-gap")
(include-book "scalar-from-field-lossy-r1cs")
(include-book "int-from-field-lossy-sound")
(include-book "scalar-write-bits-r1cs")
(include-book "scalar-from-bits-r1cs")
(include-book "int-div-pfcs")
(include-book "int-shift-pfcs")
(include-book "compute-key-from-private-key")
(include-book "group-cofactor-clears")
(include-book "group-unconditional")
(include-book "group-wire-sound")
(include-book "crv-add-complete")
(include-book "crv-sub-double")
