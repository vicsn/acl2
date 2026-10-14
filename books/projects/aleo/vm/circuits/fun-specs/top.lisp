; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications (FUN-SPEC) of the constraint-generating functions
; in snarkVM's circuit crates. Hash and commitment internals are abstract
; (see base.lisp).

(in-package "ALEOVM")

(include-book "base")

(include-book "primitives-environment")
(include-book "primitives-boolean")
(include-book "primitives-field")
(include-book "primitives-scalar")

(include-book "integers")

(include-book "curve-group")
(include-book "curve-address")
(include-book "curve-network")
(include-book "curve-account")

(include-book "values-model")
(include-book "values-helpers")
(include-book "values-string")
(include-book "values-literal")
(include-book "values-cast")
(include-book "values-plaintext")
(include-book "values-value")

(include-book "crypto-model")
(include-book "crypto-merkle")
(include-book "crypto-state-path")
(include-book "crypto-values")
(include-book "crypto-record")
(include-book "crypto-request")
(include-book "crypto-response")
