; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top book for the fb- circuit formalizations of snarkVM field and
; boolean functions.  Each book below is included for its events;
; circspec-fb.tsv records which proof obligations were discharged.

(in-package "ALEOVM")

(include-book "fb-field-from")
(include-book "fb-field-zero")
(include-book "fb-field-eq")
(include-book "fb-field-div-unchecked")
(include-book "fb-boolean-adder")
(include-book "fb-boolean-bits")
(include-book "fb-field-compare")
(include-book "fb-field-pow")
(include-book "fb-field-bits")
(include-book "fb-field-sqrt")
(include-book "fb2-boolean-lte")
(include-book "fb2-field-bits")
(include-book "fb2-field-sqrt")
(include-book "fb3-field-write-bits")
(include-book "fb3-field-sqrt")
(include-book "fb3-field-compare")
(include-book "fb3-field-pow")
