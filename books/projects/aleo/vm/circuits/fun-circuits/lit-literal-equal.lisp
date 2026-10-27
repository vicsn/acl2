; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Literal::is_equal / is_not_equal (circuit/program/src/data/literal/equal.rs)
; on operands of different variants.
;
; The match is on the host.  When the variants differ, is_equal returns
; Boolean::constant(false) and is_not_equal Boolean::constant(true); no
; constraint is emitted.  On equal variants each arm is the per-type
; is_equal / is_not_equal gadget; that dispatch is not assembled here
; because the Signature arm (account Signature::is_equal) has no verified
; circuit yet.

(in-package "ALEOVM")

(include-book "../fun-specs/values-literal")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lit-literal-equal-mismatch-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('Literal::is_equal') and @('is_not_equal') on
          operands of different variants: none (a constant output)."
  nil)

(defruled lit-literal-is-equal-mismatch-sound
  (implies (and (not (equal (literal-kind x) (literal-kind y)))
                (r1cs::r1cs-constraints-holdp (lit-literal-equal-mismatch-gadget) asg p))
           (equal (literal-is-equal x y) 0))
  :enable (literal-is-equal values-literal-equalp values-bool-to-bit))

(defruled lit-literal-is-not-equal-mismatch-sound
  (implies (and (not (equal (literal-kind x) (literal-kind y)))
                (r1cs::r1cs-constraints-holdp (lit-literal-equal-mismatch-gadget) asg p))
           (equal (literal-is-not-equal x y) 1))
  :enable (literal-is-not-equal values-literal-equalp values-bool-to-bit))

(defruled lit-literal-equal-mismatch-complete
  (r1cs::r1cs-constraints-holdp (lit-literal-equal-mismatch-gadget) asg p)
  :enable lit-literal-equal-mismatch-gadget)
