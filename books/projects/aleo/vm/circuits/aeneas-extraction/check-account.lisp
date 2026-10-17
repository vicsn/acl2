; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for ComputeKey::to_fields and Signature::to_fields, which
; add no constraints, and for BooleanHash::new, which checks each bit W1..Wn.

(include-book "check-lib")
(include-book "../fun-circuits/crv-project")
(include-book "../fun-circuits/val-collections")

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
