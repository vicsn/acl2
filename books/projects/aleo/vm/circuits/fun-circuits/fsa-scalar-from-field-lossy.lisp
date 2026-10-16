; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE for Scalar::from_field_lossy.
;
; scalar-from-field-lossy-gadget is field-to-bits-gadget, the same list as
; fb-field-write-bits-le-gadget.  fb2-field-write-bits-le-gadget-complete
; supplies the witness: the canonical field bits of the input, the
; bits-lte-const fold witness against p - 1, and the public unit 1.  Every
; field element has a scalar-from-field-lossy-funspec result, so this is
; the whole completeness statement.

(in-package "ALEOVM")

(include-book "scalar-from-field-lossy-r1cs")
(include-book "fb2-field-bits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-scalar-from-field-lossy-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (scalar-from-field-lossy-gadget x xs rs u p) asg p))
  :do-not-induct t
  :in-theory (e/d (scalar-from-field-lossy-gadget
                   fb-field-write-bits-le-gadget
                   scalar-lossy-base-prime-oddp)
                  ((:e base-prime)))
  :use (:instance fb2-field-write-bits-le-gadget-complete
                  (bits xs)))
