; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness of Integer::from_field_lossy.  Its constraints are
; Field::to_bits_le, the same field-to-bits-gadget as
; Scalar::from_field_lossy, so the Field::write_bits_le witness (the
; canonical bits of the field element and the bits-below-prime comparison
; witness) satisfies them.

(in-package "ALEOVM")

(include-book "int-from-field-lossy-sound")
(include-book "fsa-scalar-from-field-lossy")

(defruled int-divshift-from-field-lossy-gadget-complete
  (implies (and (symbolp f)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal f asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal f asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (int-from-field-lossy-sound-gadget f xs rs u p) asg p))
  :do-not-induct t
  :in-theory (e/d (int-from-field-lossy-sound-gadget)
                  ((:e base-prime)))
  :use ((:instance fsa-scalar-from-field-lossy-gadget-complete (x f))
        (:instance scalar-from-field-lossy-gadget (x f))))
