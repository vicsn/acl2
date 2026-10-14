; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar comparisons.  When the operands are not both constant, snarkVM
; computes the linear combination 2*(a - b) and decomposes it.  The result
; of is_less_than is the least significant bit (the last bit of the
; big-endian decomposition, which is the first little-endian bit).
; is_greater_than swaps the operands.  The or-equal forms are boolean not
; of the opposite less-than, so they emit the same constraints and the
; result is the linear combination 1 - bit.
;
; The decomposition below is booleanity, the power-of-two sum of the
; linear combination, and the range check, matching field to_bits.
; Soundness needs the parity fact that this bit is 1 iff a < b for scalars
; (because 2r < p).  That lemma is not proved; see bugs-crv.txt.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-scalar")
(include-book "../r1cs/field-to-bits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-double-diff-to-bits-gadget ((a symbolp)
                                               (b symbolp)
                                               (bits symbol-listp)
                                               (rs symbol-listp)
                                               (u symbolp)
                                               (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Field decomposition of the linear combination @($2(a-b)$)."
  (append (boolean-check-gadget-list bits p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 2 a)
                          (list (- p 2) b))
                 :b (list (list 1 1))
                 :c (pow2sum-vector bits 0)))
          (bits-lt-prime-gadget bits rs p)
          (zero-unit-gadget (car (last rs)) u p)))

(define crv-scalar-is-less-than-gadget ((a symbolp)
                                        (b symbolp)
                                        (bits symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-scalar-double-diff-to-bits-gadget a b bits rs u p))

(define crv-scalar-is-greater-than-gadget ((a symbolp)
                                           (b symbolp)
                                           (bits symbol-listp)
                                           (rs symbol-listp)
                                           (u symbolp)
                                           (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "is_greater_than is is_less_than with the scalars swapped."
  (crv-scalar-is-less-than-gadget b a bits rs u p))

(define crv-scalar-is-greater-than-or-equal-gadget
  ((a symbolp) (b symbolp)
   (bits symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as is_less_than.  The result is @($1 - bit$)."
  (crv-scalar-is-less-than-gadget a b bits rs u p))

(define crv-scalar-is-less-than-or-equal-gadget
  ((a symbolp) (b symbolp)
   (bits symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-scalar-is-greater-than-or-equal-gadget b a bits rs u p))
