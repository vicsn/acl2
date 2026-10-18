; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral write_bits_le, write_bits_be, to_field and to_fields
; over the wires.
;
; None of the four emits a constraint.  write_bits_le returns the byte
; bit wires in order, write_bits_be their reverse, and to_field (and the
; single element of to_fields) is the linear combination
; sum 2^i * bit_i, whose value is values-lebits-to-field of the wire
; values.  The theorems below take the identifier arm of Literal::new on
; the input: its bit rows decode to the literal's bytes
; (id-bits-matchp, which identifier-list-sound.lisp literal-identifier-new-sound
; and id-decode-rows-matchp establish for the bytes id-decode-rows reads).

(in-package "ALEOVM")

(include-book "identifier-list-sound")
(include-book "val-string-ops")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fsa-id-flatten ((bitrows true-listp))
  :verify-guards nil
  (if (atom bitrows)
      nil
    (append (car bitrows) (fsa-id-flatten (cdr bitrows)))))

(defruledl fsa-lookup-equal-list-of-append
  (equal (lookup-equal-list (append a b) asg)
         (append (lookup-equal-list a asg) (lookup-equal-list b asg)))
  :induct (len a)
  :enable lookup-equal-list)

(defruled fsa-id-flatten-lookup
  (implies (id-bits-matchp bytes bitrows asg)
           (equal (lookup-equal-list (fsa-id-flatten bitrows) asg)
                  (values-bytes-to-lebits bytes)))
  :induct (id-bits-matchp bytes bitrows asg)
  :enable (id-bits-matchp
           fsa-id-flatten
           values-bytes-to-lebits
           fsa-lookup-equal-list-of-append
           lookup-equal-list))

(defruled fsa-identifier-write-bits-le-wire-sound
  (implies (and (identifier-literalp x)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-write-bits-le-gadget) asg p))
           (equal (lookup-equal-list (fsa-id-flatten bitrows) asg)
                  (identifier-literal-to-bits-le x)))
  :enable (identifier-literal-to-bits-le)
  :use (:instance fsa-id-flatten-lookup
                  (bytes (identifier-literal->bytes x))))

(defruled fsa-identifier-write-bits-be-wire-sound
  (implies (and (identifier-literalp x)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-write-bits-be-gadget) asg p))
           (equal (rev (lookup-equal-list (fsa-id-flatten bitrows) asg))
                  (identifier-literal-to-bits-be x)))
  :enable (identifier-literal-to-bits-be)
  :use fsa-identifier-write-bits-le-wire-sound
  :disable identifier-write-bits-le-gadget
  :prep-lemmas
  ((defrule le-gadget-nil
     (equal (identifier-write-bits-le-gadget) nil)
     :enable identifier-write-bits-le-gadget)
   (defrule be-gadget-nil
     (equal (identifier-write-bits-be-gadget) nil)
     :enable identifier-write-bits-be-gadget)))

(defruled fsa-identifier-to-field-wire-sound
  (implies (and (identifier-literalp x)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-to-field-gadget) asg p))
           (equal (values-lebits-to-field
                   (lookup-equal-list (fsa-id-flatten bitrows) asg))
                  (identifier-literal-to-field x)))
  :enable (identifier-literal-to-field identifier-literal-to-bits-le)
  :use (:instance fsa-id-flatten-lookup
                  (bytes (identifier-literal->bytes x))))

(defruled fsa-identifier-to-fields-wire-sound
  (implies (and (identifier-literalp x)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-to-fields-gadget) asg p))
           (equal (list (values-lebits-to-field
                         (lookup-equal-list (fsa-id-flatten bitrows) asg)))
                  (identifier-literal-to-fields x)))
  :enable (identifier-literal-to-fields
           identifier-literal-to-field
           identifier-literal-to-bits-le)
  :use (:instance fsa-id-flatten-lookup
                  (bytes (identifier-literal->bytes x))))
