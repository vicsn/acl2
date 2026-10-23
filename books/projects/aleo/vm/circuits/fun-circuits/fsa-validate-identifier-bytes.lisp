; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; validate_identifier_bytes over the wires, for any number of bytes.
;
; identifier-new-gadget is the boolean checks on the byte bits (emitted
; by U8::new on each byte) followed by the validate_identifier_bytes
; constraints: per-byte validation, the first-byte extra gate, and the
; trailing-null chain.  When those constraints hold and the bytes are
; the decoding of the bit rows, validate-identifier-bytes of the bytes
; succeeds.  The error case of the funspec therefore has no satisfying
; assignment.

(in-package "ALEOVM")

(include-book "identifier-list-sound")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-validate-identifier-bytes-wire-sound
  (implies (and (consp bytes)
                (acl2::ubyte8-listp bytes)
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (consp bitrows)
                (consp witrows)
                (equal (len bytes) (len bitrows))
                (equal (len witrows) (len bitrows))
                (id-bits-matchp bytes bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (r1cs::r1cs-constraints-holdp
                 (identifier-new-gadget bitrows witrows
                                        partial uscore islet p)
                 asg p))
           (equal (validate-identifier-bytes bytes) t))
  :do-not-induct t
  :hints (("Goal"
           :use (id-flags-sound
                 id-new-gadget-pieces
                 (:instance id-null-symbols-lookup)
                 (:instance id-null-symbols-boundp)
                 (:instance id-trailing-sound
                            (nulls (id-null-symbols witrows))))
           :in-theory (e/d (validate-identifier-bytes
                            not-reserrp-when-bit-listp
                            bit-listp
                            reserrp)
                           (identifier-new-gadget
                            values-validate-bytes-null-flags
                            validate-trailing-nulls)))))
