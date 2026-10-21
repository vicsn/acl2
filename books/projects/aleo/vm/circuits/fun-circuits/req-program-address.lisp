; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ProgramID::to_address (circuit/program/src/id/to_address.rs):
;   A::hash_to_group_psd4(&[name.to_field(), network.to_field()]),
;   then Address::from_group (no constraint).
; The circuit is hpos-c-hash-to-group at rate 4 on the two identifier field
; linear combinations (Identifier::to_field is the identifier's field
; variable).  The bridge lemmas relate hpos-hash-to-group-spec to the
; funspecs values-hash-to-group-psd4 (program-id-to-address) and
; crypto-hash-to-group-psd.

(in-package "ALEOVM")

(include-book "hpos-hash-to-group")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/crypto-model")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled req-h2g-validp-nonzero
  (implies (hped-elligator2-encode-validp h)
           (not (equal h 0)))
  :use (:instance hped-elligator2-encode-validp-of-0)
  :in-theory nil)

(defruled req-elligator2-encode-when-validp
  (implies (hped-elligator2-encode-validp h)
           (equal (elligator2-encode h) (hped-elligator2-encode h)))
  :enable (elligator2-encode hped-elligator2-encode-total))

(defruled req-h2g-psd4-bridge
  :short "Where Poseidon hash_to_group at rate 4 succeeds in the circuit
          model, values-hash-to-group-psd4 is its point."
  (implies (and (values-field-listp in)
                (hpos-hash-to-group-validp 4 in))
           (equal (values-hash-to-group-psd4 in)
                  (values-to-group (hpos-hash-to-group-spec 4 in))))
  :use ((:instance req-h2g-validp-nonzero
                   (h (first (hpos-poseidon-hash-many 4 in 2))))
        (:instance req-h2g-validp-nonzero
                   (h (second (hpos-poseidon-hash-many 4 in 2))))
        (:instance req-elligator2-encode-when-validp
                   (h (first (hpos-poseidon-hash-many 4 in 2))))
        (:instance req-elligator2-encode-when-validp
                   (h (second (hpos-poseidon-hash-many 4 in 2))))
        (:instance groupp-of-elligator2-encode
                   (input (first (hpos-poseidon-hash-many 4 in 2))))
        (:instance groupp-of-elligator2-encode
                   (input (second (hpos-poseidon-hash-many 4 in 2)))))
  :in-theory (e/d (values-hash-to-group-psd4 hpos-hash-to-group-validp
                   hpos-hash-to-group-spec hpos-hash-to-group-fields
                   poseidon-hash-many values-group-add group-add-funspec
                   values-group-fix-when-groupp)
                  (hped-elligator2-encode-validp hped-elligator2-encode
                   elligator2-encode groupp-of-elligator2-encode)))

(defruled req-h2g-psd-bridge
  :short "crypto-hash-to-group-psd agrees with the circuit model: it fails
          exactly when hpos-hash-to-group-validp fails, and is otherwise
          hpos-hash-to-group-spec."
  (implies (and (hpos-aleo-rate-p rate) (consp in))
           (and (iff (reserrp (crypto-hash-to-group-psd rate in))
                     (not (hpos-hash-to-group-validp rate in)))
                (implies (hpos-hash-to-group-validp rate in)
                         (equal (crypto-hash-to-group-psd rate in)
                                (hpos-hash-to-group-spec rate in)))))
  :use ((:instance req-elligator2-encode-when-validp
                   (h (first (poseidon-hash-many rate in 2))))
        (:instance req-elligator2-encode-when-validp
                   (h (second (poseidon-hash-many rate in 2)))))
  :in-theory (e/d (crypto-hash-to-group-psd crypto-hash-many-psd hpos-aleo-rate-p
                   hpos-hash-to-group-validp
                   hpos-hash-to-group-spec hpos-hash-to-group-fields
                   poseidon-hash-many group-add-funspec spec-error)
                  (hped-elligator2-encode-validp hped-elligator2-encode
                   elligator2-encode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund req-program-id-to-address-circuit (xs u vs asg)
  (declare (xargs :verify-guards nil))
  (hpos-c-hash-to-group 4 xs u vs asg))

(defruled req-program-id-to-address-sound
  :short "R1CS-SOUND of ProgramID::to_address: if the name and network
          field linear combinations evaluate to the fields of @('id'), the
          constraints imply that the output point is
          @('program-id-to-address id') and that hash_to_group succeeds."
  (b* (((mv g cs & &) (req-program-id-to-address-circuit xs u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (consp xs)
                  (hpos-h2g-sound-hyps 4 xs u vs asg asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p)
                  (equal (hpos-lc-eval-list xs asgx p) (program-id-to-fields id)))
             (and (hpos-hash-to-group-validp 4 (program-id-to-fields id))
                  (equal (program-id-to-address id)
                         (values-to-group (hpos-pt-eval g asgx))))))
  :use ((:instance hpos-c-hash-to-group-sound (rate 4))
        (:instance req-h2g-psd4-bridge (in (program-id-to-fields id))))
  :in-theory '(req-program-id-to-address-circuit program-id-to-address
               values-field-listp-of-program-id-to-fields
               (:e hpos-aleo-rate-p)))

(defrule req-consp-of-program-id-to-fields
  (consp (program-id-to-fields id))
  :enable program-id-to-fields)

(defruled req-program-id-to-address-complete
  :short "R1CS-COMPLETE of ProgramID::to_address: when hash_to_group_psd4
          succeeds on the fields (crypto-hash-to-group-psd, i.e. both
          Elligator2 encodings succeed), the synthesized witness extends the
          valuation and satisfies the constraints, and its output point is the
          funspec's."
  (b* (((mv g cs & asg2) (req-program-id-to-address-circuit xs u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-h2g-bound 4 (len xs)) (len vs))
                  (hpos-lc-list-boundp xs asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (equal (hpos-lc-eval-list xs asg p) (program-id-to-fields id))
                  (not (reserrp (crypto-hash-to-group-psd 4 (program-id-to-fields id)))))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (hpos-pt-boundp g asg2))))
  :use ((:instance hpos-c-hash-to-group-complete (rate 4))
        (:instance req-h2g-psd-bridge (rate 4) (in (program-id-to-fields id))))
  :in-theory '(req-program-id-to-address-circuit program-id-to-fields
               (:e hpos-aleo-rate-p) req-consp-of-program-id-to-fields))
