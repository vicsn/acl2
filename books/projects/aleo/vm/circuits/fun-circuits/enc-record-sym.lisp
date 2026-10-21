; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::encrypt_symmetric_unchecked (snarkVM circuit/program/src/data/
; record/encrypt.rs):
;   num_randomizers  (write_bits_le of each private entry; the size is read
;                     from the bits at synthesis time)
;   randomizers = hash_many_psd8([encryption_domain, key], num_randomizers)
;   encrypt_with_randomizers(randomizers)  (no new constraints: the private
;                     entries reuse the cached bits; owner and adds are
;                     linear combinations)
; The randomizers are Poseidon output linear combinations, so the output is
; stated over their values: enc-rec-encrypt-vals is enc-rec-encrypt-out with
; randomizer values in place of randomizer wires.

(in-package "ALEOVM")

(include-book "enc-record")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner::encrypt over randomizer values.

(define enc-owner-encrypt-vals ((publicp booleanp) ax ay rvals asg)
  :verify-guards nil
  (if publicp
      (if (endp rvals)
          (crypto-ciphertext-owner-public
           (ecurve::point-finite (lookup-equal ax asg) (lookup-equal ay asg)))
        :error)
    (if (equal (len rvals) 1)
        (crypto-ciphertext-owner-private
         (list (pfield::add (lookup-equal ax asg) (car rvals) (base-prime))))
      :error)))

(defruled enc-owner-encrypt-vals-sound
  (b* ((pt (ecurve::point-finite (lookup-equal ax asg) (lookup-equal ay asg)))
       (owner (if publicp (owner-public pt) (owner-private pt)))
       (out (enc-owner-encrypt-vals publicp ax ay rvals asg))
       (spec (crypto-owner-encrypt owner rvals)))
    (implies (and (groupp pt)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (symbolp ax)
                  (r1cs::valuation-bindsp asg ax)
                  (values-field-listp rvals))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance r1cs::fep-of-lookup-equal (var ax) (valuation asg)
                   (prime (base-prime))))
  :enable (enc-owner-encrypt-vals crypto-owner-encrypt crypto-field-add crypto-group-x
           crypto-edwards-bls12-pointp-when-groupp values-field-listp
           ecurve::edwards-bls12-point->u spec-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Record::encrypt_with_randomizers over randomizer values.

(define enc-rec-encrypt-vals (pubp og data ng vbits rvals asg)
  :verify-guards nil
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       ((when (and (not pubp) (atom rvals))) :error)
       (cowner (enc-owner-encrypt-vals pubp (nth 0 og) (nth 1 og)
                                       (if pubp nil (list (car rvals))) asg))
       ((when (equal cowner :error)) :error)
       (cdata (enc-rec-entries-out data rvals (if pubp 0 1) asg))
       ((when (equal cdata :error)) :error)
       ((unless (no-duplicatesp-equal (strip-cars data))) :error))
    (crypto-ciphertext-record cowner cdata (record->nonce r) (record->version r))))

(defmacro enc-rec-vals-hyps ()
  '(and (rec-record-new-hyps)
        (groupp (rec-point-of og asg))
        (rec-record-data-typed data asg)
        (values-field-listp rvals)))

(defruled enc-rec-encrypt-vals-sound
  (b* ((out (enc-rec-encrypt-vals pubp og data ng vbits rvals asg))
       (spec (crypto-record-encrypt-with-randomizers
              (rec-record-of-wires pubp og data ng vbits asg)
              rvals)))
    (implies (and (enc-rec-vals-hyps)
                  (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance enc-rec-entries-sound (index (if pubp 0 1)))
        (:instance enc-owner-encrypt-vals-sound
                   (publicp pubp) (ax (nth 0 og)) (ay (nth 1 og))
                   (rvals (if pubp nil (list (car rvals)))))
        enc-record-entry-names-of-eval)
  :in-theory (e/d (enc-rec-encrypt-vals crypto-record-encrypt-with-randomizers
                   rec-record-of-wires rec-point-of values-field-listp
                   r1cs::valuation-binds-allp)
                  (enc-owner-encrypt-vals-sound enc-rec-entries-sound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; num_randomizers needs the bit constraints of the private entries only.

(defruled enc-entry-num-randomizers-nonprivate
  (implies (and (ptx-ewtp ew)
                (not (equal (car ew) :private)))
           (and (equal (ptx-entry-num-randomizers ew) 0)
                (equal (crypto-entry-num-randomizers (ptx-eval ew asg)) 0)))
  :enable (ptx-entry-num-randomizers crypto-entry-num-randomizers ptx-eval
           ptx-ewtp ptx-entry-wrap))

(defruled enc-rec-entries-num-randomizers-val
  (implies (and (natp acc)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data)
                                              asg (base-prime)))
           (equal (rec-record-entries-num-randomizers data acc)
                  (b* ((spec (crypto-record-entries-num-randomizers
                              (rec-record-data-eval data asg) acc)))
                    (if (reserrp spec) :error spec))))
  :induct (rec-record-entries-num-randomizers data acc)
  :in-theory (e/d (rec-record-entries-num-randomizers
                   crypto-record-entries-num-randomizers
                   rec-record-datawp rec-record-data-typed rec-record-data-eval
                   enc-rec-data-gadget r1cs::r1cs-constraints-holdp-of-append
                   spec-error primep-of-base-prime)
                  (ptx-entry-num-randomizers crypto-entry-num-randomizers))
  :hints ((and (equal (car id) '(0 1))
               (equal (len (cadr id)) 1)
               (equal (cddr id) 0)
               '(:use ((:instance rec-entry-num-randomizers-val
                                  (ew (cdar data)) (p (base-prime)))
                       (:instance enc-entry-num-randomizers-nonprivate
                                  (ew (cdar data))))))))

(defruled enc-rec-num-randomizers-sound
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (out (rec-record-num-randomizers pubp data))
       (spec (crypto-record-num-randomizers r)))
    (implies (and (rec-record-datawp data)
                  (rec-record-data-typed data asg)
                  (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use (:instance enc-rec-entries-num-randomizers-val (acc (if pubp 0 1)))
  :enable (rec-record-num-randomizers crypto-record-num-randomizers
           rec-record-of-wires crypto-owner-privatep spec-error reserrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Record::encrypt_symmetric_unchecked

(defund enc-c-rec-sym-unchecked (pubp data key vs asg)
  "Synthesis: returns (mv rs cs vs asg), rs the randomizer linear
   combinations and cs the constraints."
  (declare (xargs :verify-guards nil))
  (b* ((n (rec-record-num-randomizers pubp data))
       ((mv rs cs vs asg)
        (hpos-c-poseidon-hash-many 8 (enc-randomizer-inputs key) (nfix n) vs asg)))
    (mv rs (append (enc-rec-data-gadget data) cs) vs asg)))

(define enc-rec-sym-unchecked-out (pubp og data ng vbits rs asg)
  :verify-guards nil
  (if (equal (rec-record-num-randomizers pubp data) :error)
      :error
    (enc-rec-encrypt-vals pubp og data ng vbits
                          (hpos-lc-eval-list rs asg (base-prime)) asg)))

(defruled enc-rec-entries-num-randomizers-type
  (or (equal (rec-record-entries-num-randomizers data acc) :error)
      (natp (rec-record-entries-num-randomizers data acc)))
  :induct (rec-record-entries-num-randomizers data acc)
  :enable rec-record-entries-num-randomizers)

(defrule enc-rec-num-randomizers-type
  (or (equal (rec-record-num-randomizers pubp data) :error)
      (natp (rec-record-num-randomizers pubp data)))
  :rule-classes ((:type-prescription :corollary
                  (or (equal (rec-record-num-randomizers pubp data) :error)
                      (natp (rec-record-num-randomizers pubp data)))))
  :use (:instance enc-rec-entries-num-randomizers-type (acc (if pubp 0 1)))
  :enable rec-record-num-randomizers)

(defruled enc-record-encrypt-symmetric-unchecked-sound
  :short "R1CS-SOUND of Record::encrypt_symmetric_unchecked, given Record::new
          on the record wires and a field key wire."
  (b* (((mv rs cs & &) (enc-c-rec-sym-unchecked pubp data key vs asg0))
       (out (enc-rec-sym-unchecked-out pubp og data ng vbits rs asg))
       (spec (crypto-record-encrypt-symmetric-unchecked
              (rec-record-of-wires pubp og data ng vbits asg)
              (lookup-equal key asg))))
    (implies (and (rec-record-new-hyps)
                  (groupp (rec-point-of og asg))
                  (rec-record-data-typed data asg)
                  (symbolp key)
                  (r1cs::valuation-bindsp asg key)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance enc-rec-num-randomizers-sound)
        (:instance hpos-c-poseidon-hash-many-sound
                   (rate 8) (xs (enc-randomizer-inputs key))
                   (nout (nfix (rec-record-num-randomizers pubp data)))
                   (asg asg0) (asgx asg))
        (:instance enc-eval-randomizer-inputs)
        (:instance enc-rec-encrypt-vals-sound
                   (rvals (hpos-lc-eval-list
                           (mv-nth 0 (hpos-c-poseidon-hash-many
                                      8 (enc-randomizer-inputs key)
                                      (nfix (rec-record-num-randomizers pubp data))
                                      vs asg0))
                           asg (base-prime))))
        (:instance r1cs::fep-of-lookup-equal (var key) (valuation asg)
                   (prime (base-prime))))
  :in-theory (e/d (enc-c-rec-sym-unchecked enc-rec-sym-unchecked-out
                   crypto-record-encrypt-symmetric-unchecked
                   crypto-encryption-domain-is-values-encryption-domain
                   enc-crypto-hash-many-psd-8 poseidon-hash-many
                   enc-base-prime-value hpos-aleo-rate-p
                   r1cs::r1cs-constraints-holdp-of-append)
                  (enc-rec-encrypt-vals-sound enc-rec-num-randomizers-sound
                   hpos-c-poseidon-hash-many-sound)))

(defruled enc-record-encrypt-symmetric-unchecked-complete
  :short "R1CS-COMPLETE of Record::encrypt_symmetric_unchecked: from an
          assignment with the entry leaf witnesses and the key, Poseidon
          witness generation yields an assignment satisfying all the
          constraints.  The entry constraints are assumed to mention only
          wires bound in the starting assignment."
  (b* (((mv & cs & asg2) (enc-c-rec-sym-unchecked pubp data key vs asg)))
    (implies (and (rec-record-datawp data)
                  (rec-record-data-typed data asg)
                  (enc-rec-data-witnessp data asg (base-prime))
                  (hpos-cs-boundp (enc-rec-data-gadget data) asg)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound
                       8 2 (nfix (rec-record-num-randomizers pubp data)))
                      (len vs))
                  (symbolp key)
                  (r1cs::valuation-bindsp asg key))
             (r1cs::r1cs-constraints-holdp cs asg2 (base-prime))))
  :do-not-induct t
  :use ((:instance enc-record-encrypt-with-randomizers-complete (p (base-prime)))
        (:instance enc-hash-complete-step
                   (n (nfix (rec-record-num-randomizers pubp data))))
        (:instance hpos-holdp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many
                                   8 (enc-randomizer-inputs key)
                                   (nfix (rec-record-num-randomizers pubp data))
                                   vs asg)))
                   (cs (enc-rec-data-gadget data))
                   (p (base-prime))))
  :in-theory (e/d (enc-c-rec-sym-unchecked
                   r1cs::r1cs-constraints-holdp-of-append primep-of-base-prime)
                  (hpos-holdp-when-ext-p)))
