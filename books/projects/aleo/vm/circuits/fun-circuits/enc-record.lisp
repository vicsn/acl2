; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::<Plaintext>::encrypt_with_randomizers and
; encrypt_symmetric_unchecked (snarkVM circuit/program/src/data/record/
; encrypt.rs), over the record wires of rec-record.lisp.
;
; encrypt_with_randomizers: the owner is encrypted with no randomizer
;   (public) or randomizers[0] (private), which emits no constraint
;   (enc-owner-encrypt-*).  Each entry takes num_randomizers randomizers
;   (0 for constant and public entries; size_in_fields for a private one,
;   which runs write_bits_le); a private entry is then
;   Plaintext::encrypt_with_randomizers, whose to_fields reuses the cached
;   bits.  So the constraints are write_bits_le of each private entry, in
;   order.  Out-of-range slices and duplicate names are host halts.
; encrypt_symmetric_unchecked: num_randomizers (the same write_bits_le
;   constraints), hash_many_psd8([encryption_domain, key], n), then
;   encrypt_with_randomizers (no new constraints).

(in-package "ALEOVM")

(include-book "enc-plaintext")
(include-book "rec-record-bits")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Bridges between the crypto-record and values-plaintext encryption specs.

(defruled enc-crypto-field-list-add-is-values
  (implies (and (values-field-listp xs) (values-field-listp ys))
           (equal (crypto-field-list-add xs ys)
                  (values-field-lists-add (values-field-list-fix xs)
                                          (values-field-list-fix ys))))
  :induct (crypto-field-list-add xs ys)
  :enable (crypto-field-list-add values-field-lists-add crypto-field-add
           values-field-add values-field-list-fix values-field-fix))

(defruled enc-crypto-plaintext-encrypt-with-randomizers-is-values
  (implies (and (plaintextp pt) (values-field-listp rs))
           (equal (crypto-plaintext-encrypt-with-randomizers pt rs)
                  (plaintext-encrypt-with-randomizers pt rs)))
  :use ((:instance enc-values-field-listp-of-plaintext-to-fields (x pt)))
  :enable (crypto-plaintext-encrypt-with-randomizers plaintext-encrypt-with-randomizers
           crypto-plaintext-to-fields enc-crypto-field-list-add-is-values
           crypto-ciphertext-new values-ciphertext-from-fields
           crypto-max-data-size-in-fields values-max-data-size-in-fields))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Entries.

(define enc-rec-data-gadget (data)
  :short "Constraints of the entries: write_bits_le of each private entry."
  (if (atom data)
      nil
    (append (if (equal (car (cdar data)) :private)
                (ptx-entry-bits-gadget (cdar data) nil)
              nil)
            (enc-rec-data-gadget (cdr data)))))

(define enc-rec-entries-out (data rvals (index natp) asg)
  :short "The encrypted entries (from the wire values), or @(':error')
          where snarkVM halts."
  (b* (((when (atom data)) nil)
       (ew (cdar data))
       (k (ptx-entry-num-randomizers ew))
       ((when (equal k :error)) :error)
       (k (nfix k))
       ((when (> (+ (nfix index) k) (len rvals))) :error)
       (rs (take k (nthcdr index rvals)))
       (pt (ptx-val (cdr ew) asg))
       (centry
        (case (car ew)
          (:constant (crypto-ciphertext-entry-constant pt))
          (:public (crypto-ciphertext-entry-public pt))
          (otherwise
           (b* ((out (enc-ptx-fields-out (cdr ew))))
             (if (enc-halts out k)
                 :error
               (crypto-ciphertext-entry-private
                (values-field-lists-add (ptx-chunks-val out asg) rs)))))))
       ((when (equal centry :error)) :error)
       (rest (enc-rec-entries-out (cdr data) rvals (+ (nfix index) k) asg))
       ((when (equal rest :error)) :error))
    (cons (crypto-ciphertext-record-entry (caar data) centry) rest)))

(defruled enc-rec-entry-private-sound
  (b* ((ew (cdar data))
       (k (ptx-size-in-fields (cdr ew)))
       (rs (take k (nthcdr index rvals)))
       (out (enc-ptx-fields-out (cdr ew)))
       (spec (crypto-plaintext-encrypt-with-randomizers (ptx-val (cdr ew) asg) rs)))
    (implies (and (ptx-ewtp ew)
                  (ptx-typed (cdr ew) asg)
                  (natp k)
                  (values-field-listp rvals)
                  (<= (+ (nfix index) k) (len rvals))
                  (r1cs::r1cs-constraints-holdp (ptx-bits-gadget (cdr ew) nil)
                                                asg (base-prime)))
             (and (iff (enc-halts out k) (reserrp spec))
                  (implies (not (enc-halts out k))
                           (equal (values-field-lists-add (ptx-chunks-val out asg) rs)
                                  spec)))))
  :do-not-induct t
  :use ((:instance enc-ptx-encrypt-with-randomizers-vals
                   (wt (cdr (cdar data)))
                   (rvals (take (ptx-size-in-fields (cdr (cdar data)))
                                (nthcdr index rvals))))
        (:instance enc-crypto-plaintext-encrypt-with-randomizers-is-values
                   (pt (ptx-val (cdr (cdar data)) asg))
                   (rs (take (ptx-size-in-fields (cdr (cdar data)))
                             (nthcdr index rvals))))
        (:instance ptx-write-bits-le-sound (wt (cdr (cdar data))) (p (base-prime))))
  :enable (ptx-ewtp primep-of-base-prime values-field-listp-of-take
           values-field-listp-of-nthcdr))

(defrule enc-natp-of-plaintext-size-in-fields
  (implies (not (reserrp (plaintext-size-in-fields pt)))
           (natp (plaintext-size-in-fields pt)))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (not (reserrp (plaintext-size-in-fields pt)))
                           (<= 0 (plaintext-size-in-fields pt)))))
  :enable plaintext-size-in-fields)

(defrule enc-not-reserrp-of-cons-entry
  (not (reserrp (cons (crypto-ciphertext-record-entry n e) rest)))
  :enable (reserrp crypto-ciphertext-record-entry))

(defruled enc-rec-entries-sound
  (b* ((out (enc-rec-entries-out data rvals index asg))
       (spec (crypto-record-encrypt-entries (rec-record-data-eval data asg)
                                            rvals index)))
    (implies (and (rec-record-datawp data)
                  (rec-record-data-typed data asg)
                  (values-field-listp rvals)
                  (natp index)
                  (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :induct (enc-rec-entries-out data rvals index asg)
  :in-theory (e/d (enc-rec-entries-out crypto-record-encrypt-entries
                   rec-record-datawp rec-record-data-typed rec-record-data-eval
                   enc-rec-data-gadget r1cs::r1cs-constraints-holdp-of-append
                   crypto-randomizer-slice ptx-entry-num-randomizers
                   crypto-entry-num-randomizers ptx-eval ptx-entry-wrap ptx-ewtp
                   ptx-entry-bits-gadget primep-of-base-prime)
                  ())
  :hints ((and (equal (car id) '(0 1))
               (equal (len (cadr id)) 1)
               (equal (cddr id) 0)
               '(:use ((:instance enc-rec-entry-private-sound)
                       (:instance ptx-size-in-fields-sound
                                  (wt (cdr (cdar data))) (p (base-prime)))
                       (:instance ptx-write-bits-le-sound
                                  (wt (cdr (cdar data))) (p (base-prime))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Record::encrypt_with_randomizers

(define enc-rec-encrypt-out (pubp og data ng vbits rs asg)
  :short "The encrypted record from the wire values, or @(':error') where
          snarkVM halts."
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (rvals (lookup-equal-list rs asg))
       ((when (and (not pubp) (atom rs))) :error)
       (cowner (enc-owner-encrypt-out pubp (nth 0 og) (nth 1 og)
                                      (if pubp nil (list (car rs))) asg))
       ((when (equal cowner :error)) :error)
       (cdata (enc-rec-entries-out data rvals (if pubp 0 1) asg))
       ((when (equal cdata :error)) :error)
       ((unless (no-duplicatesp-equal (strip-cars data))) :error))
    (crypto-ciphertext-record cowner cdata (record->nonce r) (record->version r))))

(defruled enc-record-entry-names-of-eval
  (implies (rec-record-datawp data)
           (equal (crypto-record-entry-names (rec-record-data-eval data asg))
                  (strip-cars data)))
  :induct (rec-record-datawp data)
  :enable (rec-record-datawp rec-record-data-eval crypto-record-entry-names))

(defmacro enc-rec-hyps ()
  '(and (rec-record-new-hyps)
        (groupp (rec-point-of og asg))
        (rec-record-data-typed data asg)
        (symbol-listp rs)
        (r1cs::valuation-binds-allp asg rs)))

(defruled enc-record-encrypt-with-randomizers-sound
  :short "R1CS-SOUND of Record::encrypt_with_randomizers, given Record::new
          on the record wires (Address::new on the owner, Literal::new on
          each entry leaf): the output is crypto-record-encrypt-with-randomizers
          of the wire record and randomizers, and snarkVM halts exactly when
          it fails."
  (b* ((out (enc-rec-encrypt-out pubp og data ng vbits rs asg))
       (spec (crypto-record-encrypt-with-randomizers
              (rec-record-of-wires pubp og data ng vbits asg)
              (lookup-equal-list rs asg))))
    (implies (and (enc-rec-hyps)
                  (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance enc-rec-entries-sound (rvals (lookup-equal-list rs asg))
                   (index (if pubp 0 1)))
        (:instance enc-values-field-listp-of-lookup (xs rs))
        (:instance enc-owner-encrypt-sound
                   (publicp pubp) (ax (nth 0 og)) (ay (nth 1 og))
                   (rs (if pubp nil (list (car rs)))))
        enc-record-entry-names-of-eval)
  :expand ((lookup-equal-list rs asg)
           (lookup-equal-list (list (car rs)) asg)
           (lookup-equal-list nil asg))
  :in-theory (e/d (enc-rec-encrypt-out crypto-record-encrypt-with-randomizers
                   rec-record-of-wires rec-point-of
                   r1cs::valuation-binds-allp enc-owner-encrypt-gadget)
                  (enc-owner-encrypt-sound enc-rec-entries-sound)))

(define enc-rec-data-witnessp (data asg p)
  (if (atom data)
      t
    (and (or (not (equal (car (cdar data)) :private))
             (ptx-bits-witnessp (cdr (cdar data)) nil asg p))
         (enc-rec-data-witnessp (cdr data) asg p))))

(defruled enc-record-encrypt-with-randomizers-complete
  :short "R1CS-COMPLETE of Record::encrypt_with_randomizers: the leaf
          witnesses of the private entries satisfy the constraints."
  (implies (and (primep p)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (enc-rec-data-witnessp data asg p))
           (r1cs::r1cs-constraints-holdp (enc-rec-data-gadget data) asg p))
  :induct (rec-record-datawp data)
  :enable (rec-record-datawp rec-record-data-typed enc-rec-data-witnessp
           enc-rec-data-gadget r1cs::r1cs-constraints-holdp-of-append
           ptx-entry-bits-gadget ptx-ewtp)
  :hints (("Subgoal *1/2"
           :use (:instance ptx-write-bits-complete (wt (cdr (cdar data)))
                           (bigp nil)))))
