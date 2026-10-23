; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ciphertext::decrypt_with_randomizers and Ciphertext::decrypt_symmetric
; (snarkVM circuit/program/src/data/ciphertext/decrypt.rs).
;
; decrypt_with_randomizers: zip_eq of the ciphertext fields with the
;   randomizers (a host length check), Field::sub per element, which builds
;   the linear combination c_i - r_i, then Plaintext::from_fields.  The
;   linear combination is modelled by a wire d_i and the constraint
;   (c_i - r_i) * 1 = d_i, which fixes d_i to the same value.
; decrypt_symmetric: hash_many_psd8([encryption_domain, key], len) with the
;   domain a constant (hpos-aleo.lisp), then decrypt_with_randomizers.
;
; Plaintext::from_fields decides the shape of its result on ejected values
; (ptx-from-bits.lisp), so these theorems carry its condition that HV, the
; bits ejected at synthesis time, are the values of the data bits in the
; assignment.  No constraint enforces it.

(in-package "ALEOVM")

(include-book "ptx-from-bits")
(include-book "enc-record-enc")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Differences c_i - r_i.

(defund dec-sub-lc (c r)
  (declare (xargs :verify-guards nil))
  (hpos-lc-add (hpos-lc-var c)
               (hpos-lc-scale r (1- (base-prime)) (base-prime))
               (base-prime)))

(defrule dec-hpos-lc-eval-of-sub-lc
  (implies (and (symbolp c)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg c))
           (equal (hpos-lc-eval (dec-sub-lc c r) asg (base-prime))
                  (pfield::sub (lookup-equal c asg)
                               (hpos-lc-eval r asg (base-prime))
                               (base-prime))))
  :enable (dec-sub-lc pfield::sub pfield::neg enc-base-prime-value)
  :use ((:instance r1cs::fep-of-lookup-equal (var c) (valuation asg)
                   (prime (base-prime)))))

(define dec-subs-gadget (cs rs ds)
  :verify-guards nil
  (if (atom cs)
      nil
    (append (enc-lc-eq-gadget (hpos-lc-sv (dec-sub-lc (car cs) (car rs)))
                              (car ds))
            (dec-subs-gadget (cdr cs) (cdr rs) (cdr ds)))))

(defruled dec-sub-eq-holds
  (implies (and (symbolp c) (symbolp d)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg d))
           (equal (r1cs::r1cs-constraints-holdp
                   (enc-lc-eq-gadget (hpos-lc-sv (dec-sub-lc c r)) d)
                   asg (base-prime))
                  (equal (lookup-equal d asg)
                         (pfield::sub (lookup-equal c asg)
                                      (hpos-lc-eval r asg (base-prime))
                                      (base-prime)))))
  :in-theory '(dec-hpos-lc-eval-of-sub-lc)
  :use ((:instance enc-lc-eq-gadget-holds
                   (lc (hpos-lc-sv (dec-sub-lc c r))) (b d) (p (base-prime)))
        (:instance (:definition hpos-lc-eval)
                   (lc (dec-sub-lc c r)) (p (base-prime)))))

(defruled dec-subs-gadget-sound
  (implies (and (symbol-listp cs) (symbol-listp ds)
                (equal (len ds) (len cs))
                (equal (len rs) (len cs))
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg cs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::r1cs-constraints-holdp (dec-subs-gadget cs rs ds)
                                              asg (base-prime)))
           (equal (ptx-terms-val ds asg)
                  (crypto-field-list-sub (ptx-terms-val cs asg)
                                         (hpos-lc-eval-list rs asg (base-prime)))))
  :induct (dec-subs-gadget cs rs ds)
  :enable (dec-subs-gadget ptx-terms-val ptx-term-val crypto-field-list-sub
           crypto-field-sub hpos-lc-eval-list r1cs::valuation-binds-allp fieldp
           r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use ((:instance dec-sub-eq-holds
                            (c (car cs)) (d (car ds)) (r (car rs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::decrypt_with_randomizers

(define dec-ctx-gadget (cs rs ds hv)
  :short "Ciphertext::decrypt_with_randomizers on ciphertext wires CS and
          randomizer linear combinations RS; DS are the wires of the
          differences and HV the ejected data bits."
  :verify-guards nil
  (if (equal (len cs) (len rs))
      (append (dec-subs-gadget cs rs ds)
              (ptx-from-fields-gadget ds hv))
    nil))

(defmacro dec-ctx-hyps ()
  '(and (symbol-listp cs) (symbol-listp ds)
        (equal (len ds) (len cs))
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-binds-allp asg cs)
        (r1cs::valuation-binds-allp asg ds)
        (equal (ptx-terms-val (ptx-fields-bits ds) asg) hv)))

(defrule dec-values-field-listp-of-terms-val
  (implies (and (symbol-listp xs)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg xs))
           (values-field-listp (ptx-terms-val xs asg)))
  :induct (len xs)
  :enable (ptx-terms-val ptx-term-val r1cs::valuation-binds-allp
           values-field-listp fieldp)
  :hints (("Subgoal *1/2"
           :use (:instance r1cs::fep-of-lookup-equal (var (car xs))
                           (valuation asg) (prime (base-prime))))))

(define dec-ctx-res (cs rs ds hv)
  :short "@(':error') where snarkVM halts, else (jobs . wire-tree)."
  :verify-guards nil
  (if (equal (len cs) (len rs))
      (ptx-from-fields ds hv)
    :error))

(defruled dec-ctx-sound
  :short "Soundness of Ciphertext::decrypt_with_randomizers under the
          from_fields condition that HV are the values of the data bits."
  (b* ((out (dec-ctx-res cs rs ds hv))
       (spec (crypto-ciphertext-decrypt-with-randomizers
              (ptx-terms-val cs asg)
              (hpos-lc-eval-list rs asg (base-prime)))))
    (implies (and (dec-ctx-hyps)
                  (r1cs::r1cs-constraints-holdp (dec-ctx-gadget cs rs ds hv)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-val (cdr out) asg) spec)))))
  :do-not-induct t
  :use ((:instance dec-subs-gadget-sound)
        (:instance ptx-from-fields-sound (fs ds) (p (base-prime))))
  :in-theory (e/d (dec-ctx-res dec-ctx-gadget
                   crypto-ciphertext-decrypt-with-randomizers
                   crypto-plaintext-from-fields
                   r1cs::r1cs-constraints-holdp-of-append
                   primep-of-base-prime)
                  (dec-subs-gadget-sound ptx-from-fields-sound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::decrypt_symmetric

(defmacro dec-ctx-hyps-x ()
  '(and (symbol-listp cs) (symbol-listp ds)
        (equal (len ds) (len cs))
        (r1cs::r1cs-valuationp asgx (base-prime))
        (r1cs::valuation-binds-allp asgx cs)
        (r1cs::valuation-binds-allp asgx ds)
        (equal (ptx-terms-val (ptx-fields-bits ds) asgx) hv)))

(defund dec-c-ctx-sym (cs key ds hv vs asg)
  "Synthesis of Ciphertext::decrypt_symmetric: (mv res cs vs asg)."
  (declare (xargs :verify-guards nil))
  (b* ((n (len cs))
       ((mv rs hcs vs asg)
        (hpos-c-poseidon-hash-many 8 (enc-randomizer-inputs key) n vs asg)))
    (mv (if (> n (crypto-max-data-size-in-fields))
            :error
          (dec-ctx-res cs rs ds hv))
        (append hcs (dec-ctx-gadget cs rs ds hv))
        vs asg)))

(defruled dec-ctx-sym-sound
  :short "Soundness of Ciphertext::decrypt_symmetric on a field key wire,
          under the from_fields condition."
  (b* (((mv res cons & &) (dec-c-ctx-sym cs key ds hv vs asg))
       (spec (crypto-ciphertext-decrypt-symmetric (ptx-terms-val cs asgx)
                                                  (lookup-equal key asgx))))
    (implies (and (dec-ctx-hyps-x)
                  (symbolp key)
                  (r1cs::valuation-bindsp asgx key)
                  (r1cs::r1cs-constraints-holdp cons asgx (base-prime)))
             (and (iff (equal res :error) (reserrp spec))
                  (implies (not (equal res :error))
                           (equal (ptx-val (cdr res) asgx) spec)))))
  :do-not-induct t
  :use ((:instance dec-ctx-sound
                   (rs (mv-nth 0 (hpos-c-poseidon-hash-many
                                  8 (enc-randomizer-inputs key) (len cs) vs asg)))
                   (asg asgx))
        (:instance hpos-c-poseidon-hash-many-sound
                   (rate 8) (xs (enc-randomizer-inputs key)) (nout (len cs)))
        (:instance r1cs::fep-of-lookup-equal (var key) (valuation asgx)
                   (prime (base-prime)))
        (:instance enc-eval-randomizer-inputs (asg asgx)))
  :in-theory (e/d (dec-c-ctx-sym crypto-ciphertext-decrypt-symmetric
                   crypto-ciphertext-size-in-fields
                   enc-crypto-hash-many-psd-8 enc-base-prime-value
                   fieldp hpos-aleo-rate-p dec-ctx-res
                   crypto-encryption-domain-is-values-encryption-domain
                   r1cs::r1cs-constraints-holdp-of-append)
                  (dec-ctx-sound hpos-c-poseidon-hash-many-sound)))
