; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::decrypt (snarkVM circuit/program/src/data/record/decrypt.rs):
;   record_view_key = (view_key * nonce).to_x_coordinate()
;       grp-mul-gadget on Scalar::to_bits_be = the reverse of the cached
;       Scalar::to_bits_le wires rbits, with the nonce as base
;   decrypt_symmetric_unchecked(record_view_key)   (dec-record.lisp)
;   A::assert_eq(view_key.to_address(), owner)
;       net-gmul-gadget on the cached rbits (the fixed-base fold), then two
;       linear constraints owner.x = out.x, owner.y = out.y
; The owner wires are those of the public owner (Address::new) or of
; Address::from_field in the private owner's decryption.  The theorem
; carries the from_fields condition of each private entry.

(in-package "ALEOVM")

(include-book "dec-record")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The private owner's point is a subgroup point.

(defruled dec-owner-point-groupp
  (implies (and (dec-owner-hyps)
                (r1cs::r1cs-constraints-holdp (dec-owner-gadget oc r0 ow)
                                              asg (base-prime)))
           (groupp (rec-point-of ow asg)))
  :do-not-induct t
  :use ((:instance rec-from-x-gadget-crypto-group
                   (x (nth 0 ow)) (y (nth 1 ow)) (qx (nth 2 ow)) (qy (nth 3 ow))
                   (cx2 (nth 4 ow)) (cy2 (nth 5 ow)) (dxy (nth 6 ow))
                   (dx2 (nth 7 ow)) (dy2 (nth 8 ow)) (x3 (nth 9 ow))
                   (y3 (nth 10 ow)) (exy (nth 11 ow)) (ex2 (nth 12 ow))
                   (ey2 (nth 13 ow)) (p (base-prime)))
        (:instance return-type-of-crypto-group-from-x
                   (x (lookup-equal (nth 0 ow) asg)))
        (:instance rec-not-reserrp-of-point-finite
                   (a (lookup-equal (nth 0 ow) asg))
                   (b (lookup-equal (nth 1 ow) asg))))
  :in-theory (e/d (dec-owner-gadget rec-point-of
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::valuation-binds-allp)
                  (grp-from-x-coordinate-gadget rec-from-x-gadget-crypto-group
                   return-type-of-crypto-group-from-x)))

(defruled dec-crec-owner-groupp
  (implies (and (not pubp)
                (consp rlcs)
                (dec-owner-hyps)
                (r1cs::r1cs-constraints-holdp
                 (dec-crec-gadget pubp oc ow data rlcs) asg (base-prime)))
           (groupp (rec-point-of ow asg)))
  :use (:instance dec-owner-point-groupp (r0 (car rlcs)))
  :in-theory '(dec-crec-gadget r1cs::r1cs-constraints-holdp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The circuit.

(define dec-rdec-prefix (ng s rbits rs sts steps ox oy)
  :short "view_key * nonce (Scalar::to_bits_le cached as RBITS; Group::mul
          on their reverse) and view_key.to_address (the fixed-base fold)."
  :verify-guards nil
  (append (net-gmul-gadget s rbits rs sts (base-prime))
          (grp-mul-gadget (rev rbits) ox oy steps (nth 0 ng) (nth 1 ng)
                          (base-prime))))

(defund dec-c-rdec (pubp og oc ow data ng s rbits rs sts steps ox oy vs asg)
  "Synthesis of Record::decrypt: (mv n rlcs cs vs asg)."
  (declare (xargs :verify-guards nil))
  (b* ((key (enc-rec-sym-key rbits ox oy steps))
       ((mv n rlcs cs vs asg) (dec-c-crec-sym pubp oc ow data key vs asg)))
    (mv n rlcs
        (append (dec-rdec-prefix ng s rbits rs sts steps ox oy)
                cs
                (enc-nonce-gadget (net-gmul-out rbits sts (base-prime))
                                  (if pubp og ow)))
        vs asg)))

(defmacro dec-rdec-hyps ()
  '(and (net-gmul-hyps)
        (booleanp pubp)
        (symbol-listp ng) (equal (len ng) 14)
        (r1cs::valuation-binds-allp asg ng)
        (groupp (rec-point-of ng asg))
        (grp-steps-boundp steps asg)
        (equal (len steps) 250)
        (symbolp ox) (symbolp oy)
        (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
        (symbolp (first (grp-mul-out (rev rbits) ox oy steps)))
        (r1cs::valuation-bindsp asg (first (grp-mul-out (rev rbits) ox oy steps)))
        (symbolp (second (grp-mul-out (rev rbits) ox oy steps)))
        (r1cs::valuation-bindsp asg (second (grp-mul-out (rev rbits) ox oy steps)))
        (if pubp
            (and (symbol-listp og) (equal (len og) 14)
                 (r1cs::valuation-binds-allp asg og)
                 (groupp (rec-point-of og asg)))
          (and (symbolp oc)
               (symbol-listp ow) (equal (len ow) 14)
               (r1cs::valuation-bindsp asg oc)
               (r1cs::valuation-binds-allp asg ow)))
        (dec-rec-datawp data asg)))

(defruled dec-rdec-facts
  (b* (((mv & & cons & &)
        (dec-c-rdec pubp og oc ow data ng s rbits rs sts steps ox oy vs asg0))
       (key (enc-rec-sym-key rbits ox oy steps))
       (sv (lookup-equal s asg)))
    (implies (and (dec-rdec-hyps)
                  (r1cs::r1cs-constraints-holdp cons asg p))
             (and (scalarp sv)
                  (equal (lookup-equal key asg)
                         (crypto-group-x
                          (ecurve::edwards-bls12-mul (nfix sv)
                                                     (rec-point-of ng asg))))
                  (equal (rec-point-of (if pubp og ow) asg)
                         (crypto-g-scalar-multiply sv))
                  (r1cs::r1cs-constraints-holdp
                   (mv-nth 2 (dec-c-crec-sym pubp oc ow data key vs asg0))
                   asg p))))
  :do-not-induct t
  :use (enc-rec-sym-gmul-sound
        (:instance enc-rec-sym-key-sound (og ng) (sv (lookup-equal s asg)))
        (:instance enc-rec-sym-nonce-sound
                   (out (net-gmul-out rbits sts (base-prime)))
                   (ng (if pubp og ow))))
  :in-theory '(dec-c-rdec dec-rdec-prefix mv-nth car-cons cdr-cons (:e zp)
               r1cs::r1cs-constraints-holdp-of-append))

(defrule dec-crec-of-wires-nonce
  (equal (crypto-ciphertext-record->nonce (dec-crec-of-wires pubp og oc data nv vv asg))
         (values-group-fix nv))
  :enable dec-crec-of-wires)

(defruled dec-crec-out-owner-address
  (implies (not (equal (dec-crec-out pubp og oc ow data nv vv rlcs asg) :error))
           (equal (crypto-owner-address
                   (record->owner (dec-crec-out pubp og oc ow data nv vv rlcs asg)))
                  (values-group-fix (rec-point-of (if pubp og ow) asg))))
  :enable (dec-crec-out crypto-owner-address))

(defruled dec-c-rdec-outs
  (b* (((mv n rlcs & & &)
        (dec-c-rdec pubp og oc ow data ng s rbits rs sts steps ox oy vs asg0))
       ((mv n1 rlcs1 & & &)
        (dec-c-crec-sym pubp oc ow data (enc-rec-sym-key rbits ox oy steps) vs asg0)))
    (and (equal n n1) (equal rlcs rlcs1)))
  :in-theory '(dec-c-rdec mv-nth car-cons cdr-cons (:e zp)))

(defruled dec-c-crec-sym-rlcs
  (equal (mv-nth 1 (dec-c-crec-sym pubp oc ow data key vs asg))
         (mv-nth 0 (hpos-c-poseidon-hash-many
                    8 (enc-randomizer-inputs key)
                    (nfix (dec-crec-nr pubp data)) vs asg)))
  :in-theory '(dec-c-crec-sym mv-nth car-cons cdr-cons (:e zp)))

(defruled dec-crec-out-consp-rlcs
  (implies (and (not pubp)
                (not (equal (dec-crec-out pubp og oc ow data nv vv rlcs asg) :error)))
           (consp rlcs))
  :enable dec-crec-out)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Soundness.

(defruled dec-c-crec-sym-gadget-holds
  (implies (r1cs::r1cs-constraints-holdp
            (mv-nth 2 (dec-c-crec-sym pubp oc ow data key vs asg0)) asg p)
           (r1cs::r1cs-constraints-holdp
            (dec-crec-gadget pubp oc ow data
                             (mv-nth 1 (dec-c-crec-sym pubp oc ow data key vs asg0)))
            asg p))
  :in-theory '(dec-c-crec-sym mv-nth car-cons cdr-cons (:e zp)
               r1cs::r1cs-constraints-holdp-of-append))

(defruled dec-record-decrypt-sound
  :short "Soundness of Record::decrypt on a view key scalar wire S, under
          the from_fields condition on each private entry: the output is
          crypto-record-decrypt of the wire record (nonce the point of NG,
          version VV), and snarkVM halts exactly when it fails."
  (b* (((mv n rlcs cons & &)
        (dec-c-rdec pubp og oc ow data ng s rbits rs sts steps ox oy vs asg0))
       (nonce (rec-point-of ng asg))
       (out (if (equal n :error)
                :error
              (dec-crec-out pubp og oc ow data nonce vv rlcs asg)))
       (spec (crypto-record-decrypt
              (dec-crec-of-wires pubp og oc data nonce vv asg)
              (lookup-equal s asg))))
    (implies (and (dec-rdec-hyps)
                  (r1cs::r1cs-constraints-holdp cons asg p))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :cases (pubp)
  :use ((:instance dec-rdec-facts)
        (:instance dec-c-rdec-outs)
        (:instance dec-record-decrypt-symmetric-unchecked-sound
                   (key (enc-rec-sym-key rbits ox oy steps))
                   (asgx asg) (asg asg0) (nv (rec-point-of ng asg)))
        (:instance dec-c-crec-sym-gadget-holds
                   (key (enc-rec-sym-key rbits ox oy steps)))
        (:instance dec-crec-owner-groupp
                   (rlcs (mv-nth 1 (dec-c-crec-sym pubp oc ow data
                                                   (enc-rec-sym-key rbits ox oy steps)
                                                   vs asg0))))
        (:instance dec-crec-out-consp-rlcs
                   (nv (rec-point-of ng asg))
                   (rlcs (mv-nth 1 (dec-c-crec-sym pubp oc ow data
                                                   (enc-rec-sym-key rbits ox oy steps)
                                                   vs asg0))))
        (:instance dec-crec-out-owner-address
                   (nv (rec-point-of ng asg))
                   (rlcs (mv-nth 1 (dec-c-crec-sym pubp oc ow data
                                                   (enc-rec-sym-key rbits ox oy steps)
                                                   vs asg0)))))
  :in-theory '(crypto-record-decrypt enc-rec-sym-key dec-crec-of-wires-nonce
               values-group-fix-when-groupp lnfix nfix scalarp
               (:t reserrp) (:t record) dec-not-reserrp-of-record))
