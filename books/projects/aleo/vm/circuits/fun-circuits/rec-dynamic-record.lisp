; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DynamicRecord (snarkVM circuit/program/src/data/dynamic/record):
; owner: Address, root: Field, nonce: Group, version: U8.
;
; write_bits_*:  owner.x, root, nonce.x through Field::write_bits_* (Address and
;                Group write their x-coordinate), then the version's bit wires
;                (Integer::write_bits_* adds no constraint).
; find:          the path check is on the host; the result reuses the owner's
;                wires, no constraint.
;
; The owner and nonce points come from Address::new / Group::new and the
; version bits from Integer::new (R1CS-SOUND-IF); they are hypotheses here.

(in-package "ALEOVM")

(include-book "rec-dynamic-future")
(include-book "rec-owner")
(include-book "int-new")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled rec-values-group-x-of-point-finite
  (implies (and (natp x) (groupp (ecurve::point-finite x y)))
           (equal (values-group-x (ecurve::point-finite x y)) x))
  :enable (values-group-x ecurve::edwards-bls12-point->u))

(defruled rec-values-group-to-bits
  (implies (and (natp x) (groupp (ecurve::point-finite x y)))
           (and (equal (values-group-to-bits (ecurve::point-finite x y) nil)
                       (field-bits-le x))
                (equal (values-group-to-bits (ecurve::point-finite x y) t)
                       (rev (field-bits-le x)))))
  :enable (values-group-to-bits values-group-to-bits-le values-group-to-bits-be
           values-field-to-bits
           rec-values-group-x-of-point-finite)
  :use ((:instance rec-values-field-to-bits
                   (x (values-group-x (ecurve::point-finite x y))))))

(define rec-dynamic-record-of-wires ((ox symbolp) (oy symbolp) (rt symbolp)
                                     (nx symbolp) (ny symbolp)
                                     (vbits symbol-listp) (asg alistp))
  :verify-guards nil
  :returns (dr dynamic-recordp)
  (dynamic-record (ecurve::point-finite (lookup-equal ox asg) (lookup-equal oy asg))
                  (lookup-equal rt asg)
                  (ecurve::point-finite (lookup-equal nx asg) (lookup-equal ny asg))
                  (lebits=>nat (lookup-equal-list vbits asg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicRecord::write_bits_le / write_bits_be

(define rec-dynamic-record-write-bits-gadget ((ox symbolp) (rt symbolp)
                                              (nx symbolp)
                                              bitss rss (u symbolp))
  :guard (rec-bits-shapep (list ox rt nx) bitss rss)
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (symbolp ox) (symbolp rt) (symbolp nx) (symbolp u)
                              (rec-bits-shapep (list ox rt nx) bitss rss)))
  :short "Constraints of @('DynamicRecord::write_bits_le') and
          @('write_bits_be'): Field::write_bits_le on owner.x, root, nonce.x."
  (rec-fields-write-bits-gadget (list ox rt nx) bitss rss u))

(defruled rec-dynamic-record-write-bits-sound
  (b* ((xs (list ox rt nx))
       (vvals (lookup-equal-list vbits asg))
       (owner (ecurve::point-finite (lookup-equal ox asg) (lookup-equal oy asg)))
       (nonce (ecurve::point-finite (lookup-equal nx asg) (lookup-equal ny asg)))
       (dr (rec-dynamic-record-of-wires ox oy rt nx ny vbits asg)))
    (implies (and (symbolp ox) (symbolp oy) (symbolp rt) (symbolp nx) (symbolp ny)
                  (symbolp u)
                  (rec-bits-shapep xs bitss rss)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (rec-bits-boundp asg xs bitss rss)
                  (groupp owner)
                  (groupp nonce)
                  (bit-listp vvals)
                  (equal (len vvals) 8)
                  (r1cs::r1cs-constraints-holdp
                   (rec-dynamic-record-write-bits-gadget ox rt nx bitss rss u)
                   asg (base-prime)))
             (and (dynamic-recordp dr)
                  (equal (dynamic-record->owner dr) owner)
                  (equal (dynamic-record->root dr) (lookup-equal rt asg))
                  (equal (dynamic-record->nonce dr) nonce)
                  (equal (dynamic-record->version dr) (lebits=>nat vvals))
                  (equal (append (lookup-equal-list (rec-concat-le xs bitss) asg)
                                 vvals)
                         (dynamic-record-to-bits-le dr))
                  (equal (append (lookup-equal-list (rec-concat-be xs bitss) asg)
                                 (rev vvals))
                         (dynamic-record-to-bits-be dr)))))
  :do-not-induct t
  :enable (rec-dynamic-record-write-bits-gadget
           rec-dynamic-record-of-wires
           dynamic-record-to-bits-le dynamic-record-to-bits-be
           values-dynamic-record-to-bits
           crypto-field-list-bits-le crypto-field-list-bits-be
           rec-crypto-field-bits rec-values-field-to-bits
           rec-values-group-to-bits
           rec-values-uint-to-bits-of-lebits=>nat
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p
           lookup-equal-list fieldp pfield::fep
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :use ((:instance rec-fields-write-bits-sound (xs (list ox rt nx)))
        (:instance r1cs::fep-of-lookup-equal (var ox) (prime (base-prime))
                   (valuation asg))
        (:instance r1cs::fep-of-lookup-equal (var nx) (prime (base-prime))
                   (valuation asg))
        (:instance r1cs::fep-of-lookup-equal (var rt) (prime (base-prime))
                   (valuation asg))))

(defruled rec-dynamic-record-write-bits-complete
  (b* ((xs (list ox rt nx)))
    (implies (and (symbolp ox) (symbolp rt) (symbolp nx) (symbolp u)
                  (rec-bits-shapep xs bitss rss)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (rec-bits-boundp asg xs bitss rss)
                  (rec-bits-witness-okp asg xs bitss rss))
             (r1cs::r1cs-constraints-holdp
              (rec-dynamic-record-write-bits-gadget ox rt nx bitss rss u)
              asg (base-prime))))
  :enable rec-dynamic-record-write-bits-gadget
  :use (:instance rec-fields-write-bits-complete (xs (list ox rt nx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicRecord::find

(define rec-dynamic-record-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('DynamicRecord::find'): none."
  nil)

(defruled rec-dynamic-record-find-sound
  (b* ((owner (ecurve::point-finite (lookup-equal ox asg) (lookup-equal oy asg)))
       (dr (rec-dynamic-record-of-wires ox oy rt nx ny vbits asg)))
    (implies (and (groupp owner)
                  (values-access-is-owner-p path)
                  (r1cs::r1cs-constraints-holdp (rec-dynamic-record-find-gadget)
                                                asg (base-prime)))
             (equal (dynamic-record-find dr path)
                    (value-plaintext (plaintext-literal (literal-address owner))))))
  :enable (dynamic-record-find rec-dynamic-record-of-wires))

(defruled rec-dynamic-record-find-complete
  (r1cs::r1cs-constraints-holdp (rec-dynamic-record-find-gadget) asg p)
  :enable (rec-dynamic-record-find-gadget r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicRecord::to_fields: write_bits_le, the constant true, then
; Field::from_bits_le on 252-bit chunks (no constraint; linear combinations).

(defruled rec-len-of-dynamic-record-to-bits-le
  (equal (len (dynamic-record-to-bits-le dr)) 767)
  :enable (dynamic-record-to-bits-le values-dynamic-record-to-bits
           values-field-to-bits values-group-to-bits))

(defruled rec-dynamic-record-to-fields-unbounded
  (equal (dynamic-record-to-fields dr)
         (values-pack-bits (append (dynamic-record-to-bits-le dr) (list 1))))
  :do-not-induct t
  :enable (dynamic-record-to-fields values-pack-bits-bounded
           values-max-data-size-in-fields rec-len-of-dynamic-record-to-bits-le)
  :use (:instance rec-len-of-values-pack-bits-bound
                  (bits (append (dynamic-record-to-bits-le dr) (list 1)))
                  (k 4)))

(defruled rec-dynamic-record-to-fields-sound
  (b* ((xs (list ox rt nx))
       (vvals (lookup-equal-list vbits asg))
       (owner (ecurve::point-finite (lookup-equal ox asg) (lookup-equal oy asg)))
       (nonce (ecurve::point-finite (lookup-equal nx asg) (lookup-equal ny asg)))
       (dr (rec-dynamic-record-of-wires ox oy rt nx ny vbits asg)))
    (implies (and (symbolp ox) (symbolp oy) (symbolp rt) (symbolp nx) (symbolp ny)
                  (symbolp u)
                  (rec-bits-shapep xs bitss rss)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (rec-bits-boundp asg xs bitss rss)
                  (groupp owner)
                  (groupp nonce)
                  (bit-listp vvals)
                  (equal (len vvals) 8)
                  (r1cs::r1cs-constraints-holdp
                   (rec-dynamic-record-write-bits-gadget ox rt nx bitss rss u)
                   asg (base-prime)))
             (equal (values-pack-bits
                     (append (append (lookup-equal-list (rec-concat-le xs bitss) asg)
                                     vvals)
                             (list 1)))
                    (dynamic-record-to-fields dr))))
  :do-not-induct t
  :in-theory (e/d (rec-dynamic-record-to-fields-unbounded)
                  (dynamic-record-to-bits-le dynamic-record-to-fields))
  :use rec-dynamic-record-write-bits-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicRecord::new: Address::new on the owner, Field::new on the root
; (no constraint), Group::new on the nonce, U8::new on the version, all in
; Mode::Private.  A group block g lists the 14 wires of enforce_in_group:
; x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2.

(define rec-enforce-in-group ((g symbol-listp))
  :guard (equal (len g) 14)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (group-enforce-in-group-gadget (nth 0 g) (nth 1 g) (nth 2 g) (nth 3 g)
                                 (nth 4 g) (nth 5 g) (nth 6 g) (nth 7 g)
                                 (nth 8 g) (nth 9 g) (nth 10 g) (nth 11 g)
                                 (nth 12 g) (nth 13 g) (base-prime)))

(defruled rec-valuation-bindsp-of-nth
  (implies (and (r1cs::valuation-binds-allp asg g)
                (< (nfix i) (len g)))
           (r1cs::valuation-bindsp asg (nth i g)))
  :induct (nth i g)
  :enable (nth r1cs::valuation-binds-allp))

(defruled rec-enforce-in-group-sound
  (b* ((pt (ecurve::point-finite (lookup-equal (nth 0 g) asg)
                                 (lookup-equal (nth 1 g) asg))))
    (implies (and (symbol-listp g)
                  (equal (len g) 14)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg g)
                  (r1cs::r1cs-constraints-holdp (rec-enforce-in-group g)
                                                asg (base-prime)))
             (groupp pt)))
  :do-not-induct t
  :enable rec-enforce-in-group
  :use ((:instance group-new-wire-sound
                   (p (base-prime))
                   (x (nth 0 g)) (y (nth 1 g)) (qx (nth 2 g)) (qy (nth 3 g))
                   (cx2 (nth 4 g)) (cy2 (nth 5 g)) (dxy (nth 6 g))
                   (dx2 (nth 7 g)) (dy2 (nth 8 g)) (x3 (nth 9 g))
                   (y3 (nth 10 g)) (exy (nth 11 g)) (ex2 (nth 12 g))
                   (ey2 (nth 13 g)))
        (:instance rec-valuation-bindsp-of-nth (i 0))
        (:instance rec-valuation-bindsp-of-nth (i 1))
        (:instance rec-valuation-bindsp-of-nth (i 2))
        (:instance rec-valuation-bindsp-of-nth (i 3))
        (:instance rec-valuation-bindsp-of-nth (i 4))
        (:instance rec-valuation-bindsp-of-nth (i 5))
        (:instance rec-valuation-bindsp-of-nth (i 6))
        (:instance rec-valuation-bindsp-of-nth (i 7))
        (:instance rec-valuation-bindsp-of-nth (i 8))
        (:instance rec-valuation-bindsp-of-nth (i 9))
        (:instance rec-valuation-bindsp-of-nth (i 10))
        (:instance rec-valuation-bindsp-of-nth (i 11))
        (:instance rec-valuation-bindsp-of-nth (i 12))
        (:instance rec-valuation-bindsp-of-nth (i 13))))

(define rec-dynamic-record-new-gadget ((og symbol-listp) (ng symbol-listp)
                                       (vbits symbol-listp))
  :guard (and (equal (len og) 14) (equal (len ng) 14))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('DynamicRecord::new')."
  (append (rec-enforce-in-group og)
          (rec-enforce-in-group ng)
          (int-new-gadget vbits (base-prime))))

(defruled rec-dynamic-record-new-sound
  (b* ((vvals (lookup-equal-list vbits asg))
       (owner (ecurve::point-finite (lookup-equal (nth 0 og) asg)
                                    (lookup-equal (nth 1 og) asg)))
       (nonce (ecurve::point-finite (lookup-equal (nth 0 ng) asg)
                                    (lookup-equal (nth 1 ng) asg)))
       (dr (rec-dynamic-record-of-wires (nth 0 og) (nth 1 og) rt
                                        (nth 0 ng) (nth 1 ng) vbits asg)))
    (implies (and (symbol-listp og) (equal (len og) 14)
                  (symbol-listp ng) (equal (len ng) 14)
                  (symbolp rt)
                  (symbol-listp vbits) (equal (len vbits) 8)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg og)
                  (r1cs::valuation-binds-allp asg ng)
                  (r1cs::valuation-bindsp asg rt)
                  (r1cs::valuation-binds-allp asg vbits)
                  (r1cs::r1cs-constraints-holdp
                   (rec-dynamic-record-new-gadget og ng vbits) asg (base-prime)))
             (and (groupp owner)
                  (groupp nonce)
                  (bit-listp vvals)
                  (dynamic-recordp dr)
                  (equal (dynamic-record->owner dr) owner)
                  (equal (dynamic-record->root dr) (lookup-equal rt asg))
                  (equal (dynamic-record->nonce dr) nonce)
                  (equal (dynamic-record->version dr) (lebits=>nat vvals))
                  (equal (dynamic-record-new dr) dr))))
  :do-not-induct t
  :enable (rec-dynamic-record-new-gadget rec-dynamic-record-of-wires
           dynamic-record-new
           r1cs::r1cs-constraints-holdp-of-append
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p fieldp
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :use ((:instance rec-enforce-in-group-sound (g og))
        (:instance rec-enforce-in-group-sound (g ng))
        (:instance int-new-gadget-sound
                   (xs vbits) (p (base-prime)) (n 8) (signedp nil))))

(defruled rec-dynamic-record-new-complete
  :short "The constraints hold when each component's gadget holds; the
          component witnesses are those of group-enforce-in-group-gadget-complete
          (owner, nonce) and int-new-gadget-complete (version)."
  (equal (r1cs::r1cs-constraints-holdp
          (rec-dynamic-record-new-gadget og ng vbits) asg (base-prime))
         (and (r1cs::r1cs-constraints-holdp (rec-enforce-in-group og)
                                            asg (base-prime))
              (r1cs::r1cs-constraints-holdp (rec-enforce-in-group ng)
                                            asg (base-prime))
              (r1cs::r1cs-constraints-holdp (int-new-gadget vbits (base-prime))
                                            asg (base-prime))))
  :enable (rec-dynamic-record-new-gadget
           r1cs::r1cs-constraints-holdp-of-append))
