; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::decrypt_with_randomizers and Record::decrypt_symmetric_unchecked
; (snarkVM circuit/program/src/data/record/decrypt.rs).
;
; A ciphertext entry wire is (:constant . wt) or (:public . wt) with wt a
; plaintext wire tree, or (:private cs ds hv): the ciphertext field wires,
; the difference wires and the ejected data bits of
; Ciphertext::decrypt_with_randomizers (dec-ciphertext.lisp).  Constant and
; public entries pass through with no constraint.
;
; decrypt_with_randomizers: a public owner passes through; a private owner
;   is Address::from_field(c - r_0), modelled as in rec-owner-decrypt.lisp
;   with r_0 a linear combination.  Each private entry takes its slice of
;   the randomizers.  Out-of-range slices and duplicate names are host
;   halts.
; decrypt_symmetric_unchecked: num_randomizers (from the ciphertext
;   lengths, no constraint), hash_many_psd8([encryption_domain, key], n),
;   then decrypt_with_randomizers.
;
; The theorems carry the from_fields condition of each private entry
; (dec-pentry-okp): its ejected bits are the values of its data bits.

(in-package "ALEOVM")

(include-book "dec-ciphertext")
(include-book "rec-owner-decrypt")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Entries.

(defrule dec-values-field-listp-of-hpos-lc-eval-list
  (values-field-listp (hpos-lc-eval-list lcs asg primes::*bls12-377-scalar-field-prime*))
  :induct (len lcs)
  :enable (hpos-lc-eval-list values-field-listp fieldp))

(defrule dec-hpos-lc-eval-list-of-nthcdr
  (equal (hpos-lc-eval-list (nthcdr n lcs) asg p)
         (nthcdr n (hpos-lc-eval-list lcs asg p)))
  :induct (nthcdr n lcs)
  :enable (hpos-lc-eval-list nthcdr))

(defrule dec-hpos-lc-eval-list-of-take
  (implies (<= (nfix n) (len lcs))
           (equal (hpos-lc-eval-list (take n lcs) asg p)
                  (take n (hpos-lc-eval-list lcs asg p))))
  :induct (take n lcs)
  :enable (hpos-lc-eval-list take))

(define dec-cent-val (cew asg)
  :verify-guards nil
  (case (car cew)
    (:constant (crypto-ciphertext-entry-constant (ptx-val (cdr cew) asg)))
    (:public (crypto-ciphertext-entry-public (ptx-val (cdr cew) asg)))
    (otherwise (crypto-ciphertext-entry-private
                (ptx-terms-val (nth 0 (cdr cew)) asg)))))

(define dec-rec-data-eval (data asg)
  :verify-guards nil
  (if (atom data)
      nil
    (cons (crypto-ciphertext-record-entry (caar data) (dec-cent-val (cdar data) asg))
          (dec-rec-data-eval (cdr data) asg))))

(define dec-pentry-okp (cew asg)
  :verify-guards nil
  (b* ((cs (nth 0 (cdr cew))) (ds (nth 1 (cdr cew))) (hv (nth 2 (cdr cew))))
    (dec-ctx-hyps)))

(define dec-rec-datawp (data asg)
  :short "Well-formed entry wires, bound in ASG, and the from_fields
          condition on each private entry."
  :verify-guards nil
  (if (atom data)
      (null data)
    (b* ((cew (cdar data)))
      (and (consp (car data))
           (member-equal (car cew) '(:constant :public :private))
           (or (not (equal (car cew) :private))
               (dec-pentry-okp cew asg))
           (dec-rec-datawp (cdr data) asg)))))

(define dec-rec-data-gadget (data rlcs (index natp))
  :verify-guards nil
  (b* (((when (atom data)) nil)
       (cew (cdar data))
       ((unless (equal (car cew) :private))
        (dec-rec-data-gadget (cdr data) rlcs index))
       (cs (nth 0 (cdr cew))) (ds (nth 1 (cdr cew))) (hv (nth 2 (cdr cew)))
       (k (len cs)))
    (append (if (> (+ (nfix index) k) (len rlcs))
                nil
              (dec-ctx-gadget cs (take k (nthcdr index rlcs)) ds hv))
            (dec-rec-data-gadget (cdr data) rlcs (+ (nfix index) k)))))

(define dec-rec-entries-out (data rlcs (index natp) asg)
  :short "The decrypted entries, or @(':error') where snarkVM halts."
  :verify-guards nil
  (b* (((when (atom data)) nil)
       (cew (cdar data))
       (cs (nth 0 (cdr cew))) (ds (nth 1 (cdr cew))) (hv (nth 2 (cdr cew)))
       (k (if (equal (car cew) :private) (len cs) 0))
       ((when (> k (crypto-max-data-size-in-fields))) :error)
       ((when (> (+ (nfix index) k) (len rlcs))) :error)
       (pentry
        (case (car cew)
          (:constant (entry-constant (ptx-val (cdr cew) asg)))
          (:public (entry-public (ptx-val (cdr cew) asg)))
          (otherwise
           (b* ((res (dec-ctx-res cs (take k (nthcdr index rlcs)) ds hv)))
             (if (equal res :error)
                 :error
               (entry-private (ptx-val (cdr res) asg)))))))
       ((when (equal pentry :error)) :error)
       (rest (dec-rec-entries-out (cdr data) rlcs (+ (nfix index) k) asg))
       ((when (equal rest :error)) :error))
    (cons (record-entry (caar data) pentry) rest)))

(defrule dec-not-reserrp-of-cons-record-entry
  (not (reserrp (cons (record-entry n e) rest)))
  :enable (reserrp record-entry))

(defruled dec-randomizer-slice-ok
  (implies (and (natp index) (natp k)
                (values-field-listp rvals)
                (<= (+ index k) (len rvals)))
           (equal (crypto-randomizer-slice rvals index k)
                  (take k (nthcdr index rvals))))
  :enable crypto-randomizer-slice)

(defruled dec-randomizer-slice-err
  (implies (and (natp index) (natp k)
                (< (len rvals) (+ index k)))
           (reserrp (crypto-randomizer-slice rvals index k)))
  :enable crypto-randomizer-slice)

(defruled dec-num-randomizers-of-cent-val
  (equal (crypto-ciphertext-entry-num-randomizers (dec-cent-val cew asg))
         (if (member-equal (car cew) '(:constant :public))
             0
           (crypto-ciphertext-size-in-fields
            (values-field-list-fix (ptx-terms-val (nth 0 (cdr cew)) asg)))))
  :enable (dec-cent-val crypto-ciphertext-entry-num-randomizers))

(defruled dec-decrypt-entries-of-cons
  (equal (crypto-record-decrypt-entries
          (cons (crypto-ciphertext-record-entry name e) rest) rvals index)
         (b* ((entry (crypto-ciphertext-entry-fix e))
              ((fty::ok k) (crypto-ciphertext-entry-num-randomizers entry))
              (k (nfix k))
              ((fty::ok rs) (crypto-randomizer-slice rvals index k))
              ((fty::ok pentry)
               (crypto-ciphertext-entry-case entry
                 :constant (entry-constant entry.get)
                 :public (entry-public entry.get)
                 :private (b* (((fty::ok p) (crypto-ciphertext-decrypt-with-randomizers
                                             entry.get rs)))
                            (entry-private p))))
              ((fty::ok rest) (crypto-record-decrypt-entries rest rvals
                                                             (+ (lnfix index) k))))
           (cons (record-entry (identifier-fix name) pentry) rest)))
  :expand ((crypto-record-decrypt-entries
            (cons (crypto-ciphertext-record-entry name e) rest) rvals index)))

(defruled dec-private-head-sound-0
  (b* ((k (len cs))
       (res (dec-ctx-res cs (take k (nthcdr index rlcs)) ds hv))
       (spec (crypto-ciphertext-decrypt-with-randomizers
              (ptx-terms-val cs asg)
              (take k (nthcdr index (hpos-lc-eval-list rlcs asg (base-prime)))))))
    (implies (and (dec-ctx-hyps)
                  (natp index)
                  (<= (+ index k) (len rlcs))
                  (r1cs::r1cs-constraints-holdp
                   (dec-ctx-gadget cs (take k (nthcdr index rlcs)) ds hv)
                   asg (base-prime)))
             (and (iff (equal res :error) (reserrp spec))
                  (implies (not (equal res :error))
                           (equal (ptx-val (cdr res) asg) spec)))))
  :use ((:instance dec-ctx-sound (rs (take (len cs) (nthcdr index rlcs)))))
  :in-theory '(dec-hpos-lc-eval-list-of-take dec-hpos-lc-eval-list-of-nthcdr
               acl2::len-of-nthcdr nfix natp acl2::natp-compound-recognizer
               (:t len) fix))

(defruled dec-private-head-sound
  (b* ((cs (nth 0 (cdr cew))) (ds (nth 1 (cdr cew))) (hv (nth 2 (cdr cew)))
       (k (len cs))
       (res (dec-ctx-res cs (take k (nthcdr index rlcs)) ds hv))
       (spec (crypto-ciphertext-decrypt-with-randomizers
              (values-field-list-fix (ptx-terms-val cs asg))
              (take k (nthcdr index (hpos-lc-eval-list rlcs asg (base-prime)))))))
    (implies (and (dec-pentry-okp cew asg)
                  (natp index)
                  (<= (+ index k) (len rlcs))
                  (r1cs::r1cs-constraints-holdp
                   (dec-ctx-gadget cs (take k (nthcdr index rlcs)) ds hv)
                   asg (base-prime)))
             (and (iff (equal res :error) (reserrp spec))
                  (implies (not (equal res :error))
                           (equal (ptx-val (cdr res) asg) spec)))))
  :use ((:instance dec-private-head-sound-0
                   (cs (nth 0 (cdr cew))) (ds (nth 1 (cdr cew)))
                   (hv (nth 2 (cdr cew)))))
  :in-theory '(dec-pentry-okp dec-values-field-listp-of-terms-val
               values-field-list-fix-when-values-field-listp))

(defrule dec-cent-val-private-get
  (implies (and (not (equal (car cew) :constant))
                (not (equal (car cew) :public)))
           (equal (crypto-ciphertext-entry-private->get (dec-cent-val cew asg))
                  (values-field-list-fix (ptx-terms-val (nth 0 (cdr cew)) asg))))
  :enable dec-cent-val)

(defrule dec-cent-val-kind
  (equal (crypto-ciphertext-entry-kind (dec-cent-val cew asg))
         (case (car cew)
           (:constant :constant)
           (:public :public)
           (otherwise :private)))
  :enable dec-cent-val)

(defrule dec-cent-val-constant-get
  (implies (equal (car cew) :constant)
           (equal (crypto-ciphertext-entry-constant->get (dec-cent-val cew asg))
                  (ptx-val (cdr cew) asg)))
  :enable dec-cent-val)

(defrule dec-cent-val-public-get
  (implies (equal (car cew) :public)
           (equal (crypto-ciphertext-entry-public->get (dec-cent-val cew asg))
                  (ptx-val (cdr cew) asg)))
  :enable dec-cent-val)

(defrule dec-crypto-ciphertext-entry-fix-of-cent-val
  (equal (crypto-ciphertext-entry-fix (dec-cent-val cew asg))
         (dec-cent-val cew asg))
  :enable dec-cent-val)

(defrule dec-decrypt-entries-of-atom
  (implies (atom data)
           (equal (crypto-record-decrypt-entries data rvals index) nil))
  :enable crypto-record-decrypt-entries)

(defruled dec-rec-entries-sound
  (b* ((out (dec-rec-entries-out data rlcs index asg))
       (spec (crypto-record-decrypt-entries
              (dec-rec-data-eval data asg)
              (hpos-lc-eval-list rlcs asg (base-prime))
              index)))
    (implies (and (dec-rec-datawp data asg)
                  (natp index)
                  (r1cs::r1cs-constraints-holdp (dec-rec-data-gadget data rlcs index)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :induct (dec-rec-entries-out data rlcs index asg)
  :in-theory (e/d (dec-rec-entries-out dec-rec-data-eval dec-rec-datawp
                   dec-rec-data-gadget dec-decrypt-entries-of-cons
                   dec-num-randomizers-of-cent-val
                   crypto-ciphertext-size-in-fields
                   r1cs::r1cs-constraints-holdp-of-append)
                  (dec-cent-val crypto-record-decrypt-entries dec-ctx-res
                   dec-ctx-gadget crypto-ciphertext-decrypt-with-randomizers
                   take nthcdr ptx-val dec-pentry-okp))
  :hints ((and (equal (car id) '(0 1))
               (equal (len (cadr id)) 1)
               '(:use ((:instance dec-private-head-sound (cew (cdar data)))
                       (:instance dec-randomizer-slice-ok
                                  (rvals (hpos-lc-eval-list rlcs asg (base-prime)))
                                  (k (if (equal (cadr (car data)) :private)
                                         (len (nth 0 (cdr (cdar data)))) 0)))
                       (:instance dec-randomizer-slice-err
                                  (rvals (hpos-lc-eval-list rlcs asg (base-prime)))
                                  (k (if (equal (cadr (car data)) :private)
                                         (len (nth 0 (cdr (cdar data)))) 0))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner::decrypt with a linear-combination randomizer.

(define dec-owner-gadget (oc r0 ow)
  :short "Private Owner::decrypt with the randomizer a linear combination:
          (oc - r0) * 1 = x, then Group::from_x_coordinate on the 14 wires
          OW (x first, y second)."
  :verify-guards nil
  (append (enc-lc-eq-gadget (hpos-lc-sv (dec-sub-lc oc r0)) (nth 0 ow))
          (grp-from-x-coordinate-gadget
           (nth 0 ow) (nth 1 ow) (nth 2 ow) (nth 3 ow) (nth 4 ow) (nth 5 ow)
           (nth 6 ow) (nth 7 ow) (nth 8 ow) (nth 9 ow) (nth 10 ow) (nth 11 ow)
           (nth 12 ow) (nth 13 ow) (base-prime))))

(defmacro dec-owner-hyps ()
  '(and (symbolp oc)
        (symbol-listp ow) (equal (len ow) 14)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-bindsp asg oc)
        (r1cs::valuation-binds-allp asg ow)))

(defruled dec-owner-gadget-sound
  (implies (and (dec-owner-hyps)
                (r1cs::r1cs-constraints-holdp (dec-owner-gadget oc r0 ow)
                                              asg (base-prime)))
           (equal (crypto-owner-decrypt
                   (crypto-ciphertext-owner-private (list (lookup-equal oc asg)))
                   (list (hpos-lc-eval r0 asg (base-prime))))
                  (owner-private (rec-point-of ow asg))))
  :do-not-induct t
  :use ((:instance dec-sub-eq-holds (c oc) (d (nth 0 ow)) (r r0))
        (:instance rec-from-x-gadget-crypto-group
                   (x (nth 0 ow)) (y (nth 1 ow)) (qx (nth 2 ow)) (qy (nth 3 ow))
                   (cx2 (nth 4 ow)) (cy2 (nth 5 ow)) (dxy (nth 6 ow))
                   (dx2 (nth 7 ow)) (dy2 (nth 8 ow)) (x3 (nth 9 ow))
                   (y3 (nth 10 ow)) (exy (nth 11 ow)) (ex2 (nth 12 ow))
                   (ey2 (nth 13 ow)) (p (base-prime)))
        (:instance grp-from-x-coordinate-gadget-sound
                   (x (nth 0 ow)) (y (nth 1 ow)) (qx (nth 2 ow)) (qy (nth 3 ow))
                   (cx2 (nth 4 ow)) (cy2 (nth 5 ow)) (dxy (nth 6 ow))
                   (dx2 (nth 7 ow)) (dy2 (nth 8 ow)) (x3 (nth 9 ow))
                   (y3 (nth 10 ow)) (exy (nth 11 ow)) (ex2 (nth 12 ow))
                   (ey2 (nth 13 ow)) (p (base-prime)))
        (:instance return-type-of-group-from-x-coordinate-funspec
                   (x (lookup-equal (nth 0 ow) asg)))
        (:instance rec-not-reserrp-of-point-finite
                   (a (lookup-equal (nth 0 ow) asg))
                   (b (lookup-equal (nth 1 ow) asg)))
        (:instance r1cs::fep-of-lookup-equal (var oc) (valuation asg)
                   (prime (base-prime))))
  :in-theory (e/d (dec-owner-gadget crypto-owner-decrypt crypto-field-sub
                   rec-point-of r1cs::r1cs-constraints-holdp-of-append
                   r1cs::valuation-binds-allp fieldp)
                  (grp-from-x-coordinate-gadget pfield::sub
                   rec-from-x-gadget-crypto-group
                   grp-from-x-coordinate-gadget-sound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Record::decrypt_with_randomizers

(define dec-crec-of-wires (pubp og oc data nv vv asg)
  :short "The ciphertext record of the wires: the owner (the point of OG if
          public, the field wire OC if private), the entries, and the nonce
          and version values NV and VV."
  :verify-guards nil
  (crypto-ciphertext-record
   (if pubp
       (crypto-ciphertext-owner-public (rec-point-of og asg))
     (crypto-ciphertext-owner-private (list (lookup-equal oc asg))))
   (dec-rec-data-eval data asg)
   nv vv))

(define dec-crec-gadget (pubp oc ow data rlcs)
  :verify-guards nil
  (append (if (or pubp (atom rlcs)) nil (dec-owner-gadget oc (car rlcs) ow))
          (dec-rec-data-gadget data rlcs (if pubp 0 1))))

(define dec-crec-out (pubp og oc ow data nv vv rlcs asg)
  :short "The decrypted record, or @(':error') where snarkVM halts."
  :verify-guards nil
  (declare (ignorable oc))
  (b* (((when (and (not pubp) (atom rlcs))) :error)
       (owner (if pubp
                  (owner-public (rec-point-of og asg))
                (owner-private (rec-point-of ow asg))))
       (pdata (dec-rec-entries-out data rlcs (if pubp 0 1) asg))
       ((when (equal pdata :error)) :error)
       ((unless (no-duplicatesp-equal
                 (crypto-ciphertext-record-entry-names (dec-rec-data-eval data asg))))
        :error))
    (record owner pdata nv vv)))

(defmacro dec-crec-hyps ()
  '(and (booleanp pubp)
        (r1cs::r1cs-valuationp asg (base-prime))
        (if pubp
            (groupp (rec-point-of og asg))
          (dec-owner-hyps))
        (dec-rec-datawp data asg)))

(defrule dec-not-reserrp-of-record
  (not (reserrp (record o d n v)))
  :enable (reserrp record))

(defrule dec-crypto-ciphertext-record-entry-listp-of-data-eval
  (crypto-ciphertext-record-entry-listp (dec-rec-data-eval data asg))
  :induct (len data)
  :enable dec-rec-data-eval)

(defruled dec-record-decrypt-with-randomizers-sound
  :short "Soundness of Record::decrypt_with_randomizers on randomizer linear
          combinations, under the from_fields condition on each private
          entry."
  (b* ((out (dec-crec-out pubp og oc ow data nv vv rlcs asg))
       (spec (crypto-record-decrypt-with-randomizers
              (dec-crec-of-wires pubp og oc data nv vv asg)
              (hpos-lc-eval-list rlcs asg (base-prime)))))
    (implies (and (dec-crec-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (dec-crec-gadget pubp oc ow data rlcs) asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance dec-rec-entries-sound (index (if pubp 0 1)))
        (:instance dec-owner-gadget-sound (r0 (car rlcs))))
  :expand ((hpos-lc-eval-list rlcs asg (base-prime)))
  :in-theory (e/d (dec-crec-out dec-crec-gadget dec-crec-of-wires
                   crypto-record-decrypt-with-randomizers crypto-owner-decrypt
                   r1cs::r1cs-constraints-holdp-of-append)
                  (dec-rec-entries-sound dec-owner-gadget-sound
                   dec-rec-entries-out dec-rec-data-gadget dec-owner-gadget
                   crypto-record-decrypt-entries)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Record::decrypt_symmetric_unchecked

(define dec-entries-nr (data acc)
  :short "Host computation of the entries' randomizer count."
  :verify-guards nil
  (b* (((when (atom data)) (nfix acc))
       (cew (cdar data))
       (k (if (equal (car cew) :private) (len (nth 0 (cdr cew))) 0))
       ((when (> k (crypto-max-data-size-in-fields))) :error)
       (acc (+ (nfix acc) k))
       ((when (>= acc 65536)) :error))
    (dec-entries-nr (cdr data) acc)))

(define dec-crec-nr (pubp data)
  :short "Record::<Ciphertext>::num_randomizers, from the wire shapes."
  :verify-guards nil
  (b* ((n (dec-entries-nr data (if pubp 0 1)))
       ((when (equal n :error)) :error)
       ((when (> (nfix n) (crypto-max-data-size-in-fields))) :error))
    (nfix n)))

(defruled dec-entries-nr-sound
  (b* ((n (dec-entries-nr data acc))
       (spec (crypto-ciphertext-record-entries-num-randomizers
              (dec-rec-data-eval data asg) acc)))
    (implies (and (dec-rec-datawp data asg) (natp acc))
             (and (iff (equal n :error) (reserrp spec))
                  (implies (not (equal n :error)) (equal n spec)))))
  :induct (dec-entries-nr data acc)
  :in-theory (e/d (dec-entries-nr dec-rec-data-eval dec-rec-datawp
                   crypto-ciphertext-record-entries-num-randomizers
                   dec-num-randomizers-of-cent-val
                   crypto-ciphertext-size-in-fields dec-pentry-okp)
                  (dec-cent-val)))

(defruled dec-crec-nr-sound
  (b* ((n (dec-crec-nr pubp data))
       (spec (crypto-ciphertext-record-num-randomizers
              (dec-crec-of-wires pubp og oc data nv vv asg))))
    (implies (dec-rec-datawp data asg)
             (and (iff (equal n :error) (reserrp spec))
                  (implies (not (equal n :error)) (equal n spec)))))
  :use (:instance dec-entries-nr-sound (acc (if pubp 0 1)))
  :in-theory (e/d (dec-crec-nr dec-crec-of-wires
                   crypto-ciphertext-record-num-randomizers)
                  (dec-entries-nr-sound)))

(defund dec-c-crec-sym (pubp oc ow data key vs asg)
  "Synthesis of Record::decrypt_symmetric_unchecked:
   (mv n rlcs cs vs asg), n the randomizer count (or :error)."
  (declare (xargs :verify-guards nil))
  (b* ((n (dec-crec-nr pubp data))
       ((mv rlcs hcs vs asg)
        (hpos-c-poseidon-hash-many 8 (enc-randomizer-inputs key) (nfix n) vs asg)))
    (mv n rlcs
        (append hcs (dec-crec-gadget pubp oc ow data rlcs))
        vs asg)))

(defmacro dec-crec-hyps-x ()
  '(and (booleanp pubp)
        (r1cs::r1cs-valuationp asgx (base-prime))
        (if pubp
            (groupp (rec-point-of og asgx))
          (and (symbolp oc)
               (symbol-listp ow) (equal (len ow) 14)
               (r1cs::valuation-bindsp asgx oc)
               (r1cs::valuation-binds-allp asgx ow)))
        (dec-rec-datawp data asgx)))

(defruled dec-record-decrypt-symmetric-unchecked-sound
  :short "Soundness of Record::decrypt_symmetric_unchecked on a field key
          wire, under the from_fields condition on each private entry."
  (b* (((mv n rlcs cons & &) (dec-c-crec-sym pubp oc ow data key vs asg))
       (out (if (equal n :error)
                :error
              (dec-crec-out pubp og oc ow data nv vv rlcs asgx)))
       (spec (crypto-record-decrypt-symmetric-unchecked
              (dec-crec-of-wires pubp og oc data nv vv asgx)
              (lookup-equal key asgx))))
    (implies (and (dec-crec-hyps-x)
                  (symbolp key)
                  (r1cs::valuation-bindsp asgx key)
                  (r1cs::r1cs-constraints-holdp cons asgx (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance dec-crec-nr-sound (asg asgx))
        (:instance dec-record-decrypt-with-randomizers-sound
                   (rlcs (mv-nth 0 (hpos-c-poseidon-hash-many
                                    8 (enc-randomizer-inputs key)
                                    (nfix (dec-crec-nr pubp data)) vs asg)))
                   (asg asgx))
        (:instance hpos-c-poseidon-hash-many-sound
                   (rate 8) (xs (enc-randomizer-inputs key))
                   (nout (nfix (dec-crec-nr pubp data))))
        (:instance r1cs::fep-of-lookup-equal (var key) (valuation asgx)
                   (prime (base-prime)))
        (:instance enc-eval-randomizer-inputs (asg asgx)))
  :in-theory (e/d (dec-c-crec-sym crypto-record-decrypt-symmetric-unchecked
                   enc-crypto-hash-many-psd-8 enc-base-prime-value
                   crypto-encryption-domain-is-values-encryption-domain
                   fieldp hpos-aleo-rate-p
                   r1cs::r1cs-constraints-holdp-of-append)
                  (dec-crec-nr-sound dec-record-decrypt-with-randomizers-sound
                   hpos-c-poseidon-hash-many-sound dec-crec-out
                   dec-crec-gadget dec-crec-nr dec-crec-of-wires)))
