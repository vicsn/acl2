; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value::write_bits_le / write_bits_be / write_bits_raw_le / write_bits_raw_be
; / to_fields / to_fields_raw (snarkVM circuit/program/src/data/value): a
; dispatch on the variant to the arm's write_bits (the raw variants differ
; only on plaintexts), then packing into fields.
(in-package "ALEOVM")

(include-book "rec-value")
(include-book "rec-future-bits")
(set-verify-guards-eagerness 0)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Wires used by write_bits: a record wire continues with the owner / nonce
; x-coordinate bit and range-check wires and the is_hiding witnesses
; (obits ors nbits nrs vm vr); a dynamic record wire with the bit and
; range-check wires of (owner.x root nonce.x).

(define rec-rw-obits (w) (nth 5 w))
(define rec-rw-ors (w) (nth 6 w))
(define rec-rw-nbits (w) (nth 7 w))
(define rec-rw-nrs (w) (nth 8 w))
(define rec-rw-vm (w) (nth 9 w))
(define rec-rw-vr (w) (nth 10 w))

(define rec-drw-xs (w)
  (list (nth 0 (rec-drw-og w)) (rec-drw-rt w) (nth 0 (rec-drw-ng w))))
(define rec-drw-bitss (w) (nth 4 w))
(define rec-drw-rss (w) (nth 5 w))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Value::write_bits_le / write_bits_be: each arm's write_bits.

(define rec-vbits-gadget (vw bigp u)
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (ptx-bits-gadget w bigp))
      (:record (rec-record-bits-gadget (rec-rw-og w) (rec-rw-data w) (rec-rw-ng w)
                                       (rec-rw-vbits w) (rec-rw-obits w)
                                       (rec-rw-ors w) (rec-rw-nbits w)
                                       (rec-rw-nrs w) u (rec-rw-vm w)
                                       (rec-rw-vr w) bigp))
      (:future (rec-fbits-gadget w bigp u))
      (:dynamic-record (rec-dynamic-record-write-bits-gadget
                        (nth 0 (rec-drw-og w)) (rec-drw-rt w) (nth 0 (rec-drw-ng w))
                        (rec-drw-bitss w) (rec-drw-rss w) u))
      (otherwise (rec-dfbits-gadget w u)))))

(define rec-vbits-out (vw bigp)
  :short "The output bit terms, or @(':error') where snarkVM halts."
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (ptx-bits-out w bigp))
      (:record (rec-record-bits-out (rec-rw-pubp w) (rec-rw-data w)
                                    (rec-rw-vbits w) (rec-rw-obits w)
                                    (rec-rw-nbits w) (rec-rw-vr w) bigp))
      (:future (rec-fbits-out w bigp))
      (:dynamic-record
       (if bigp
           (append (rec-concat-be (rec-drw-xs w) (rec-drw-bitss w))
                   (rev (rec-drw-vbits w)))
         (append (rec-concat-le (rec-drw-xs w) (rec-drw-bitss w))
                 (rec-drw-vbits w))))
      (otherwise (rec-dfbits-out w bigp)))))

(define rec-vbits-hyps (vw asg)
  :short "The arm's R1CS-SOUND-IF of write_bits: what the arm's Inject
          establishes (literal leaves typed, points on the curve, version
          bits boolean) and the bit / range-check wires bound."
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (ptx-typed w asg))
      (:record
       (b* ((og (rec-rw-og w)) (ng (rec-rw-ng w)))
         (and (rec-rbinds w asg)
              (groupp (rec-point-of og asg))
              (groupp (rec-point-of ng asg))
              (bit-listp (lookup-equal-list (rec-rw-vbits w) asg))
              (rec-record-data-typed (rec-rw-data w) asg)
              (symbolp (rec-rw-vm w)) (symbolp (rec-rw-vr w))
              (r1cs::valuation-bindsp asg (rec-rw-vm w))
              (r1cs::valuation-bindsp asg (rec-rw-vr w))
              (rec-bits-shapep (list (nth 0 og)) (list (rec-rw-obits w))
                               (list (rec-rw-ors w)))
              (rec-bits-shapep (list (nth 0 ng)) (list (rec-rw-nbits w))
                               (list (rec-rw-nrs w)))
              (rec-bits-boundp asg (list (nth 0 og)) (list (rec-rw-obits w))
                               (list (rec-rw-ors w)))
              (rec-bits-boundp asg (list (nth 0 ng)) (list (rec-rw-nbits w))
                               (list (rec-rw-nrs w))))))
      (:future (rec-ftyped w asg))
      (:dynamic-record
       (and (rec-drbinds w asg)
            (groupp (rec-point-of (rec-drw-og w) asg))
            (groupp (rec-point-of (rec-drw-ng w) asg))
            (bit-listp (lookup-equal-list (rec-drw-vbits w) asg))
            (rec-bits-shapep (rec-drw-xs w) (rec-drw-bitss w) (rec-drw-rss w))
            (rec-bits-boundp asg (rec-drw-xs w) (rec-drw-bitss w) (rec-drw-rss w))))
      (otherwise (rec-dftyped w asg)))))

(defrule rec-true-listp-of-concat
  (and (true-listp (rec-concat-le xs bitss))
       (true-listp (rec-concat-be xs bitss)))
  :induct (len xs)
  :enable (rec-concat-le rec-concat-be))

(defrule rec-consp-of-ptx-bits-out
  (consp (ptx-bits-out wt bigp))
  :expand ((ptx-bits-out wt bigp)))

(defruled rec-consp-of-values-uint-to-bits
  (implies (posp n) (consp (values-uint-to-bits x n bigp)))
  :use len-of-values-uint-to-bits
  :in-theory (disable len-of-values-uint-to-bits))

(defrule rec-consp-of-fbits-out
  (implies (consp fw) (consp (rec-fbits-out fw bigp)))
  :expand ((rec-fbits-out fw bigp))
  :enable rec-consp-of-values-uint-to-bits)

(defrule rec-true-listp-of-dfbits-out
  (true-listp (rec-dfbits-out dfw bigp))
  :enable rec-dfbits-out)

(defmacro rec-vbits-sound-concl ()
  '(b* ((out (rec-vbits-out vw bigp))
        (spec (values-value-to-bits (rec-vval vw asg) bigp)))
     (and (iff (equal out :error) (reserrp spec))
          (implies (not (equal out :error))
                   (equal (ptx-terms-val out asg) spec)))))

(defruled rec-vbits-sound-ptx
  (implies (and (rec-u-hyps) (booleanp bigp)
                (equal (car vw) :plaintext)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :cases (bigp)
  :do-not-induct t
  :enable (rec-vbits-out rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
           values-value-to-bits plaintext-to-bits-le plaintext-to-bits-be
           primep-of-base-prime)
  :use ((:instance ptx-write-bits-le-sound (wt (cdr vw)))
        (:instance ptx-write-bits-be-sound (wt (cdr vw)))))

(defruled rec-vb-record-to-bits-bigp
  (implies (booleanp bigp)
           (equal (values-record-to-bits r bigp)
                  (if bigp (crypto-record-write-bits-be r)
                    (crypto-record-write-bits-le r))))
  :use rec-vb-record-to-bits)

(defruled rec-vbits-sound-record
  (implies (and (rec-u-hyps) (booleanp bigp)
                (equal (car vw) :record)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :do-not-induct t
  :in-theory (e/d (rec-vbits-out rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
                   rec-rwp rec-rbinds rec-rval values-value-to-bits
                   rec-vb-record-to-bits-bigp)
                  (rec-record-bits-out rec-record-bits-gadget
                   crypto-record-write-bits-le crypto-record-write-bits-be
                   values-record-to-bits))
  :use ((:instance rec-record-write-bits-sound
                   (pubp (rec-rw-pubp (cdr vw))) (og (rec-rw-og (cdr vw)))
                   (data (rec-rw-data (cdr vw))) (ng (rec-rw-ng (cdr vw)))
                   (vbits (rec-rw-vbits (cdr vw))) (obits (rec-rw-obits (cdr vw)))
                   (ors (rec-rw-ors (cdr vw))) (nbits (rec-rw-nbits (cdr vw)))
                   (nrs (rec-rw-nrs (cdr vw))) (vm (rec-rw-vm (cdr vw)))
                   (vr (rec-rw-vr (cdr vw))))))

(defruled rec-vbits-sound-future
  (implies (and (rec-u-hyps) (booleanp bigp)
                (equal (car vw) :future)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :cases (bigp)
  :do-not-induct t
  :enable (rec-vbits-out rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
           values-value-to-bits future-to-bits-le future-to-bits-be)
  :use ((:instance rec-future-write-bits-le-sound (fw (cdr vw)))
        (:instance rec-future-write-bits-be-sound (fw (cdr vw)))))

(defruled rec-vbits-sound-dr
  (implies (and (rec-u-hyps) (booleanp bigp)
                (equal (car vw) :dynamic-record)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :cases (bigp)
  :do-not-induct t
  :enable (rec-vbits-out rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
           rec-drwp rec-drbinds rec-drval rec-drw-xs rec-point-of
           values-value-to-bits dynamic-record-to-bits-le dynamic-record-to-bits-be
           rec-terms-val-of-symbols rec-symbol-listp-of-concat
           lookup-equal-list-of-rev rec-symbol-listp-of-rev lookup-equal-list-of-append)
  :use ((:instance rec-dynamic-record-write-bits-sound
                   (ox (nth 0 (rec-drw-og (cdr vw)))) (oy (nth 1 (rec-drw-og (cdr vw))))
                   (rt (rec-drw-rt (cdr vw)))
                   (nx (nth 0 (rec-drw-ng (cdr vw)))) (ny (nth 1 (rec-drw-ng (cdr vw))))
                   (vbits (rec-drw-vbits (cdr vw)))
                   (bitss (rec-drw-bitss (cdr vw))) (rss (rec-drw-rss (cdr vw))))))

(defruled rec-vbits-sound-df
  (implies (and (rec-u-hyps) (booleanp bigp)
                (equal (car vw) :dynamic-future)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :cases (bigp)
  :do-not-induct t
  :enable (rec-vbits-out rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
           values-value-to-bits)
  :use ((:instance rec-dfbits-sound (dfw (cdr vw)))))

(defruled rec-vbits-sound
  (implies (and (rec-u-hyps) (booleanp bigp)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (rec-vbits-sound-concl))
  :do-not-induct t
  :in-theory '(rec-vwp)
  :use (rec-vbits-sound-ptx rec-vbits-sound-record rec-vbits-sound-future
        rec-vbits-sound-dr rec-vbits-sound-df))

(defruled rec-value-write-bits-le-sound
  :short "R1CS-SOUND of Value::write_bits_le."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw nil u) asg p))
           (b* ((out (rec-vbits-out vw nil))
                (spec (value-to-bits-le (rec-vval vw asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-terms-val out asg) spec)))))
  :enable value-to-bits-le
  :use (:instance rec-vbits-sound (bigp nil)))

(defruled rec-value-write-bits-be-sound
  :short "R1CS-SOUND of Value::write_bits_be."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw t u) asg p))
           (b* ((out (rec-vbits-out vw t))
                (spec (value-to-bits-be (rec-vval vw asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-terms-val out asg) spec)))))
  :enable value-to-bits-be
  :use (:instance rec-vbits-sound (bigp t)))

(defruled rec-value-write-bits-gadget-arms
  :short "write_bits adds no constraint to its arm's, so its completeness is
          the arm's: ptx-write-bits-complete, rec-record-write-bits-complete,
          rec-future-write-bits-complete, rec-dynamic-record-write-bits-complete,
          rec-dfbits-complete."
  (b* ((w (cdr vw)))
    (equal (rec-vbits-gadget vw bigp u)
           (case (car vw)
             (:plaintext (ptx-bits-gadget w bigp))
             (:record (rec-record-bits-gadget
                       (rec-rw-og w) (rec-rw-data w) (rec-rw-ng w) (rec-rw-vbits w)
                       (rec-rw-obits w) (rec-rw-ors w) (rec-rw-nbits w)
                       (rec-rw-nrs w) u (rec-rw-vm w) (rec-rw-vr w) bigp))
             (:future (rec-fbits-gadget w bigp u))
             (:dynamic-record (rec-dynamic-record-write-bits-gadget
                               (nth 0 (rec-drw-og w)) (rec-drw-rt w)
                               (nth 0 (rec-drw-ng w)) (rec-drw-bitss w)
                               (rec-drw-rss w) u))
             (otherwise (rec-dfbits-gadget w u)))))
  :enable rec-vbits-gadget)

(defruled rec-value-write-bits-complete
  :short "R1CS-COMPLETE of Value::write_bits_le / _be on the arms whose
          completeness is witness-based (plaintext, future, dynamic future);
          the record and dynamic-record arms are by
          rec-value-write-bits-gadget-arms and their arm theorems."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg))
           (and (implies (and (equal (car vw) :plaintext)
                              (ptx-bits-witnessp (cdr vw) bigp asg p))
                         (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u)
                                                       asg p))
                (implies (and (equal (car vw) :future)
                              (rec-fbits-witnessp (cdr vw) bigp asg p))
                         (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u)
                                                       asg p))
                (implies (and (equal (car vw) :dynamic-future)
                              (rec-bits-witness-okp asg (rec-dfw-xs (cdr vw))
                                                    (nth 4 (cdr vw))
                                                    (nth 5 (cdr vw))))
                         (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u)
                                                       asg p))
                (implies (and (equal (car vw) :dynamic-record)
                              (symbolp u)
                              (rec-bits-witness-okp asg (rec-drw-xs (cdr vw))
                                                    (rec-drw-bitss (cdr vw))
                                                    (rec-drw-rss (cdr vw))))
                         (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u)
                                                       asg p))))
  :do-not-induct t
  :enable (rec-vbits-gadget rec-vwp rec-vbits-hyps primep-of-base-prime
           rec-drwp rec-drw-xs)
  :use ((:instance ptx-write-bits-complete (wt (cdr vw)))
        (:instance rec-future-write-bits-complete (fw (cdr vw)))
        (:instance rec-dfbits-complete (dfw (cdr vw)))
        (:instance rec-dynamic-record-write-bits-complete
                   (ox (nth 0 (rec-drw-og (cdr vw)))) (rt (rec-drw-rt (cdr vw)))
                   (nx (nth 0 (rec-drw-ng (cdr vw))))
                   (bitss (rec-drw-bitss (cdr vw))) (rss (rec-drw-rss (cdr vw))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; write_bits_raw_le / _be: the plaintext arm writes its raw bits; the other
; arms write their ordinary bits.  The constraints are write_bits'.

(define rec-vraw-out (vw bigp)
  (if (eq (car vw) :plaintext)
      (ptx-raw-out (cdr vw) bigp)
    (rec-vbits-out vw bigp)))

(defruled rec-vraw-sound
  (implies (and (rec-u-hyps) (booleanp bigp)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw bigp u) asg p))
           (b* ((out (rec-vraw-out vw bigp))
                (spec (values-value-to-bits-raw (rec-vval vw asg) bigp)))
             (and (implies (reserrp spec) (equal out :error))
                  (implies (not (reserrp spec))
                           (equal (ptx-terms-val out asg) spec)))))
  :do-not-induct t
  :cases (bigp)
  :enable (rec-vraw-out values-value-to-bits-raw)
  :use (rec-vbits-sound
        (:instance ptx-write-bits-raw-le-sound (wt (cdr vw)))
        (:instance ptx-write-bits-raw-be-sound (wt (cdr vw))))
  :hints ('(:in-theory (enable rec-vraw-out values-value-to-bits-raw
                               rec-vbits-gadget rec-vbits-hyps rec-vwp rec-vval
                               plaintext-to-bits-raw-le plaintext-to-bits-raw-be
                               primep-of-base-prime))))

(defruled rec-value-write-bits-raw-le-sound
  :short "R1CS-SOUND of Value::write_bits_raw_le."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw nil u) asg p))
           (b* ((out (rec-vraw-out vw nil))
                (spec (value-to-bits-raw-le (rec-vval vw asg))))
             (and (implies (reserrp spec) (equal out :error))
                  (implies (not (reserrp spec))
                           (equal (ptx-terms-val out asg) spec)))))
  :enable value-to-bits-raw-le
  :use (:instance rec-vraw-sound (bigp nil)))

(defruled rec-value-write-bits-raw-be-sound
  :short "R1CS-SOUND of Value::write_bits_raw_be."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw t u) asg p))
           (b* ((out (rec-vraw-out vw t))
                (spec (value-to-bits-raw-be (rec-vval vw asg))))
             (and (implies (reserrp spec) (equal out :error))
                  (implies (not (reserrp spec))
                           (equal (ptx-terms-val out asg) spec)))))
  :enable value-to-bits-raw-be
  :use (:instance rec-vraw-sound (bigp t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; to_fields: write_bits_le, the constant 1, packed into fields (linear);
; to_fields_raw: the plaintext arm packs its raw bits without the terminus,
; the other arms are to_fields.  The constraints are write_bits_le's.

(define rec-vfields-out (vw)
  (b* ((bits (rec-vbits-out vw nil)))
    (if (equal bits :error)
        :error
      (ptx-to-fields-out (append bits (list 1))))))

(define rec-vfields-raw-out (vw)
  (if (eq (car vw) :plaintext)
      (ptx-to-fields-out (ptx-raw-out (cdr vw) nil))
    (rec-vfields-out vw)))

(defruled rec-value-to-fields-of-bits
  (b* ((bits (values-value-to-bits v nil)))
    (and (implies (reserrp bits) (reserrp (value-to-fields v)))
         (implies (not (reserrp bits))
                  (equal (value-to-fields v)
                         (values-pack-bits-bounded (append bits (list 1)))))))
  :enable (value-to-fields values-value-to-bits plaintext-to-fields
           plaintext-to-bits-le values-record-to-fields future-to-fields
           future-to-bits-le dynamic-record-to-fields dynamic-record-to-bits-le
           dynamic-future-to-fields dynamic-future-to-bits-le))

(defruled rec-bit-listp-of-value-to-bits
  (implies (not (reserrp (values-value-to-bits v bigp)))
           (bit-listp (values-value-to-bits v bigp)))
  :use (:instance bit-list-resultp-of-values-value-to-bits)
  :enable bit-list-resultp)

(defruled rec-value-to-fields-sound
  :short "R1CS-SOUND of Value::to_fields."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw nil u) asg p))
           (b* ((out (rec-vfields-out vw))
                (spec (value-to-fields (rec-vval vw asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :do-not-induct t
  :enable rec-vfields-out
  :use ((:instance rec-vbits-sound (bigp nil))
        (:instance rec-value-to-fields-of-bits (v (rec-vval vw asg)))
        (:instance rec-bit-listp-of-value-to-bits (v (rec-vval vw asg)) (bigp nil))
        (:instance ptx-to-fields-out-correct
                   (terms (append (rec-vbits-out vw nil) (list 1))))))

(defruled rec-value-to-fields-raw-sound
  :short "R1CS-SOUND of Value::to_fields_raw."
  (implies (and (rec-u-hyps)
                (rec-vwp vw)
                (rec-vbits-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vbits-gadget vw nil u) asg p))
           (b* ((out (rec-vfields-raw-out vw))
                (spec (value-to-fields-raw (rec-vval vw asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :do-not-induct t
  :cases ((equal (car vw) :plaintext))
  :hints (("Subgoal 2" :in-theory (enable rec-vfields-raw-out value-to-fields-raw
                                          rec-vval rec-vwp)
           :use rec-value-to-fields-sound)
          ("Subgoal 1" :in-theory (enable rec-vfields-raw-out value-to-fields-raw
                                          rec-vval rec-vwp rec-vbits-hyps
                                          rec-vbits-gadget primep-of-base-prime)
           :use (:instance ptx-to-fields-raw-sound (wt (cdr vw))))))
