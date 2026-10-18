; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bridges between the Record<Plaintext> specs used by Value
; (values-record-* in fun-specs/values-value.lisp) and the crypto-record-*
; specs that the rec-record* circuits are proved against.  Both describe
; snarkVM circuit/program/src/data/record on the same record type:
; write_bits_le/be and to_fields coincide, is_equal/is_not_equal coincide,
; find coincides up to the error value, and Record::new (Entry::new on the
; data, re-inserted into an IndexMap) returns the record when each entry is
; a fixed point of Entry::new and the entry names have distinct fields.

(in-package "ALEOVM")

(include-book "rec-record-bits")
(include-book "rec-ciphertext")
(include-book "../fun-specs/values-value")

(set-verify-guards-eagerness 0)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))

(defruled rec-vb-field-bits
  (implies (fieldp x)
           (and (equal (crypto-field-bits-le x) (values-field-to-bits-le x))
                (equal (crypto-field-bits-be x) (values-field-to-bits-be x))))
  :use rec-crypto-field-bits
  :enable (crypto-field-bits-le crypto-nat->lebits values-field-to-bits-le
           values-field-to-bits-be values-nat-to-lebits base-field-size-in-bits
           field-bits-le values-field-fix))

(defruled rec-vb-group-x
  (implies (groupp p) (equal (crypto-group-x p) (values-group-x p)))
  :enable (crypto-group-x values-group-x values-group-fix
           curve-edwards-bls12-pointp-when-groupp))

(defruled rec-vb-group-bits
  (implies (groupp p)
           (and (equal (crypto-group-bits-le p) (values-group-to-bits-le p))
                (equal (crypto-group-bits-be p) (values-group-to-bits-be p))))
  :enable (crypto-group-bits-le crypto-group-bits-be values-group-to-bits-le
           values-group-to-bits-be rec-vb-group-x rec-vb-field-bits))

(defruled rec-vb-identifier-bits
  (and (equal (crypto-identifier-bits-le id) (identifier-to-bits-le id))
       (equal (crypto-identifier-bits-be id) (identifier-to-bits-be id)))
  :enable (crypto-identifier-bits-le crypto-identifier-bits-be identifier-to-bits-le
           identifier-to-bits-be identifier-size-in-bits rec-vb-field-bits)
  :use identifier-size-in-bits-upper-bound)

(defruled rec-vb-nat-bits
  (implies (natp x)
           (and (equal (crypto-nat->lebits n x) (values-nat-to-lebits n x))
                (equal (crypto-nat->bebits n x) (values-nat-to-bebits n x))))
  :enable (crypto-nat->lebits crypto-nat->bebits values-nat-to-lebits
           values-nat-to-bebits acl2::nat=>bebits acl2::nat=>bendian
           acl2::nat=>lebits))

(defruled rec-vb-data-bits
  (and (equal (values-record-data-to-bits data nil) (crypto-record-data-bits-le data))
       (equal (values-record-data-to-bits data t) (crypto-record-data-bits-be data)))
  :induct (len data)
  :enable (values-record-data-to-bits crypto-record-data-bits-le
           crypto-record-data-bits-be values-identifier-to-bits
           rec-vb-identifier-bits rec-crypto-entry-bits-le rec-crypto-entry-bits-be))

(defruled rec-vb-record-to-bits
  (and (equal (values-record-to-bits r nil) (crypto-record-write-bits-le r))
       (equal (values-record-to-bits r t) (crypto-record-write-bits-be r)))
  :enable (values-record-to-bits crypto-record-write-bits-le crypto-record-write-bits-be
           crypto-record-layout-bits-le crypto-record-layout-bits-be
           rec-vb-data-bits values-group-to-bits values-uint-to-bits
           values-int-to-bits-le values-int-to-bits-be rec-vb-nat-bits
           rec-vb-group-bits crypto-record-is-hiding crypto-owner-privatep
           crypto-owner-address values-owner-address))

(defruled rec-vb-record-to-fields
  (equal (values-record-to-fields r) (crypto-record-to-fields r))
  :enable (values-record-to-fields crypto-record-to-fields rec-vb-record-to-bits
           crypto-bits-to-fields-checked crypto-bits-to-fields-with-terminus
           values-pack-bits-bounded rec-crypto-pack-bits
           crypto-max-data-size-in-fields values-max-data-size-in-fields))

(defruled rec-vb-data-equalp
  (equal (crypto-record-data-is-equal a b)
         (values-bool-to-bit (values-record-data-equalp a b)))
  :induct (crypto-record-data-is-equal a b)
  :enable (crypto-record-data-is-equal values-record-data-equalp
           crypto-entry-is-equal values-entry-equalp values-entry-plaintext
           entry-kind crypto-bit-and crypto-bit-eq values-bool-to-bit))

(defruled rec-vb-owner-equalp
  (equal (crypto-owner-is-equal a b)
         (values-bool-to-bit
          (and (equal (owner-kind a) (owner-kind b))
               (equal (values-owner-address a) (values-owner-address b)))))
  :enable (crypto-owner-is-equal crypto-plaintext-is-equal values-owner-address
           values-bool-to-bit)
  :hints (("Goal" :cases ((owner-case a :public)))
          '(:use ((:instance plaintext-literal->get-of-plaintext-literal
                             (get (literal-address (owner-private->address a))))
                  (:instance plaintext-literal->get-of-plaintext-literal
                             (get (literal-address (owner-private->address b))))
                  (:instance literal-address->get-of-literal-address
                             (get (owner-private->address a)))
                  (:instance literal-address->get-of-literal-address
                             (get (owner-private->address b)))))))

(defruled rec-vb-record-equalp
  (and (equal (crypto-record-is-equal x y)
              (values-bool-to-bit (values-record-equalp x y)))
       (equal (crypto-record-is-not-equal x y)
              (values-bool-to-bit (not (values-record-equalp x y)))))
  :enable (crypto-record-is-equal crypto-record-is-not-equal values-record-equalp
           rec-vb-data-equalp rec-vb-owner-equalp crypto-bit-and crypto-bit-eq
           crypto-bit-not values-bool-to-bit))

(defruled rec-vb-owner-field
  (equal (identifier->field (crypto-owner-identifier))
         (values-owner-identifier-field))
  :enable ((:e crypto-owner-identifier) (:e values-owner-identifier-field)))

(defruled rec-vb-data-lookup
  (equal (values-record-data-lookup name data)
         (b* ((e (crypto-record-entry-lookup name data)))
           (if (reserrp e) nil e)))
  :induct (len data)
  :enable (values-record-data-lookup crypto-record-entry-lookup spec-error))

(defruled rec-vb-record-find
  (implies (access-listp path)
           (b* ((v (values-record-find r path))
                (c (crypto-record-find r path)))
             (and (iff (reserrp v) (reserrp c))
                  (implies (not (reserrp c)) (equal v c)))))
  :enable (values-record-find crypto-record-find values-access-is-owner-p
           rec-vb-owner-field rec-vb-data-lookup crypto-entry-find
           values-owner-to-entry crypto-owner-to-entry spec-error))

(define rec-vb-name-notin (f data)
  (or (atom data)
      (and (not (equal (identifier->field (record-entry->name (car data))) f))
           (rec-vb-name-notin f (cdr data)))))

(define rec-vb-names-distinctp (data)
  :short "The record entry names have pairwise distinct identifier fields
          (the keys of the console record's IndexMap)."
  (or (atom data)
      (and (rec-vb-name-notin (identifier->field (record-entry->name (car data)))
                              (cdr data))
           (rec-vb-names-distinctp (cdr data)))))

(define rec-vb-disjointp (d acc)
  (or (atom d)
      (and (rec-vb-name-notin (identifier->field (record-entry->name (car d))) acc)
           (rec-vb-disjointp (cdr d) acc))))

(defruled rec-vb-name-notin-of-append
  (equal (rec-vb-name-notin f (append a b))
         (and (rec-vb-name-notin f a) (rec-vb-name-notin f b)))
  :induct (len a)
  :enable rec-vb-name-notin)

(defruled rec-vb-disjointp-of-append
  (equal (rec-vb-disjointp d (append a b))
         (and (rec-vb-disjointp d a) (rec-vb-disjointp d b)))
  :induct (len d)
  :enable (rec-vb-disjointp rec-vb-name-notin-of-append))

(defruled rec-vb-disjointp-of-singleton
  (equal (rec-vb-disjointp d (list e))
         (rec-vb-name-notin (identifier->field (record-entry->name e)) d))
  :induct (len d)
  :enable (rec-vb-disjointp rec-vb-name-notin))

(defruled rec-vb-data-insert-new
  (implies (and (record-entry-listp acc)
                (rec-vb-name-notin (identifier->field name) acc))
           (equal (values-record-data-insert name e acc)
                  (append acc (list (make-record-entry :name name :entry e)))))
  :induct (len acc)
  :enable (values-record-data-insert rec-vb-name-notin))

(defruled rec-vb-data-new
  (implies (and (record-entry-listp d)
                (record-entry-listp acc)
                (rec-record-data-newp d)
                (rec-vb-names-distinctp d)
                (rec-vb-disjointp d acc))
           (equal (values-record-data-new d acc) (append acc d)))
  :induct (values-record-data-new d acc)
  :enable (values-record-data-new rec-record-data-newp rec-vb-names-distinctp
           rec-vb-data-insert-new rec-vb-disjointp-of-append
           rec-vb-disjointp-of-singleton)
  :hints ('(:expand ((rec-vb-disjointp d acc)))))

(defruled rec-vb-disjointp-of-nil
  (rec-vb-disjointp d nil)
  :induct (len d)
  :enable (rec-vb-disjointp rec-vb-name-notin))

(defruled rec-vb-record-new
  (implies (and (rec-record-data-newp (record->data r))
                (rec-vb-names-distinctp (record->data r)))
           (equal (values-record-new r) (record-fix r)))
  :enable (values-record-new rec-vb-disjointp-of-nil)
  :use (:instance rec-vb-data-new (d (record->data r)) (acc nil)))
