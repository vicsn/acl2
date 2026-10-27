; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Values used by the crypto-*.lisp specs, on top of values-model.lisp:
; ciphertexts and ciphertext records (Record<A, Ciphertext<A>>, which
; values-model.lisp does not model), the bit and field encodings of
; identifiers, program IDs, groups, and plaintexts, and Plaintext::find.
;
; The bit serializations of plaintexts, futures, dynamic records, and
; dynamic futures (Plaintext/Future/DynamicRecord/DynamicFuture::write_bits_le
; and Plaintext::from_bits_le) are abstract functions here, constrained only
; by their result types; they are specified elsewhere (values-*.lisp).
; Everything built on top of them (terminus bit, 252-bit packing, size
; limits, randomizers, hashing) is concrete.

(in-package "ALEOVM")

(include-book "crypto-model")
(include-book "values-model")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ciphertexts and ciphertext records.

; snarkVM circuit/program/src/data/ciphertext/mod.rs: Ciphertext(Vec<Field>),
; modeled as a values-field-list.

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner<A, Ciphertext<A>>.
(fty::deftagsum crypto-ciphertext-owner
  (:public ((address values-group)))
  (:private ((ciphertext values-field-list)))
  :pred crypto-ciphertext-ownerp)

; snarkVM circuit/program/src/data/record/entry/mod.rs: Entry<A, Ciphertext<A>>.
(fty::deftagsum crypto-ciphertext-entry
  (:constant ((get plaintext)))
  (:public ((get plaintext)))
  (:private ((get values-field-list)))
  :pred crypto-ciphertext-entryp)

(fty::defprod crypto-ciphertext-record-entry
  ((name identifier)
   (entry crypto-ciphertext-entry))
  :tag :crypto-ciphertext-record-entry
  :pred crypto-ciphertext-record-entryp)

(fty::deflist crypto-ciphertext-record-entry-list
  :elt-type crypto-ciphertext-record-entry
  :true-listp t
  :elementp-of-nil nil
  :pred crypto-ciphertext-record-entry-listp)

; snarkVM circuit/program/src/data/record/mod.rs: Record<A, Ciphertext<A>>.
(fty::defprod crypto-ciphertext-record
  ((owner crypto-ciphertext-owner)
   (data crypto-ciphertext-record-entry-list)
   (nonce values-group)
   (version acl2::ubyte8))
  :tag :crypto-ciphertext-record
  :pred crypto-ciphertext-recordp)

(fty::defresult crypto-ciphertext-owner-result
  :ok crypto-ciphertext-owner
  :pred crypto-ciphertext-owner-resultp
  :prepwork ((local (in-theory (enable crypto-ciphertext-owner-kind)))))

(fty::defresult crypto-ciphertext-entry-result
  :ok crypto-ciphertext-entry
  :pred crypto-ciphertext-entry-resultp
  :prepwork ((local (in-theory (enable crypto-ciphertext-entry-kind)))))

(fty::defresult crypto-ciphertext-record-result
  :ok crypto-ciphertext-record
  :pred crypto-ciphertext-record-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Abstract serializations (specified elsewhere).

(encapsulate
  (((crypto-plaintext-bits-le *) => * :formals (p) :guard (plaintextp p))
   ((crypto-plaintext-bits-be *) => * :formals (p) :guard (plaintextp p))
   ((crypto-plaintext-from-bits-le *) => * :formals (bits) :guard (bit-listp bits))
   ((crypto-future-bits-le *) => * :formals (f) :guard (futurep f))
   ((crypto-dynamic-record-bits-le *) => * :formals (r) :guard (dynamic-recordp r))
   ((crypto-dynamic-future-bits-le *) => * :formals (f) :guard (dynamic-futurep f)))

  (local (defun crypto-plaintext-bits-le (p) (declare (ignore p)) nil))
  (local (defun crypto-plaintext-bits-be (p) (declare (ignore p)) nil))
  (local (defun crypto-plaintext-from-bits-le (bits) (declare (ignore bits)) (spec-error)))
  (local (defun crypto-future-bits-le (f) (declare (ignore f)) nil))
  (local (defun crypto-dynamic-record-bits-le (r) (declare (ignore r)) nil))
  (local (defun crypto-dynamic-future-bits-le (f) (declare (ignore f)) nil))

  ; snarkVM circuit/program/src/data/plaintext/to_bits.rs: Plaintext::write_bits_le.
  (defrule bit-listp-of-crypto-plaintext-bits-le
    (bit-listp (crypto-plaintext-bits-le p)))

  ; snarkVM circuit/program/src/data/plaintext/to_bits.rs: Plaintext::write_bits_be.
  (defrule bit-listp-of-crypto-plaintext-bits-be
    (bit-listp (crypto-plaintext-bits-be p)))

  ; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_le.
  (defrule plaintext-resultp-of-crypto-plaintext-from-bits-le
    (plaintext-resultp (crypto-plaintext-from-bits-le bits))
    :enable spec-error)

  ; snarkVM circuit/program/src/data/future/to_bits.rs: Future::write_bits_le.
  (defrule bit-listp-of-crypto-future-bits-le
    (bit-listp (crypto-future-bits-le f)))

  ; snarkVM circuit/program/src/data/dynamic/record/to_bits.rs: DynamicRecord::write_bits_le.
  (defrule bit-listp-of-crypto-dynamic-record-bits-le
    (bit-listp (crypto-dynamic-record-bits-le r)))

  ; snarkVM circuit/program/src/data/dynamic/future/to_bits.rs: DynamicFuture::write_bits_le.
  (defrule bit-listp-of-crypto-dynamic-future-bits-le
    (bit-listp (crypto-dynamic-future-bits-le f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodings of groups, addresses, identifiers, and program IDs.

(defrule crypto-fieldp-when-values-field-listp
  (implies (and (values-field-listp x) (consp x))
           (fieldp (car x))))

(defrule crypto-field-listp-when-values-field-listp
  (implies (values-field-listp x)
           (crypto-field-listp x))
  :enable (crypto-field-listp values-field-listp))

(defrule crypto-values-field-listp-when-crypto-field-listp
  (implies (crypto-field-listp x)
           (values-field-listp x))
  :enable (crypto-field-listp values-field-listp))

; snarkVM circuit/types/group/src/helpers/to_bits.rs: Group::write_bits_le
; (the bits of the x-coordinate); also Address::write_bits_le.
(define crypto-group-bits-le ((p groupp))
  :returns (bits bit-listp)
  (crypto-field-bits-le (crypto-group-x p)))

; snarkVM circuit/types/group/src/helpers/to_bits.rs: Group::write_bits_be;
; also Address::write_bits_be.
(define crypto-group-bits-be ((p groupp))
  :returns (bits bit-listp)
  (crypto-field-bits-be (crypto-group-x p)))

; snarkVM circuit/types/group/src/helpers/from_x_coordinate.rs: Group::from_x_coordinate
; (also Address::from_field): the subgroup point with the given x-coordinate;
; from_xy_coordinates enforces subgroup membership, so the constraints are
; unsatisfiable if there is none.  At most one subgroup point has a given
; x-coordinate (the other candidate differs by the 2-torsion point (0,-1)).
(defchoose crypto-group-with-x (p) (x)
  (and (groupp p)
       (equal (ecurve::edwards-bls12-point->u p) x)))

(define crypto-group-from-x ((x fieldp))
  :returns (p (implies (not (reserrp p)) (groupp p)))
  (b* ((p (crypto-group-with-x x)))
    (if (and (groupp p)
             (equal (crypto-group-x p) x))
        p
      (spec-error))))

; snarkVM circuit/program/src/data/identifier/to_bits.rs: Identifier::write_bits_le
; (the field bits truncated to 8 * size bits).
(define crypto-identifier-bits-le ((id identifierp))
  :returns (bits bit-listp)
  (b* ((bits (crypto-field-bits-le (identifier->field id)))
       (n (* 8 (identifier->size id))))
    (take (min n (len bits)) bits)))

; snarkVM circuit/program/src/data/identifier/to_bits.rs: Identifier::write_bits_be
; (the reverse of write_bits_le).
(define crypto-identifier-bits-be ((id identifierp))
  :returns (bits bit-listp)
  (rev (crypto-identifier-bits-le id))
  :prepwork ((local (include-book "std/lists/rev" :dir :system))
             (local (defrule bit-listp-of-rev
                      (implies (bit-listp x) (bit-listp (rev x)))
                      :enable (rev bit-listp)))))

; snarkVM circuit/program/src/data/identifier/size_in_bits.rs: Identifier::size_in_bits
; (a u8 constant; 8 * size never overflows since size <= 31).
(define crypto-identifier-size-in-bits ((id identifierp))
  :returns (n natp)
  (* 8 (identifier->size id)))

; snarkVM circuit/program/src/id/to_bits.rs: ProgramID::write_bits_le (name || network).
(define crypto-program-id-bits-le ((pid program-idp))
  :returns (bits bit-listp)
  (append (crypto-identifier-bits-le (program-id->name pid))
          (crypto-identifier-bits-le (program-id->network pid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field encodings with a terminus bit.

; snarkVM: bits_le.push(true); bits_le.chunks(252).map(Field::from_bits_le), halting
; if there are more than MAX_DATA_SIZE_IN_FIELDS fields (the shared body of
; Plaintext/Record/Future/DynamicRecord/DynamicFuture/Entry::to_fields).
(define crypto-bits-to-fields-checked ((bits bit-listp))
  :returns (fields (implies (not (reserrp fields)) (values-field-listp fields)))
  (b* ((fields (crypto-bits-to-fields-with-terminus bits)))
    (if (> (len fields) (crypto-max-data-size-in-fields))
        (spec-error)
      fields)))

; snarkVM circuit/program/src/data/plaintext/to_fields.rs: Plaintext::to_fields
; (the concrete plaintext-to-fields of values-plaintext.lisp).
(define crypto-plaintext-to-fields ((p plaintextp))
  :returns (fields (implies (not (reserrp fields)) (values-field-listp fields))
                   :hints (("Goal" :use (:instance values-field-list-resultp-of-plaintext-to-fields
                                                   (pt p))
                                   :in-theory (enable values-field-list-resultp))))
  (plaintext-to-fields p))

; snarkVM circuit/program/src/data/plaintext/size_in_fields.rs: Plaintext::size_in_fields
; (also Plaintext::num_randomizers; the concrete plaintext-size-in-fields).
(define crypto-plaintext-size-in-fields ((p plaintextp))
  :returns (n (implies (not (reserrp n)) (natp n))
              :hints (("Goal" :in-theory (enable plaintext-size-in-fields))))
  (plaintext-size-in-fields p)
  ///
  (defret crypto-plaintext-size-in-fields-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable plaintext-size-in-fields spec-error)))))

; The data bits of field elements: the first 252 bits of each.
(define crypto-fields-data-bits ((fields values-field-listp))
  :returns (bits bit-listp)
  (if (endp fields)
      nil
    (append (take 252 (crypto-field-bits-le (car fields)))
            (crypto-fields-data-bits (cdr fields))))
  :guard-hints (("Goal" :in-theory (enable values-field-listp))))

; Remove the trailing zeros and the terminus bit (the last 1):
; iterate from the end, skipping up to and including the first 1.
(define crypto-strip-terminus ((rev-bits bit-listp))
  :returns (rev-rest bit-listp :hyp (bit-listp rev-bits))
  (cond ((endp rev-bits) nil)
        ((equal (car rev-bits) 1) (cdr rev-bits))
        (t (crypto-strip-terminus (cdr rev-bits)))))

; snarkVM circuit/program/src/data/plaintext/from_fields.rs: Plaintext::from_fields
; (the concrete plaintext-from-fields of values-plaintext.lisp).
(define crypto-plaintext-from-fields ((fields values-field-listp))
  :returns (p plaintext-resultp)
  (plaintext-from-fields fields))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plaintext equality and find.

; snarkVM circuit/program/src/data/plaintext/equal.rs: Plaintext::is_equal.
; Structural: literals of different variants, structs/arrays of different
; lengths, and different variants are unequal; otherwise member names,
; members, and elements are compared pairwise and conjoined.
(define crypto-plaintext-is-equal ((a plaintextp) (b plaintextp))
  :returns (r bitp)
  (if (equal (plaintext-fix a) (plaintext-fix b)) 1 0))

; IndexMap::get on struct members (the first member with the name).
(define crypto-plaintext-member-lookup ((name identifierp)
                                        (members plaintext-member-listp))
  :returns (p (implies (not (reserrp p)) (plaintextp p)))
  (b* (((when (endp members)) (spec-error))
       (member (car members)))
    (if (equal (plaintext-member->name member) (identifier-fix name))
        (plaintext-member->value member)
      (crypto-plaintext-member-lookup name (cdr members)))))

(define crypto-plaintext-find-loop ((p plaintextp) (path access-listp))
  :returns (q (implies (not (reserrp q)) (plaintextp q)))
  (b* (((when (endp path)) (plaintext-fix p))
       (access (car path))
       ((fty::ok q)
        (cond ((and (plaintext-case p :struct) (acl2::access-case access :member))
               (crypto-plaintext-member-lookup (acl2::access-member->name access)
                                               (plaintext-struct->members p)))
              ((and (plaintext-case p :array) (acl2::access-case access :index))
               (b* ((elements (plaintext-array->elements p))
                    (index (acl2::access-index->index access)))
                 (if (< index (len elements))
                     (plaintext-fix (nth index elements))
                   (spec-error))))
              (t (spec-error)))))
    (crypto-plaintext-find-loop q (cdr path)))
  :measure (len path)
  :verify-guards nil)

; snarkVM circuit/program/src/data/plaintext/find.rs: Plaintext::find.
; Halts on an empty path and on a literal; fails on a missing member,
; an out-of-range index, or a mismatched access (array indices are constants).
(define crypto-plaintext-find ((p plaintextp) (path access-listp))
  :returns (q (implies (not (reserrp q)) (plaintextp q)))
  (b* (((when (endp path)) (spec-error))
       ((when (plaintext-case p :literal)) (spec-error)))
    (crypto-plaintext-find-loop p path))
  :verify-guards nil)
