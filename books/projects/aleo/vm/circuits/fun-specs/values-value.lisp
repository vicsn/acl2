; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FUN-SPECs of Future, Argument, DynamicFuture, DynamicRecord, Value,
; and the state-path leaves of the circuit program crate
; (snarkVM circuit/program/src/data/{future,dynamic,value}, state_path).
;
; The record operations used by Value (to_bits, to_fields, find, equality,
; injection of Record<Plaintext>) are defined here as values-record-*
; helpers.  The console-only data of dynamic records and futures
; (Option<...> fields that never enter the circuit) is not modeled.

(in-package "ALEOVM")

(include-book "values-plaintext")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (enable spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers.

(define values-field-to-bits ((x fieldp) (bigp booleanp))
  :returns (bits bit-listp)
  (if bigp (values-field-to-bits-be x) (values-field-to-bits-le x)))

(define values-group-to-bits ((g groupp) (bigp booleanp))
  :returns (bits bit-listp)
  (if bigp (values-group-to-bits-be g) (values-group-to-bits-le g)))

; snarkVM console Identifier::from_str("owner"): its field element.
(define values-owner-identifier-field ()
  :returns (f fieldp)
  (values-lebits-to-field
   (values-bytes-to-lebits (values-chars-to-bytes (coerce "owner" 'list)))))

(define values-access-is-owner-p ((path access-listp))
  :returns (yes/no booleanp)
  :short "Rust @('path.len() == 1 && path[0] == Access::Member(Identifier::from_str(\"owner\"))')
          (identifiers are compared by their field elements)."
  (and (consp path)
       (endp (cdr path))
       (acl2::access-case (car path) :member)
       (equal (identifier->field (acl2::access-member->name (car path)))
              (values-owner-identifier-field))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; DynamicFuture.

; snarkVM circuit/program/src/data/dynamic/future/mod.rs: DynamicFuture::new (Inject).
(define dynamic-future-new ((df dynamic-futurep))
  :returns (df1 dynamic-futurep)
  (dynamic-future-fix df))

(define values-dynamic-future-to-bits ((df dynamic-futurep) (bigp booleanp))
  :returns (bits bit-listp)
  (append (values-field-to-bits (dynamic-future->program-name df) bigp)
          (values-field-to-bits (dynamic-future->program-network df) bigp)
          (values-field-to-bits (dynamic-future->function-name df) bigp)
          (values-field-to-bits (dynamic-future->checksum df) bigp)))

; snarkVM circuit/program/src/data/dynamic/future/to_bits.rs: DynamicFuture::write_bits_le.
(define dynamic-future-to-bits-le ((df dynamic-futurep))
  :returns (bits bit-listp)
  (values-dynamic-future-to-bits df nil))

; snarkVM circuit/program/src/data/dynamic/future/to_bits.rs: DynamicFuture::write_bits_be.
(define dynamic-future-to-bits-be ((df dynamic-futurep))
  :returns (bits bit-listp)
  (values-dynamic-future-to-bits df t))

; snarkVM circuit/program/src/data/dynamic/future/to_fields.rs: DynamicFuture::to_fields.
(define dynamic-future-to-fields ((df dynamic-futurep))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded (append (dynamic-future-to-bits-le df) (list 1))))

; snarkVM circuit/program/src/data/dynamic/future/equal.rs: DynamicFuture::is_equal.
(define dynamic-future-is-equal ((x dynamic-futurep) (y dynamic-futurep))
  :returns (b bitp)
  (values-bool-to-bit (equal (dynamic-future-fix x) (dynamic-future-fix y))))

; snarkVM circuit/program/src/data/dynamic/future/equal.rs: DynamicFuture::is_not_equal.
(define dynamic-future-is-not-equal ((x dynamic-futurep) (y dynamic-futurep))
  :returns (b bitp)
  (values-b-not (dynamic-future-is-equal x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Future and Argument.

; snarkVM circuit/program/src/data/future/to_bits.rs: Future::write_bits_le / write_bits_be,
; and circuit/program/src/data/future/argument.rs: Argument::write_bits_le / write_bits_be.
(defines values-future-to-bits
  :flag-local nil

  (define values-future-to-bits ((f futurep) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (future-count f)
    (b* ((pid-bits (if bigp
                       (program-id-to-bits-be (future->program-id f))
                     (program-id-to-bits-le (future->program-id f))))
         (fname-bits (values-identifier-to-bits (future->function-name f) bigp))
         (args (future->arguments f)))
      (append (values-uint-to-bits (len pid-bits) 16 bigp)
              pid-bits
              (values-uint-to-bits (len fname-bits) 16 bigp)
              fname-bits
              (values-uint-to-bits (len args) 8 bigp)
              (values-arguments-to-bits args bigp))))

  (define values-argument-to-bits ((arg argumentp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (argument-count arg)
    (argument-case
     arg
     :plaintext (cons 0 (values-plaintext-to-bits arg.get bigp))
     :future (cons 1 (values-future-to-bits arg.get bigp))
     :dynamic-future (cons 1 (append (repeat 12 0)
                                     (values-dynamic-future-to-bits arg.get bigp)))))

  (define values-arguments-to-bits ((args argument-listp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (argument-list-count args)
    (b* (((when (endp args)) nil)
         (arg-bits (values-argument-to-bits (car args) bigp))
         (n (len arg-bits)))
      (append (if (<= n 65535)
                  (values-uint-to-bits n 16 bigp)
                (values-uint-to-bits n 32 bigp))
              arg-bits
              (values-arguments-to-bits (cdr args) bigp))))

  :prepwork ((local (in-theory (enable bitp)))
             (local (defrule bit-listp-of-repeat-0
                      (bit-listp (repeat n 0))
                      :enable (repeat bit-listp)))))

; snarkVM circuit/program/src/data/future/to_bits.rs: Future::write_bits_le.
(define future-to-bits-le ((f futurep))
  :returns (bits bit-listp)
  (values-future-to-bits f nil))

; snarkVM circuit/program/src/data/future/to_bits.rs: Future::write_bits_be.
(define future-to-bits-be ((f futurep))
  :returns (bits bit-listp)
  (values-future-to-bits f t))

; snarkVM circuit/program/src/data/future/to_fields.rs: Future::to_fields.
(define future-to-fields ((f futurep))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded (append (future-to-bits-le f) (list 1))))

; snarkVM circuit/program/src/data/future/argument.rs: Argument::write_bits_le.
(define argument-to-bits-le ((arg argumentp))
  :returns (bits bit-listp)
  (values-argument-to-bits arg nil))

; snarkVM circuit/program/src/data/future/argument.rs: Argument::write_bits_be.
(define argument-to-bits-be ((arg argumentp))
  :returns (bits bit-listp)
  (values-argument-to-bits arg t))

; snarkVM circuit/program/src/data/future/equal.rs: Future::is_equal
; (false if the numbers of arguments differ; else program ID, function name,
; and arguments pairwise), and circuit/program/src/data/future/argument.rs: Argument::is_equal.
(defines values-future-equalp
  :flag-local nil

  (define values-future-equalp ((x futurep) (y futurep))
    :returns (yes/no booleanp)
    :measure (future-count x)
    (and (equal (len (future->arguments x)) (len (future->arguments y)))
         (equal (program-id-is-equal (future->program-id x) (future->program-id y)) 1)
         (equal (identifier-is-equal (future->function-name x) (future->function-name y)) 1)
         (values-arguments-equalp (future->arguments x) (future->arguments y))))

  (define values-argument-equalp ((x argumentp) (y argumentp))
    :returns (yes/no booleanp)
    :measure (argument-count x)
    (argument-case
     x
     :plaintext (and (argument-case y :plaintext)
                     (values-plaintext-equalp x.get (argument-plaintext->get y)))
     :future (and (argument-case y :future)
                  (values-future-equalp x.get (argument-future->get y)))
     :dynamic-future (and (argument-case y :dynamic-future)
                          (equal (dynamic-future-is-equal
                                  x.get (argument-dynamic-future->get y))
                                 1))))

  (define values-arguments-equalp ((xs argument-listp) (ys argument-listp))
    :returns (yes/no booleanp)
    :measure (argument-list-count xs)
    (or (endp xs)
        (endp ys)
        (and (values-argument-equalp (car xs) (car ys))
             (values-arguments-equalp (cdr xs) (cdr ys))))))

; snarkVM circuit/program/src/data/future/equal.rs: Future::is_equal.
(define future-is-equal ((x futurep) (y futurep))
  :returns (b bitp)
  (values-bool-to-bit (values-future-equalp x y)))

; snarkVM circuit/program/src/data/future/equal.rs: Future::is_not_equal (computed dually).
(define future-is-not-equal ((x futurep) (y futurep))
  :returns (b bitp)
  (values-bool-to-bit (not (values-future-equalp x y))))

; snarkVM circuit/program/src/data/future/argument.rs: Argument::is_equal.
(define argument-is-equal ((x argumentp) (y argumentp))
  :returns (b bitp)
  (values-bool-to-bit (values-argument-equalp x y)))

; snarkVM circuit/program/src/data/future/argument.rs: Argument::is_not_equal.
(define argument-is-not-equal ((x argumentp) (y argumentp))
  :returns (b bitp)
  (values-bool-to-bit (not (values-argument-equalp x y))))

; snarkVM circuit/program/src/data/future/mod.rs: Future::new (Inject; ProgramID::constant,
; Identifier::constant, Argument::new on the arguments),
; and circuit/program/src/data/future/argument.rs: Argument::new (Inject).
(defines future-new
  :flag-local nil
  :verify-guards nil

  (define future-new ((f futurep))
    :returns (f1 future-resultp)
    :measure (future-count f)
    (b* (((fty::ok args) (values-arguments-new (future->arguments f))))
      (change-future f :arguments args)))

  (define argument-new ((arg argumentp))
    :returns (arg1 argument-resultp)
    :measure (argument-count arg)
    (argument-case
     arg
     :plaintext (b* (((fty::ok pt) (plaintext-new arg.get)))
                  (argument-plaintext pt))
     :future (b* (((fty::ok f) (future-new arg.get)))
               (argument-future f))
     :dynamic-future (argument-dynamic-future (dynamic-future-new arg.get))))

  (define values-arguments-new ((args argument-listp))
    :returns (args1 argument-list-resultp)
    :measure (argument-list-count args)
    (b* (((when (endp args)) nil)
         ((fty::ok arg) (argument-new (car args)))
         ((fty::ok rest) (values-arguments-new (cdr args))))
      (cons arg rest))))

(verify-guards future-new)

(define values-argument-to-value ((arg argumentp))
  :returns (v valuep)
  (argument-case
   arg
   :plaintext (value-plaintext arg.get)
   :future (value-future arg.get)
   :dynamic-future (value-dynamic-future arg.get)))

(define values-future-find-aux ((ref argumentp) (path access-listp))
  :returns (v value-resultp)
  :measure (len path)
  (b* (((when (endp path)) (values-argument-to-value ref))
       (access (car path)))
    (cond
     ((and (argument-case ref :plaintext)
           (plaintext-case (argument-plaintext->get ref) :struct)
           (acl2::access-case access :member))
      (b* ((member (values-plaintext-members-lookup
                    (acl2::access-member->name access)
                    (plaintext-struct->members (argument-plaintext->get ref))))
           ((unless member) (spec-error)))
        (values-future-find-aux (argument-plaintext member) (cdr path))))
     ((and (argument-case ref :plaintext)
           (plaintext-case (argument-plaintext->get ref) :array)
           (acl2::access-case access :index))
      (b* ((elements (plaintext-array->elements (argument-plaintext->get ref)))
           (index (acl2::access-index->index access))
           ((unless (< index (len elements))) (spec-error)))
        (values-future-find-aux (argument-plaintext (nth index elements)) (cdr path))))
     ((and (argument-case ref :future)
           (acl2::access-case access :index))
      (b* ((args (future->arguments (argument-future->get ref)))
           (index (acl2::access-index->index access))
           ((unless (< index (len args))) (spec-error)))
        (values-future-find-aux (nth index args) (cdr path))))
     (t (spec-error)))))

; snarkVM circuit/program/src/data/future/find.rs: Future::find
; (the indices must be constants; their values are modeled).
(define future-find ((f futurep) (path access-listp))
  :returns (v value-resultp)
  (if (endp path)
      (spec-error)
    (values-future-find-aux (argument-future f) path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record<Plaintext> helpers (snarkVM circuit/program/src/data/record).

(define values-owner-address ((owner ownerp))
  :returns (address groupp)
  (owner-case owner
              :public owner.address
              :private owner.address))

(define values-record-data-to-bits ((data record-entry-listp) (bigp booleanp))
  :returns (bits bit-listp)
  (b* (((when (endp data)) nil)
       (name (record-entry->name (car data)))
       (entry (record-entry->entry (car data))))
    (append (values-identifier-to-bits name bigp)
            (if bigp (entry-to-bits-be entry) (entry-to-bits-le entry))
            (values-record-data-to-bits (cdr data) bigp))))

; snarkVM circuit/program/src/data/record/to_bits.rs: Record<Plaintext>::write_bits_le / write_bits_be.
(define values-record-to-bits ((r recordp) (bigp booleanp))
  :returns (bits bit-list-resultp)
  (b* ((owner (record->owner r))
       (data-bits (values-record-data-to-bits (record->data r) bigp))
       ((unless (< (len data-bits) (expt 2 31))) (spec-error))
       (hiding (if (equal (record->version r) 0) 0 1))
       (owner-bits (cons (if (owner-case owner :private) 1 0)
                         (values-group-to-bits (values-owner-address owner) bigp))))
    (append owner-bits
            (if bigp
                (cons hiding (cdr (values-int-to-bits-be (len data-bits) 32)))
              (append (take 31 (values-int-to-bits-le (len data-bits) 32))
                      (list hiding)))
            data-bits
            (values-group-to-bits (record->nonce r) bigp)
            (values-uint-to-bits (record->version r) 8 bigp))))

; snarkVM circuit/program/src/data/record/to_fields.rs: Record<Plaintext>::to_fields.
(define values-record-to-fields ((r recordp))
  :returns (fs values-field-list-resultp)
  (b* (((fty::ok bits) (values-record-to-bits r nil)))
    (values-pack-bits-bounded (append bits (list 1)))))

(define values-record-data-lookup ((name identifierp) (data record-entry-listp))
  :returns (entry? (implies entry? (entryp entry?)))
  (b* (((when (endp data)) nil))
    (if (equal (identifier->field (record-entry->name (car data)))
               (identifier->field name))
        (record-entry->entry (car data))
      (values-record-data-lookup name (cdr data)))))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::to_entry.
(define values-owner-to-entry ((owner ownerp))
  :returns (e entryp)
  (owner-case owner
              :public (entry-public (plaintext-literal (literal-address owner.address)))
              :private (entry-private (plaintext-literal (literal-address owner.address)))))

; snarkVM circuit/program/src/data/record/find.rs: Record<Plaintext>::find.
(define values-record-find ((r recordp) (path access-listp))
  :returns (e entry-resultp)
  (b* (((when (values-access-is-owner-p path))
        (values-owner-to-entry (record->owner r)))
       ((when (endp path)) (spec-error))
       (first (car path))
       ((unless (acl2::access-case first :member)) (spec-error))
       (entry (values-record-data-lookup (acl2::access-member->name first) (record->data r)))
       ((unless entry) (spec-error)))
    (if (endp (cdr path))
        entry
      (entry-find entry (cdr path)))))

(define values-record-data-equalp ((xs record-entry-listp) (ys record-entry-listp))
  :returns (yes/no booleanp)
  (or (endp xs)
      (endp ys)
      (and (equal (identifier->field (record-entry->name (car xs)))
                  (identifier->field (record-entry->name (car ys))))
           (values-entry-equalp (record-entry->entry (car xs))
                                (record-entry->entry (car ys)))
           (values-record-data-equalp (cdr xs) (cdr ys)))))

; snarkVM circuit/program/src/data/record/equal.rs: Record::is_equal
; (false if the data sizes differ; else owner, data pairwise, nonce, version).
(define values-record-equalp ((x recordp) (y recordp))
  :returns (yes/no booleanp)
  (and (equal (len (record->data x)) (len (record->data y)))
       (equal (owner-kind (record->owner x)) (owner-kind (record->owner y)))
       (equal (values-owner-address (record->owner x))
              (values-owner-address (record->owner y)))
       (values-record-data-equalp (record->data x) (record->data y))
       (equal (record->nonce x) (record->nonce y))
       (equal (record->version x) (record->version y))))

(define values-record-data-insert ((name identifierp) (entry entryp) (data record-entry-listp))
  :returns (data1 record-entry-listp)
  :short "IndexMap insertion, as in @(tsee values-plaintext-members-insert)."
  (b* (((when (endp data))
        (list (make-record-entry :name name :entry entry))))
    (if (equal (identifier->field (record-entry->name (car data)))
               (identifier->field name))
        (cons (change-record-entry (car data) :entry entry)
              (record-entry-list-fix (cdr data)))
      (cons (record-entry-fix (car data))
            (values-record-data-insert name entry (cdr data))))))

(define values-record-data-new ((data record-entry-listp) (acc record-entry-listp))
  :returns (data1 record-entry-list-resultp)
  (b* (((when (endp data)) (record-entry-list-fix acc))
       ((fty::ok entry) (entry-new (record-entry->entry (car data))))
       (acc (values-record-data-insert (record-entry->name (car data)) entry acc)))
    (values-record-data-new (cdr data) acc)))

; snarkVM circuit/program/src/data/record/mod.rs: Record<Plaintext>::new (Inject;
; Owner::new, Identifier::constant and Entry::new on the data, Group::new, U8::new).
(define values-record-new ((r recordp))
  :returns (r1 record-resultp)
  (b* (((fty::ok data) (values-record-data-new (record->data r) nil)))
    (change-record r :data data)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; DynamicRecord.

; snarkVM circuit/program/src/data/dynamic/record/mod.rs: DynamicRecord::new (Inject;
; Address::new, Field::new, Group::new, U8::new).
(define dynamic-record-new ((dr dynamic-recordp))
  :returns (dr1 dynamic-recordp)
  (dynamic-record-fix dr))

(define values-dynamic-record-to-bits ((dr dynamic-recordp) (bigp booleanp))
  :returns (bits bit-listp)
  (append (values-group-to-bits (dynamic-record->owner dr) bigp)
          (values-field-to-bits (dynamic-record->root dr) bigp)
          (values-group-to-bits (dynamic-record->nonce dr) bigp)
          (values-uint-to-bits (dynamic-record->version dr) 8 bigp)))

; snarkVM circuit/program/src/data/dynamic/record/to_bits.rs: DynamicRecord::write_bits_le.
(define dynamic-record-to-bits-le ((dr dynamic-recordp))
  :returns (bits bit-listp)
  (values-dynamic-record-to-bits dr nil))

; snarkVM circuit/program/src/data/dynamic/record/to_bits.rs: DynamicRecord::write_bits_be.
(define dynamic-record-to-bits-be ((dr dynamic-recordp))
  :returns (bits bit-listp)
  (values-dynamic-record-to-bits dr t))

; snarkVM circuit/program/src/data/dynamic/record/to_fields.rs: DynamicRecord::to_fields.
(define dynamic-record-to-fields ((dr dynamic-recordp))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded (append (dynamic-record-to-bits-le dr) (list 1))))

; snarkVM circuit/program/src/data/dynamic/record/equal.rs: DynamicRecord::is_equal.
(define dynamic-record-is-equal ((x dynamic-recordp) (y dynamic-recordp))
  :returns (b bitp)
  (values-bool-to-bit (equal (dynamic-record-fix x) (dynamic-record-fix y))))

; snarkVM circuit/program/src/data/dynamic/record/equal.rs: DynamicRecord::is_not_equal.
(define dynamic-record-is-not-equal ((x dynamic-recordp) (y dynamic-recordp))
  :returns (b bitp)
  (values-b-not (dynamic-record-is-equal x y)))

; snarkVM circuit/program/src/data/dynamic/record/find.rs: DynamicRecord::find
; (only the path ["owner"], giving the owner address as a plaintext value).
(define dynamic-record-find ((dr dynamic-recordp) (path access-listp))
  :returns (v value-resultp)
  (if (values-access-is-owner-p path)
      (value-plaintext (plaintext-literal (literal-address (dynamic-record->owner dr))))
    (spec-error)))

;; Record data Merkle tree (snarkVM circuit/collections/src/merkle_tree/mod.rs: MerkleTree::new,
;; with DEPTH = RECORD_DATA_TREE_DEPTH = 5, the leaf hasher Poseidon8 and the path hasher
;; Poseidon2 set up with the domains "DynamicRecordLeafHasher" and "DynamicRecordPathHasher").

; snarkVM circuit/collections/src/merkle_tree/helpers/leaf_hash.rs: Poseidon::hash_leaf.
(define values-dynamic-record-leaf-hash ((leaf values-field-listp))
  :returns (h fieldp)
  (car (poseidon-hash-many "DynamicRecordLeafHasher"
                           (cons 0 (values-field-list-fix leaf))
                           1)))

; snarkVM circuit/collections/src/merkle_tree/helpers/path_hash.rs: Poseidon::hash_children.
(define values-dynamic-record-path-hash ((left fieldp) (right fieldp))
  :returns (h fieldp)
  (car (poseidon-hash-many "DynamicRecordPathHasher"
                           (list 1 (values-field-fix left) (values-field-fix right))
                           1)))

(in-theory (disable (:e values-dynamic-record-leaf-hash)
                    (:e values-dynamic-record-path-hash)))

(fty::deflist values-field-list-list
  :elt-type values-field-list
  :true-listp t
  :pred values-field-list-listp)

(fty::defresult values-field-list-list-result
  :ok values-field-list-list
  :pred values-field-list-list-resultp)

(in-theory (enable values-field-list-listp-when-result-not-error
                   not-reserrp-when-values-field-list-listp))

(define values-merkle-leaf-hashes ((leaves values-field-list-listp))
  :returns (hashes values-field-listp)
  (if (endp leaves)
      nil
    (cons (values-dynamic-record-leaf-hash (values-field-list-fix (car leaves)))
          (values-merkle-leaf-hashes (cdr leaves)))))

(define values-merkle-level ((hashes values-field-listp))
  :returns (parents values-field-listp)
  :short "Hash consecutive pairs of nodes (of an even-length level)."
  (if (or (endp hashes) (endp (cdr hashes)))
      nil
    (cons (values-dynamic-record-path-hash (car hashes) (cadr hashes))
          (values-merkle-level (cddr hashes)))))

(define values-merkle-root-of-levels ((hashes values-field-listp) (depth natp))
  :returns (root fieldp)
  :short "Root of the full binary tree of depth @('depth') with the given leaves."
  (if (zp depth)
      (if (consp hashes) (values-field-fix (car hashes)) 0)
    (values-merkle-root-of-levels (values-merkle-level hashes) (1- depth)))
  :prepwork ((local (in-theory (enable values-fieldp-of-0)))))

(define values-merkle-pad-root ((root fieldp) (empty fieldp) (n natp))
  :returns (root1 fieldp)
  (if (zp n)
      (values-field-fix root)
    (values-merkle-pad-root (values-dynamic-record-path-hash root empty) empty (1- n))))

; log2 of Rust usize::checked_next_power_of_two(n) (1 for n = 0), for n <= 32.
(define values-merkle-tree-depth ((n natp))
  :returns (d natp)
  (cond ((<= (lnfix n) 1) 0)
        ((<= (lnfix n) 2) 1)
        ((<= (lnfix n) 4) 2)
        ((<= (lnfix n) 8) 3)
        ((<= (lnfix n) 16) 4)
        (t 5))
  ///
  (defret values-merkle-tree-depth-upper-bound
    (<= d 5)
    :rule-classes :linear)
  (defret values-merkle-tree-depth-covers-leaves
    (implies (<= (nfix n) 32)
             (<= (nfix n) (expt 2 d)))
    :rule-classes ((:linear :trigger-terms ((expt 2 (values-merkle-tree-depth n)))))))

; snarkVM circuit/collections/src/merkle_tree/mod.rs: MerkleTree::new (the root).
; The tree is the full binary tree over the leaf hashes padded with
; empty_hash = hash_children(0, 0) to the next power of two (the circuit
; assigns hash_children(empty_hash, empty_hash) directly to the nodes without
; leaves, which is the same value); its root is then hashed with empty_hash
; up to depth 5.  More than 32 leaves exceed the depth: error.
(define values-dynamic-record-merkle-root ((leaves values-field-list-listp))
  :returns (root values-field-resultp)
  (b* ((n (len leaves))
       ((unless (<= n 32)) (spec-error))
       (depth (values-merkle-tree-depth n))
       (empty (values-dynamic-record-path-hash 0 0))
       (hashes (append (values-merkle-leaf-hashes leaves)
                       (repeat (- (expt 2 depth) n) empty)))
       (root (values-merkle-root-of-levels hashes depth)))
    (values-merkle-pad-root root empty (- 5 depth)))
  :prepwork ((local (in-theory (enable values-fieldp-of-0)))))

(define values-dynamic-record-leaves ((data record-entry-listp))
  :returns (leaves values-field-list-list-resultp)
  :short "One leaf per entry: the identifier field followed by the entry fields."
  (b* (((when (endp data)) nil)
       ((fty::ok fields) (entry-to-fields (record-entry->entry (car data))))
       ((fty::ok rest) (values-dynamic-record-leaves (cdr data))))
    (cons (cons (identifier->field (record-entry->name (car data))) fields)
          rest)))

; snarkVM circuit/program/src/data/dynamic/record/mod.rs: DynamicRecord::merkleize_data.
; The result is the root of the Merkle tree (the only part of the tree used
; by from_record); the other nodes of the tree are not modeled.
(define dynamic-record-merkleize-data ((data record-entry-listp))
  :returns (root values-field-resultp)
  (b* (((fty::ok leaves) (values-dynamic-record-leaves data)))
    (values-dynamic-record-merkle-root leaves)))

; snarkVM circuit/program/src/data/dynamic/record/mod.rs: DynamicRecord::from_record.
(define dynamic-record-from-record ((r recordp))
  :returns (dr dynamic-record-resultp)
  (b* (((fty::ok root) (dynamic-record-merkleize-data (record->data r))))
    (make-dynamic-record :owner (values-owner-address (record->owner r))
                         :root root
                         :nonce (record->nonce r)
                         :version (record->version r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Value.

; snarkVM circuit/program/src/data/value/mod.rs: Value::new (Inject).
(define value-new ((v valuep))
  :returns (v1 value-resultp)
  (value-case
   v
   :plaintext (b* (((fty::ok pt) (plaintext-new v.get))) (value-plaintext pt))
   :record (b* (((fty::ok r) (values-record-new v.get))) (value-record r))
   :future (b* (((fty::ok f) (future-new v.get))) (value-future f))
   :dynamic-record (value-dynamic-record (dynamic-record-new v.get))
   :dynamic-future (value-dynamic-future (dynamic-future-new v.get))))

(define values-value-to-bits ((v valuep) (bigp booleanp))
  :returns (bits bit-list-resultp)
  (value-case
   v
   :plaintext (values-plaintext-to-bits v.get bigp)
   :record (values-record-to-bits v.get bigp)
   :future (values-future-to-bits v.get bigp)
   :dynamic-record (values-dynamic-record-to-bits v.get bigp)
   :dynamic-future (values-dynamic-future-to-bits v.get bigp)))

; snarkVM circuit/program/src/data/value/to_bits.rs: Value::write_bits_le.
(define value-to-bits-le ((v valuep))
  :returns (bits bit-list-resultp)
  (values-value-to-bits v nil))

; snarkVM circuit/program/src/data/value/to_bits.rs: Value::write_bits_be.
(define value-to-bits-be ((v valuep))
  :returns (bits bit-list-resultp)
  (values-value-to-bits v t))

(define values-value-to-bits-raw ((v valuep) (bigp booleanp))
  :returns (bits bit-list-resultp)
  (value-case
   v
   :plaintext (values-plaintext-to-bits-raw v.get bigp)
   :otherwise (values-value-to-bits v bigp)))

; snarkVM circuit/program/src/data/value/to_bits_raw.rs: Value::write_bits_raw_le.
(define value-to-bits-raw-le ((v valuep))
  :returns (bits bit-list-resultp)
  (values-value-to-bits-raw v nil))

; snarkVM circuit/program/src/data/value/to_bits_raw.rs: Value::write_bits_raw_be.
(define value-to-bits-raw-be ((v valuep))
  :returns (bits bit-list-resultp)
  (values-value-to-bits-raw v t))

; snarkVM circuit/program/src/data/value/to_fields.rs: Value::to_fields.
(define value-to-fields ((v valuep))
  :returns (fs values-field-list-resultp)
  (value-case
   v
   :plaintext (plaintext-to-fields v.get)
   :record (values-record-to-fields v.get)
   :future (future-to-fields v.get)
   :dynamic-record (dynamic-record-to-fields v.get)
   :dynamic-future (dynamic-future-to-fields v.get)))

; snarkVM circuit/program/src/data/value/to_fields_raw.rs: Value::to_fields_raw.
(define value-to-fields-raw ((v valuep))
  :returns (fs values-field-list-resultp)
  (value-case
   v
   :plaintext (plaintext-to-fields-raw v.get)
   :otherwise (value-to-fields v)))

(define values-value-equalp ((x valuep) (y valuep))
  :returns (yes/no booleanp)
  (value-case
   x
   :plaintext (and (value-case y :plaintext)
                   (values-plaintext-equalp x.get (value-plaintext->get y)))
   :record (and (value-case y :record)
                (values-record-equalp x.get (value-record->get y)))
   :future (and (value-case y :future)
                (values-future-equalp x.get (value-future->get y)))
   :dynamic-record (and (value-case y :dynamic-record)
                        (equal (dynamic-record-is-equal x.get (value-dynamic-record->get y)) 1))
   :dynamic-future (and (value-case y :dynamic-future)
                        (equal (dynamic-future-is-equal x.get (value-dynamic-future->get y)) 1))))

; snarkVM circuit/program/src/data/value/equal.rs: Value::is_equal.
(define value-is-equal ((x valuep) (y valuep))
  :returns (b bitp)
  (values-bool-to-bit (values-value-equalp x y)))

; snarkVM circuit/program/src/data/value/equal.rs: Value::is_not_equal.
(define value-is-not-equal ((x valuep) (y valuep))
  :returns (b bitp)
  (values-bool-to-bit (not (values-value-equalp x y))))

; snarkVM circuit/program/src/data/value/find.rs: Value::find.
(define value-find ((v valuep) (path access-listp))
  :returns (v1 value-resultp)
  (value-case
   v
   :plaintext (b* (((fty::ok pt) (plaintext-find v.get path))) (value-plaintext pt))
   :record (b* (((fty::ok e) (values-record-find v.get path)))
             (value-plaintext (values-entry-plaintext e)))
   :future (future-find v.get path)
   :dynamic-record (dynamic-record-find v.get path)
   :dynamic-future (spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State-path leaves.

(define values-header-leaf-to-bits ((leaf header-leafp) (bigp booleanp))
  :returns (bits bit-listp)
  (append (values-uint-to-bits (header-leaf->index leaf) 8 bigp)
          (values-field-to-bits (header-leaf->id leaf) bigp)))

; snarkVM circuit/program/src/state_path/helpers/header_leaf.rs: HeaderLeaf::write_bits_le.
(define header-leaf-to-bits-le ((leaf header-leafp))
  :returns (bits bit-listp)
  (values-header-leaf-to-bits leaf nil))

; snarkVM circuit/program/src/state_path/helpers/header_leaf.rs: HeaderLeaf::write_bits_be.
(define header-leaf-to-bits-be ((leaf header-leafp))
  :returns (bits bit-listp)
  (values-header-leaf-to-bits leaf t))

(define values-transaction-leaf-to-bits ((leaf transaction-leafp) (bigp booleanp))
  :returns (bits bit-listp)
  (append (values-uint-to-bits (transaction-leaf->variant leaf) 8 bigp)
          (values-uint-to-bits (transaction-leaf->index leaf) 16 bigp)
          (values-field-to-bits (transaction-leaf->id leaf) bigp)))

; snarkVM circuit/program/src/state_path/helpers/transaction_leaf.rs: TransactionLeaf::write_bits_le.
(define transaction-leaf-to-bits-le ((leaf transaction-leafp))
  :returns (bits bit-listp)
  (values-transaction-leaf-to-bits leaf nil))

; snarkVM circuit/program/src/state_path/helpers/transaction_leaf.rs: TransactionLeaf::write_bits_be.
(define transaction-leaf-to-bits-be ((leaf transaction-leafp))
  :returns (bits bit-listp)
  (values-transaction-leaf-to-bits leaf t))

(define values-transition-leaf-to-bits ((leaf transition-leafp) (bigp booleanp))
  :returns (bits bit-listp)
  (append (values-uint-to-bits (transition-leaf->version leaf) 8 bigp)
          (values-uint-to-bits (transition-leaf->index leaf) 8 bigp)
          (values-uint-to-bits (transition-leaf->variant leaf) 8 bigp)
          (values-field-to-bits (transition-leaf->id leaf) bigp)))

; snarkVM circuit/program/src/state_path/helpers/transition_leaf.rs: TransitionLeaf::write_bits_le.
(define transition-leaf-to-bits-le ((leaf transition-leafp))
  :returns (bits bit-listp)
  (values-transition-leaf-to-bits leaf nil))

; snarkVM circuit/program/src/state_path/helpers/transition_leaf.rs: TransitionLeaf::write_bits_be.
(define transition-leaf-to-bits-be ((leaf transition-leafp))
  :returns (bits bit-listp)
  (values-transition-leaf-to-bits leaf t))
