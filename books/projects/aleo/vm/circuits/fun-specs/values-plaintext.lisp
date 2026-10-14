; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FUN-SPECs of Plaintext and Entry<Plaintext> of the circuit program crate
; (snarkVM circuit/program/src/data/plaintext, data/record/entry).
;
; Not modeled: the bit caches (OnceCell) of circuit plaintexts.
; The specs of to_bits are those of plaintexts with empty caches.
; snarkVM fills the cache of a plaintext built by from_bits with the input
; bits, including any trailing bits beyond the parsed ones, and uses one
; cache for both the little-endian and the big-endian bits; on such
; plaintexts, a later to_bits returns the cached bits instead.

(in-package "ALEOVM")

(include-book "values-literal")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(fty::defresult values-nat-result
  :ok nat
  :pred values-nat-resultp)

(in-theory (enable natp-when-result-not-error
                   not-reserrp-when-natp))

(local (in-theory (enable spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers.

(define values-uint-to-bits ((x integerp) (n natp) (bigp booleanp))
  :returns (bits bit-listp)
  :short "Bits of the unsigned integer @('x mod 2^n'), little- or big-endian
          (Rust @('UN::new(x as uN).write_bits_le/be'))."
  (if bigp
      (values-int-to-bits-be x n)
    (values-int-to-bits-le x n))
  ///
  (defret len-of-values-uint-to-bits
    (equal (len bits) (nfix n))
    :hints (("Goal" :in-theory (disable acl2::|(equal 0 (len x))|
                                        acl2::|(equal (if a b c) x)|)))))

(define values-bits-to-nat ((bits bit-listp) (bigp booleanp))
  :returns (n natp :rule-classes :type-prescription)
  :short "Rust @('UN::from_bits_le/be') on exactly N bits."
  (lebits=>nat (if bigp (rev bits) bits))
  ///
  (defret values-bits-to-nat-upper-bound
    (< n (expt 2 (len bits)))
    :rule-classes :linear)
  (defret values-ubyte8p-of-bits-to-nat-of-take
    (implies (and (bit-listp bits0) (<= 8 (len bits0)))
             (ubyte8p (values-bits-to-nat (take 8 bits0) bigp)))
    :hints (("Goal" :in-theory (e/d (ubyte8p unsigned-byte-p)
                                    (values-bits-to-nat))
             :use (:instance values-bits-to-nat-upper-bound
                   (bits (take 8 bits0)))))))

(define values-identifier-to-bits ((id identifierp) (bigp booleanp))
  :returns (bits bit-listp)
  (if bigp
      (identifier-to-bits-be id)
    (identifier-to-bits-le id)))

; snarkVM: IndexMap::insert (an existing key, compared by its field, keeps its
; position and gets the new value; a new key goes at the end).
(define values-plaintext-members-insert ((name identifierp)
                                         (value plaintextp)
                                         (members plaintext-member-listp))
  :returns (members1 plaintext-member-listp)
  (b* (((when (endp members))
        (list (make-plaintext-member :name name :value value)))
       (member (car members)))
    (if (equal (identifier->field (plaintext-member->name member))
               (identifier->field name))
        (cons (change-plaintext-member member :value value)
              (plaintext-member-list-fix (cdr members)))
      (cons (plaintext-member-fix member)
            (values-plaintext-members-insert name value (cdr members))))))

; snarkVM: IndexMap::get (by field equality of the identifiers).
(define values-plaintext-members-lookup ((name identifierp)
                                         (members plaintext-member-listp))
  :returns (value? (implies value? (plaintextp value?)))
  (b* (((when (endp members)) nil)
       (member (car members)))
    (if (equal (identifier->field (plaintext-member->name member))
               (identifier->field name))
        (plaintext-member->value member)
      (values-plaintext-members-lookup name (cdr members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To bits.

; snarkVM circuit/program/src/data/plaintext/to_bits.rs: Plaintext::write_bits_le / write_bits_be
; (prefix bits [0,0] literal, [0,1] struct, [1,0] array, written as is in both orders).
(defines values-plaintext-to-bits
  :flag-local nil

  (define values-plaintext-to-bits ((pt plaintextp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-count pt)
    (plaintext-case
     pt
     :literal (append (list 0 0)
                      (values-uint-to-bits (literal-variant pt.get) 8 bigp)
                      (values-uint-to-bits (literal-size-in-bits pt.get) 16 bigp)
                      (if bigp
                          (literal-to-bits-be pt.get)
                        (literal-to-bits-le pt.get)))
     :struct (append (list 0 1)
                     (values-uint-to-bits (len pt.members) 8 bigp)
                     (values-plaintext-members-to-bits pt.members bigp))
     :array (append (list 1 0)
                    (values-uint-to-bits (len pt.elements) 32 bigp)
                    (values-plaintext-elements-to-bits pt.elements bigp))))

  (define values-plaintext-members-to-bits ((members plaintext-member-listp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-member-list-count members)
    (b* (((when (endp members)) nil)
         (name (plaintext-member->name (car members)))
         (value-bits (values-plaintext-to-bits (plaintext-member->value (car members)) bigp)))
      (append (values-uint-to-bits (identifier-size-in-bits name) 8 bigp)
              (values-identifier-to-bits name bigp)
              (values-uint-to-bits (len value-bits) 16 bigp)
              value-bits
              (values-plaintext-members-to-bits (cdr members) bigp))))

  (define values-plaintext-elements-to-bits ((elements plaintext-listp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-list-count elements)
    (b* (((when (endp elements)) nil)
         (value-bits (values-plaintext-to-bits (car elements) bigp)))
      (append (values-uint-to-bits (len value-bits) 16 bigp)
              value-bits
              (values-plaintext-elements-to-bits (cdr elements) bigp))))

  :prepwork ((local (in-theory (enable bitp)))))

; snarkVM circuit/program/src/data/plaintext/to_bits.rs: Plaintext::write_bits_le.
(define plaintext-to-bits-le ((pt plaintextp))
  :returns (bits bit-listp)
  (values-plaintext-to-bits pt nil))

; snarkVM circuit/program/src/data/plaintext/to_bits.rs: Plaintext::write_bits_be.
(define plaintext-to-bits-be ((pt plaintextp))
  :returns (bits bit-listp)
  (values-plaintext-to-bits pt t))

; snarkVM circuit/program/src/data/plaintext/to_bits_raw.rs: Plaintext::write_bits_raw_le / write_bits_raw_be
; (only the literal bits, concatenated).
(defines values-plaintext-to-bits-raw
  :flag-local nil

  (define values-plaintext-to-bits-raw ((pt plaintextp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-count pt)
    (plaintext-case
     pt
     :literal (if bigp
                  (literal-to-bits-be pt.get)
                (literal-to-bits-le pt.get))
     :struct (values-plaintext-members-to-bits-raw pt.members bigp)
     :array (values-plaintext-elements-to-bits-raw pt.elements bigp)))

  (define values-plaintext-members-to-bits-raw ((members plaintext-member-listp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-member-list-count members)
    (if (endp members)
        nil
      (append (values-plaintext-to-bits-raw (plaintext-member->value (car members)) bigp)
              (values-plaintext-members-to-bits-raw (cdr members) bigp))))

  (define values-plaintext-elements-to-bits-raw ((elements plaintext-listp) (bigp booleanp))
    :returns (bits bit-listp)
    :measure (plaintext-list-count elements)
    (if (endp elements)
        nil
      (append (values-plaintext-to-bits-raw (car elements) bigp)
              (values-plaintext-elements-to-bits-raw (cdr elements) bigp)))))

; snarkVM circuit/program/src/data/plaintext/to_bits_raw.rs: Plaintext::write_bits_raw_le.
(define plaintext-to-bits-raw-le ((pt plaintextp))
  :returns (bits bit-listp)
  (values-plaintext-to-bits-raw pt nil))

; snarkVM circuit/program/src/data/plaintext/to_bits_raw.rs: Plaintext::write_bits_raw_be.
(define plaintext-to-bits-raw-be ((pt plaintextp))
  :returns (bits bit-listp)
  (values-plaintext-to-bits-raw pt t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To fields.

; snarkVM: bits.chunks(252).map(Field::from_bits_le), halting beyond MAX_DATA_SIZE_IN_FIELDS fields.
(define values-pack-bits-bounded ((bits bit-listp))
  :returns (fs values-field-list-resultp)
  (b* ((fields (values-pack-bits bits)))
    (if (<= (len fields) (values-max-data-size-in-fields))
        fields
      (spec-error))))

; snarkVM circuit/program/src/data/plaintext/to_fields.rs: Plaintext::to_fields
; (the bits followed by the terminus bit 1).
(define plaintext-to-fields ((pt plaintextp))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded (append (plaintext-to-bits-le pt) (list 1))))

; snarkVM circuit/program/src/data/plaintext/to_fields_raw.rs: Plaintext::to_fields_raw.
(define plaintext-to-fields-raw ((pt plaintextp))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded (plaintext-to-bits-raw-le pt)))

; snarkVM circuit/program/src/data/plaintext/size_in_fields.rs: Plaintext::size_in_fields (Visibility).
(define plaintext-size-in-fields ((pt plaintextp))
  :returns (n values-nat-resultp)
  (b* ((num-bits (+ (len (plaintext-to-bits-le pt)) 1))
       (num-fields (ceiling num-bits 252)))
    (if (<= num-fields (values-max-data-size-in-fields))
        num-fields
      (spec-error))))

; snarkVM circuit/program/src/data/plaintext/num_randomizers.rs: Plaintext::num_randomizers.
(define plaintext-num-randomizers ((pt plaintextp))
  :returns (n values-nat-resultp)
  (plaintext-size-in-fields pt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From bits.

; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_le_internal / from_bits_be_internal
; (halts beyond depth MAX_DATA_DEPTH, on missing bits, and on prefix [1,1];
; trailing bits are ignored).
(defines values-plaintext-from-bits-internal
  :flag-local nil

  (define values-plaintext-from-bits-internal ((bits bit-listp) (depth natp) (bigp booleanp))
    :returns (pt plaintext-resultp)
    :measure (len bits)
    (b* (((when (> (lnfix depth) (values-max-data-depth))) (spec-error))
         (bits (bit-list-fix bits))
         ((unless (<= 2 (len bits))) (spec-error))
         (b1 (first bits))
         (b2 (second bits))
         (bits (nthcdr 2 bits)))
      (cond
       ((and (equal b1 0) (equal b2 0))
        (b* (((unless (<= 24 (len bits))) (spec-error))
             (variant (values-bits-to-nat (take 8 bits) bigp))
             (size (values-bits-to-nat (take 16 (nthcdr 8 bits)) bigp))
             (bits (nthcdr 24 bits))
             ((unless (<= size (len bits))) (spec-error))
             ((fty::ok lit) (values-literal-from-bits variant (take size bits) bigp)))
          (plaintext-literal lit)))
       ((and (equal b1 0) (equal b2 1))
        (b* (((unless (<= 8 (len bits))) (spec-error))
             (num-members (values-bits-to-nat (take 8 bits) bigp))
             ((fty::ok members)
              (values-plaintext-members-from-bits (nthcdr 8 bits)
                                                  num-members
                                                  (1+ (lnfix depth))
                                                  bigp
                                                  nil)))
          (plaintext-struct members)))
       ((and (equal b1 1) (equal b2 0))
        (b* (((unless (<= 32 (len bits))) (spec-error))
             (num-elements (values-bits-to-nat (take 32 bits) bigp))
             ((fty::ok elements)
              (values-plaintext-elements-from-bits (nthcdr 32 bits)
                                                   num-elements
                                                   (1+ (lnfix depth))
                                                   bigp)))
          (plaintext-array elements)))
       (t (spec-error)))))

  (define values-plaintext-members-from-bits ((bits bit-listp)
                                              (count natp)
                                              (depth natp)
                                              (bigp booleanp)
                                              (acc plaintext-member-listp))
    :returns (members plaintext-member-list-resultp)
    :measure (len bits)
    (b* (((when (zp count)) (plaintext-member-list-fix acc))
         (bits (bit-list-fix bits))
         ((unless (<= 8 (len bits))) (spec-error))
         (id-size (values-bits-to-nat (take 8 bits) bigp))
         (bits (nthcdr 8 bits))
         ((unless (<= id-size (len bits))) (spec-error))
         ((fty::ok name) (if bigp
                             (identifier-from-bits-be (take id-size bits))
                           (identifier-from-bits-le (take id-size bits))))
         (bits (nthcdr id-size bits))
         ((unless (<= 16 (len bits))) (spec-error))
         (member-size (values-bits-to-nat (take 16 bits) bigp))
         (bits (nthcdr 16 bits))
         ((unless (<= member-size (len bits))) (spec-error))
         ((fty::ok value)
          (values-plaintext-from-bits-internal (take member-size bits) depth bigp))
         (acc (values-plaintext-members-insert name value acc)))
      (values-plaintext-members-from-bits (nthcdr member-size bits)
                                          (1- count)
                                          depth
                                          bigp
                                          acc)))

  (define values-plaintext-elements-from-bits ((bits bit-listp)
                                               (count natp)
                                               (depth natp)
                                               (bigp booleanp))
    :returns (elements plaintext-list-resultp)
    :measure (len bits)
    (b* (((when (zp count)) nil)
         (bits (bit-list-fix bits))
         ((unless (<= 16 (len bits))) (spec-error))
         (element-size (values-bits-to-nat (take 16 bits) bigp))
         (bits (nthcdr 16 bits))
         ((unless (<= element-size (len bits))) (spec-error))
         ((fty::ok value)
          (values-plaintext-from-bits-internal (take element-size bits) depth bigp))
         ((fty::ok values)
          (values-plaintext-elements-from-bits (nthcdr element-size bits)
                                               (1- count)
                                               depth
                                               bigp)))
      (cons value values)))

  :verify-guards nil)

(verify-guards values-plaintext-from-bits-internal
  :hints (("Goal" :in-theory (e/d (bitp acl2::len-of-nthcdr)
                                  (acl2::open-small-nthcdr acl2::nthcdr-of-cdr)))))

; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_le_internal.
(define plaintext-from-bits-le-internal ((bits bit-listp) (depth natp))
  :returns (pt plaintext-resultp)
  (values-plaintext-from-bits-internal bits depth nil))

; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_be_internal.
(define plaintext-from-bits-be-internal ((bits bit-listp) (depth natp))
  :returns (pt plaintext-resultp)
  (values-plaintext-from-bits-internal bits depth t))

; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_le.
(define plaintext-from-bits-le ((bits bit-listp))
  :returns (pt plaintext-resultp)
  (plaintext-from-bits-le-internal bits 0))

; snarkVM circuit/program/src/data/plaintext/from_bits.rs: Plaintext::from_bits_be.
(define plaintext-from-bits-be ((bits bit-listp))
  :returns (pt plaintext-resultp)
  (plaintext-from-bits-be-internal bits 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; From fields.

(define values-fields-to-data-bits ((fields values-field-listp))
  :returns (bits bit-listp)
  :short "Rust @('fields.flat_map(|f| f.to_bits_le().take(252))')."
  (if (endp fields)
      nil
    (append (take 252 (values-field-to-bits-le (car fields)))
            (values-fields-to-data-bits (cdr fields)))))

(define values-strip-terminus ((rev-bits bit-listp))
  :returns (rev-bits1 bit-listp)
  :short "Drop the bits up to and including the last 1
          (given the bits in reverse order)."
  (cond ((endp rev-bits) nil)
        ((equal (bfix (car rev-bits)) 1) (bit-list-fix (cdr rev-bits)))
        (t (values-strip-terminus (cdr rev-bits)))))

; snarkVM circuit/program/src/data/plaintext/from_fields.rs: Plaintext::from_fields (FromFields).
(define plaintext-from-fields ((fields values-field-listp))
  :returns (pt plaintext-resultp)
  (b* (((when (> (len fields) (values-max-data-size-in-fields))) (spec-error))
       (bits (values-fields-to-data-bits fields))
       (bits (rev (values-strip-terminus (rev bits)))))
    (plaintext-from-bits-le bits)))

; snarkVM circuit/program/src/data/plaintext/from_fields.rs: Plaintext::from (From<Vec<Field>>, From<&[Field]>).
(define plaintext-from ((fields values-field-listp))
  :returns (pt plaintext-resultp)
  (plaintext-from-fields fields))

; snarkVM circuit/program/src/data/plaintext/mod.rs: Plaintext::from_bit_array.
(define plaintext-from-bit-array ((bits bit-listp) (length ubyte32p))
  :returns (pt plaintext-resultp)
  (if (equal (len bits) (acl2::ubyte32-fix length))
      (plaintext-array (values-bits-to-boolean-plaintexts bits))
    (spec-error))
  :prepwork
  ((define values-bits-to-boolean-plaintexts ((bits bit-listp))
     :returns (pts plaintext-listp)
     (if (endp bits)
         nil
       (cons (plaintext-literal (literal-boolean (car bits)))
             (values-bits-to-boolean-plaintexts (cdr bits))))
     :guard-hints (("Goal" :in-theory (enable bit-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injection.

; snarkVM circuit/program/src/data/plaintext/mod.rs: Plaintext::new (Inject;
; Literal::new on the literals, Identifier::constant on the member names,
; members collected into an IndexMap).
(defines plaintext-new
  :flag-local nil
  :verify-guards nil

  (define plaintext-new ((pt plaintextp))
    :returns (pt1 plaintext-resultp)
    :measure (plaintext-count pt)
    (plaintext-case
     pt
     :literal (b* (((fty::ok lit) (literal-new pt.get)))
                (plaintext-literal lit))
     :struct (b* (((fty::ok members) (values-plaintext-members-new pt.members nil)))
               (plaintext-struct members))
     :array (b* (((fty::ok elements) (values-plaintext-elements-new pt.elements)))
              (plaintext-array elements))))

  (define values-plaintext-members-new ((members plaintext-member-listp)
                                        (acc plaintext-member-listp))
    :returns (members1 plaintext-member-list-resultp)
    :measure (plaintext-member-list-count members)
    (b* (((when (endp members)) (plaintext-member-list-fix acc))
         ((fty::ok value) (plaintext-new (plaintext-member->value (car members))))
         (acc (values-plaintext-members-insert (plaintext-member->name (car members))
                                               value
                                               acc)))
      (values-plaintext-members-new (cdr members) acc)))

  (define values-plaintext-elements-new ((elements plaintext-listp))
    :returns (elements1 plaintext-list-resultp)
    :measure (plaintext-list-count elements)
    (b* (((when (endp elements)) nil)
         ((fty::ok value) (plaintext-new (car elements)))
         ((fty::ok values) (values-plaintext-elements-new (cdr elements))))
      (cons value values))))

(verify-guards plaintext-new)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Equality.

; snarkVM circuit/program/src/data/plaintext/equal.rs: Plaintext::is_equal
; (literals by Literal::is_equal; structs and arrays of the same length
; memberwise, member names by Identifier::is_equal; else false).
(defines values-plaintext-equalp
  :flag-local nil

  (define values-plaintext-equalp ((x plaintextp) (y plaintextp))
    :returns (yes/no booleanp)
    :measure (plaintext-count x)
    (cond ((and (plaintext-case x :literal) (plaintext-case y :literal))
           (values-literal-equalp (plaintext-literal->get x)
                                  (plaintext-literal->get y)))
          ((and (plaintext-case x :struct) (plaintext-case y :struct))
           (and (equal (len (plaintext-struct->members x))
                       (len (plaintext-struct->members y)))
                (values-plaintext-members-equalp (plaintext-struct->members x)
                                                 (plaintext-struct->members y))))
          ((and (plaintext-case x :array) (plaintext-case y :array))
           (and (equal (len (plaintext-array->elements x))
                       (len (plaintext-array->elements y)))
                (values-plaintext-elements-equalp (plaintext-array->elements x)
                                                  (plaintext-array->elements y))))
          (t nil)))

  (define values-plaintext-members-equalp ((xs plaintext-member-listp)
                                           (ys plaintext-member-listp))
    :returns (yes/no booleanp)
    :measure (plaintext-member-list-count xs)
    (or (endp xs)
        (endp ys)
        (and (equal (identifier->field (plaintext-member->name (car xs)))
                    (identifier->field (plaintext-member->name (car ys))))
             (values-plaintext-equalp (plaintext-member->value (car xs))
                                      (plaintext-member->value (car ys)))
             (values-plaintext-members-equalp (cdr xs) (cdr ys)))))

  (define values-plaintext-elements-equalp ((xs plaintext-listp)
                                            (ys plaintext-listp))
    :returns (yes/no booleanp)
    :measure (plaintext-list-count xs)
    (or (endp xs)
        (endp ys)
        (and (values-plaintext-equalp (car xs) (car ys))
             (values-plaintext-elements-equalp (cdr xs) (cdr ys))))))

; snarkVM circuit/program/src/data/plaintext/equal.rs: Plaintext::is_equal.
(define plaintext-is-equal ((x plaintextp) (y plaintextp))
  :returns (b bitp)
  (values-bool-to-bit (values-plaintext-equalp x y)))

; snarkVM circuit/program/src/data/plaintext/equal.rs: Plaintext::is_not_equal
; (the negation of is_equal, computed dually).
(define plaintext-is-not-equal ((x plaintextp) (y plaintextp))
  :returns (b bitp)
  (values-bool-to-bit (not (values-plaintext-equalp x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Find.

(define values-plaintext-find-aux ((pt plaintextp) (path access-listp))
  :returns (pt1 plaintext-resultp)
  (b* (((when (endp path)) (plaintext-fix pt))
       (access (car path)))
    (cond ((and (plaintext-case pt :struct) (acl2::access-case access :member))
           (b* ((member (values-plaintext-members-lookup
                         (acl2::access-member->name access)
                         (plaintext-struct->members pt)))
                ((unless member) (spec-error)))
             (values-plaintext-find-aux member (cdr path))))
          ((and (plaintext-case pt :array) (acl2::access-case access :index))
           (b* ((index (acl2::access-index->index access))
                (elements (plaintext-array->elements pt))
                ((unless (< index (len elements))) (spec-error)))
             (values-plaintext-find-aux (nth index elements) (cdr path))))
          (t (spec-error))))
  :measure (len path))

; snarkVM circuit/program/src/data/plaintext/find.rs: Plaintext::find
; (the indices must be constants; their values are modeled).
(define plaintext-find ((pt plaintextp) (path access-listp))
  :returns (pt1 plaintext-resultp)
  (b* (((when (endp path)) (spec-error))
       ((when (plaintext-case pt :literal)) (spec-error)))
    (values-plaintext-find-aux pt path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encryption.

; snarkVM console/network/src/lib.rs: encryption_domain = Field::from_bytes_le_mod_order(b"AleoSymmetricEncryption0").
(define values-encryption-domain ()
  :returns (f fieldp)
  (values-lebits-to-field
   (values-bytes-to-lebits
    (values-chars-to-bytes (coerce "AleoSymmetricEncryption0" 'list)))))

(define values-field-lists-add ((xs values-field-listp) (ys values-field-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs values-field-listp)
  (if (or (endp xs) (endp ys))
      nil
    (cons (values-field-add (car xs) (car ys))
          (values-field-lists-add (cdr xs) (cdr ys)))))

; snarkVM circuit/program/src/data/ciphertext/from_fields.rs: Ciphertext::from_fields
; (halts beyond MAX_DATA_SIZE_IN_FIELDS fields); the ciphertext is its list of fields.
(define values-ciphertext-from-fields ((fields values-field-listp))
  :returns (c values-field-list-resultp)
  (if (<= (len fields) (values-max-data-size-in-fields))
      (values-field-list-fix fields)
    (spec-error)))

; snarkVM circuit/program/src/data/plaintext/encrypt.rs: Plaintext::encrypt_with_randomizers
; (zip_eq halts on different lengths).  The result is the ciphertext fields.
(define plaintext-encrypt-with-randomizers ((pt plaintextp) (randomizers values-field-listp))
  :returns (c values-field-list-resultp)
  (b* (((fty::ok fields) (plaintext-to-fields pt))
       ((unless (equal (len fields) (len randomizers))) (spec-error)))
    (values-ciphertext-from-fields (values-field-lists-add fields randomizers))))

; snarkVM circuit/program/src/data/plaintext/encrypt.rs: Plaintext::encrypt_symmetric
; (randomizers = hash_many_psd8([encryption_domain, plaintext_view_key], num_randomizers)).
(define plaintext-encrypt-symmetric ((pt plaintextp) (plaintext-view-key fieldp))
  :returns (c values-field-list-resultp)
  (b* (((fty::ok num-randomizers) (plaintext-num-randomizers pt))
       (randomizers (poseidon-hash-many 8
                                        (list (values-encryption-domain)
                                              (values-field-fix plaintext-view-key))
                                        num-randomizers)))
    (plaintext-encrypt-with-randomizers pt randomizers)))

; snarkVM circuit/program/src/data/plaintext/encrypt.rs: Plaintext::encrypt
; (plaintext view key = (address * randomizer).x).
(define plaintext-encrypt ((pt plaintextp) (address groupp) (randomizer scalarp))
  :returns (c values-field-list-resultp)
  (plaintext-encrypt-symmetric pt (values-group-x (values-group-mul randomizer address))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry<Plaintext>.

(define values-entry-plaintext ((e entryp))
  :returns (pt plaintextp)
  (entry-case e
              :constant e.get
              :public e.get
              :private e.get))

(define values-entry-visibility-bits ((e entryp))
  :returns (bits bit-listp)
  (entry-case e
              :constant (list 0 0)
              :public (list 0 1)
              :private (list 1 0)))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::write_bits_le_with_visibility_as_mode
; (the mode only affects the variable kind of the visibility bits).
(define entry-write-bits-le-with-visibility-as-mode ((e entryp))
  :returns (bits bit-listp)
  (append (values-entry-visibility-bits e)
          (plaintext-to-bits-le (values-entry-plaintext e))))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::write_bits_le.
(define entry-to-bits-le ((e entryp))
  :returns (bits bit-listp)
  (entry-write-bits-le-with-visibility-as-mode e))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::write_bits_be.
(define entry-to-bits-be ((e entryp))
  :returns (bits bit-listp)
  (append (values-entry-visibility-bits e)
          (plaintext-to-bits-be (values-entry-plaintext e))))

; snarkVM circuit/program/src/data/record/entry/to_fields.rs: Entry::to_fields_with_visibility_as_mode.
(define entry-to-fields-with-visibility-as-mode ((e entryp))
  :returns (fs values-field-list-resultp)
  (values-pack-bits-bounded
   (append (entry-write-bits-le-with-visibility-as-mode e) (list 1))))

; snarkVM circuit/program/src/data/record/entry/to_fields.rs: Entry::to_fields.
(define entry-to-fields ((e entryp))
  :returns (fs values-field-list-resultp)
  (entry-to-fields-with-visibility-as-mode e))

; snarkVM circuit/program/src/data/record/entry/num_randomizers.rs: Entry::num_randomizers.
(define entry-num-randomizers ((e entryp))
  :returns (n values-nat-resultp)
  (entry-case e
              :constant 0
              :public 0
              :private (plaintext-size-in-fields e.get)))

; snarkVM circuit/program/src/data/record/entry/equal.rs: Entry::is_equal.
(define values-entry-equalp ((x entryp) (y entryp))
  :returns (yes/no booleanp)
  (and (equal (entry-kind x) (entry-kind y))
       (values-plaintext-equalp (values-entry-plaintext x)
                                (values-entry-plaintext y))))

(define entry-is-equal ((x entryp) (y entryp))
  :returns (b bitp)
  (values-bool-to-bit (values-entry-equalp x y)))

; snarkVM circuit/program/src/data/record/entry/equal.rs: Entry::is_not_equal.
(define entry-is-not-equal ((x entryp) (y entryp))
  :returns (b bitp)
  (values-bool-to-bit (not (values-entry-equalp x y))))

; snarkVM circuit/program/src/data/record/entry/mod.rs: Entry::new (Inject for Entry<Plaintext>).
(define entry-new ((e entryp))
  :returns (e1 entry-resultp)
  (b* (((fty::ok pt) (plaintext-new (values-entry-plaintext e))))
    (entry-case e
                :constant (entry-constant pt)
                :public (entry-public pt)
                :private (entry-private pt))))

; snarkVM circuit/program/src/data/record/entry/find.rs: Entry::find.
(define entry-find ((e entryp) (path access-listp))
  :returns (e1 entry-resultp)
  (b* (((fty::ok pt) (plaintext-find (values-entry-plaintext e) path)))
    (entry-case e
                :constant (entry-constant pt)
                :public (entry-public pt)
                :private (entry-private pt))))
