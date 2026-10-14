; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Model of the values manipulated by snarkVM's circuit program crate
; (circuit/program/src/data) and string crate (circuit/types/string):
; literals, identifiers, program IDs, plaintexts, entries, records,
; futures, arguments, dynamic records/futures, values, accesses,
; and the state-path leaves.
;
; Conventions on top of base.lisp:
;   - Each Rust circuit type is modeled by a fixtype of its ejected value.
;     Variable modes are not modeled (see base.lisp).
;   - A field element / scalar / group element is a values-field /
;     values-scalar / values-group, i.e. a fieldp / scalarp / groupp.
;   - Addresses are group elements (snarkVM Address wraps a Group).
;   - Unsigned/signed integers of width n are acl2::ubyte<n> / acl2::sbyte<n>.
;   - Bits are ACL2 bits (0/1); bit sequences are acl2::bit-list.
;   - Rust IndexMaps (struct members, record data) are lists of
;     (name, value) pairs in insertion order.
;   - A circuit Identifier is, as in Rust, a pair of a field element
;     (the little-endian bytes of the identifier string) and its byte size.
;     All Rust constructors guarantee a size of at most 31 bytes
;     (Field::SIZE_IN_DATA_BITS / 8), hence the size is a ubyte5.
;   - The bit caches (OnceCell) of circuit plaintexts and the console-only
;     data of dynamic records/futures (Option<...> fields that are never
;     part of the circuit) are not modeled.
;   - Records are records of plaintext entries (Record<A, Plaintext<A>>),
;     the only kind of record that is a Value.

(in-package "ALEOVM")

(include-book "base")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "kestrel/fty/bit-list" :dir :system)
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte8" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)
(include-book "kestrel/fty/ubyte64" :dir :system)
(include-book "kestrel/fty/ubyte128" :dir :system)
(include-book "kestrel/fty/sbyte8" :dir :system)
(include-book "kestrel/fty/sbyte16" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/fty/sbyte128" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fixtypes for field elements, scalars, and group elements.

(defruled values-fieldp-of-0
  (fieldp 0)
  :enable (fieldp pfield::fep base-prime (:e ecurve::edwards-bls12-q)))

(defruled values-scalarp-of-0
  (scalarp 0)
  :enable (scalarp pfield::fep scalar-prime (:e ecurve::edwards-bls12-r)))

(defruled values-groupp-of-zero
  (groupp (ecurve::twisted-edwards-zero))
  :enable (groupp ecurve::edwards-bls12-r-pointp))

(define values-field-fix ((x fieldp))
  :returns (x1 fieldp :hints (("Goal" :in-theory (enable values-fieldp-of-0))))
  (mbe :logic (if (fieldp x) x 0) :exec x)
  ///
  (defrule values-field-fix-when-fieldp
    (implies (fieldp x) (equal (values-field-fix x) x))))

(fty::deffixtype values-field
  :pred fieldp
  :fix values-field-fix
  :equiv values-field-equiv
  :define t
  :forward t)

(define values-scalar-fix ((x scalarp))
  :returns (x1 scalarp :hints (("Goal" :in-theory (enable values-scalarp-of-0))))
  (mbe :logic (if (scalarp x) x 0) :exec x)
  ///
  (defrule values-scalar-fix-when-scalarp
    (implies (scalarp x) (equal (values-scalar-fix x) x))))

(fty::deffixtype values-scalar
  :pred scalarp
  :fix values-scalar-fix
  :equiv values-scalar-equiv
  :define t
  :forward t)

(define values-group-fix ((x groupp))
  :returns (x1 groupp :hints (("Goal" :in-theory (enable values-groupp-of-zero))))
  (mbe :logic (if (groupp x) x (ecurve::twisted-edwards-zero)) :exec x)
  ///
  (defrule values-group-fix-when-groupp
    (implies (groupp x) (equal (values-group-fix x) x))))

(fty::deffixtype values-group
  :pred groupp
  :fix values-group-fix
  :equiv values-group-equiv
  :define t
  :forward t)

(fty::deflist values-field-list
  :elt-type values-field
  :true-listp t
  :pred values-field-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literals.

; snarkVM circuit/account/src/compute_key/mod.rs: ComputeKey { pk_sig, pr_sig, sk_prf }.
(fty::defprod compute-key
  ((pk-sig values-group)
   (pr-sig values-group)
   (sk-prf values-scalar))
  :tag :compute-key
  :pred compute-keyp)

; snarkVM circuit/account/src/signature/mod.rs: Signature { challenge, response, compute_key }.
(fty::defprod signature
  ((challenge values-scalar)
   (response values-scalar)
   (compute-key compute-key))
  :tag :signature
  :pred signaturep)

; snarkVM circuit/types/string/src/lib.rs: StringType { mode, bytes, size_in_bytes }.
; The size_in_bytes field is always the number of bytes (it is constrained so),
; hence only the bytes are modeled.
(fty::defprod string-type
  ((bytes acl2::ubyte8-list))
  :tag :string-type
  :pred string-typep)

; snarkVM circuit/types/string/src/identifier_literal/mod.rs:
; IdentifierLiteral { bytes: [U8; 31] }.
; Validity (31 bytes, [a-zA-Z0-9_] then trailing nulls, leading letter)
; is enforced by the constructors, see values-string.lisp.
(fty::defprod identifier-literal
  ((bytes acl2::ubyte8-list))
  :tag :identifier-literal
  :pred identifier-literalp)

; snarkVM circuit/program/src/data/literal/mod.rs: enum Literal.
(fty::deftagsum literal
  (:address ((get values-group)))
  (:boolean ((get bit)))
  (:field ((get values-field)))
  (:group ((get values-group)))
  (:i8 ((get acl2::sbyte8)))
  (:i16 ((get acl2::sbyte16)))
  (:i32 ((get acl2::sbyte32)))
  (:i64 ((get acl2::sbyte64)))
  (:i128 ((get acl2::sbyte128)))
  (:u8 ((get acl2::ubyte8)))
  (:u16 ((get acl2::ubyte16)))
  (:u32 ((get acl2::ubyte32)))
  (:u64 ((get acl2::ubyte64)))
  (:u128 ((get acl2::ubyte128)))
  (:scalar ((get values-scalar)))
  (:signature ((get signature)))
  (:string ((get string-type)))
  (:identifier ((get identifier-literal)))
  :pred literalp)

; snarkVM console/program/src/data_types/literal_type/mod.rs: enum LiteralType.
(fty::deftagsum literal-type
  (:address ())
  (:boolean ())
  (:field ())
  (:group ())
  (:i8 ())
  (:i16 ())
  (:i32 ())
  (:i64 ())
  (:i128 ())
  (:u8 ())
  (:u16 ())
  (:u32 ())
  (:u64 ())
  (:u128 ())
  (:scalar ())
  (:signature ())
  (:string ())
  (:identifier ())
  :pred literal-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifiers and program IDs.

; snarkVM circuit/program/src/data/identifier/mod.rs: Identifier(Field, u8).
(fty::defprod identifier
  ((field values-field)
   (size acl2::ubyte5))
  :tag :identifier
  :pred identifierp)

(fty::deflist identifier-list
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

; snarkVM circuit/program/src/id/mod.rs: ProgramID { name, network }.
(fty::defprod program-id
  ((name identifier)
   (network identifier))
  :tag :program-id
  :pred program-idp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plaintexts.

; snarkVM circuit/program/src/data/plaintext/mod.rs: enum Plaintext
; (Literal | Struct(IndexMap<Identifier, Plaintext>) | Array(Vec<Plaintext>)).
(fty::deftypes plaintexts

  (fty::deftagsum plaintext
    (:literal ((get literal)))
    (:struct ((members plaintext-member-list)))
    (:array ((elements plaintext-list)))
    :pred plaintextp
    :measure (acl2::two-nats-measure (acl2-count x) 0))

  (fty::defprod plaintext-member
    ((name identifier)
     (value plaintext))
    :tag :plaintext-member
    :pred plaintext-memberp
    :measure (acl2::two-nats-measure (acl2-count x) 1))

  (fty::deflist plaintext-member-list
    :elt-type plaintext-member
    :true-listp t
    :elementp-of-nil nil
    :pred plaintext-member-listp
    :measure (acl2::two-nats-measure (acl2-count x) 0))

  (fty::deflist plaintext-list
    :elt-type plaintext
    :true-listp t
    :elementp-of-nil nil
    :pred plaintext-listp
    :measure (acl2::two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entries and records.

; snarkVM circuit/program/src/data/record/entry/mod.rs:
; enum Entry<A, Plaintext<A>> { Constant, Public, Private }.
(fty::deftagsum entry
  (:constant ((get plaintext)))
  (:public ((get plaintext)))
  (:private ((get plaintext)))
  :pred entryp)

; snarkVM circuit/program/src/data/record/helpers/owner.rs:
; enum Owner<A, Plaintext<A>> { Public(Address), Private(Plaintext) }.
; Owner::new halts unless a private owner is an address literal,
; hence both variants carry an address.
(fty::deftagsum owner
  (:public ((address values-group)))
  (:private ((address values-group)))
  :pred ownerp)

(fty::defprod record-entry
  ((name identifier)
   (entry entry))
  :tag :record-entry
  :pred record-entryp)

(fty::deflist record-entry-list
  :elt-type record-entry
  :true-listp t
  :elementp-of-nil nil
  :pred record-entry-listp)

; snarkVM circuit/program/src/data/record/mod.rs:
; Record<A, Plaintext<A>> { owner, data, nonce, version }.
(fty::defprod record
  ((owner owner)
   (data record-entry-list)
   (nonce values-group)
   (version acl2::ubyte8))
  :tag :record
  :pred recordp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Dynamic records and futures, futures, arguments.

; snarkVM circuit/program/src/data/dynamic/record/mod.rs:
; DynamicRecord { owner, root, nonce, version, data: Option<console data> }.
(fty::defprod dynamic-record
  ((owner values-group)
   (root values-field)
   (nonce values-group)
   (version acl2::ubyte8))
  :tag :dynamic-record
  :pred dynamic-recordp)

; snarkVM circuit/program/src/data/dynamic/future/mod.rs:
; DynamicFuture { program_name, program_network, function_name, checksum,
;                 arguments: Option<console arguments> }.
(fty::defprod dynamic-future
  ((program-name values-field)
   (program-network values-field)
   (function-name values-field)
   (checksum values-field))
  :tag :dynamic-future
  :pred dynamic-futurep)

; snarkVM circuit/program/src/data/future/mod.rs: Future { program_id, function_name, arguments },
; and circuit/program/src/data/future/argument.rs: enum Argument.
(fty::deftypes futures

  (fty::defprod future
    ((program-id program-id)
     (function-name identifier)
     (arguments argument-list))
    :tag :future
    :pred futurep
    :measure (acl2::two-nats-measure (acl2-count x) 1))

  (fty::deftagsum argument
    (:plaintext ((get plaintext)))
    (:future ((get future)))
    (:dynamic-future ((get dynamic-future)))
    :pred argumentp
    :measure (acl2::two-nats-measure (acl2-count x) 0))

  (fty::deflist argument-list
    :elt-type argument
    :true-listp t
    :elementp-of-nil nil
    :pred argument-listp
    :measure (acl2::two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values.

; snarkVM circuit/program/src/data/value/mod.rs: enum Value.
(fty::deftagsum value
  (:plaintext ((get plaintext)))
  (:record ((get record)))
  (:future ((get future)))
  (:dynamic-record ((get dynamic-record)))
  (:dynamic-future ((get dynamic-future)))
  :pred valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Accesses (paths into plaintexts, records, futures).

; snarkVM circuit/program/src/data/access/mod.rs: enum Access { Member(Identifier), Index(U32) }.
; find requires indices to be constants; the values are modeled.
(fty::deftagsum access
  (:member ((name identifier)))
  (:index ((index acl2::ubyte32)))
  :pred accessp)

(fty::deflist access-list
  :elt-type access
  :true-listp t
  :elementp-of-nil nil
  :pred access-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State-path leaves.

; snarkVM circuit/program/src/state_path/helpers/header_leaf.rs: HeaderLeaf { index, id }.
(fty::defprod header-leaf
  ((index acl2::ubyte8)
   (id values-field))
  :tag :header-leaf
  :pred header-leafp)

; snarkVM circuit/program/src/state_path/helpers/transaction_leaf.rs:
; TransactionLeaf { variant, index, id }.
(fty::defprod transaction-leaf
  ((variant acl2::ubyte8)
   (index acl2::ubyte16)
   (id values-field))
  :tag :transaction-leaf
  :pred transaction-leafp)

; snarkVM circuit/program/src/state_path/helpers/transition_leaf.rs:
; TransitionLeaf { version, index, variant, id }.
(fty::defprod transition-leaf
  ((version acl2::ubyte8)
   (index acl2::ubyte8)
   (variant acl2::ubyte8)
   (id values-field))
  :tag :transition-leaf
  :pred transition-leafp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Result types (good values or (spec-error)).
;; Errors are propagated with the b* binder fty::ok,
;; so that every error is (spec-error).

(defrule values-not-reserrp-when-fep
  (implies (pfield::fep x p)
           (not (reserrp x)))
  :enable (pfield::fep reserrp))

(defrule values-not-reserrp-when-edwards-bls12-r-pointp
  (implies (ecurve::edwards-bls12-r-pointp x)
           (not (reserrp x)))
  :enable (ecurve::edwards-bls12-r-pointp
           ecurve::edwards-bls12-pointp
           ecurve::pointp
           ecurve::twisted-edwards-zero
           ecurve::point-finite
           reserrp))

(defrule values-not-edwards-bls12-r-pointp-of-cons-error
  (not (ecurve::edwards-bls12-r-pointp (cons :error y)))
  :enable (ecurve::edwards-bls12-r-pointp
           ecurve::edwards-bls12-pointp
           ecurve::pointp
           ecurve::twisted-edwards-zero
           ecurve::point-finite))

(defrule values-edwards-bls12-r-pointp-of-zero
  (ecurve::edwards-bls12-r-pointp (ecurve::twisted-edwards-zero))
  :use values-groupp-of-zero
  :enable groupp)

(fty::defresult values-field-result
  :ok values-field
  :pred values-field-resultp)

(fty::defresult values-scalar-result
  :ok values-scalar
  :pred values-scalar-resultp)

(fty::defresult values-group-result
  :ok values-group
  :pred values-group-resultp)

(fty::defresult values-bit-result
  :ok bit
  :pred values-bit-resultp)

(fty::defresult values-integer-result
  :ok int
  :pred values-integer-resultp)

(fty::defresult bit-list-result
  :ok acl2::bit-list
  :pred bit-list-resultp)

(fty::defresult values-field-list-result
  :ok values-field-list
  :pred values-field-list-resultp)

(fty::defresult literal-result
  :ok literal
  :pred literal-resultp
  :prepwork ((local (in-theory (enable literal-kind)))))

(fty::defresult string-type-result
  :ok string-type
  :pred string-type-resultp)

(fty::defresult identifier-literal-result
  :ok identifier-literal
  :pred identifier-literal-resultp)

(fty::defresult identifier-result
  :ok identifier
  :pred identifier-resultp)

(fty::defresult plaintext-result
  :ok plaintext
  :pred plaintext-resultp
  :prepwork ((local (in-theory (enable plaintext-kind)))))

(fty::defresult plaintext-member-list-result
  :ok plaintext-member-list
  :pred plaintext-member-list-resultp)

(fty::defresult plaintext-list-result
  :ok plaintext-list
  :pred plaintext-list-resultp)

(fty::defresult entry-result
  :ok entry
  :pred entry-resultp
  :prepwork ((local (in-theory (enable entry-kind)))))

(fty::defresult record-result
  :ok record
  :pred record-resultp)

(fty::defresult future-result
  :ok future
  :pred future-resultp)

(fty::defresult argument-result
  :ok argument
  :pred argument-resultp
  :prepwork ((local (in-theory (enable argument-kind)))))

(fty::defresult dynamic-record-result
  :ok dynamic-record
  :pred dynamic-record-resultp)

(fty::defresult dynamic-future-result
  :ok dynamic-future
  :pred dynamic-future-resultp)

(fty::defresult value-result
  :ok value
  :pred value-resultp
  :prepwork ((local (in-theory (enable value-kind)))))

(fty::defresult argument-list-result
  :ok argument-list
  :pred argument-list-resultp)

(fty::defresult record-entry-list-result
  :ok record-entry-list
  :pred record-entry-list-resultp)

(fty::defresult owner-result
  :ok owner
  :pred owner-resultp
  :prepwork ((local (in-theory (enable owner-kind)))))
