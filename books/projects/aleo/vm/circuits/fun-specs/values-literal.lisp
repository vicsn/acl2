; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FUN-SPECs of the circuit program crate (snarkVM circuit/program):
; Identifier, Literal (with Signature), ProgramID, compute_function_id.

(in-package "ALEOVM")

(include-book "values-string")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (enable spec-error)))

(fty::defresult values-signature-result
  :ok signature
  :pred values-signature-resultp)

(in-theory (enable signaturep-when-result-not-error
                   not-reserrp-when-signaturep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Console identifier strings (console/program/src/data/identifier/parse.rs).

(define values-chars-to-bytes ((chars character-listp))
  :returns (bytes acl2::ubyte8-listp :hints (("Goal" :in-theory (enable ubyte8p))))
  (if (endp chars)
      nil
    (cons (char-code (car chars))
          (values-chars-to-bytes (cdr chars)))))

(define values-ascii-letter-p ((b ubyte8p))
  :returns (yes/no booleanp)
  (b* ((b (acl2::ubyte8-fix b)))
    (or (and (<= 65 b) (<= b 90))
        (and (<= 97 b) (<= b 122)))))

(define values-ascii-alnum-or-underscore-p ((b ubyte8p))
  :returns (yes/no booleanp)
  (b* ((b (acl2::ubyte8-fix b)))
    (or (values-ascii-letter-p b)
        (and (<= 48 b) (<= b 57))
        (equal b 95))))

(define values-all-ascii-alnum-or-underscore-p ((bytes acl2::ubyte8-listp))
  :returns (yes/no booleanp)
  (or (endp bytes)
      (and (values-ascii-alnum-or-underscore-p (car bytes))
           (values-all-ascii-alnum-or-underscore-p (cdr bytes)))))

; console/program/src/data_types/literal_type/mod.rs: LiteralType::type_name.
(define values-literal-type-names ()
  :returns (names string-listp)
  (list "address" "boolean" "field" "group"
        "i8" "i16" "i32" "i64" "i128"
        "u8" "u16" "u32" "u64" "u128"
        "scalar" "signature" "string" "identifier"))

(define values-reserved-identifier-p ((bytes acl2::ubyte8-listp))
  :returns (yes/no booleanp)
  (values-reserved-identifier-p-aux bytes (values-literal-type-names))
  :prepwork
  ((define values-reserved-identifier-p-aux ((bytes acl2::ubyte8-listp) (names string-listp))
     :returns (yes/no booleanp)
     (and (consp names)
          (or (equal (acl2::ubyte8-list-fix bytes)
                     (values-chars-to-bytes (coerce (car names) 'list)))
              (values-reserved-identifier-p-aux bytes (cdr names)))))))

; snarkVM console/program/src/data/identifier/parse.rs: Identifier::from_str
; (on the UTF-8 bytes of the string; non-ASCII bytes are rejected either by
; str::from_utf8 or by the ASCII character checks).
(define values-valid-identifier-bytes-p ((bytes acl2::ubyte8-listp))
  :returns (yes/no booleanp)
  (and (consp bytes)
       (values-ascii-letter-p (car bytes))
       (values-all-ascii-alnum-or-underscore-p bytes)
       (<= (len bytes) 31)
       (not (values-reserved-identifier-p bytes))))

(define values-index-of-first-zero ((bytes acl2::ubyte8-listp))
  :returns (n natp :rule-classes :type-prescription)
  :short "Rust @('bytes.iter().position(|&b| b == 0)'), or the length if none."
  (cond ((endp bytes) 0)
        ((equal (acl2::ubyte8-fix (car bytes)) 0) 0)
        (t (1+ (values-index-of-first-zero (cdr bytes)))))
  ///
  (defret values-index-of-first-zero-upper-bound
    (<= n (len bytes))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier.

; snarkVM circuit/program/src/data/identifier/mod.rs: Identifier::public.
(define identifier-public ((id identifierp))
  :returns (id1 identifierp)
  (identifier-fix id))

; snarkVM circuit/program/src/data/identifier/to_field.rs: Identifier::to_field.
(define identifier-to-field ((id identifierp))
  :returns (f fieldp)
  (identifier->field id))

; snarkVM circuit/program/src/data/identifier/size_in_bits.rs: Identifier::size_in_bits
; (8 * size; never overflows u8 since size <= 31).
(define identifier-size-in-bits ((id identifierp))
  :returns (n natp :rule-classes :type-prescription)
  (* 8 (identifier->size id))
  ///
  (defret identifier-size-in-bits-upper-bound
    (<= n 248)
    :rule-classes :linear
    :hints (("Goal" :in-theory (e/d (acl2::ubyte5p unsigned-byte-p)
                             (ubyte5p-of-identifier->size))
             :use (:instance ubyte5p-of-identifier->size (x id))))))

; snarkVM circuit/program/src/data/identifier/equal.rs: Identifier::is_equal.
(define identifier-is-equal ((x identifierp) (y identifierp))
  :returns (b bitp)
  (values-bool-to-bit (equal (identifier->field x) (identifier->field y))))

; snarkVM circuit/program/src/data/identifier/equal.rs: Identifier::is_not_equal.
(define identifier-is-not-equal ((x identifierp) (y identifierp))
  :returns (b bitp)
  (values-bool-to-bit (not (equal (identifier->field x) (identifier->field y)))))

; snarkVM circuit/program/src/data/identifier/to_bits.rs: Identifier::write_bits_le
; (the field bits truncated to 8 * size bits).
(define identifier-to-bits-le ((id identifierp))
  :returns (bits bit-listp)
  (take (identifier-size-in-bits id)
        (values-field-to-bits-le (identifier->field id)))
  ///
  (defret len-of-identifier-to-bits-le
    (equal (len bits) (identifier-size-in-bits id))))

; snarkVM circuit/program/src/data/identifier/to_bits.rs: Identifier::write_bits_be.
(define identifier-to-bits-be ((id identifierp))
  :returns (bits bit-listp)
  (rev (identifier-to-bits-le id))
  ///
  (defret len-of-identifier-to-bits-be
    (equal (len bits) (identifier-size-in-bits id))))

; snarkVM circuit/program/src/data/identifier/from_bits.rs: Identifier::from_bits_le
; (circuit Field::from_bits_le, then console Identifier::from_bits_le for the size).
; The field element keeps all the input bits, including any bits after the
; first null byte.
(defruledl values-ubyte5p-when-valid-identifier-prefix
  (implies (values-valid-identifier-bytes-p (take (values-index-of-first-zero bytes) bytes))
           (acl2::ubyte5p (values-index-of-first-zero bytes)))
  :enable (values-valid-identifier-bytes-p acl2::ubyte5p unsigned-byte-p))

(define identifier-from-bits-le ((bits bit-listp))
  :guard-hints (("Goal" :in-theory (enable values-ubyte5p-when-valid-identifier-prefix)))
  :returns (id identifier-resultp)
  (b* (((fty::ok field) (values-field-from-bits-le bits))
       ((unless (<= (len bits) 253)) (spec-error))
       (bytes (values-lebits-to-bytes bits))
       (num-bytes (values-index-of-first-zero bytes))
       (string-bytes (take num-bytes bytes))
       ((unless (values-valid-identifier-bytes-p string-bytes)) (spec-error)))
    (make-identifier :field field :size num-bytes)))

; snarkVM circuit/program/src/data/identifier/from_bits.rs: Identifier::from_bits_be.
(define identifier-from-bits-be ((bits bit-listp))
  :returns (id identifier-resultp)
  (identifier-from-bits-le (rev bits)))

; snarkVM circuit/program/src/data/identifier/from_field.rs: Identifier::from_field.
(define identifier-from-field ((x fieldp))
  :returns (id identifier-resultp)
  (identifier-from-bits-le (values-field-to-bits-le x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Signatures and compute keys (circuit/account), as used by literals.

; snarkVM circuit/account/src/compute_key/from.rs: ComputeKey::from((pk_sig, pr_sig)).
(define values-compute-key-from ((pk-sig groupp) (pr-sig groupp))
  :returns (ck compute-keyp)
  (make-compute-key
   :pk-sig pk-sig
   :pr-sig pr-sig
   :sk-prf (values-hash-to-scalar-psd4 (list (values-group-x pk-sig)
                                             (values-group-x pr-sig)))))

; snarkVM circuit/account/src/signature/mod.rs: Signature::new
; (Scalar::new, ComputeKey::new: Group::new on pk_sig, pr_sig and sk_prf recomputed).
(define values-signature-new ((sig signaturep))
  :returns (sig1 signaturep)
  (b* ((ck (signature->compute-key sig)))
    (make-signature
     :challenge (signature->challenge sig)
     :response (signature->response sig)
     :compute-key (values-compute-key-from (compute-key->pk-sig ck)
                                           (compute-key->pr-sig ck)))))

; snarkVM circuit/account/src/signature/helpers/to_bits.rs: Signature::write_bits_le
; (challenge, response, compute key = pk_sig, pr_sig).
(define values-signature-to-bits-le ((sig signaturep))
  :returns (bits bit-listp)
  (b* ((ck (signature->compute-key sig)))
    (append (values-scalar-to-bits-le (signature->challenge sig))
            (values-scalar-to-bits-le (signature->response sig))
            (values-group-to-bits-le (compute-key->pk-sig ck))
            (values-group-to-bits-le (compute-key->pr-sig ck)))))

(define values-signature-to-bits-be ((sig signaturep))
  :returns (bits bit-listp)
  (b* ((ck (signature->compute-key sig)))
    (append (values-scalar-to-bits-be (signature->challenge sig))
            (values-scalar-to-bits-be (signature->response sig))
            (values-group-to-bits-be (compute-key->pk-sig ck))
            (values-group-to-bits-be (compute-key->pr-sig ck)))))

; snarkVM circuit/account/src/signature/helpers/to_fields.rs: Signature::to_fields.
(define values-signature-to-fields ((sig signaturep))
  :returns (fs values-field-listp)
  (b* ((ck (signature->compute-key sig)))
    (list (signature->challenge sig)
          (signature->response sig)
          (values-group-x (compute-key->pk-sig ck))
          (values-group-x (compute-key->pr-sig ck)))))

; snarkVM circuit/account/src/signature/helpers/from_bits.rs: Signature::from_bits_le
; (slices of 251, 251, 506 bits; halts if missing; extra bits ignored).
(define values-signature-from-bits ((bits bit-listp) (bigp booleanp))
  :returns (sig values-signature-resultp)
  (b* (((unless (<= 1008 (len bits))) (spec-error))
       (c-bits (take 251 bits))
       (r-bits (take 251 (nthcdr 251 bits)))
       (pk-bits (take 253 (nthcdr 502 bits)))
       (pr-bits (take 253 (nthcdr 755 bits)))
       ((fty::ok c) (if bigp
                        (values-scalar-from-bits-be c-bits)
                      (values-scalar-from-bits-le c-bits)))
       ((fty::ok r) (if bigp
                        (values-scalar-from-bits-be r-bits)
                      (values-scalar-from-bits-le r-bits)))
       ((fty::ok pk) (if bigp
                         (values-group-from-bits-be pk-bits)
                       (values-group-from-bits-le pk-bits)))
       ((fty::ok pr) (if bigp
                         (values-group-from-bits-be pr-bits)
                       (values-group-from-bits-le pr-bits))))
    (make-signature :challenge c
                    :response r
                    :compute-key (values-compute-key-from pk pr))))

; snarkVM circuit/account/src/signature/equal.rs: Signature::is_equal
; (challenge, response, and compute key pk_sig, pr_sig, sk_prf).
(define values-signature-equalp ((x signaturep) (y signaturep))
  :returns (yes/no booleanp)
  (equal (signature-fix x) (signature-fix y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal.

; snarkVM circuit/program/src/data/literal/variant.rs: Literal::variant.
(define literal-variant ((x literalp))
  :returns (v natp :rule-classes :type-prescription)
  (literal-case x
                :address 0 :boolean 1 :field 2 :group 3
                :i8 4 :i16 5 :i32 6 :i64 7 :i128 8
                :u8 9 :u16 10 :u32 11 :u64 12 :u128 13
                :scalar 14 :signature 15 :string 16 :identifier 17)
  ///
  (defret literal-variant-upper-bound
    (< v 256)
    :rule-classes :linear))

; snarkVM circuit/program/src/data/literal/to_bits.rs: Literal::write_bits_le.
(define literal-to-bits-le ((x literalp))
  :returns (bits bit-listp)
  (literal-case
   x
   :address (values-group-to-bits-le x.get)
   :boolean (list x.get)
   :field (values-field-to-bits-le x.get)
   :group (values-group-to-bits-le x.get)
   :i8 (values-int-to-bits-le x.get 8)
   :i16 (values-int-to-bits-le x.get 16)
   :i32 (values-int-to-bits-le x.get 32)
   :i64 (values-int-to-bits-le x.get 64)
   :i128 (values-int-to-bits-le x.get 128)
   :u8 (values-int-to-bits-le x.get 8)
   :u16 (values-int-to-bits-le x.get 16)
   :u32 (values-int-to-bits-le x.get 32)
   :u64 (values-int-to-bits-le x.get 64)
   :u128 (values-int-to-bits-le x.get 128)
   :scalar (values-scalar-to-bits-le x.get)
   :signature (values-signature-to-bits-le x.get)
   :string (string-type-to-bits-le x.get)
   :identifier (identifier-literal-to-bits-le x.get)))

; snarkVM circuit/program/src/data/literal/to_bits.rs: Literal::write_bits_be.
(define literal-to-bits-be ((x literalp))
  :returns (bits bit-listp)
  (literal-case
   x
   :address (values-group-to-bits-be x.get)
   :boolean (list x.get)
   :field (values-field-to-bits-be x.get)
   :group (values-group-to-bits-be x.get)
   :i8 (values-int-to-bits-be x.get 8)
   :i16 (values-int-to-bits-be x.get 16)
   :i32 (values-int-to-bits-be x.get 32)
   :i64 (values-int-to-bits-be x.get 64)
   :i128 (values-int-to-bits-be x.get 128)
   :u8 (values-int-to-bits-be x.get 8)
   :u16 (values-int-to-bits-be x.get 16)
   :u32 (values-int-to-bits-be x.get 32)
   :u64 (values-int-to-bits-be x.get 64)
   :u128 (values-int-to-bits-be x.get 128)
   :scalar (values-scalar-to-bits-be x.get)
   :signature (values-signature-to-bits-be x.get)
   :string (string-type-to-bits-be x.get)
   :identifier (identifier-literal-to-bits-be x.get)))

; snarkVM circuit/program/src/data/literal/size_in_bits.rs: Literal::size_in_bits
; (a u16; for strings, the number of bits cast with 'as u16').
(define literal-size-in-bits ((x literalp))
  :returns (n natp :rule-classes :type-prescription)
  (literal-case
   x
   :address 253 :boolean 1 :field 253 :group 253
   :i8 8 :i16 16 :i32 32 :i64 64 :i128 128
   :u8 8 :u16 16 :u32 32 :u64 64 :u128 128
   :scalar 251 :signature 1008
   :string (mod (len (string-type-to-bits-le x.get)) (expt 2 16))
   :identifier 248))

; snarkVM circuit/program/src/data/literal/to_fields.rs: Literal::to_fields.
(define literal-to-fields ((x literalp))
  :returns (fs values-field-listp)
  (literal-case
   x
   :address (list (values-group-x x.get))
   :boolean (list x.get)
   :field (list x.get)
   :group (list (values-group-x x.get))
   :i8 (list (values-int-to-field x.get 8))
   :i16 (list (values-int-to-field x.get 16))
   :i32 (list (values-int-to-field x.get 32))
   :i64 (list (values-int-to-field x.get 64))
   :i128 (list (values-int-to-field x.get 128))
   :u8 (list (values-int-to-field x.get 8))
   :u16 (list (values-int-to-field x.get 16))
   :u32 (list (values-int-to-field x.get 32))
   :u64 (list (values-int-to-field x.get 64))
   :u128 (list (values-int-to-field x.get 128))
   :scalar (list x.get)
   :signature (values-signature-to-fields x.get)
   :string (string-type-to-fields x.get)
   :identifier (identifier-literal-to-fields x.get))
  :prepwork
  ((local (in-theory (enable values-fieldp-when-bounded bitp)))))

; snarkVM circuit/program/src/data/literal/equal.rs: Literal::is_equal (true iff the literal
; values are equal: Group/Address is_equal compares both coordinates).
(define values-literal-equalp ((x literalp) (y literalp))
  :returns (yes/no booleanp)
  (cond ((and (literal-case x :string) (literal-case y :string))
         (equal (string-type-is-equal (literal-string->get x)
                                      (literal-string->get y))
                1))
        ((and (literal-case x :identifier) (literal-case y :identifier))
         (equal (identifier-literal-is-equal (literal-identifier->get x)
                                             (literal-identifier->get y))
                1))
        ((and (literal-case x :signature) (literal-case y :signature))
         (values-signature-equalp (literal-signature->get x)
                                  (literal-signature->get y)))
        (t (equal (literal-fix x) (literal-fix y)))))

(define literal-is-equal ((x literalp) (y literalp))
  :returns (b bitp)
  (values-bool-to-bit (values-literal-equalp x y)))

; snarkVM circuit/program/src/data/literal/equal.rs: Literal::is_not_equal.
(define literal-is-not-equal ((x literalp) (y literalp))
  :returns (b bitp)
  (values-bool-to-bit (not (values-literal-equalp x y))))

; snarkVM circuit/program/src/data/literal/mod.rs: Literal::new (Inject).
(define literal-new ((x literalp))
  :returns (r literal-resultp)
  (literal-case
   x
   :signature (literal-signature (values-signature-new x.get))
   :string (b* (((fty::ok s) (string-type-new x.get)))
             (literal-string s))
   :identifier (b* (((fty::ok id) (identifier-literal-new x.get)))
                 (literal-identifier id))
   :otherwise (literal-fix x)))

; snarkVM circuit/program/src/data/literal/from_bits.rs: Literal::from_bits_le / from_bits_be.
(define values-literal-from-bits ((variant ubyte8p) (bits bit-listp) (bigp booleanp))
  :returns (r literal-resultp)
  (b* ((variant (acl2::ubyte8-fix variant))
       (bits (bit-list-fix bits)))
    (case variant
      ((0 3) (b* (((fty::ok g) (if bigp
                                   (values-group-from-bits-be bits)
                                 (values-group-from-bits-le bits))))
               (if (equal variant 0) (literal-address g) (literal-group g))))
      (1 (if (equal (len bits) 1)
             (literal-boolean (car bits))
           (spec-error)))
      (2 (b* (((fty::ok f) (if bigp
                               (values-field-from-bits-be bits)
                             (values-field-from-bits-le bits))))
           (literal-field f)))
      ((4 5 6 7 8 9 10 11 12 13)
       (b* ((signedp (< variant 9))
            (n (case variant
                 ((4 9) 8) ((5 10) 16) ((6 11) 32) ((7 12) 64) (t 128)))
            ((fty::ok i) (if bigp
                             (values-int-from-bits-be bits signedp n)
                           (values-int-from-bits-le bits signedp n))))
         (case variant
           (4 (literal-i8 i)) (5 (literal-i16 i)) (6 (literal-i32 i))
           (7 (literal-i64 i)) (8 (literal-i128 i))
           (9 (literal-u8 i)) (10 (literal-u16 i)) (11 (literal-u32 i))
           (12 (literal-u64 i)) (t (literal-u128 i)))))
      (14 (b* (((fty::ok s) (if bigp
                                (values-scalar-from-bits-be bits)
                              (values-scalar-from-bits-le bits))))
            (literal-scalar s)))
      (15 (b* (((fty::ok sig) (values-signature-from-bits bits bigp)))
            (literal-signature sig)))
      (16 (b* (((fty::ok s) (if bigp
                                (string-type-from-bits-be bits)
                              (string-type-from-bits-le bits))))
            (literal-string s)))
      (17 (b* (((fty::ok id) (if bigp
                                 (identifier-literal-from-bits-be bits)
                               (identifier-literal-from-bits-le bits))))
            (literal-identifier id)))
      (t (spec-error))))
  :guard-hints (("Goal" :in-theory (enable bitp bit-listp
                                           sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p
                                           ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p))))

; snarkVM circuit/program/src/data/literal/from_bits.rs: Literal::from_bits_le.
(define literal-from-bits-le ((variant ubyte8p) (bits bit-listp))
  :returns (r literal-resultp)
  (values-literal-from-bits variant bits nil))

; snarkVM circuit/program/src/data/literal/from_bits.rs: Literal::from_bits_be.
(define literal-from-bits-be ((variant ubyte8p) (bits bit-listp))
  :returns (r literal-resultp)
  (values-literal-from-bits variant bits t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ProgramID.

; snarkVM circuit/program/src/id/mod.rs: ProgramID::public.
(define program-id-public ((id program-idp))
  :returns (id1 program-idp)
  (make-program-id :name (identifier-public (program-id->name id))
                   :network (identifier-public (program-id->network id))))

; snarkVM circuit/program/src/id/mod.rs: ProgramID::is_equal.
(define program-id-is-equal ((x program-idp) (y program-idp))
  :returns (b bitp)
  (values-b-and (identifier-is-equal (program-id->name x) (program-id->name y))
                (identifier-is-equal (program-id->network x) (program-id->network y))))

; snarkVM circuit/program/src/id/mod.rs: ProgramID::is_not_equal.
(define program-id-is-not-equal ((x program-idp) (y program-idp))
  :returns (b bitp)
  (values-b-or (identifier-is-not-equal (program-id->name x) (program-id->name y))
               (identifier-is-not-equal (program-id->network x) (program-id->network y))))

; snarkVM circuit/program/src/id/to_bits.rs: ProgramID::write_bits_le.
(define program-id-to-bits-le ((id program-idp))
  :returns (bits bit-listp)
  (append (identifier-to-bits-le (program-id->name id))
          (identifier-to-bits-le (program-id->network id))))

; snarkVM circuit/program/src/id/to_bits.rs: ProgramID::write_bits_be.
(define program-id-to-bits-be ((id program-idp))
  :returns (bits bit-listp)
  (append (identifier-to-bits-be (program-id->name id))
          (identifier-to-bits-be (program-id->network id))))

; snarkVM circuit/program/src/id/to_fields.rs: ProgramID::to_fields.
(define program-id-to-fields ((id program-idp))
  :returns (fs values-field-listp)
  (list (identifier-to-field (program-id->name id))
        (identifier-to-field (program-id->network id))))

; snarkVM circuit/program/src/id/to_address.rs: ProgramID::to_address
; (Address::from_group of hash_to_group_psd4 of the name and network fields).
(define program-id-to-address ((id program-idp))
  :returns (address values-group-resultp)
  (values-hash-to-group-psd4 (program-id-to-fields id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function IDs.

; snarkVM circuit/program/src/function_id/mod.rs: compute_function_id
; (hash_bhp1024 of the little-endian bits of the tuple
; (network_id, name size in bits, name, network size in bits, network,
; function name size in bits, function name)).
(define compute-function-id ((network-id ubyte16p)
                             (program-id program-idp)
                             (function-name identifierp))
  :returns (id fieldp)
  (b* ((name (program-id->name program-id))
       (network (program-id->network program-id)))
    (values-hash-bhp1024
     (append (values-int-to-bits-le (acl2::ubyte16-fix network-id) 16)
             (values-int-to-bits-le (identifier-size-in-bits name) 8)
             (identifier-to-bits-le name)
             (values-int-to-bits-le (identifier-size-in-bits network) 8)
             (identifier-to-bits-le network)
             (values-int-to-bits-le (identifier-size-in-bits function-name) 8)
             (identifier-to-bits-le function-name)))))
