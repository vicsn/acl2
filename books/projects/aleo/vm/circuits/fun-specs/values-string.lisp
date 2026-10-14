; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FUN-SPECs of the circuit string types (snarkVM circuit/types/string):
; StringType, IdentifierLiteral, and the identifier byte validation helpers.
;
; Unit-returning validation functions return t when the constraints are
; satisfiable and (spec-error) otherwise.

(in-package "ALEOVM")

(include-book "values-helpers")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean gates on bits (snarkVM circuit/types/boolean: and, or, xor, not).

(define values-b-and ((a bitp) (b bitp))
  :returns (c bitp)
  (if (and (equal (bfix a) 1) (equal (bfix b) 1)) 1 0))

(define values-b-or ((a bitp) (b bitp))
  :returns (c bitp)
  (if (or (equal (bfix a) 1) (equal (bfix b) 1)) 1 0))

(define values-b-xor ((a bitp) (b bitp))
  :returns (c bitp)
  (if (equal (bfix a) (bfix b)) 0 1))

(define values-b-not ((a bitp))
  :returns (c bitp)
  (if (equal (bfix a) 1) 0 1))

(define values-unit-resultp (x)
  :short "Result of unit-returning functions: @('t') or an error."
  (or (eq x t) (reserrp x))
  ///
  (defrule values-unit-resultp-of-t
    (values-unit-resultp t))
  (defrule values-unit-resultp-when-reserrp
    (implies (reserrp x) (values-unit-resultp x))))

(local (in-theory (enable spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier byte validation (identifier_literal/mod.rs).

(fty::defprod byte-validation-data
  ((b4b3 bit)
   (b1b0 bit)
   (all-zero-5 bit))
  :tag :byte-validation-data
  :pred byte-validation-datap)

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: ByteValidationData::new.
(define byte-validation-data-new ((b0 bitp) (b1 bitp) (b2 bitp) (b3 bitp) (b4 bitp))
  :returns (data byte-validation-datap)
  (make-byte-validation-data
   :b4b3 (values-b-and b4 b3)
   :b1b0 (values-b-and b1 b0)
   :all-zero-5 (values-bool-to-bit
                (equal (+ (bfix b0) (bfix b1) (bfix b2) (bfix b3) (bfix b4)) 0))))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: is_invalid_digit_offset.
(define is-invalid-digit-offset ((b1 bitp) (b2 bitp) (b3 bitp))
  :returns (bit bitp)
  (values-b-and b3 (values-b-or b2 b1)))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: is_invalid_uppercase_offset.
(define is-invalid-uppercase-offset ((data byte-validation-datap) (b2 bitp))
  :returns (bit bitp)
  (values-b-and (byte-validation-data->b4b3 data)
                (values-b-xor b2 (byte-validation-data->b1b0 data))))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: is_invalid_lowercase_offset.
(define is-invalid-lowercase-offset ((data byte-validation-datap) (b2 bitp))
  :returns (bit bitp)
  (values-b-and (byte-validation-data->b4b3 data)
                (values-b-or b2 (byte-validation-data->b1b0 data))))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: validate_byte.
; Input: the 8 little-endian bits of the byte; output: the null flag.
; Each check below is one constraint of the circuit, in the same order.
(define validate-byte ((bits bit-listp) (first-byte-p booleanp))
  :guard (equal (len bits) 8)
  :returns (null-flag values-bit-resultp)
  (b* ((b0 (bfix (nth 0 bits))) (b1 (bfix (nth 1 bits)))
       (b2 (bfix (nth 2 bits))) (b3 (bfix (nth 3 bits)))
       (b4 (bfix (nth 4 bits))) (b5 (bfix (nth 5 bits)))
       (b6 (bfix (nth 6 bits))) (b7 (bfix (nth 7 bits)))
       ((unless (equal b7 0)) (spec-error))
       (data (byte-validation-data-new b0 b1 b2 b3 b4))
       (all-zero-5 (byte-validation-data->all-zero-5 data))
       (null (values-b-and (values-b-not b6) (values-b-not b5)))
       (lower (values-b-and b6 b5))
       (upper-lc (- b6 lower))
       (digit-lc (- b5 lower))
       (any-low5 (values-b-not all-zero-5))
       ((unless (equal (* null any-low5) 0)) (spec-error))
       (invalid-digit (is-invalid-digit-offset b1 b2 b3))
       ((unless (equal (* digit-lc (+ (- 1 b4) invalid-digit)) 0)) (spec-error))
       (bad-upper (is-invalid-uppercase-offset data b2))
       ((unless (equal (* upper-lc (+ all-zero-5 bad-upper)) 0)) (spec-error))
       (bad-lower (is-invalid-lowercase-offset data b2))
       ((unless (equal (* lower (+ all-zero-5 bad-lower)) 0)) (spec-error))
       ((when (and first-byte-p
                   (b* ((partial (values-b-and (byte-validation-data->b4b3 data)
                                               (byte-validation-data->b1b0 data)))
                        (is-underscore-offset (values-b-and partial b2))
                        (is-letter (values-b-and b6 (values-b-not is-underscore-offset))))
                     (not (equal is-letter 1)))))
        (spec-error)))
    null))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: validate_trailing_nulls.
(define validate-trailing-nulls ((null-flags bit-listp))
  :returns (r values-unit-resultp)
  (b* (((when (or (endp null-flags) (endp (cdr null-flags)))) t)
       ((unless (equal (* (bfix (car null-flags))
                          (values-b-not (cadr null-flags)))
                       0))
        (spec-error)))
    (validate-trailing-nulls (cdr null-flags))))

(define values-validate-bytes-null-flags ((bytes acl2::ubyte8-listp) (first-byte-p booleanp))
  :returns (flags bit-list-resultp)
  (b* (((when (endp bytes)) nil)
       ((fty::ok flag)
        (validate-byte (values-nat-to-lebits 8 (acl2::ubyte8-fix (car bytes))) first-byte-p))
       ((fty::ok flags) (values-validate-bytes-null-flags (cdr bytes) nil)))
    (cons flag flags)))

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: validate_identifier_bytes
; (via validate_identifier_bits; the bytes are the 31 bytes of the literal).
(define validate-identifier-bytes ((bytes acl2::ubyte8-listp))
  :returns (r values-unit-resultp)
  (b* (((fty::ok flags) (values-validate-bytes-null-flags bytes t)))
    (validate-trailing-nulls flags)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; IdentifierLiteral.

; snarkVM circuit/types/string/src/identifier_literal/mod.rs: IdentifierLiteral::new (Inject; from_bytes).
(define identifier-literal-new ((x identifier-literalp))
  :returns (r identifier-literal-resultp)
  (b* (((fty::ok -) (validate-identifier-bytes (identifier-literal->bytes x))))
    (identifier-literal-fix x)))

(define values-bits-all-zero-p ((bits bit-listp))
  :returns (yes/no booleanp)
  (or (endp bits)
      (and (equal (bfix (car bits)) 0)
           (values-bits-all-zero-p (cdr bits)))))

; snarkVM circuit/types/string/src/identifier_literal/helpers/from_bits.rs: IdentifierLiteral::from_bits_le.
(define identifier-literal-from-bits-le ((bits bit-listp))
  :returns (r identifier-literal-resultp)
  (b* (((unless (or (<= (len bits) 248)
                    (values-bits-all-zero-p (nthcdr 248 bits))))
        (spec-error))
       (padded (values-bits-resize bits 248))
       (bytes (values-lebits-to-bytes padded)))
    (identifier-literal-new (make-identifier-literal :bytes bytes))))

; snarkVM circuit/types/string/src/identifier_literal/helpers/from_bits.rs: IdentifierLiteral::from_bits_be.
(define identifier-literal-from-bits-be ((bits bit-listp))
  :returns (r identifier-literal-resultp)
  (identifier-literal-from-bits-le (rev bits)))

; snarkVM circuit/types/string/src/identifier_literal/helpers/from_field.rs: IdentifierLiteral::from_field.
(define identifier-literal-from-field ((x fieldp))
  :returns (r identifier-literal-resultp)
  (identifier-literal-from-bits-le (values-field-to-bits-le x)))

; snarkVM circuit/types/string/src/identifier_literal/helpers/to_bits.rs: IdentifierLiteral::write_bits_le.
(define identifier-literal-to-bits-le ((x identifier-literalp))
  :returns (bits bit-listp)
  (values-bytes-to-lebits (identifier-literal->bytes x)))

; snarkVM circuit/types/string/src/identifier_literal/helpers/to_bits.rs: IdentifierLiteral::write_bits_be.
(define identifier-literal-to-bits-be ((x identifier-literalp))
  :returns (bits bit-listp)
  (rev (identifier-literal-to-bits-le x)))

; snarkVM circuit/types/string/src/identifier_literal/helpers/to_field.rs: IdentifierLiteral::to_field
; (248 bits, so the reduction in values-lebits-to-field is the identity).
(define identifier-literal-to-field ((x identifier-literalp))
  :returns (f fieldp)
  (values-lebits-to-field (identifier-literal-to-bits-le x)))

; snarkVM circuit/types/string/src/identifier_literal/helpers/to_fields.rs: IdentifierLiteral::to_fields.
(define identifier-literal-to-fields ((x identifier-literalp))
  :returns (fs values-field-listp)
  (list (identifier-literal-to-field x)))

; snarkVM circuit/types/string/src/identifier_literal/equal.rs: IdentifierLiteral::is_equal.
(define identifier-literal-is-equal ((x identifier-literalp) (y identifier-literalp))
  :returns (b bitp)
  (values-bool-to-bit (equal (identifier-literal-to-field x)
                             (identifier-literal-to-field y))))

; snarkVM circuit/types/string/src/identifier_literal/equal.rs: IdentifierLiteral::is_not_equal.
(define identifier-literal-is-not-equal ((x identifier-literalp) (y identifier-literalp))
  :returns (b bitp)
  (values-bool-to-bit (not (equal (identifier-literal-to-field x)
                                  (identifier-literal-to-field y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; StringType.
;; The circuit also stores size_in_bytes, a field element that every
;; constructor sets to the number of bytes; it is the length of the bytes here.

; snarkVM circuit/types/string/src/lib.rs: StringType::new (Inject; halts if the length does not fit in u32).
(define string-type-new ((s string-typep))
  :returns (r string-type-resultp)
  (if (< (len (string-type->bytes s)) (expt 2 32))
      (string-type-fix s)
    (spec-error)))

; snarkVM circuit/types/string/src/helpers/from_bits.rs: StringType::inject_size_in_bytes.
(define string-type-inject-size-in-bytes ((bits bit-listp))
  :returns (size values-field-resultp
                 :hints (("Goal" :in-theory (enable values-fieldp-when-bounded))))
  (b* ((n (len bits))
       ((unless (equal (mod n 8) 0)) (spec-error))
       (k (floor n 8))
       ((unless (< k (expt 2 32))) (spec-error)))
    k))

; snarkVM circuit/types/string/src/helpers/from_bits.rs: StringType::from_bits_le.
(define string-type-from-bits-le ((bits bit-listp))
  :returns (r string-type-resultp)
  (b* (((fty::ok -) (string-type-inject-size-in-bytes bits)))
    (make-string-type :bytes (values-lebits-to-bytes bits))))

; snarkVM circuit/types/string/src/helpers/from_bits.rs: StringType::from_bits_be.
(define string-type-from-bits-be ((bits bit-listp))
  :returns (r string-type-resultp)
  (b* (((fty::ok -) (string-type-inject-size-in-bytes bits)))
    (make-string-type :bytes (values-bebits-to-bytes bits))))

; snarkVM circuit/types/string/src/helpers/to_bits.rs: StringType::write_bits_le.
(define string-type-to-bits-le ((s string-typep))
  :returns (bits bit-listp)
  (values-bytes-to-lebits (string-type->bytes s)))

; snarkVM circuit/types/string/src/helpers/to_bits.rs: StringType::write_bits_be.
(define string-type-to-bits-be ((s string-typep))
  :returns (bits bit-listp)
  (values-bytes-to-bebits (string-type->bytes s)))

; snarkVM circuit/types/string/src/helpers/to_fields.rs: StringType::to_fields.
(define string-type-to-fields ((s string-typep))
  :returns (fs values-field-listp)
  (values-pack-bits (string-type-to-bits-le s)))

(define values-field-lists-zip-equal ((xs values-field-listp) (ys values-field-listp))
  :returns (yes/no booleanp)
  :short "Rust @('xs.iter().zip(ys)') folded with field equality."
  (or (endp xs)
      (endp ys)
      (and (equal (values-field-fix (car xs)) (values-field-fix (car ys)))
           (values-field-lists-zip-equal (cdr xs) (cdr ys)))))

; snarkVM circuit/types/string/src/equal.rs: StringType::is_equal.
(define string-type-is-equal ((s string-typep) (u string-typep))
  :returns (b bitp)
  (values-bool-to-bit
   (and (equal (len (string-type->bytes s)) (len (string-type->bytes u)))
        (values-field-lists-zip-equal (string-type-to-fields s)
                                      (string-type-to-fields u)))))

; snarkVM circuit/types/string/src/equal.rs: StringType::is_not_equal.
(define string-type-is-not-equal ((s string-typep) (u string-typep))
  :returns (b bitp)
  (values-b-not (string-type-is-equal s u)))
