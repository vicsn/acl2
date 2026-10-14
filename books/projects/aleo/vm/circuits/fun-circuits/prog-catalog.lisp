; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remaining program-crate circuit functions, smallest wrappers first.
; A gadget whose body is nil and whose :short says the constraints are not
; expanded is intentionally incomplete: its R1CS-SPEC flag is 0.
; Funspec-match lemmas are unconditional equalities of the specifications.

(in-package "ALEOVM")

(include-book "prog-primitives")
(include-book "prog-equal")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/values-value")
(include-book "../fun-specs/values-cast")
(include-book "../fun-specs/values-plaintext")
(include-book "../fun-specs/crypto-record")
(include-book "../fun-specs/crypto-request")
(include-book "../fun-specs/crypto-response")
(include-book "../fun-specs/crypto-state-path")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compute-function-id-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "to_bits_le of the tuple, then BHP1024. Hash abstracted; bit constraints not expanded."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled argument-is-not-equal-funspecs-match
  (implies (and (bitp (argument-is-equal x y)))
           (equal (argument-is-not-equal x y)
                  (boolean-not-funspec (argument-is-equal x y))))
  :hints (("Goal"
           :cases ((values-argument-equalp x y))
           :in-theory (enable argument-is-not-equal argument-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean::cast is cast_lossy, except IdentifierLiteral which casts through Field and always fails."
  nil)

(defruled boolean-cast-funspecs-match
  (equal (boolean-cast b to) (if (literal-type-case to :identifier) (field-cast (bfix b) to) (boolean-cast-lossy b to)))
  :enable boolean-cast)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean::cast_lossy is a ternary between generator/one and zero. No range assert."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-decrypt-symmetric-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-decrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-ciphertext-is-not-equal-funspecs-match
  (equal (crypto-ciphertext-is-not-equal a b) (boolean-not-funspec (crypto-ciphertext-is-equal a b)))
  :hints (("Goal"
           :cases ((equal (crypto-ciphertext-is-equal a b) 0))
           :in-theory (enable crypto-ciphertext-is-not-equal
                              crypto-bit-not
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-from-record-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-merkleize-data-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled dynamic-record-is-not-equal-funspecs-match
  (equal (dynamic-record-is-not-equal x y) (boolean-not-funspec (dynamic-record-is-equal x y)))
  :hints (("Goal"
           :cases ((equal (dynamic-record-is-equal x y) 0))
           :in-theory (enable dynamic-record-is-not-equal
                              values-b-not
                              boolean-not-funspec
                              bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-fields-with-visibility-as-mode-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-write-bits-le-with-visibility-as-mode-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled entry-is-not-equal-funspecs-match
  (implies (and (bitp (entry-is-equal x y)))
           (equal (entry-is-not-equal x y)
                  (boolean-not-funspec (entry-is-equal x y))))
  :hints (("Goal"
           :cases ((values-entry-equalp x y))
           :in-theory (enable entry-is-not-equal entry-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Field::cast dispatches on the destination. Boolean asserts zero-or-one. Integer and scalar assert a range. Address and group recover the unique subgroup point."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Field::cast_lossy takes the low bits, the LSB, or Elligator2 / the subgroup point. No ordering constraint beyond the unique subgroup point."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled future-is-not-equal-funspecs-match
  (implies (and (bitp (future-is-equal x y)))
           (equal (future-is-not-equal x y)
                  (boolean-not-funspec (future-is-equal x y))))
  :hints (("Goal"
           :cases ((values-future-equalp x y))
           :in-theory (enable future-is-not-equal future-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define header-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define header-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled identifier-from-bits-be-funspecs-match
  (equal (identifier-from-bits-be bits) (identifier-from-bits-le (rev bits)))
  :enable identifier-from-bits-be)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-field-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled identifier-from-field-funspecs-match
  (equal (identifier-from-field x) (identifier-from-bits-le (values-field-to-bits-le x)))
  :enable identifier-from-field)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-literal-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "IdentifierLiteral::cast is to_field then Field::cast."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-input-id-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Integer::cast goes through to_field, which asserts the value is in range, then Field::cast."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Integer::cast_lossy truncates or sign-extends, then Field::cast_lossy for address and group."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-from-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-from-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled literal-is-not-equal-funspecs-match
  (implies (and (bitp (literal-is-equal x y)))
           (equal (literal-is-not-equal x y)
                  (boolean-not-funspec (literal-is-equal x y))))
  :hints (("Goal"
           :cases ((values-literal-equalp x y))
           :in-theory (enable literal-is-not-equal literal-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-decrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-to-entry-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-symmetric-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bit-array-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bits-be-internal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Same as the little-endian parser, caching the raw big-endian bits. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bits-le-internal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Parses a variant prefix and caches the raw input bits in a OnceCell. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Forwards to size_in_fields."
  nil)

(defruled plaintext-num-randomizers-funspecs-match
  (equal (plaintext-num-randomizers pt) (plaintext-size-in-fields pt))
  :enable plaintext-num-randomizers)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled plaintext-is-not-equal-funspecs-match
  (implies (and (bitp (plaintext-is-equal x y)))
           (equal (plaintext-is-not-equal x y)
                  (boolean-not-funspec (plaintext-is-equal x y))))
  :hints (("Goal"
           :cases ((values-plaintext-equalp x y))
           :in-theory (enable plaintext-is-not-equal plaintext-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled plaintext-from-funspecs-match
  (equal (plaintext-from fields) (plaintext-from-fields fields))
  :enable plaintext-from)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled plaintext-from-bits-be-funspecs-match
  (equal (plaintext-from-bits-be bits) (plaintext-from-bits-be-internal bits 0))
  :enable plaintext-from-bits-be)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled plaintext-from-bits-le-funspecs-match
  (equal (plaintext-from-bits-le bits) (plaintext-from-bits-le-internal bits 0))
  :enable plaintext-from-bits-le)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Returns the OnceCell cache when the plaintext was built by from_bits; otherwise recomputes. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Returns the OnceCell cache when the plaintext was built by from_bits; otherwise recomputes. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Packs to_bits_le, so a cached raw bitstring is packed instead of the recomputed encoding."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-fields-raw-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Packs raw literal bits. Does not use the from_bits cache."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-size-in-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Host u16, ceiling of (len(to_bits_le)+1)/252. The length follows the cache."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-decrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-decrypt-symmetric-unchecked-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-decrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-record-encrypt-funspecs-match
  (equal (crypto-record-encrypt r randomizer) (b* (((fty::ok res) (crypto-record-encrypt-symmetric r randomizer))) (crypto-ciphertext-record-fix (first res))))
  :enable crypto-record-encrypt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-symmetric-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-symmetric-unchecked-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-serial-number-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-serial-number-from-gamma-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-to-commitment-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-record-is-not-equal-funspecs-match
  (equal (crypto-record-is-not-equal a b) (boolean-not-funspec (crypto-record-is-equal a b)))
  :hints (("Goal"
           :cases ((equal (crypto-record-is-equal a b) 0))
           :in-theory (enable crypto-record-is-not-equal
                              crypto-bit-not
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-check-input-ids-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Per-input equality and hash checks. Hash and encryption abstracted."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-to-tpk-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Group scalar multiplication and addition. Edwards formulas are not expanded here."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-verify-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean conjunction of input-id, root, and checksum checks. Hashes abstracted."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-response-from-outputs-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Per-output hash (abstract) and OutputID constructors, including the record disjunction."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-response-process-outputs-from-callback-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Same family as from_outputs, with the callback record id."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Scalar::cast asserts 0 or 1 for boolean and a bit-width bound for integers."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Scalar::cast_lossy takes the low bits. Address and group use Field::cast_lossy."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-state-path-verify-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Merkle path checks (BHP/PSD abstracted) conjoined with boolean ANDs."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transaction-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transaction-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transition-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transition-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled value-is-not-equal-funspecs-match
  (implies (and (bitp (value-is-equal x y)))
           (equal (value-is-not-equal x y)
                  (boolean-not-funspec (value-is-equal x y))))
  :hints (("Goal"
           :cases ((values-value-equalp x y))
           :in-theory (enable value-is-not-equal value-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-fields-raw-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)
