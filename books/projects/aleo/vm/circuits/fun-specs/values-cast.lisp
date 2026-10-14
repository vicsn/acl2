; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FUN-SPECs of the literal casts of the circuit program crate
; (snarkVM circuit/program/src/data/literal/cast and cast_lossy).
;
; Each Rust trait impl family Cast<T> / CastLossy<T> for a source type is
; specified by one function parameterized by the target literal type T,
; returning the literal of type T, or (spec-error) when the circuit halts or
; is unsatisfiable.  Target types without an impl (signature, string, and
; identifier for CastLossy) return (spec-error), as Literal::cast and
; Literal::cast_lossy bail on them.

(in-package "ALEOVM")

(include-book "values-literal")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (enable spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Integer literal types.

(define values-literal-type-integerp ((to literal-typep))
  :returns (yes/no booleanp)
  (and (member-eq (literal-type-kind to)
                  '(:i8 :i16 :i32 :i64 :i128 :u8 :u16 :u32 :u64 :u128))
       t))

(define values-literal-type-signedp ((to literal-typep))
  :returns (yes/no booleanp)
  (and (member-eq (literal-type-kind to) '(:i8 :i16 :i32 :i64 :i128))
       t))

(define values-literal-type-width ((to literal-typep))
  :returns (n posp)
  (case (literal-type-kind to)
    ((:i8 :u8) 8)
    ((:i16 :u16) 16)
    ((:i32 :u32) 32)
    ((:i64 :u64) 64)
    (t 128)))

(define values-integer-literal ((to literal-typep) (x integerp))
  :guard (values-literal-type-integerp to)
  :returns (lit literalp)
  :short "The integer literal of type @('to') with value @('x')
          (always in range where used)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tests of the ranges below only serve guard verification:
     the literal constructors fix out-of-range values to 0 anyway."))
  (case (literal-type-kind to)
    (:i8 (literal-i8 (if (acl2::sbyte8p x) x 0)))
    (:i16 (literal-i16 (if (acl2::sbyte16p x) x 0)))
    (:i32 (literal-i32 (if (acl2::sbyte32p x) x 0)))
    (:i64 (literal-i64 (if (acl2::sbyte64p x) x 0)))
    (:i128 (literal-i128 (if (acl2::sbyte128p x) x 0)))
    (:u8 (literal-u8 (if (acl2::ubyte8p x) x 0)))
    (:u16 (literal-u16 (if (acl2::ubyte16p x) x 0)))
    (:u32 (literal-u32 (if (acl2::ubyte32p x) x 0)))
    (:u64 (literal-u64 (if (acl2::ubyte64p x) x 0)))
    (t (literal-u128 (if (acl2::ubyte128p x) x 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field casts.

; snarkVM circuit/program/src/data/literal/cast/field.rs: Field::cast (Cast<T> for Field, all T;
; Address/Group: from_x_coordinate; Boolean: 0 or 1; Integer: Integer::from_field;
; Scalar: Scalar::from_field; IdentifierLiteral: IdentifierLiteral::from_field).
(define field-cast ((x fieldp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((x (values-field-fix x)))
    (cond
     ((values-literal-type-integerp to)
      (b* (((fty::ok i) (values-int-from-field x
                                               (values-literal-type-signedp to)
                                               (values-literal-type-width to))))
        (values-integer-literal to i)))
     (t
      (literal-type-case
       to
       :address (b* (((fty::ok g) (values-group-from-x x))) (literal-address g))
       :boolean (if (or (equal x 0) (equal x 1))
                    (literal-boolean x)
                  (spec-error))
       :field (literal-field x)
       :group (b* (((fty::ok g) (values-group-from-x x))) (literal-group g))
       :scalar (b* (((fty::ok s) (values-scalar-from-field x))) (literal-scalar s))
       :identifier (b* (((fty::ok id) (identifier-literal-from-field x)))
                     (literal-identifier id))
       :otherwise (spec-error))))))

; snarkVM circuit/program/src/data/literal/cast_lossy/field.rs: CastLossy<Group> for Field
; (the subgroup point with x-coordinate x if any; else the generator if x = 1;
; else Elligator2::encode of x, or of 1 if x = 0).
(define values-field-cast-lossy-to-group ((x fieldp))
  :returns (g groupp)
  (b* ((x (values-field-fix x)))
    (cond ((values-x-in-subgroupp x)
           (values-to-group
            (ecurve::point-finite x (values-x-in-subgroupp-witness x))))
          ((equal x 1) (values-group-generator))
          (t (elligator2-encode (if (equal x 0) 1 x)))))
  :guard-hints (("Goal" :in-theory (enable values-x-in-subgroupp))))

; snarkVM circuit/program/src/data/literal/cast_lossy/field.rs: Field::cast_lossy (CastLossy<T> for Field;
; Boolean: least significant bit; Integer: Integer::from_field_lossy (low bits);
; Scalar: Scalar::from_field_lossy).
(define field-cast-lossy ((x fieldp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((x (values-field-fix x)))
    (cond
     ((values-literal-type-integerp to)
      (b* ((n (values-literal-type-width to)))
        (values-integer-literal
         to
         (values-int-of-unsigned (mod x (expt 2 n))
                                 (values-literal-type-signedp to)
                                 n))))
     (t
      (literal-type-case
       to
       :address (literal-address (values-field-cast-lossy-to-group x))
       :boolean (literal-boolean (mod x 2))
       :field (literal-field x)
       :group (literal-group (values-field-cast-lossy-to-group x))
       :scalar (literal-scalar (values-scalar-from-field-lossy x))
       :otherwise (spec-error))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group and address casts (helpers of Literal::cast / Literal::cast_lossy).

; snarkVM circuit/program/src/data/literal/cast/mod.rs: cast_group_to_type.
(define values-group-cast ((g groupp) (to literal-typep))
  :returns (r literal-resultp)
  (literal-type-case
   to
   :address (literal-address g)
   :group (literal-group g)
   :otherwise (field-cast (values-group-x g) to)))

; snarkVM circuit/program/src/data/literal/cast_lossy/mod.rs: cast_lossy_group_to_type.
(define values-group-cast-lossy ((g groupp) (to literal-typep))
  :returns (r literal-resultp)
  (literal-type-case
   to
   :address (literal-address g)
   :group (literal-group g)
   :otherwise (field-cast-lossy (values-group-x g) to)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean casts.

; snarkVM circuit/program/src/data/literal/cast_lossy/boolean.rs: Boolean::cast_lossy (CastLossy<T> for Boolean;
; Address/Group: generator if true, zero if false; numbers: 1 or 0).
(define boolean-cast-lossy ((b bitp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((b (bfix b)))
    (cond
     ((values-literal-type-integerp to) (values-integer-literal to b))
     (t
      (literal-type-case
       to
       :address (literal-address (if (equal b 1) (values-group-generator) (values-group-zero)))
       :boolean (literal-boolean b)
       :field (literal-field b)
       :group (literal-group (if (equal b 1) (values-group-generator) (values-group-zero)))
       :scalar (literal-scalar b)
       :otherwise (spec-error)))))
  :prepwork ((local (in-theory (enable bitp values-fieldp-when-bounded
                                       values-scalarp-when-bounded)))))

; snarkVM circuit/program/src/data/literal/cast/boolean.rs: Boolean::cast (Cast<T> for Boolean:
; cast_lossy, except IdentifierLiteral: Field cast of the boolean, which always fails).
(define boolean-cast ((b bitp) (to literal-typep))
  :returns (r literal-resultp)
  (if (literal-type-case to :identifier)
      (field-cast (bfix b) to)
    (boolean-cast-lossy b to))
  :prepwork ((local (in-theory (enable bitp values-fieldp-when-bounded)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Integer casts.
;; The source integer has value x and width n (its signedness does not
;; affect the results, given the value).

; snarkVM circuit/program/src/data/literal/cast/integer.rs: Integer::cast (Cast<T> for Integer<I>;
; Address/Group/IdentifierLiteral: Field cast of to_field; Boolean: 0 or 1;
; Field: to_field; Integer<I1>: the same value, which must be in range of I1;
; Scalar: Scalar::from_bits_le of the bits, i.e. the unsigned reading).
(define integer-cast ((x integerp) (n posp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((x (ifix x))
       (u (values-int-to-field x n)))
    (cond
     ((values-literal-type-integerp to)
      (if (int-valuep x
                      (values-literal-type-signedp to)
                      (values-literal-type-width to))
          (values-integer-literal to x)
        (spec-error)))
     (t
      (literal-type-case
       to
       :boolean (if (or (equal x 0) (equal x 1))
                    (literal-boolean x)
                  (spec-error))
       :field (literal-field u)
       :scalar (literal-scalar u)
       :signature (spec-error)
       :string (spec-error)
       :otherwise (field-cast u to)))))
  :guard (<= n 128)
  :prepwork ((local (in-theory (enable values-fieldp-when-bounded
                                       values-scalarp-when-bounded
)))))

; snarkVM circuit/program/src/data/literal/cast_lossy/integer.rs: Integer::cast_lossy (CastLossy<T> for Integer<I>;
; Address/Group: Field cast_lossy of to_field; Boolean: least significant bit;
; Field: to_field; Integer<I1>: sign/zero-extend or truncate to I1;
; Scalar: to_scalar, the unsigned reading).
(define integer-cast-lossy ((x integerp) (n posp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((x (ifix x))
       (u (values-int-to-field x n)))
    (cond
     ((values-literal-type-integerp to)
      (values-integer-literal to (int-wrap x
                                           (values-literal-type-signedp to)
                                           (values-literal-type-width to))))
     (t
      (literal-type-case
       to
       :address (literal-address (values-field-cast-lossy-to-group u))
       :boolean (literal-boolean (mod x 2))
       :field (literal-field u)
       :group (literal-group (values-field-cast-lossy-to-group u))
       :scalar (literal-scalar u)
       :otherwise (spec-error)))))
  :guard (<= n 128)
  :prepwork ((local (in-theory (enable values-fieldp-when-bounded
                                       values-scalarp-when-bounded
)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Scalar casts.

; snarkVM circuit/program/src/data/literal/cast/scalar.rs: Scalar::cast (Cast<T> for Scalar;
; Address/Group/IdentifierLiteral: Field cast of the scalar; Boolean: 0 or 1;
; Integer: Integer::from_bits_le of the 251 bits, i.e. below 2^n, two's complement).
(define scalar-cast ((s scalarp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((s (values-scalar-fix s)))
    (cond
     ((values-literal-type-integerp to)
      (b* ((n (values-literal-type-width to)))
        (if (< s (expt 2 n))
            (values-integer-literal
             to (values-int-of-unsigned s (values-literal-type-signedp to) n))
          (spec-error))))
     (t
      (literal-type-case
       to
       :boolean (if (or (equal s 0) (equal s 1))
                    (literal-boolean s)
                  (spec-error))
       :field (literal-field s)
       :scalar (literal-scalar s)
       :signature (spec-error)
       :string (spec-error)
       :otherwise (field-cast s to)))))
  :prepwork ((local (in-theory (enable bitp)))))

; snarkVM circuit/program/src/data/literal/cast_lossy/scalar.rs: Scalar::cast_lossy (CastLossy<T> for Scalar;
; Address/Group: Field cast_lossy; Boolean: least significant bit;
; Integer: the low n bits, two's complement).
(define scalar-cast-lossy ((s scalarp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((s (values-scalar-fix s)))
    (cond
     ((values-literal-type-integerp to)
      (b* ((n (values-literal-type-width to)))
        (values-integer-literal
         to (values-int-of-unsigned (mod s (expt 2 n))
                                    (values-literal-type-signedp to)
                                    n))))
     (t
      (literal-type-case
       to
       :address (literal-address (values-field-cast-lossy-to-group s))
       :boolean (literal-boolean (mod s 2))
       :field (literal-field s)
       :group (literal-group (values-field-cast-lossy-to-group s))
       :scalar (literal-scalar s)
       :otherwise (spec-error))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier literal casts.

; snarkVM circuit/program/src/data/literal/cast/identifier.rs: IdentifierLiteral::cast (Cast<T> for IdentifierLiteral;
; Field: to_field; IdentifierLiteral: itself; otherwise the Field cast of to_field).
(define identifier-literal-cast ((id identifier-literalp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((f (identifier-literal-to-field id)))
    (literal-type-case
     to
     :field (literal-field f)
     :identifier (literal-identifier id)
     :signature (spec-error)
     :string (spec-error)
     :otherwise (field-cast f to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal casts.

(define values-literal-int-width ((x literalp))
  :returns (n posp)
  (literal-case x
                :i8 8 :i16 16 :i32 32 :i64 64
                :u8 8 :u16 16 :u32 32 :u64 64
                :otherwise 128))

(define values-literal-int-value ((x literalp))
  :returns (i integerp)
  (literal-case x
                :i8 x.get :i16 x.get :i32 x.get :i64 x.get :i128 x.get
                :u8 x.get :u16 x.get :u32 x.get :u64 x.get :u128 x.get
                :otherwise 0))

; snarkVM circuit/program/src/data/literal/cast/mod.rs: Literal::cast.
(define literal-cast ((x literalp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((n (values-literal-int-width x)))
    (literal-case
     x
     :address (values-group-cast x.get to)
     :boolean (boolean-cast x.get to)
     :field (field-cast x.get to)
     :group (values-group-cast x.get to)
     :scalar (scalar-cast x.get to)
     :signature (spec-error)
     :string (spec-error)
     :identifier (identifier-literal-cast x.get to)
     :otherwise (integer-cast (values-literal-int-value x) n to)))
  :guard-hints (("Goal" :in-theory (enable values-literal-int-width))))

; snarkVM circuit/program/src/data/literal/cast_lossy/mod.rs: Literal::cast_lossy.
(define literal-cast-lossy ((x literalp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((n (values-literal-int-width x)))
    (literal-case
     x
     :address (values-group-cast-lossy x.get to)
     :boolean (boolean-cast-lossy x.get to)
     :field (field-cast-lossy x.get to)
     :group (values-group-cast-lossy x.get to)
     :scalar (scalar-cast-lossy x.get to)
     :signature (spec-error)
     :string (spec-error)
     :identifier (spec-error)
     :otherwise (integer-cast-lossy (values-literal-int-value x) n to)))
  :guard-hints (("Goal" :in-theory (enable values-literal-int-width))))
