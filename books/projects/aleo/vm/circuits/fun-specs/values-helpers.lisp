; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helpers for the specs of the values-*.lisp books:
; network constants, bit and byte encodings, and the value-level behavior of
; the Boolean/Field/Scalar/Integer/Group operations that the program and
; string crates call (circuit/types/*), defined locally on top of base.lisp.
;
; Naming: helpers are prefixed with 'values-' to avoid clashes with the
; books of the other spec authors in this directory.

(in-package "ALEOVM")

(include-book "values-model")
(include-book "std/lists/rev" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(in-theory (enable
           argument-listp-when-result-not-error
           argumentp-when-result-not-error
           bit-listp-when-result-not-error
           bitp-when-result-not-error
           dynamic-futurep-when-result-not-error
           dynamic-recordp-when-result-not-error
           entryp-when-result-not-error
           fieldp-when-result-not-error
           futurep-when-result-not-error
           groupp-when-result-not-error
           identifier-literalp-when-result-not-error
           identifierp-when-result-not-error
           integerp-when-result-not-error
           literalp-when-result-not-error
           not-reserrp-when-argument-listp
           not-reserrp-when-argumentp
           not-reserrp-when-bit-listp
           not-reserrp-when-bitp
           not-reserrp-when-dynamic-futurep
           not-reserrp-when-dynamic-recordp
           not-reserrp-when-entryp
           not-reserrp-when-fieldp
           not-reserrp-when-futurep
           not-reserrp-when-groupp
           not-reserrp-when-identifier-literalp
           not-reserrp-when-identifierp
           not-reserrp-when-integerp
           not-reserrp-when-literalp
           not-reserrp-when-ownerp
           not-reserrp-when-plaintext-listp
           not-reserrp-when-plaintext-member-listp
           not-reserrp-when-plaintextp
           not-reserrp-when-record-entry-listp
           not-reserrp-when-recordp
           not-reserrp-when-scalarp
           not-reserrp-when-string-typep
           not-reserrp-when-valuep
           not-reserrp-when-values-field-listp
           ownerp-when-result-not-error
           plaintext-listp-when-result-not-error
           plaintext-member-listp-when-result-not-error
           plaintextp-when-result-not-error
           record-entry-listp-when-result-not-error
           recordp-when-result-not-error
           scalarp-when-result-not-error
           string-typep-when-result-not-error
           valuep-when-result-not-error
           values-field-listp-when-result-not-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Network constants.

; snarkVM Field::size_in_data_bits() = 252.
(define values-field-data-bits ()
  :returns (n posp)
  252)

; snarkVM Scalar::size_in_data_bits() = 250.
(define values-scalar-data-bits ()
  :returns (n posp)
  250)

; snarkVM console/network/src/lib.rs: MAX_DATA_SIZE_IN_FIELDS = (128 * 1024 * 8) / 252.
(define values-max-data-size-in-fields ()
  :returns (n natp)
  (floor (* 128 1024 8) 252))

; snarkVM console/network/src/lib.rs: MAX_DATA_DEPTH = 32.
(define values-max-data-depth ()
  :returns (n natp)
  32)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic facts.

(defrule values-base-prime-bounds
  (and (< (expt 2 252) (base-prime))
       (< (base-prime) (expt 2 253)))
  :rule-classes nil
  :enable (base-prime (:e ecurve::edwards-bls12-q)))

(defrule values-scalar-prime-bounds
  (and (< (expt 2 250) (scalar-prime))
       (< (scalar-prime) (expt 2 251)))
  :rule-classes nil
  :enable (scalar-prime (:e ecurve::edwards-bls12-r)))

(defrule values-natp-when-fieldp
  (implies (fieldp x) (natp x))
  :rule-classes (:rewrite :forward-chaining)
  :enable (fieldp pfield::fep))

(defrule values-field-upper-bound
  (implies (fieldp x) (< x (base-prime)))
  :rule-classes :forward-chaining
  :enable (fieldp pfield::fep))

(defrule values-fieldp-when-bounded
  (implies (and (natp x) (< x (base-prime)))
           (fieldp x))
  :enable (fieldp pfield::fep))

(defrule values-natp-when-scalarp
  (implies (scalarp x) (natp x))
  :rule-classes (:rewrite :forward-chaining)
  :enable (scalarp pfield::fep))

(defrule values-scalar-upper-bound
  (implies (scalarp x) (< x (scalar-prime)))
  :rule-classes :forward-chaining
  :enable (scalarp pfield::fep))

(defrule values-scalarp-when-bounded
  (implies (and (natp x) (< x (scalar-prime)))
           (scalarp x))
  :enable (scalarp pfield::fep))

(defrule values-natp-of-values-field-fix
  (natp (values-field-fix x))
  :rule-classes :type-prescription
  :use (:instance values-natp-when-fieldp (x (values-field-fix x))))

(defrule values-natp-of-values-scalar-fix
  (natp (values-scalar-fix x))
  :rule-classes :type-prescription
  :use (:instance values-natp-when-scalarp (x (values-scalar-fix x))))

(defrule values-fieldp-when-scalarp
  (implies (scalarp x) (fieldp x))
  :enable (scalarp fieldp pfield::fep scalar-prime base-prime
           (:e ecurve::edwards-bls12-q) (:e ecurve::edwards-bls12-r)))

(defrule values-edwards-bls12-pointp-when-groupp
  (implies (groupp x) (ecurve::edwards-bls12-pointp x))
  :enable groupp)

(defrule values-lebits=>nat-upper-bound
  (< (lebits=>nat bits) (expt 2 (len bits)))
  :rule-classes ((:linear :trigger-terms ((lebits=>nat bits))))
  :enable lebits=>nat
  :use (:instance acl2::lendian=>nat-upper-bound (base 2) (digits bits)))

(defrule values-bit-listp-of-rev
  (implies (bit-listp x) (bit-listp (rev x)))
  :enable (bit-listp rev))

(defrule values-bit-listp-of-append
  (implies (and (bit-listp x) (bit-listp y))
           (bit-listp (append x y)))
  :enable bit-listp)

(defrule values-bit-listp-of-take
  (implies (and (bit-listp x) (<= (nfix n) (len x)))
           (bit-listp (take n x)))
  :enable bit-listp)

(defrule values-bit-listp-of-nthcdr
  (implies (bit-listp x) (bit-listp (nthcdr n x)))
  :enable bit-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bit sequences.

(define values-nat-to-lebits ((n natp) (x integerp))
  :returns (bits bit-listp)
  :short "Little-endian bits of width @('n') of @('x') modulo @($2^n$)."
  (acl2::nat=>lebits n (mod (ifix x) (expt 2 (nfix n))))
  ///
  (defret len-of-values-nat-to-lebits
    (equal (len bits) (nfix n))))

(define values-nat-to-bebits ((n natp) (x integerp))
  :returns (bits bit-listp)
  :short "Big-endian bits of width @('n') of @('x') modulo @($2^n$)."
  (rev (values-nat-to-lebits n x))
  ///
  (defret len-of-values-nat-to-bebits
    (equal (len bits) (nfix n))))

(define values-bits-resize ((bits bit-listp) (n natp))
  :returns (bits1 bit-listp)
  :short "Rust @('Vec::resize(n, false)'): truncate or pad with zeros."
  (if (zp n)
      nil
    (cons (if (consp bits) (bfix (car bits)) 0)
          (values-bits-resize (if (consp bits) (cdr bits) nil) (1- n))))
  ///
  (defret len-of-values-bits-resize
    (equal (len bits1) (nfix n))))

(define values-bits-chunks ((bits bit-listp) (k posp))
  :returns (chunks true-listp)
  :short "Rust @('slice::chunks(k)'): the last chunk may be shorter."
  :measure (len bits)
  (if (or (endp bits) (not (mbt (posp k))))
      nil
    (cons (take (min (len bits) k) bits)
          (values-bits-chunks (nthcdr k bits) k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bytes (U8 values) and their bits.

; snarkVM Integer<U8>::write_bits_le (8 little-endian bits).
(define values-bytes-to-lebits ((bytes acl2::ubyte8-listp))
  :returns (bits bit-listp)
  (if (endp bytes)
      nil
    (append (values-nat-to-lebits 8 (acl2::ubyte8-fix (car bytes)))
            (values-bytes-to-lebits (cdr bytes))))
  ///
  (defret len-of-values-bytes-to-lebits
    (equal (len bits) (* 8 (len bytes)))))

; snarkVM [U8]::write_bits_be (each byte big-endian, in byte order).
(define values-bytes-to-bebits ((bytes acl2::ubyte8-listp))
  :returns (bits bit-listp)
  (if (endp bytes)
      nil
    (append (values-nat-to-bebits 8 (acl2::ubyte8-fix (car bytes)))
            (values-bytes-to-bebits (cdr bytes))))
  ///
  (defret len-of-values-bytes-to-bebits
    (equal (len bits) (* 8 (len bytes)))))

(defrule values-ubyte8p-of-lebits=>nat
  (implies (<= (len bits) 8)
           (ubyte8p (lebits=>nat bits)))
  :enable ubyte8p
  :use values-lebits=>nat-upper-bound
  :disable values-lebits=>nat-upper-bound)

; snarkVM bits.chunks(8).map(U8::from_bits_le) on byte-aligned bits.
(define values-lebits-to-bytes ((bits bit-listp))
  :returns (bytes acl2::ubyte8-listp)
  :measure (len bits)
  (if (endp bits)
      nil
    (cons (lebits=>nat (take (min (len bits) 8) bits))
          (values-lebits-to-bytes (nthcdr 8 bits)))))

; snarkVM bits.chunks(8).map(U8::from_bits_be) on byte-aligned bits.
(define values-bebits-to-bytes ((bits bit-listp))
  :returns (bytes acl2::ubyte8-listp)
  :measure (len bits)
  (if (endp bits)
      nil
    (cons (lebits=>nat (rev (take (min (len bits) 8) bits)))
          (values-bebits-to-bytes (nthcdr 8 bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field elements.

; snarkVM circuit/types/field/src/helpers/to_bits.rs: Field::write_bits_le (253 bits).
(define values-field-to-bits-le ((x fieldp))
  :returns (bits bit-listp)
  (values-nat-to-lebits 253 (values-field-fix x))
  ///
  (defret len-of-values-field-to-bits-le
    (equal (len bits) 253)))

; snarkVM circuit/types/field/src/helpers/to_bits.rs: Field::write_bits_be.
(define values-field-to-bits-be ((x fieldp))
  :returns (bits bit-listp)
  (rev (values-field-to-bits-le x))
  ///
  (defret len-of-values-field-to-bits-be
    (equal (len bits) 253)))

; snarkVM circuit/types/field/src/helpers/from_bits.rs: Field::from_bits_le.
; Excess bits (beyond 253) must be zero and the value must be below the modulus,
; i.e. the little-endian value of all the bits is below the modulus.
(define values-field-from-bits-le ((bits bit-listp))
  :returns (x values-field-resultp)
  (b* ((n (lebits=>nat bits)))
    (if (< n (base-prime))
        n
      (spec-error)))
  :prepwork ((local (in-theory (enable spec-error)))))

; snarkVM circuit/types/field/src/helpers/from_bits.rs: Field::from_bits_be.
(define values-field-from-bits-be ((bits bit-listp))
  :returns (x values-field-resultp)
  (values-field-from-bits-le (rev bits)))

; snarkVM: Field::from_bits_le on at most 252 bits never reduces nor fails;
; the reduction modulo the prime below is the identity on such inputs.
(define values-lebits-to-field ((bits bit-listp))
  :returns (x fieldp :hints (("Goal" :in-theory (enable fieldp pfield::fep))))
  (mod (lebits=>nat bits) (base-prime)))

(defrule values-lebits-to-field-when-short
  (implies (<= (len bits) 252)
           (equal (values-lebits-to-field bits)
                  (lebits=>nat bits)))
  :enable values-lebits-to-field
  :use values-lebits=>nat-upper-bound
  :disable values-lebits=>nat-upper-bound)

; snarkVM: bits.chunks(Field::size_in_data_bits()).map(Field::from_bits_le).
(define values-pack-bits ((bits bit-listp))
  :returns (fields values-field-listp)
  :measure (len bits)
  (if (endp bits)
      nil
    (cons (values-lebits-to-field (take (min (len bits) 252) bits))
          (values-pack-bits (nthcdr 252 bits)))))

(define values-field-list-to-bits-le ((xs values-field-listp))
  :returns (bits bit-listp)
  (if (endp xs)
      nil
    (append (values-field-to-bits-le (car xs))
            (values-field-list-to-bits-le (cdr xs)))))

; snarkVM circuit/types/field: Field::is_zero / is_one / is_equal as bits.
(define values-bool-to-bit ((b booleanp))
  :returns (bit bitp)
  (if b 1 0))

(define values-field-add ((x fieldp) (y fieldp))
  :returns (z fieldp :hints (("Goal" :in-theory (enable fieldp))))
  (pfield::add (values-field-fix x) (values-field-fix y) (base-prime))
  :guard-hints (("Goal" :in-theory (enable fieldp))))

(define values-field-sub ((x fieldp) (y fieldp))
  :returns (z fieldp :hints (("Goal" :in-theory (enable fieldp))))
  (pfield::sub (values-field-fix x) (values-field-fix y) (base-prime))
  :guard-hints (("Goal" :in-theory (enable fieldp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Scalars.

; snarkVM circuit/types/scalar/src/helpers/to_bits.rs: Scalar::write_bits_le (251 bits).
(define values-scalar-to-bits-le ((s scalarp))
  :returns (bits bit-listp)
  (values-nat-to-lebits 251 (values-scalar-fix s))
  ///
  (defret len-of-values-scalar-to-bits-le
    (equal (len bits) 251)))

(define values-scalar-to-bits-be ((s scalarp))
  :returns (bits bit-listp)
  (rev (values-scalar-to-bits-le s)))

; snarkVM circuit/types/scalar/src/helpers/from_bits.rs: Scalar::from_bits_le
; (excess bits zero, value below the scalar modulus).
(define values-scalar-from-bits-le ((bits bit-listp))
  :returns (s values-scalar-resultp)
  (b* ((n (lebits=>nat bits)))
    (if (< n (scalar-prime))
        n
      (spec-error)))
  :prepwork ((local (in-theory (enable spec-error)))))

(define values-scalar-from-bits-be ((bits bit-listp))
  :returns (s values-scalar-resultp)
  (values-scalar-from-bits-le (rev bits)))

; snarkVM circuit/types/scalar/src/helpers/from_field.rs: Scalar::from_field
; (Scalar::from_bits_le of the 253 field bits).
(define values-scalar-from-field ((x fieldp))
  :returns (s values-scalar-resultp)
  (b* ((x (values-field-fix x)))
    (if (< x (scalar-prime))
        x
      (spec-error)))
  :prepwork ((local (in-theory (enable spec-error)))))

; snarkVM circuit/types/scalar/src/helpers/from_field_lossy.rs: Scalar::from_field_lossy
; (the low 250 bits of the field element).
(define values-scalar-from-field-lossy ((x fieldp))
  :returns (s scalarp)
  (mod (values-field-fix x) (expt 2 250)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Integers.

; snarkVM circuit/types/integers/src/helpers/to_bits.rs: Integer::write_bits_le.
(define values-int-to-bits-le ((x integerp) (n natp))
  :returns (bits bit-listp)
  (values-nat-to-lebits n x)
  ///
  (defret len-of-values-int-to-bits-le
    (equal (len bits) (nfix n))))

(define values-int-to-bits-be ((x integerp) (n natp))
  :returns (bits bit-listp)
  (values-nat-to-bebits n x)
  ///
  (defret len-of-values-int-to-bits-be
    (equal (len bits) (nfix n))))

; The integer of type (signedp, n) whose n-bit two's complement
; representation is the natural u < 2^n.
(define values-int-of-unsigned ((u natp) (signedp booleanp) (n posp))
  :returns (x integerp)
  (b* ((u (nfix u)))
    (if (and signedp (>= u (expt 2 (1- (acl2::pos-fix n)))))
        (- u (expt 2 (acl2::pos-fix n)))
      u)))

; snarkVM circuit/types/integers/src/helpers/from_bits.rs: Integer::from_bits_le
; (excess bits zero, missing bits zero-padded, two's complement reading).
(define values-int-from-bits-le ((bits bit-listp) (signedp booleanp) (n posp))
  :returns (x values-integer-resultp)
  (b* ((u (lebits=>nat bits)))
    (if (< u (expt 2 (acl2::pos-fix n)))
        (values-int-of-unsigned u signedp n)
      (spec-error)))
  :prepwork ((local (in-theory (enable spec-error)))))

(define values-int-from-bits-be ((bits bit-listp) (signedp booleanp) (n posp))
  :returns (x values-integer-resultp)
  (values-int-from-bits-le (rev bits) signedp n))

(defrule values-expt-2-of-predecessor
  (implies (posp n)
           (equal (expt 2 n) (* 2 (expt 2 (+ -1 n)))))
  :rule-classes :linear
  :enable expt)

(defruled values-int-from-bits-le-range
  (b* ((x (values-int-from-bits-le bits signedp n)))
    (implies (and (posp n) (not (reserrp x)))
             (if signedp
                 (signed-byte-p n x)
               (unsigned-byte-p n x))))
  :enable (values-int-from-bits-le values-int-of-unsigned spec-error
           signed-byte-p unsigned-byte-p))

(defrule values-signed-byte-p-of-int-from-bits-le
  (implies (and signedp (posp n)
                (not (reserrp (values-int-from-bits-le bits signedp n))))
           (signed-byte-p n (values-int-from-bits-le bits signedp n)))
  :use values-int-from-bits-le-range)

(defrule values-unsigned-byte-p-of-int-from-bits-le
  (implies (and (not signedp) (posp n)
                (not (reserrp (values-int-from-bits-le bits signedp n))))
           (unsigned-byte-p n (values-int-from-bits-le bits signedp n)))
  :use values-int-from-bits-le-range)

(defrule values-signed-byte-p-of-int-from-bits-be
  (implies (and signedp (posp n)
                (not (reserrp (values-int-from-bits-be bits signedp n))))
           (signed-byte-p n (values-int-from-bits-be bits signedp n)))
  :enable values-int-from-bits-be)

(defrule values-unsigned-byte-p-of-int-from-bits-be
  (implies (and (not signedp) (posp n)
                (not (reserrp (values-int-from-bits-be bits signedp n))))
           (unsigned-byte-p n (values-int-from-bits-be bits signedp n)))
  :enable values-int-from-bits-be)

; snarkVM circuit/types/integers/src/helpers/to_field.rs: Integer::to_field
; (the field element of the n bits, i.e. the unsigned reading).
(define values-int-to-field ((x integerp) (n natp))
  :returns (f natp :rule-classes :type-prescription)
  (mod (ifix x) (expt 2 (nfix n))))

(defrule values-fieldp-of-int-to-field
  (implies (<= (nfix n) 252)
           (fieldp (values-int-to-field x n)))
  :enable values-int-to-field
  :use (:instance values-fieldp-when-bounded (x (values-int-to-field x n))))

(defrule values-scalarp-of-int-to-field
  (implies (<= (nfix n) 250)
           (scalarp (values-int-to-field x n)))
  :enable values-int-to-field
  :use (:instance values-scalarp-when-bounded (x (values-int-to-field x n))))

(defrule values-bitp-of-mod-2
  (implies (integerp x)
           (bitp (mod x 2)))
  :enable bitp)

; snarkVM circuit/types/integers/src/helpers/from_field.rs: Integer::from_field
; (Field::to_lower_bits_le(n): the field element must be below 2^n).
(define values-int-from-field ((x fieldp) (signedp booleanp) (n posp))
  :returns (y values-integer-resultp)
  (b* ((x (values-field-fix x)))
    (if (< x (expt 2 (acl2::pos-fix n)))
        (values-int-of-unsigned x signedp n)
      (spec-error)))
  :prepwork ((local (in-theory (enable spec-error)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group elements.

; snarkVM circuit/types/group/src/helpers/to_x_coordinate.rs: Group::to_x_coordinate.
(define values-group-x ((p groupp))
  :returns (x fieldp :hints (("Goal" :in-theory (enable fieldp pfield::fep base-prime
                                                 (:e ecurve::edwards-bls12-q))
                              :use (:instance ecurve::edwards-bls12-point->u-upper-bound
                                    (point (values-group-fix p))))))
  (ecurve::edwards-bls12-point->u (values-group-fix p)))

; snarkVM circuit/types/group/src/helpers/to_bits.rs: Group::write_bits_le (the x-coordinate).
(define values-group-to-bits-le ((p groupp))
  :returns (bits bit-listp)
  (values-field-to-bits-le (values-group-x p))
  ///
  (defret len-of-values-group-to-bits-le
    (equal (len bits) 253)))

(define values-group-to-bits-be ((p groupp))
  :returns (bits bit-listp)
  (values-field-to-bits-be (values-group-x p))
  ///
  (defret len-of-values-group-to-bits-be
    (equal (len bits) 253)))

; snarkVM circuit/types/group/src/zero.rs: Group::zero.
(define values-group-zero ()
  :returns (p groupp :hints (("Goal" :in-theory (enable values-groupp-of-zero))))
  (ecurve::twisted-edwards-zero))

(define values-to-group (x)
  :returns (p groupp :hints (("Goal" :in-theory (enable values-groupp-of-zero))))
  :short "Identity on subgroup points."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applied only to points that are in the prime-order subgroup
     mathematically, but not provably so with the available ACL2 libraries
     (the generator, sums and scalar multiples of subgroup points).
     On those points it is the identity, so the specs are not affected;
     it only gives the results the type @(tsee groupp).
     Since @(tsee groupp) is not executable, neither is this function."))
  (if (groupp x) x (ecurve::twisted-edwards-zero)))

(in-theory (disable (:e values-to-group) (:e groupp) (:e ecurve::edwards-bls12-r-pointp)))

; snarkVM circuit/types/group/src/lib.rs: Group::generator
; = console Group::generator (snarkVM curves/src/edwards_bls12/parameters.rs:
; GENERATOR_X, GENERATOR_Y), a point of the prime-order subgroup.
(define values-group-generator ()
  :returns (p groupp :hints (("Goal" :in-theory '(groupp-of-values-to-group values-group-generator))))
  (values-to-group
   (ecurve::point-finite
    1540945439182663264862696551825005342995406165131907382295858612069623286213
    8003546896475222703853313610036801932325312921786952001586936882361378122196)))

(in-theory (disable (:e values-group-generator)))

; There exists a subgroup point with x-coordinate x.
; At most one such point exists: the other curve point with x-coordinate x
; is (x, -y) = (0, -1) - (x, y), where (0, -1) has order 2,
; hence it is not in the subgroup (of odd order) when (x, y) is.
(define-sk values-x-in-subgroupp ((x fieldp))
  (exists (y) (and (natp y) (groupp (ecurve::point-finite x y)))))

; snarkVM circuit/types/group/src/helpers/from_x_coordinate.rs: Group::from_x_coordinate
; (the witness y is the y-coordinate of the console point, and
; from_xy_coordinates enforces that the point is in the subgroup).
(define values-group-from-x ((x fieldp))
  :returns (p values-group-resultp
              :hints (("Goal" :use (:instance values-x-in-subgroupp-suff
                                    (y (values-x-in-subgroupp-witness x)))
                       :in-theory (enable values-x-in-subgroupp))))
  (if (values-x-in-subgroupp x)
      (ecurve::point-finite x (values-x-in-subgroupp-witness x))
    (spec-error))
  :guard-hints (("Goal" :in-theory (enable values-x-in-subgroupp)))
  :prepwork ((local (in-theory (enable spec-error)))))

; snarkVM circuit/types/group/src/helpers/from_bits.rs: Group::from_bits_le.
(define values-group-from-bits-le ((bits bit-listp))
  :returns (p values-group-resultp)
  (b* (((fty::ok x) (values-field-from-bits-le bits)))
    (values-group-from-x x)))

(define values-group-from-bits-be ((bits bit-listp))
  :returns (p values-group-resultp)
  (b* (((fty::ok x) (values-field-from-bits-be bits)))
    (values-group-from-x x)))

; snarkVM circuit/types/group/src/add.rs: Group + Group.
(define values-group-add ((p groupp) (q groupp))
  :returns (r groupp)
  (values-to-group
   (ecurve::edwards-bls12-add (values-group-fix p) (values-group-fix q))))

; snarkVM circuit/types/group/src/mul.rs: Group * Scalar.
(define values-group-mul ((s scalarp) (p groupp))
  :returns (r groupp)
  (values-to-group
   (ecurve::edwards-bls12-mul (values-scalar-fix s) (values-group-fix p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Network hashes (on the abstract primitives of base.lisp).
;; Instances of base.lisp's abstract hashes are identified by their first
;; argument: the network instances by their rate (Poseidon) or size (BHP),
;; other instances (e.g. Poseidon set up with another domain) by their
;; domain string.

(defrule values-fieldp-of-car-of-poseidon-hash-many
  (implies (posp n)
           (fieldp (car (poseidon-hash-many rate inputs n))))
  :enable (fieldp len)
  :disable len-of-poseidon-hash-many
  :use ((:instance fe-listp-of-poseidon-hash-many (num-outputs n))
        (:instance len-of-poseidon-hash-many (num-outputs n))))

(defrule values-fieldp-of-poseidon-hash
  (fieldp (poseidon-hash rate inputs))
  :enable poseidon-hash)

(defrule values-field-listp-of-poseidon-hash-many
  (values-field-listp (poseidon-hash-many rate inputs n))
  :use (:instance fe-listp-of-poseidon-hash-many (num-outputs n))
  :prep-lemmas
  ((defrule lemma
     (implies (pfield::fe-listp x (base-prime))
              (values-field-listp x))
     :enable (pfield::fe-listp values-field-listp fieldp))))

; snarkVM circuit/algorithms/src/poseidon/hash_to_scalar.rs: Poseidon::hash_to_scalar
; (AleoV0::hash_to_scalar_psd4).
(define values-hash-to-scalar-psd4 ((inputs values-field-listp))
  :returns (s scalarp)
  (values-scalar-from-field-lossy (poseidon-hash 4 (values-field-list-fix inputs))))

; snarkVM circuit/algorithms/src/poseidon/hash_to_group.rs: Poseidon::hash_to_group
; (AleoV0::hash_to_group_psd4): MapToGroup(h1) + MapToGroup(h0) of HashMany(input, 2).
; Halts on empty input; Elligator2::encode asserts that its input is nonzero.
; (The other assertions inside Elligator2::encode belong to its abstract spec.)
(define values-hash-to-group-psd4 ((inputs values-field-listp))
  :returns (p values-group-resultp)
  (b* (((when (endp inputs)) (spec-error))
       (hs (poseidon-hash-many 4 (values-field-list-fix inputs) 2))
       (h0 (first hs))
       (h1 (second hs))
       ((when (or (equal h0 0) (equal h1 0))) (spec-error)))
    (values-group-add (elligator2-encode h1) (elligator2-encode h0)))
  :prepwork ((local (in-theory (enable spec-error)))))

; snarkVM circuit/algorithms/src/bhp/hash.rs: BHP::hash = hash_uncompressed(..).to_x_coordinate()
; (AleoV0::hash_bhp1024).
(define values-hash-bhp1024 ((bits bit-listp))
  :returns (h fieldp)
  (values-group-x (bhp-hash-uncompressed 1024 (bit-list-fix bits))))
