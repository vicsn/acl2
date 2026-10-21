; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Network parameters, bit encodings, and the network's hash/commitment
; functions (snarkVM circuit/network/src/v0.rs), expressed on top of the
; abstract primitives of base.lisp.  Shared by the crypto-*.lisp books.
;
; Conventions on top of base.lisp:
;   - The first argument of an abstract primitive of base.lisp identifies
;     the hash instance.  The network's instances are identified by
;     their size (BHP: 256, 512, 768, 1024) or rate (Poseidon: 2, 4, 8).
;     A non-network instance (e.g. a Merkle hasher set up with another domain)
;     is identified by any other value.
;   - The generator G and the domain separators of the network
;     are abstract constants.
;   - Group values are Edwards-BLS12 points;
;     operations use ecurve::edwards-bls12-add/-mul.

(in-package "ALEOVM")

(include-book "base")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Network parameters (abstract constants).

; snarkVM console/network/src/lib.rs: Network::g_powers()[0], commitment_domain,
; encryption_domain, serial_number_domain.
(encapsulate
  (((crypto-generator-g) => *)
   ((crypto-commitment-domain) => *)
   ((crypto-encryption-domain) => *)
   ((crypto-serial-number-domain) => *))

  (local (defun crypto-generator-g () (ecurve::twisted-edwards-zero)))
  (local (defun crypto-commitment-domain () 0))
  (local (defun crypto-encryption-domain () 0))
  (local (defun crypto-serial-number-domain () 0))

  (defrule groupp-of-crypto-generator-g
    (groupp (crypto-generator-g))
    :enable (groupp ecurve::edwards-bls12-r-pointp))

  (defrule fieldp-of-crypto-commitment-domain
    (fieldp (crypto-commitment-domain))
    :enable fieldp)

  (defrule fieldp-of-crypto-encryption-domain
    (fieldp (crypto-encryption-domain))
    :enable fieldp)

  (defrule fieldp-of-crypto-serial-number-domain
    (fieldp (crypto-serial-number-domain))
    :enable fieldp))

; snarkVM console/network/src/lib.rs: MAX_DATA_SIZE_IN_FIELDS = (128 * 1024 * 8) / 252.
(define crypto-max-data-size-in-fields ()
  :returns (n natp)
  (floor (* 128 1024 8) 252))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic facts.

(defrule crypto-natp-when-fieldp
  (implies (fieldp x) (natp x))
  :rule-classes :forward-chaining
  :enable (fieldp pfield::fep))

(defrule crypto-natp-when-scalarp
  (implies (scalarp x) (natp x))
  :rule-classes :forward-chaining
  :enable (scalarp pfield::fep))

(defrule crypto-field-upper-bound-when-fieldp
  (implies (fieldp x) (< x (expt 2 253)))
  :rule-classes :forward-chaining
  :enable (fieldp pfield::fep))

(defrule crypto-edwards-bls12-pointp-when-groupp
  (implies (groupp x) (ecurve::edwards-bls12-pointp x))
  :enable groupp)

(defrule crypto-fieldp-of-edwards-bls12-point->u
  (implies (ecurve::edwards-bls12-pointp p)
           (fieldp (ecurve::edwards-bls12-point->u p)))
  :enable (fieldp pfield::fep base-prime (:e ecurve::edwards-bls12-q))
  :use (:instance ecurve::edwards-bls12-point->u-upper-bound (point p)))

(defrule crypto-fieldp-of-0
  (fieldp 0)
  :enable (fieldp pfield::fep))

(defrule crypto-fieldp-of-1
  (fieldp 1)
  :enable (fieldp pfield::fep base-prime (:e ecurve::edwards-bls12-q)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean helpers (snarkVM Boolean &, !, and is_equal on bits/values).

(define crypto-bit-and ((a bitp) (b bitp))
  :returns (c bitp)
  (if (and (equal a 1) (equal b 1)) 1 0))

(define crypto-bit-not ((b bitp))
  :returns (c bitp)
  (if (equal b 1) 0 1))

(define crypto-bit-eq (a b)
  :returns (c bitp)
  (if (equal a b) 1 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field and group helpers.

; snarkVM circuit/types/field: Field::add (modular addition).
(define crypto-field-add ((x fieldp) (y fieldp))
  :returns (z fieldp :hints (("Goal" :in-theory (enable fieldp))))
  (pfield::add x y (base-prime))
  :guard-hints (("Goal" :in-theory (enable fieldp))))

; snarkVM circuit/types/field: Field::sub (modular subtraction).
(define crypto-field-sub ((x fieldp) (y fieldp))
  :returns (z fieldp :hints (("Goal" :in-theory (enable fieldp))))
  (pfield::sub x y (base-prime))
  :guard-hints (("Goal" :in-theory (enable fieldp))))

(define crypto-field-listp (x)
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (fieldp (car x))
         (crypto-field-listp (cdr x))))
  ///
  (defrule crypto-field-listp-of-cons
    (equal (crypto-field-listp (cons a x))
           (and (fieldp a) (crypto-field-listp x))))
  (defrule crypto-field-listp-of-append
    (implies (and (crypto-field-listp x) (crypto-field-listp y))
             (crypto-field-listp (append x y))))
  (defrule true-listp-when-crypto-field-listp
    (implies (crypto-field-listp x) (true-listp x))
    :rule-classes :forward-chaining)
  (defrule crypto-field-listp-of-take
    (implies (and (crypto-field-listp x) (<= (nfix n) (len x)))
             (crypto-field-listp (take n x))))
  (defrule crypto-field-listp-of-nthcdr
    (implies (crypto-field-listp x)
             (crypto-field-listp (nthcdr n x))))
  (defrule fieldp-of-car-when-crypto-field-listp
    (implies (and (crypto-field-listp x) (consp x))
             (fieldp (car x))))
  (defrule fieldp-of-nth-when-crypto-field-listp
    (implies (and (crypto-field-listp x) (< (nfix n) (len x)))
             (fieldp (nth n x)))))

(defrule crypto-field-listp-when-fe-listp
  (implies (pfield::fe-listp x (base-prime))
           (crypto-field-listp x))
  :enable (crypto-field-listp pfield::fe-listp fieldp))

; snarkVM circuit/types/group: Group::to_x_coordinate.
(define crypto-group-x ((p ecurve::edwards-bls12-pointp))
  :returns (x fieldp)
  (mbe :logic (if (ecurve::edwards-bls12-pointp p)
                  (ecurve::edwards-bls12-point->u p)
                0)
       :exec (ecurve::edwards-bls12-point->u p)))

; snarkVM circuit/types/group: Group::mul_by_cofactor (doubles twice).
(define crypto-mul-by-cofactor ((p ecurve::edwards-bls12-pointp))
  :returns (q ecurve::edwards-bls12-pointp
              :hyp (ecurve::edwards-bls12-pointp p))
  (ecurve::edwards-bls12-mul 4 p))

; snarkVM circuit/network/src/v0.rs: AleoV0::g_scalar_multiply.
; The fold over g_powers = [G, 2G, 4G, ...] with the scalar bits
; computes scalar * G.
(define crypto-g-scalar-multiply ((s scalarp))
  :returns (p ecurve::edwards-bls12-pointp)
  (ecurve::edwards-bls12-mul (nfix s) (crypto-generator-g)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bit encodings.

(define crypto-nat->lebits ((n natp) (x natp))
  :returns (bits bit-listp)
  :short "Little-endian bits of width @('n') (the natural is reduced modulo @($2^n$))."
  (acl2::nat=>lebits n (mod (nfix x) (expt 2 (nfix n))))
  ///
  (defret len-of-crypto-nat->lebits
    (equal (len bits) (nfix n))))

(define crypto-nat->bebits ((n natp) (x natp))
  :returns (bits bit-listp)
  (acl2::nat=>bebits n (mod (nfix x) (expt 2 (nfix n))))
  ///
  (defret len-of-crypto-nat->bebits
    (equal (len bits) (nfix n))))

; snarkVM circuit/types/field: Field::write_bits_le (253 bits).
(define crypto-field-bits-le ((x fieldp))
  :returns (bits bit-listp)
  (crypto-nat->lebits (base-field-size-in-bits) x)
  ///
  (defret len-of-crypto-field-bits-le
    (equal (len bits) 253)
    :hints (("Goal" :in-theory (enable base-field-size-in-bits)))))

; snarkVM circuit/types/field: Field::write_bits_be (253 bits).
(define crypto-field-bits-be ((x fieldp))
  :returns (bits bit-listp)
  (crypto-nat->bebits (base-field-size-in-bits) x))

(define crypto-field-list-bits-le ((xs crypto-field-listp))
  :returns (bits bit-listp)
  (if (endp xs)
      nil
    (append (crypto-field-bits-le (car xs))
            (crypto-field-list-bits-le (cdr xs)))))

(define crypto-field-list-bits-be ((xs crypto-field-listp))
  :returns (bits bit-listp)
  (if (endp xs)
      nil
    (append (crypto-field-bits-be (car xs))
            (crypto-field-list-bits-be (cdr xs)))))

(defrule crypto-bit-listp-of-take
  (implies (and (bit-listp x) (<= (nfix n) (len x)))
           (bit-listp (take n x)))
  :enable bit-listp)

(defrule crypto-bit-listp-of-nthcdr
  (implies (bit-listp x)
           (bit-listp (nthcdr n x)))
  :enable bit-listp)

(defrule crypto-lebits=>nat-upper-bound
  (< (acl2::lebits=>nat bits) (expt 2 (len bits)))
  :rule-classes ((:linear :trigger-terms ((acl2::lebits=>nat bits))))
  :enable acl2::lebits=>nat
  :use (:instance acl2::lendian=>nat-upper-bound (base 2) (digits bits)))

; snarkVM circuit/types/field: Field::from_bits_le (on at most 252 bits,
; where no reduction modulo the base prime takes place).
(define crypto-lebits->field ((bits bit-listp))
  :returns (x natp :rule-classes :type-prescription)
  (acl2::lebits=>nat bits)
  ///
  (defret fieldp-of-crypto-lebits->field
    (implies (<= (len bits) 252)
             (fieldp x))
    :hints (("Goal"
             :in-theory (e/d (fieldp pfield::fep)
                             (crypto-lebits=>nat-upper-bound))
             :use crypto-lebits=>nat-upper-bound))))

; snarkVM: bits_le.chunks(252).map(Field::from_bits_le)
; (Rust slice::chunks: the last chunk may be shorter).
(defruledl crypto-len-of-nthcdr
  (equal (len (nthcdr n x))
         (nfix (- (len x) (nfix n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(defrule crypto-len-of-nthcdr-decreases
  (implies (and (consp x) (posp n))
           (< (len (nthcdr n x)) (len x)))
  :rule-classes :linear
  :enable crypto-len-of-nthcdr)

(define crypto-pack-bits ((bits bit-listp))
  :returns (fields crypto-field-listp)
  :measure (len bits)
  (if (endp bits)
      nil
    (cons (crypto-lebits->field (take (min (len bits) 252) bits))
          (crypto-pack-bits (nthcdr 252 bits)))))

; snarkVM: bits_le.push(true); bits_le.chunks(252).map(Field::from_bits_le),
; the packing used by Plaintext/Record/Entry::to_fields.
(define crypto-bits-to-fields-with-terminus ((bits bit-listp))
  :returns (fields crypto-field-listp)
  (crypto-pack-bits (append bits (list 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Network hash and commitment functions.

(defrule crypto-fieldp-of-poseidon-hash
  (fieldp (poseidon-hash rate inputs))
  :enable (poseidon-hash fieldp len)
  :disable len-of-poseidon-hash-many
  :use ((:instance fe-listp-of-poseidon-hash-many (num-outputs 1))
        (:instance len-of-poseidon-hash-many (num-outputs 1))))

(defrule crypto-field-listp-of-poseidon-hash-many
  (crypto-field-listp (poseidon-hash-many rate inputs num-outputs))
  :use ((:instance crypto-field-listp-when-fe-listp
         (x (poseidon-hash-many rate inputs num-outputs)))
        fe-listp-of-poseidon-hash-many)
  :disable (crypto-field-listp-when-fe-listp fe-listp-of-poseidon-hash-many))

; snarkVM circuit/algorithms/src/poseidon/hash.rs: Poseidon::hash, for any instance.
(define crypto-poseidon-hash-instance (instance (inputs true-listp))
  :returns (h fieldp
              :hints (("Goal" :use (:instance crypto-fieldp-of-poseidon-hash
                                    (rate instance))
                       :in-theory (enable poseidon-hash))))
  (car (poseidon-hash-many instance inputs 1)))

; snarkVM circuit/network/src/v0.rs: AleoV0::hash_psd2/4/8 (Poseidon::hash).
(define crypto-hash-psd ((rate posp) (inputs true-listp))
  :returns (h fieldp)
  (poseidon-hash rate inputs))

; snarkVM circuit/network/src/v0.rs: AleoV0::hash_many_psd2/4/8 (Poseidon::hash_many).
(define crypto-hash-many-psd ((rate posp) (inputs true-listp) (num-outputs natp))
  :returns (hs crypto-field-listp)
  (poseidon-hash-many rate inputs num-outputs)
  ///
  (defret len-of-crypto-hash-many-psd
    (equal (len hs) (nfix num-outputs))))

; snarkVM circuit/types/scalar/src/helpers/from_field_lossy.rs: Scalar::from_field_lossy
; (keeps the low 250 = size_in_data_bits bits of the field element).
(define crypto-field-to-scalar-lossy ((x fieldp))
  :returns (s scalarp :hints (("Goal" :in-theory (enable scalarp pfield::fep))))
  (mod (nfix x) (expt 2 250)))

; snarkVM circuit/algorithms/src/poseidon/hash_to_scalar.rs: Poseidon::hash_to_scalar
; (AleoV0::hash_to_scalar_psd2/4/8).
(define crypto-hash-to-scalar-psd ((rate posp) (inputs true-listp))
  :returns (s scalarp)
  (crypto-field-to-scalar-lossy (crypto-hash-psd rate inputs)))

; snarkVM circuit/algorithms/src/poseidon/hash_to_group.rs: Poseidon::hash_to_group
; (AleoV0::hash_to_group_psd2/4/8).  Halts on empty input; Elligator2::encode
; asserts that its input is nonzero.
(define crypto-hash-to-group-psd ((rate posp) (inputs true-listp))
  :returns (p (implies (not (reserrp p)) (ecurve::edwards-bls12-pointp p)))
  (b* (((when (endp inputs)) (spec-error))
       (hs (crypto-hash-many-psd rate inputs 2))
       (h0 (first hs))
       (h1 (second hs))
       ((unless (and (hped-elligator2-encode-validp h0)
                     (hped-elligator2-encode-validp h1)))
        (spec-error)))
    (ecurve::edwards-bls12-add (elligator2-encode h1) (elligator2-encode h0))))

; snarkVM circuit/algorithms/src/bhp/hash.rs: BHP::hash
; (AleoV0::hash_bhp256/512/768/1024 for instance = 256/512/768/1024).
(define crypto-hash-bhp (instance (input bit-listp))
  :returns (h fieldp)
  (crypto-group-x (bhp-hash-uncompressed instance input)))

; snarkVM circuit/network/src/v0.rs: AleoV0::hash_keccak256/... and Keccak::hash
; (circuit/algorithms/src/keccak/hash.rs), which halts on empty input.
(define crypto-hash-keccak (instance (input bit-listp))
  :returns (h (implies (not (reserrp h)) (bit-listp h)))
  (if (endp input)
      (spec-error)
    (keccak-family-hash instance input)))

; snarkVM circuit/algorithms/src/bhp/commit.rs: BHP::commit
; (AleoV0::commit_bhp256/512/768/1024 for instance = 256/512/768/1024).
(define crypto-commit-bhp (instance (input bit-listp) (randomizer scalarp))
  :returns (h fieldp)
  (crypto-group-x (bhp-commit-uncompressed instance input randomizer)))
