; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shared foundation for the functional specifications (FUN-SPEC) of the
; constraint-generating functions in snarkVM's circuit crates.
;
; Conventions used by all books in this directory:
;   - A circuit field element is a natural below (base-prime),
;     the BLS12-377 scalar field prime, which is also the Edwards-BLS12 base field.
;   - A scalar is a natural below (scalar-prime), the Edwards-BLS12 subgroup order.
;   - A boolean is a bit (0 or 1).
;   - A group element is an Edwards-BLS12 point in the prime-order subgroup.
;   - An integer of type (signedp, width) is an ACL2 integer in range.
;   - A spec returns (reserr ...) exactly when snarkVM halts or
;     the generated constraints are unsatisfiable for the given inputs.
;   - Specs are about values only; variable modes (constant/public/private)
;     do not change the specified result.
;   - Hash and commitment internals (Poseidon, BHP, Pedersen, Keccak, Elligator2)
;     are excluded from FUN-SPEC: they are abstract functions below,
;     constrained only by the types of their results.

(in-package "ALEOVM")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fields

(define base-prime ()
  :returns (p dm::primep)
  (ecurve::edwards-bls12-q))

(define scalar-prime ()
  :returns (r dm::primep)
  (ecurve::edwards-bls12-r))

(define base-field-size-in-bits ()
  :returns (n posp)
  253)

(define scalar-field-size-in-bits ()
  :returns (n posp)
  251)

(define fieldp (x)
  :returns (yes/no booleanp)
  (pfield::fep x (base-prime)))

(define scalarp (x)
  :returns (yes/no booleanp)
  (pfield::fep x (scalar-prime)))

(define groupp (x)
  :returns (yes/no booleanp)
  (ecurve::edwards-bls12-r-pointp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Integers

(define integer-widthp (n)
  :returns (yes/no booleanp)
  (and (member n '(8 16 32 64 128)) t))

(define int-min ((signedp booleanp) (n posp))
  :returns (min integerp)
  (b* ((n (acl2::pos-fix n)))
    (if signedp (- (expt 2 (1- n))) 0)))

(define int-max ((signedp booleanp) (n posp))
  :returns (max integerp)
  (b* ((n (acl2::pos-fix n)))
    (if signedp (1- (expt 2 (1- n))) (1- (expt 2 n)))))

(define int-valuep (x (signedp booleanp) (n posp))
  :returns (yes/no booleanp)
  (and (integerp x)
       (<= (int-min signedp n) x)
       (<= x (int-max signedp n))))

(define int-wrap ((x integerp) (signedp booleanp) (n posp))
  :returns (y integerp)
  :short "Reduce an integer into the range of the type, modulo @($2^n$)."
  (b* ((m (mod (ifix x) (expt 2 n))))
    (if (and signedp (>= m (expt 2 (1- n))))
        (- m (expt 2 n))
      m)))

(define int->lebits ((x integerp) (n natp))
  :returns (bits bit-listp)
  :short "Two's complement little-endian bits of width @('n')."
  (acl2::nat=>lebits n (mod (ifix x) (expt 2 (nfix n)))))

(define lebits->int ((bits bit-listp) (signedp booleanp))
  :returns (x integerp)
  :short "Inverse of @(tsee int->lebits) for the given signedness."
  (b* ((u (acl2::lebits=>nat bits))
       (n (len bits)))
    (if (and signedp (> n 0) (>= u (expt 2 (1- n))))
        (- u (expt 2 n))
      u)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Errors

(define spec-error ()
  :short "The error result of a spec: snarkVM halts or the constraints are unsatisfiable."
  (reserr nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Abstract hash and commitment primitives (excluded from FUN-SPEC).

(local
 (defun fun-specs-zeros (n)
   (if (zp n) nil (cons 0 (fun-specs-zeros (1- n))))))

(encapsulate
  (((poseidon-hash-many * * *) => *
    :formals (rate inputs num-outputs) :guard t)
   ((bhp-hash-uncompressed * *) => *
    :formals (size input-bits) :guard t)
   ((bhp-commit-uncompressed * * *) => *
    :formals (size input-bits randomizer) :guard t)
   ((pedersen-hash-uncompressed * *) => *
    :formals (size input-bits) :guard t)
   ((pedersen-commit-uncompressed * * *) => *
    :formals (size input-bits randomizer) :guard t)
   ((keccak-family-hash * *) => *
    :formals (variant input-bits) :guard t)
   ((elligator2-encode *) => *
    :formals (input) :guard t))

  (local (defun poseidon-hash-many (rate inputs num-outputs)
           (declare (ignore rate inputs))
           (fun-specs-zeros num-outputs)))
  (local (defun bhp-hash-uncompressed (size input-bits)
           (declare (ignore size input-bits))
           (ecurve::twisted-edwards-zero)))
  (local (defun bhp-commit-uncompressed (size input-bits randomizer)
           (declare (ignore size input-bits randomizer))
           (ecurve::twisted-edwards-zero)))
  (local (defun pedersen-hash-uncompressed (size input-bits)
           (declare (ignore size input-bits))
           (ecurve::twisted-edwards-zero)))
  (local (defun pedersen-commit-uncompressed (size input-bits randomizer)
           (declare (ignore size input-bits randomizer))
           (ecurve::twisted-edwards-zero)))
  (local (defun keccak-family-hash (variant input-bits)
           (declare (ignore variant input-bits))
           nil))
  (local (defun elligator2-encode (input)
           (declare (ignore input))
           (ecurve::twisted-edwards-zero)))

  (local (in-theory (enable fieldp groupp ecurve::edwards-bls12-r-pointp)))

  (local
   (defthm fe-listp-of-fun-specs-zeros
     (implies (posp p)
              (pfield::fe-listp (fun-specs-zeros n) p))
     :hints (("Goal" :induct (fun-specs-zeros n)
              :in-theory (enable pfield::fe-listp pfield::fep)))))

  (defrule fe-listp-of-poseidon-hash-many
    (pfield::fe-listp (poseidon-hash-many rate inputs num-outputs) (base-prime)))

  (defrule true-listp-of-poseidon-hash-many
    (true-listp (poseidon-hash-many rate inputs num-outputs))
    :rule-classes (:rewrite :type-prescription))

  (defrule len-of-poseidon-hash-many
    (equal (len (poseidon-hash-many rate inputs num-outputs))
           (nfix num-outputs)))

  (defrule groupp-of-bhp-hash-uncompressed
    (groupp (bhp-hash-uncompressed size input-bits)))

  (defrule groupp-of-bhp-commit-uncompressed
    (groupp (bhp-commit-uncompressed size input-bits randomizer)))

  (defrule groupp-of-pedersen-hash-uncompressed
    (groupp (pedersen-hash-uncompressed size input-bits)))

  (defrule groupp-of-pedersen-commit-uncompressed
    (groupp (pedersen-commit-uncompressed size input-bits randomizer)))

  (defrule bit-listp-of-keccak-family-hash
    (bit-listp (keccak-family-hash variant input-bits)))

  (defrule groupp-of-elligator2-encode
    (groupp (elligator2-encode input))))

(define poseidon-hash ((rate posp) inputs)
  :short "snarkVM @('Poseidon::hash'): the single-output case of @(tsee poseidon-hash-many)."
  (car (poseidon-hash-many rate inputs 1)))
