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
;   - Hashes and commitments (Poseidon, BHP, Pedersen, Keccak, Elligator2)
;     are the concrete functions of the hash-*.lisp books; only the
;     hash-to-curve setup of the BHP and Pedersen bases is abstract.

(in-package "ALEOVM")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

; The hash books' library dependencies (sha-3, poseidon) enable many
; bit-vector rewrite rules and disable unsigned-byte-p.  Undo that for the
; books built on this one: disable the rewrite, linear and forward-chaining
; rules those libraries add (definitions, executable counterparts and type
; prescriptions stay enabled) and re-enable what they disable.
(deftheory base-theory-before-hash-deps (current-theory :here))
(include-book "kestrel/crypto/sha-3/sha-3" :dir :system)
(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)
(include-book "projects/poseidon/rate-2-alpha-17" :dir :system)
(include-book "projects/poseidon/rate-4-alpha-17" :dir :system)
(include-book "projects/poseidon/rate-8-alpha-17" :dir :system)
(deftheory base-theory-after-hash-deps (current-theory :here))

(defun base-hash-deps-rules (runes)
  (declare (xargs :mode :program))
  (cond ((atom runes) nil)
        ((and (consp (car runes))
              (member-eq (caar runes) '(:rewrite :linear :forward-chaining)))
         (cons (car runes) (base-hash-deps-rules (cdr runes))))
        (t (base-hash-deps-rules (cdr runes)))))

(include-book "hash-poseidon")
(include-book "hash-bhp")
(include-book "hash-pedersen")
(include-book "hash-keccak")
(include-book "hash-elligator2")

(in-theory (union-theories
            (set-difference-theories
             (current-theory :here)
             (base-hash-deps-rules
              (set-difference-theories (theory 'base-theory-after-hash-deps)
                                       (theory 'base-theory-before-hash-deps))))
            (set-difference-theories (theory 'base-theory-before-hash-deps)
                                     (theory 'base-theory-after-hash-deps))))

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

;; Hash and commitment primitives.
;;
;; These are the concrete network instances of hash-poseidon.lisp,
;; hash-bhp.lisp, hash-pedersen.lisp, hash-keccak.lisp and
;; hash-elligator2.lisp.  Only the BHP and Pedersen bases, which snarkVM
;; derives with Blake2Xs::hash_to_curve, are abstract (hbhp-setup-gens,
;; hbhp-setup-random-base, hped-setup-bases, hped-setup-random-bases).
;; The callees do not verify guards; ec-call keeps these total with guard t.

(define poseidon-hash-many (rate inputs num-outputs)
  :short "snarkVM @('Poseidon::hash_many') of a network Poseidon instance."
  :long "<p>@('rate') is 2, 4 or 8 for @('Poseidon{rate}::setup(\"AleoPoseidon{rate}\")')
  (@(tsee hpos-poseidon-hash-many)), or a pair @('(domain . rate)') with a
  string @('domain') and rate 2, 4 or 8 for
  @('Poseidon{rate}::setup(domain)') (e.g. @('(\"DynamicRecordLeafHasher\" . 8)')).
  Any other value gives @('num_outputs') zeros.</p>"
  (if (and (consp rate)
           (stringp (car rate))
           (ec-call (hpos-aleo-rate-p (cdr rate))))
      (ec-call (hpos-hash-many (ec-call (hpos-domain-fe (car rate)))
                               inputs num-outputs (cdr rate)
                               (ec-call (hpos-aleo-params (cdr rate)))))
    (ec-call (hpos-poseidon-hash-many rate inputs num-outputs)))
  ///
  (local (in-theory (enable base-prime)))

  (defrule fe-listp-of-poseidon-hash-many
    (pfield::fe-listp (poseidon-hash-many rate inputs num-outputs) (base-prime))
    :use ((:instance hpos-aleo-params-shape (rate (cdr rate)))
          (:instance hpos-fe-listp-of-hpos-hash-many
                     (domain (hpos-domain-fe (car rate)))
                     (rate (cdr rate))
                     (params (hpos-aleo-params (cdr rate))))))

  (defrule true-listp-of-poseidon-hash-many
    (true-listp (poseidon-hash-many rate inputs num-outputs))
    :rule-classes (:rewrite :type-prescription)
    :use fe-listp-of-poseidon-hash-many
    :in-theory '(pfield::true-listp-when-fe-listp))

  (defrule len-of-poseidon-hash-many
    (equal (len (poseidon-hash-many rate inputs num-outputs))
           (nfix num-outputs))
    :use ((:instance hpos-aleo-params-shape (rate (cdr rate)))
          (:instance hpos-len-of-hpos-hash-many
                     (domain (hpos-domain-fe (car rate)))
                     (rate (cdr rate))
                     (params (hpos-aleo-params (cdr rate)))))
    :disable hpos-len-of-hpos-hash-many))

(define bhp-hash-uncompressed (size input-bits)
  :short "BHP@('size')::hash_uncompressed (size 256, 512, 768, 1024): @(tsee hbhp-bhp-hash-uncompressed)."
  (ec-call (hbhp-bhp-hash-uncompressed size input-bits))
  ///
  (defrule groupp-of-bhp-hash-uncompressed
    (groupp (bhp-hash-uncompressed size input-bits))
    :enable groupp))

(define bhp-commit-uncompressed (size input-bits randomizer)
  :short "BHP@('size')::commit_uncompressed: @(tsee hbhp-bhp-commit-uncompressed)."
  (ec-call (hbhp-bhp-commit-uncompressed size input-bits randomizer))
  ///
  (defrule groupp-of-bhp-commit-uncompressed
    (groupp (bhp-commit-uncompressed size input-bits randomizer))
    :enable groupp))

(define pedersen-hash-uncompressed (size input-bits)
  :short "Pedersen@('size')::hash_uncompressed (size 64, 128):
          @(tsee hped-aleo-pedersen-hash-uncompressed)."
  (ec-call (hped-aleo-pedersen-hash-uncompressed size input-bits))
  ///
  (defrule groupp-of-pedersen-hash-uncompressed
    (groupp (pedersen-hash-uncompressed size input-bits))
    :enable groupp))

(define pedersen-commit-uncompressed (size input-bits randomizer)
  :short "Pedersen@('size')::commit_uncompressed:
          @(tsee hped-aleo-pedersen-commit-uncompressed)."
  (ec-call (hped-aleo-pedersen-commit-uncompressed size input-bits randomizer))
  ///
  (defrule groupp-of-pedersen-commit-uncompressed
    (groupp (pedersen-commit-uncompressed size input-bits randomizer))
    :enable groupp))

(define keccak-family-hash (variant input-bits)
  :short "@('Keccak<TYPE, VARIANT>::hash') for @('variant') = @('(TYPE . VARIANT)'),
          TYPE 0 (Keccak) or 1 (SHA-3), VARIANT 224/256/384/512:
          @(tsee hkec-keccak-family-hash).  Other values give @('nil')."
  (ec-call (hkec-keccak-family-hash variant (true-list-fix input-bits)))
  ///
  (defrule bit-listp-of-keccak-family-hash
    (bit-listp (keccak-family-hash variant input-bits)))
  (defrule len-of-keccak-family-hash
    (implies (hkec-variant-p variant)
             (equal (len (keccak-family-hash variant input-bits))
                    (cdr variant)))))

(define elligator2-encode (input)
  :short "@('Elligator2::encode'); the zero point where
          @(tsee hped-elligator2-encode-validp) fails: @(tsee hped-elligator2-encode-total)."
  (hped-elligator2-encode-total input)
  ///
  (defrule groupp-of-elligator2-encode
    (groupp (elligator2-encode input))
    :enable groupp))

(define poseidon-hash ((rate posp) inputs)
  :short "snarkVM @('Poseidon::hash'): the single-output case of @(tsee poseidon-hash-many)."
  (car (poseidon-hash-many rate inputs 1)))
