; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the Aleo trait functions
; of snarkVM's circuit/network crate (AleoV0, AleoTestnetV0, AleoCanaryV0),
; on top of the abstract primitives of base.lisp.
;
; The three networks behave identically for every function specified here:
; they use the same curve, the same generator G
; (hash to curve of "AleoAccountEncryptionAndSignatureScheme0"),
; and hash instances set up from the same domain strings
; ("AleoBHP256", ..., "AleoPedersen64", ..., "AleoPoseidon2", ...),
; so the specs below have no network argument.
; As in the other books, the first argument of an abstract primitive
; identifies the instance by its size (BHP, Pedersen) or rate (Poseidon).
;
; See curve-group.lisp for the conventions of the curve-* books.

(in-package "ALEOVM")

(include-book "curve-group")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (e/d (spec-error curve-not-reserrp-when-pointp)
                        (bitp (:e base-prime) (:e scalar-prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The generator.

; snarkVM console/network/src/mainnet_v0.rs (testnet_v0.rs, canary_v0.rs): Network::g_powers()[0]
(define curve-generator-g ()
  :returns (g ecurve::pointp)
  :short "The base @($G$) of the account signature and encryption schemes,
          obtained in snarkVM as
          @('Blake2Xs::hash_to_curve(\"AleoAccountEncryptionAndSignatureScheme0\")');
          it is the same on all three networks.
          The other powers @('g_powers()[i]') are @($2^i G$)."
  (ecurve::point-finite
   522678458525321116977504528531602186870683848189190546523208313015552693483
   4625467284263880392848236339834904393692054417272076479096796531274999498606)
  ///
  (defrule edwards-bls12-pointp-of-curve-generator-g
    (ecurve::edwards-bls12-pointp (curve-generator-g))
    :in-theory '((:e ecurve::edwards-bls12-pointp)
                 (:e curve-generator-g)))
  (in-theory (disable (:e curve-generator-g))))

;; The coordinates above, and the subgroup membership of G,
;; checked against the powers printed by snarkVM (g_powers()[1], g_powers()[250]).

(assert-event
 (equal (ecurve::edwards-bls12-mul-fast 2 (curve-generator-g))
        (ecurve::point-finite
         635729210006270224914087040697919839390416031021817704229162077382650990011
         2715027396194992440884724922975940687547603080066254501565260354846395663765)))

(assert-event
 (equal (ecurve::edwards-bls12-mul-fast (expt 2 250) (curve-generator-g))
        (ecurve::point-finite
         4287019517498917834496788416812040337655953337199894656919038479329623788626
         375032525666601023659940772951751933508444499870339497270509592994165661625)))

(assert-event
 (and (not (equal (curve-generator-g) (ecurve::twisted-edwards-zero)))
      (equal (ecurve::edwards-bls12-mul-fast (scalar-prime) (curve-generator-g))
             (ecurve::twisted-edwards-zero))))

; snarkVM circuit/network/src/v0.rs (testnet_v0.rs, canary_v0.rs): Aleo::g_scalar_multiply
(define aleo-g-scalar-multiply-funspec ((s scalarp))
  :returns (p ecurve::edwards-bls12-pointp)
  :short "@($s G$): the sum of the powers @($2^i G$) for the set bits
          @($i$) of the 251 little-endian bits of @($s$)."
  (ecurve::edwards-bls12-mul (lnfix s) (curve-generator-g)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Failure of Elligator2.

(encapsulate
  (((curve-elligator2-encode-validp *) => *
    :formals (input) :guard t))

  (local (defun curve-elligator2-encode-validp (input)
           (not (equal input 0))))

  (defrule booleanp-of-curve-elligator2-encode-validp
    (booleanp (curve-elligator2-encode-validp input))
    :rule-classes :type-prescription)

  (defrule curve-elligator2-encode-validp-of-0
    (not (curve-elligator2-encode-validp 0))))

(defxdoc curve-elligator2-encode-validp
  :parents (elligator2-encode)
  :short "Abstract condition under which snarkVM's circuit
          @('Elligator2::encode') (circuit/algorithms/src/elligator2/encode.rs)
          neither halts nor generates unsatisfiable constraints."
  :long "<p>Elligator2 internals are excluded from FUN-SPEC.
         The circuit asserts that the input is non-zero,
         that @($A^2 u r^2 \\neq B (1 + u r^2)^2$) and that
         @($v e x y \\neq 0$); we only constrain the first condition.
         When the condition holds the result is @(tsee elligator2-encode).</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generic wrappers, instantiated below for each instance size or rate.

(defrule curve-x-of-groupp-is-fieldp
  (implies (groupp p)
           (fieldp (ecurve::point-finite->x p)))
  :enable groupp)

; snarkVM circuit/algorithms/src/bhp/commit.rs: Commit::commit (through Aleo::commit_bhp*)
(define curve-commit-bhp ((size posp) (bits bit-listp) (randomizer scalarp))
  :returns (x fieldp)
  :short "The x-coordinate of the uncompressed BHP commitment."
  (ecurve::point-finite->x (bhp-commit-uncompressed size bits randomizer)))

; snarkVM circuit/algorithms/src/pedersen/hash_uncompressed.rs: HashUncompressed::hash_uncompressed
(define curve-hash-to-group-ped ((size posp) (bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "The Pedersen hash halts on inputs longer than the instance size;
          shorter inputs are padded with zeros (inside the abstract primitive)."
  (if (> (len bits) size)
      (spec-error)
    (pedersen-hash-uncompressed size bits)))

; snarkVM circuit/algorithms/src/pedersen/commit_uncompressed.rs: CommitUncompressed::commit_uncompressed
(define curve-commit-to-group-ped ((size posp) (bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "The commitment first hashes the input, which halts on overlong inputs."
  (if (> (len bits) size)
      (spec-error)
    (pedersen-commit-uncompressed size bits randomizer)))

; snarkVM circuit/algorithms/src/pedersen/commit.rs: Commit::commit
(define curve-commit-ped ((size posp) (bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (fieldp res)))
  :short "The x-coordinate of the uncompressed Pedersen commitment."
  (b* ((p (curve-commit-to-group-ped size bits randomizer))
       ((when (reserrp p)) p))
    (ecurve::point-finite->x p)))

; snarkVM circuit/algorithms/src/poseidon/hash_many.rs: HashMany::hash_many
(define curve-hash-many-psd ((rate posp)
                             (inputs (pfield::fe-listp inputs (base-prime)))
                             (num-outputs natp))
  :guard (< num-outputs 65536)
  :returns (outputs (pfield::fe-listp outputs (base-prime)))
  :short "The extended Poseidon hash, with @('num_outputs') a @('u16')."
  (poseidon-hash-many rate inputs num-outputs))

; snarkVM circuit/algorithms/src/poseidon/hash_to_group.rs: HashToGroup::hash_to_group
(define curve-hash-to-group-psd ((rate posp)
                                 (inputs (pfield::fe-listp inputs (base-prime))))
  :returns (res (implies (not (reserrp res)) (ecurve::edwards-bls12-pointp res)))
  :short "Halts on empty input; otherwise
          @('Elligator2::encode(h1) + Elligator2::encode(h0)')
          where @('[h0, h1] = hash_many(input, 2)')."
  (b* (((when (endp inputs)) (spec-error))
       (hs (poseidon-hash-many rate inputs 2))
       (h0 (first hs))
       (h1 (second hs))
       ((unless (and (curve-elligator2-encode-validp h0)
                     (curve-elligator2-encode-validp h1)))
        (spec-error)))
    (ecurve::edwards-bls12-add (elligator2-encode h1) (elligator2-encode h0))))

(defrule curve-fieldp-of-poseidon-hash
  (implies (posp rate)
           (fieldp (poseidon-hash rate inputs)))
  :enable (poseidon-hash fieldp)
  :use ((:instance fe-listp-of-poseidon-hash-many (num-outputs 1))
        (:instance len-of-poseidon-hash-many (num-outputs 1)))
  :prep-lemmas
  ((defrule curve-fep-of-car-when-fe-listp
     (implies (and (pfield::fe-listp l p) (equal (len l) 1))
              (pfield::fep (car l) p))
     :enable (pfield::fe-listp len))))

; snarkVM circuit/algorithms/src/poseidon/hash_to_scalar.rs: HashToScalar::hash_to_scalar
(define curve-hash-to-scalar-psd ((rate posp)
                                  (inputs (pfield::fe-listp inputs (base-prime))))
  :returns (s scalarp)
  :short "@('Scalar::from_field_lossy') of the Poseidon hash:
          its low 250 bits."
  (curve-scalar-from-field-lossy (poseidon-hash rate inputs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Merkle paths.

(define curve-merkle-order ((indicator-bit bitp) (current fieldp) (sibling fieldp))
  :returns (mv (left fieldp :hyp :guard) (right fieldp :hyp :guard))
  :short "The children ordering at one level:
          the indicator is the negated leaf index bit;
          if the index bit is 0, the current hash is the left child."
  (if (equal indicator-bit 1)
      (mv current sibling)
    (mv sibling current)))

; snarkVM circuit/collections/src/merkle_tree/helpers/path_hash.rs: PathHash::hash_children (BHP)
(define curve-merkle-hash-children-bhp ((left fieldp) (right fieldp))
  :returns (h fieldp)
  :short "BHP512 hash of @('true || bits_le(left) || bits_le(right)')."
  (ecurve::point-finite->x
   (bhp-hash-uncompressed 512 (cons 1 (append (curve-field-to-bits-le left)
                                              (curve-field-to-bits-le right))))))

; snarkVM circuit/collections/src/merkle_tree/helpers/leaf_hash.rs: LeafHash::hash_leaf (BHP)
(define curve-merkle-hash-leaf-bhp ((leaf bit-listp))
  :returns (h fieldp)
  :short "BHP1024 hash of @('false || leaf')."
  (ecurve::point-finite->x (bhp-hash-uncompressed 1024 (cons 0 leaf))))

; snarkVM circuit/collections/src/merkle_tree/helpers/path_hash.rs: PathHash::hash_children (Poseidon)
(define curve-merkle-hash-children-psd ((left fieldp) (right fieldp))
  :returns (h fieldp)
  :short "Poseidon2 hash of @('[1, left, right]')."
  (poseidon-hash 2 (list 1 left right)))

; snarkVM circuit/collections/src/merkle_tree/helpers/leaf_hash.rs: LeafHash::hash_leaf (Poseidon)
(define curve-merkle-hash-leaf-psd ((leaf (pfield::fe-listp leaf (base-prime))))
  :returns (h fieldp)
  :short "Poseidon4 hash of @('[0, leaf...]')."
  (poseidon-hash 4 (cons 0 leaf)))

(define curve-merkle-root-bhp ((index-bits bit-listp)
                               (siblings (pfield::fe-listp siblings (base-prime)))
                               (current fieldp))
  :guard (equal (len index-bits) (len siblings))
  :returns (root fieldp :hyp (fieldp current))
  (b* (((when (endp siblings)) current)
       ((mv left right) (curve-merkle-order (- 1 (acl2::lbfix (car index-bits)))
                                            current
                                            (car siblings))))
    (curve-merkle-root-bhp (cdr index-bits)
                           (cdr siblings)
                           (curve-merkle-hash-children-bhp left right)))
  :guard-hints (("Goal" :in-theory (enable pfield::fe-listp)))
  :prepwork ((local (in-theory (enable pfield::fe-listp)))))

(define curve-merkle-root-psd ((index-bits bit-listp)
                               (siblings (pfield::fe-listp siblings (base-prime)))
                               (current fieldp))
  :guard (equal (len index-bits) (len siblings))
  :returns (root fieldp :hyp (fieldp current))
  (b* (((when (endp siblings)) current)
       ((mv left right) (curve-merkle-order (- 1 (acl2::lbfix (car index-bits)))
                                            current
                                            (car siblings))))
    (curve-merkle-root-psd (cdr index-bits)
                           (cdr siblings)
                           (curve-merkle-hash-children-psd left right)))
  :guard-hints (("Goal" :in-theory (enable pfield::fe-listp)))
  :prepwork ((local (in-theory (enable pfield::fe-listp)))))

(define curve-merkle-path-errorp ((depth natp) (leaf-index natp) (siblings true-listp))
  :returns (yes/no booleanp)
  :short "The Merkle path checks: the leaf index is below @($2^{depth}$),
          there are @('depth') siblings,
          and the depth is at most 64 (the bits of the @('u64') leaf index
          are zipped exactly with the siblings)."
  (or (>= (lnfix leaf-index) (expt 2 (lnfix depth)))
      (not (equal (len siblings) (lnfix depth)))
      (> (lnfix depth) 64)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Aleo trait functions (identical for AleoV0, AleoTestnetV0, AleoCanaryV0).

; snarkVM circuit/network/src/v0.rs: Aleo::commit_bhp256
(define aleo-commit-bhp256-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (x fieldp)
  (curve-commit-bhp 256 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_bhp512
(define aleo-commit-bhp512-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (x fieldp)
  (curve-commit-bhp 512 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_bhp768
(define aleo-commit-bhp768-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (x fieldp)
  (curve-commit-bhp 768 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_bhp1024
(define aleo-commit-bhp1024-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (x fieldp)
  (curve-commit-bhp 1024 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_ped64
(define aleo-commit-ped64-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (fieldp res)))
  (curve-commit-ped 64 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_ped128
(define aleo-commit-ped128-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (fieldp res)))
  (curve-commit-ped 128 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_bhp256
(define aleo-commit-to-group-bhp256-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (p groupp)
  (bhp-commit-uncompressed 256 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_bhp512
(define aleo-commit-to-group-bhp512-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (p groupp)
  (bhp-commit-uncompressed 512 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_bhp768
(define aleo-commit-to-group-bhp768-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (p groupp)
  (bhp-commit-uncompressed 768 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_bhp1024
(define aleo-commit-to-group-bhp1024-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (p groupp)
  (bhp-commit-uncompressed 1024 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_ped64
(define aleo-commit-to-group-ped64-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (curve-commit-to-group-ped 64 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::commit_to_group_ped128
(define aleo-commit-to-group-ped128-funspec ((bits bit-listp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (curve-commit-to-group-ped 128 bits randomizer))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_many_psd2
(define aleo-hash-many-psd2-funspec ((inputs (pfield::fe-listp inputs (base-prime)))
                                     (num-outputs natp))
  :guard (< num-outputs 65536)
  :returns (outputs (pfield::fe-listp outputs (base-prime)))
  (curve-hash-many-psd 2 inputs num-outputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_many_psd4
(define aleo-hash-many-psd4-funspec ((inputs (pfield::fe-listp inputs (base-prime)))
                                     (num-outputs natp))
  :guard (< num-outputs 65536)
  :returns (outputs (pfield::fe-listp outputs (base-prime)))
  (curve-hash-many-psd 4 inputs num-outputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_many_psd8
(define aleo-hash-many-psd8-funspec ((inputs (pfield::fe-listp inputs (base-prime)))
                                     (num-outputs natp))
  :guard (< num-outputs 65536)
  :returns (outputs (pfield::fe-listp outputs (base-prime)))
  (curve-hash-many-psd 8 inputs num-outputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_bhp256
(define aleo-hash-to-group-bhp256-funspec ((bits bit-listp))
  :returns (p groupp)
  (bhp-hash-uncompressed 256 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_bhp512
(define aleo-hash-to-group-bhp512-funspec ((bits bit-listp))
  :returns (p groupp)
  (bhp-hash-uncompressed 512 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_bhp768
(define aleo-hash-to-group-bhp768-funspec ((bits bit-listp))
  :returns (p groupp)
  (bhp-hash-uncompressed 768 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_bhp1024
(define aleo-hash-to-group-bhp1024-funspec ((bits bit-listp))
  :returns (p groupp)
  (bhp-hash-uncompressed 1024 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_ped64
(define aleo-hash-to-group-ped64-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (curve-hash-to-group-ped 64 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_ped128
(define aleo-hash-to-group-ped128-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  (curve-hash-to-group-ped 128 bits))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_psd2
(define aleo-hash-to-group-psd2-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (res (implies (not (reserrp res)) (ecurve::edwards-bls12-pointp res)))
  (curve-hash-to-group-psd 2 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_psd4
(define aleo-hash-to-group-psd4-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (res (implies (not (reserrp res)) (ecurve::edwards-bls12-pointp res)))
  (curve-hash-to-group-psd 4 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_group_psd8
(define aleo-hash-to-group-psd8-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (res (implies (not (reserrp res)) (ecurve::edwards-bls12-pointp res)))
  (curve-hash-to-group-psd 8 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_scalar_psd2
(define aleo-hash-to-scalar-psd2-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (s scalarp)
  (curve-hash-to-scalar-psd 2 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_scalar_psd4
(define aleo-hash-to-scalar-psd4-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (s scalarp)
  (curve-hash-to-scalar-psd 4 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::hash_to_scalar_psd8
(define aleo-hash-to-scalar-psd8-funspec ((inputs (pfield::fe-listp inputs (base-prime))))
  :returns (s scalarp)
  (curve-hash-to-scalar-psd 8 inputs))

; snarkVM circuit/network/src/v0.rs: Aleo::verify_merkle_path_bhp
; (circuit/collections/src/merkle_tree/verify.rs: MerklePath::verify with BHP1024, BHP512)
(define aleo-verify-merkle-path-bhp-funspec
  ((depth natp)
   (leaf-index natp)
   (siblings (pfield::fe-listp siblings (base-prime)))
   (root fieldp)
   (leaf bit-listp))
  :returns (res (implies (not (reserrp res)) (bitp res)))
  :short "Whether hashing the leaf (BHP1024) up the path (BHP512) yields the root;
          @('depth') is the const generic @('DEPTH'), @('leaf-index') the @('u64') index."
  (b* (((when (curve-merkle-path-errorp depth leaf-index siblings)) (spec-error))
       (computed (curve-merkle-root-bhp (acl2::nat=>lebits depth leaf-index)
                                        siblings
                                        (curve-merkle-hash-leaf-bhp leaf))))
    (if (equal root computed) 1 0))
  :guard-hints (("Goal" :in-theory (enable curve-merkle-path-errorp))))

; snarkVM circuit/network/src/v0.rs: Aleo::verify_merkle_path_psd
; (circuit/collections/src/merkle_tree/verify.rs: MerklePath::verify with Poseidon4, Poseidon2)
(define aleo-verify-merkle-path-psd-funspec
  ((depth natp)
   (leaf-index natp)
   (siblings (pfield::fe-listp siblings (base-prime)))
   (root fieldp)
   (leaf (pfield::fe-listp leaf (base-prime))))
  :returns (res (implies (not (reserrp res)) (bitp res)))
  :short "Whether hashing the leaf (Poseidon4) up the path (Poseidon2) yields the root."
  (b* (((when (curve-merkle-path-errorp depth leaf-index siblings)) (spec-error))
       (computed (curve-merkle-root-psd (acl2::nat=>lebits depth leaf-index)
                                        siblings
                                        (curve-merkle-hash-leaf-psd leaf))))
    (if (equal root computed) 1 0))
  :guard-hints (("Goal" :in-theory (enable curve-merkle-path-errorp))))

; snarkVM circuit/network/src/v0.rs: Environment::enforce
(define aleo-enforce-funspec ((a fieldp) (b fieldp) (c fieldp))
  :short "Delegates to the circuit environment:
          the R1CS relation @($A \\cdot B = C$) on the values of the linear
          combinations (constraint and density limits are not modeled)."
  (if (equal (pfield::mul a b (base-prime)) c) nil (spec-error)))
