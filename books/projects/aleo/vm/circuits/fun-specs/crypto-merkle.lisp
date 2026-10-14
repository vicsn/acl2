; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of snarkVM's circuit collections crate:
; binary Merkle paths and trees (circuit/collections/src/merkle_tree)
; and k-ary Merkle paths (circuit/collections/src/kary_merkle_tree).
;
; A hasher (a BHP, Poseidon, or Keccak instance used as a Merkle
; leaf or path hasher) is designated by:
;   (:bhp . instance)              BHP, hash is a field element
;   (:poseidon . instance)         Poseidon, hash is a field element
;   (:keccak instance . variant)   Keccak/SHA3, hash is a list of VARIANT bits
;                                  (BooleanHash<VARIANT>)
; where instance is passed as the first argument of the abstract primitive
; of base.lisp.  The network's Merkle hashers are (:bhp . 1024) / (:bhp . 512)
; and (:poseidon . 4) / (:poseidon . 2) (AleoV0::verify_merkle_path_bhp/psd).
; A BHP or Keccak leaf is a list of bits; a Poseidon leaf is a list of fields.

(in-package "ALEOVM")

(include-book "crypto-model")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Hashers and hashes.

(define crypto-hasher-p (h)
  :returns (yes/no booleanp)
  (and (consp h)
       (or (eq (car h) :bhp)
           (eq (car h) :poseidon)
           (and (eq (car h) :keccak)
                (consp (cdr h))
                (posp (cddr h)))))
  ///
  (defrule consp-when-crypto-hasher-p
    (implies (crypto-hasher-p h) (consp h))
    :rule-classes :forward-chaining))

(define crypto-field-hasher-p (h)
  :returns (yes/no booleanp)
  :short "BHP and Poseidon hashers, whose hashes are field elements."
  (and (consp h)
       (or (eq (car h) :bhp)
           (eq (car h) :poseidon)))
  ///
  (defrule crypto-hasher-p-when-crypto-field-hasher-p
    (implies (crypto-field-hasher-p h)
             (crypto-hasher-p h))
    :enable crypto-hasher-p))

(define crypto-keccak-hasher-p ((h crypto-hasher-p))
  :returns (yes/no booleanp)
  (eq (car h) :keccak))

(define crypto-keccak-variant ((h crypto-hasher-p))
  :guard (crypto-keccak-hasher-p h)
  :returns (n posp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (acl2::pos-fix (cddr h))
       :exec (cddr h))
  :guard-hints (("Goal" :in-theory (enable crypto-hasher-p
                                           crypto-keccak-hasher-p))))

(define crypto-merkle-hash-p ((ph crypto-hasher-p) x)
  :returns (yes/no booleanp)
  :short "Recognize the hashes of a hasher: field elements or BooleanHash bits."
  (if (crypto-keccak-hasher-p ph)
      (and (bit-listp x)
           (equal (len x) (crypto-keccak-variant ph)))
    (fieldp x)))

(define crypto-merkle-hash-list-p ((ph crypto-hasher-p) x)
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (crypto-merkle-hash-p ph (car x))
         (crypto-merkle-hash-list-p ph (cdr x))))
  ///
  (defrule crypto-merkle-hash-list-p-of-nil
    (crypto-merkle-hash-list-p ph nil))
  (defrule crypto-merkle-hash-list-p-of-cons
    (equal (crypto-merkle-hash-list-p ph (cons a x))
           (and (crypto-merkle-hash-p ph a)
                (crypto-merkle-hash-list-p ph x))))
  (defrule crypto-merkle-hash-p-of-nth
    (implies (and (crypto-merkle-hash-list-p ph x)
                  (< (nfix n) (len x)))
             (crypto-merkle-hash-p ph (nth n x)))))

(define crypto-merkle-hash-list-list-p ((ph crypto-hasher-p) x)
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (crypto-merkle-hash-list-p ph (car x))
         (crypto-merkle-hash-list-list-p ph (cdr x)))))

(define crypto-merkle-leaf-p ((lh crypto-hasher-p) x)
  :returns (yes/no booleanp)
  (if (eq (car lh) :poseidon)
      (crypto-field-listp x)
    (bit-listp x)))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs:
; Default for BooleanHash, and Field::default.
(define crypto-merkle-hash-default ((ph crypto-hasher-p))
  :returns (h (crypto-merkle-hash-p ph h)
              :hyp (crypto-hasher-p ph)
              :hints (("Goal" :in-theory (enable crypto-merkle-hash-p))))
  (if (crypto-keccak-hasher-p ph)
      (repeat (crypto-keccak-variant ph) 0)
    0)
  :prepwork ((local (defrule bit-listp-of-repeat-0
                      (bit-listp (repeat n 0))
                      :enable (repeat bit-listp)))))

; snarkVM: Field::write_bits_le, or the bits of a BooleanHash.
(define crypto-merkle-hash-bits ((ph crypto-hasher-p) x)
  :guard (crypto-merkle-hash-p ph x)
  :returns (bits bit-listp
                 :hyp (crypto-merkle-hash-p ph x)
                 :hints (("Goal" :in-theory (enable crypto-merkle-hash-p))))
  (if (crypto-keccak-hasher-p ph)
      x
    (crypto-field-bits-le x))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-p))))

(define crypto-merkle-hash-list-bits ((ph crypto-hasher-p) xs)
  :guard (crypto-merkle-hash-list-p ph xs)
  :returns (bits bit-listp
                 :hyp (crypto-merkle-hash-list-p ph xs)
                 :hints (("Goal" :in-theory (enable crypto-merkle-hash-list-p))))
  (if (endp xs)
      nil
    (append (crypto-merkle-hash-bits ph (car xs))
            (crypto-merkle-hash-list-bits ph (cdr xs))))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-list-p))))

; snarkVM kary_merkle_tree/helpers/{leaf,path}_hash.rs (Keccak):
; result.0.clone_from_slice(&output[..VARIANT]).
(define crypto-keccak-truncate (output (variant natp))
  :returns (h (or (reserrp h)
                  (and (bit-listp h) (equal (len h) (nfix variant)))))
  (b* (((when (reserrp output)) (spec-error))
       ((unless (and (bit-listp output)
                     (<= (nfix variant) (len output))))
        (spec-error)))
    (take variant output))
  ///
  (defret bit-listp-of-crypto-keccak-truncate
    (implies (not (reserrp h)) (bit-listp h)))
  (defret len-of-crypto-keccak-truncate
    (implies (not (reserrp h)) (equal (len h) (nfix variant)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf and path hashes.

; snarkVM circuit/collections/src/{merkle_tree,kary_merkle_tree}/helpers/leaf_hash.rs:
; LeafHash::hash_leaf for BHP (prepend a false bit), Poseidon (prepend 0field),
; and Keccak (prepend a false bit, keep the first VARIANT output bits).
(define crypto-merkle-hash-leaf ((lh crypto-hasher-p) leaf)
  :guard (crypto-merkle-leaf-p lh leaf)
  :returns (h (implies (not (reserrp h)) (crypto-merkle-hash-p lh h))
              :hyp (crypto-hasher-p lh)
              :hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                                 crypto-keccak-hasher-p
                                                 crypto-hasher-p))))
  (case (car lh)
    (:bhp (crypto-hash-bhp (cdr lh) (cons 0 leaf)))
    (:poseidon (crypto-poseidon-hash-instance (cdr lh) (cons 0 leaf)))
    (otherwise (crypto-keccak-truncate
                (crypto-hash-keccak (cadr lh) (cons 0 leaf))
                (crypto-keccak-variant lh))))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-leaf-p
                                           crypto-hasher-p
                                           crypto-keccak-hasher-p))))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/path_hash.rs:
; PathHash::hash_children for BHP (prepend a true bit to the children's bits),
; Poseidon (prepend 1field to the children), and Keccak (prepend a true bit,
; keep the first VARIANT output bits).
; Also merkle_tree/helpers/path_hash.rs: PathHash::hash_children(left, right)
; for BHP and Poseidon, with children = (list left right).
(define crypto-merkle-hash-children ((ph crypto-hasher-p) children)
  :guard (crypto-merkle-hash-list-p ph children)
  :returns (h (implies (not (reserrp h)) (crypto-merkle-hash-p ph h))
              :hyp (crypto-hasher-p ph)
              :hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                                 crypto-keccak-hasher-p
                                                 crypto-hasher-p))))
  (case (car ph)
    (:bhp (crypto-hash-bhp (cdr ph)
                           (cons 1 (crypto-merkle-hash-list-bits ph children))))
    (:poseidon (crypto-poseidon-hash-instance (cdr ph)
                                              (cons 1 (true-list-fix children))))
    (otherwise (crypto-keccak-truncate
                (crypto-hash-keccak (cadr ph)
                                    (cons 1 (crypto-merkle-hash-list-bits
                                             ph children)))
                (crypto-keccak-variant ph))))
  :guard-hints (("Goal" :in-theory (enable crypto-hasher-p
                                           crypto-keccak-hasher-p)))
  ///
  (defrule fieldp-of-crypto-merkle-hash-children
    (implies (crypto-field-hasher-p ph)
             (fieldp (crypto-merkle-hash-children ph children)))
    :enable crypto-field-hasher-p)
  (defrule fieldp-of-crypto-merkle-hash-leaf
    (implies (crypto-field-hasher-p lh)
             (fieldp (crypto-merkle-hash-leaf lh leaf)))
    :enable (crypto-field-hasher-p crypto-merkle-hash-leaf)))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/path_hash.rs:
; PathHash::hash_empty (trait default): hash ARITY default hashes.
(define crypto-kary-merkle-hash-empty ((ph crypto-hasher-p) (arity natp))
  :returns (h (implies (not (reserrp h)) (crypto-merkle-hash-p ph h))
              :hyp (crypto-hasher-p ph))
  (crypto-merkle-hash-children ph (repeat arity (crypto-merkle-hash-default ph)))
  :guard-hints (("Goal" :in-theory (enable repeat)))
  :prepwork ((local (defrule crypto-merkle-hash-list-p-of-repeat
                      (implies (crypto-merkle-hash-p ph x)
                               (crypto-merkle-hash-list-p ph (repeat n x)))
                      :enable repeat))))

; snarkVM circuit/collections/src/merkle_tree/helpers/path_hash.rs:
; PathHash::hash_empty (trait default): hash_children(0field, 0field).
(define crypto-merkle-hash-empty ((ph crypto-field-hasher-p))
  :returns (h fieldp :hyp (crypto-field-hasher-p ph))
  (crypto-merkle-hash-children ph (list 0 0))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                           crypto-field-hasher-p
                                           crypto-keccak-hasher-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BooleanHash (kary_merkle_tree/helpers/mod.rs).

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs: BooleanHash::new (Inject).
(define crypto-boolean-hash-new ((variant natp) (bits bit-listp))
  :returns (h (implies (not (reserrp h)) (bit-listp h)) :hyp (bit-listp bits))
  (if (equal (len bits) (nfix variant))
      bits
    (spec-error)))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs: BooleanHash::is_equal
; (conjunction of bitwise equalities; zip_eq halts on a length mismatch).
(define crypto-boolean-hash-is-equal ((a bit-listp) (b bit-listp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (if (equal (len a) (len b))
      (if (equal a b) 1 0)
    (spec-error)))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs: BooleanHash::is_not_equal.
(define crypto-boolean-hash-is-not-equal ((a bit-listp) (b bit-listp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (b* (((fty::ok eq) (crypto-boolean-hash-is-equal a b)))
    (if (equal eq 1) 0 1)))

; snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs: BooleanHash::ternary
; (bitwise Boolean::ternary; zip_eq halts on a length mismatch).
(define crypto-boolean-hash-ternary ((condition bitp) (a bit-listp) (b bit-listp))
  :returns (r (implies (not (reserrp r)) (bit-listp r))
              :hyp (and (bit-listp a) (bit-listp b)))
  (if (equal (len a) (len b))
      (if (equal condition 1) a b)
    (spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Binary Merkle paths (merkle_tree/verify.rs).

; A binary Merkle path is (list leaf-index siblings),
; with leaf-index a u64 value and siblings a list of field elements.
(define crypto-merkle-path-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 2)
       (natp (first x))
       (< (first x) (expt 2 64))
       (crypto-field-listp (second x))))

; Process the levels from the leaf to the root: the indicator is the negated
; leaf index bit; (left, right) = indicator ? (current, sibling) : (sibling, current).
(define crypto-merkle-path-loop ((ph crypto-field-hasher-p)
                                 (index-bits bit-listp)
                                 (siblings crypto-field-listp)
                                 (current fieldp))
  :guard (equal (len index-bits) (len siblings))
  :returns (root fieldp :hyp (and (crypto-field-hasher-p ph) (fieldp current)))
  (b* (((when (endp siblings)) current)
       (indicator (if (equal (car index-bits) 1) 0 1))
       (sibling (car siblings))
       (left (if (equal indicator 1) current sibling))
       (right (if (equal indicator 1) sibling current))
       (current (crypto-merkle-hash-children ph (list left right))))
    (crypto-merkle-path-loop ph (cdr index-bits) (cdr siblings) current))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                           crypto-field-hasher-p
                                           crypto-keccak-hasher-p))))

; snarkVM circuit/collections/src/merkle_tree/verify.rs: MerklePath::verify.
; Halts if the leaf index is >= 2^DEPTH or the path length is not DEPTH;
; the indicators are the first DEPTH bits of the u64 leaf index, so
; zip_eq with the siblings also halts if DEPTH > 64.
(define crypto-merkle-path-verify ((lh crypto-field-hasher-p)
                                   (ph crypto-field-hasher-p)
                                   (depth natp)
                                   (path crypto-merkle-path-p)
                                   (root fieldp)
                                   leaf)
  :guard (crypto-merkle-leaf-p lh leaf)
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (b* (((list leaf-index siblings) path)
       ((when (>= leaf-index (expt 2 (nfix depth)))) (spec-error))
       ((unless (equal (len siblings) (nfix depth))) (spec-error))
       ((when (> (nfix depth) 64)) (spec-error))
       (current (crypto-merkle-hash-leaf lh leaf))
       (index-bits (take depth (crypto-nat->lebits 64 leaf-index)))
       (current (crypto-merkle-path-loop ph index-bits siblings current)))
    (if (equal root current) 1 0))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-path-p))))

; snarkVM circuit/collections/src/merkle_tree/mod.rs: MerklePath::new (Inject).
(define crypto-merkle-path-new ((depth natp) (leaf-index natp) (siblings crypto-field-listp))
  :returns (path (implies (not (reserrp path)) (true-listp path)))
  (if (equal (len siblings) (nfix depth))
      (list leaf-index siblings)
    (spec-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Binary Merkle trees (merkle_tree/mod.rs).

(define crypto-merkle-hash-leaves ((lh crypto-field-hasher-p) leaves)
  :guard (and (true-listp leaves)
              (crypto-merkle-leaf-list-p lh leaves))
  :returns (hashes crypto-field-listp :hyp (crypto-field-hasher-p lh))
  (if (endp leaves)
      nil
    (cons (crypto-merkle-hash-leaf lh (car leaves))
          (crypto-merkle-hash-leaves lh (cdr leaves))))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-leaf-list-p)))
  :prepwork
  ((define crypto-merkle-leaf-list-p ((lh crypto-hasher-p) x)
     :returns (yes/no booleanp)
     (if (atom x)
         (null x)
       (and (crypto-merkle-leaf-p lh (car x))
            (crypto-merkle-leaf-list-p lh (cdr x)))))))

; Hash consecutive pairs of a level: (h0 h1 h2 h3 ...) -> (H(h0,h1) H(h2,h3) ...).
(define crypto-merkle-pair-level ((ph crypto-field-hasher-p) (level crypto-field-listp))
  :returns (parents crypto-field-listp :hyp (crypto-field-hasher-p ph))
  (if (or (endp level) (endp (cdr level)))
      nil
    (cons (crypto-merkle-hash-children ph (list (first level) (second level)))
          (crypto-merkle-pair-level ph (cddr level))))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                           crypto-field-hasher-p
                                           crypto-keccak-hasher-p)))
  ///
  (defret len-of-crypto-merkle-pair-level
    (<= (* 2 (len parents)) (len level))
    :rule-classes :linear
    :hints (("Goal" :induct (crypto-merkle-pair-level ph level)
                    :in-theory (enable crypto-merkle-pair-level)))))

; All levels of a full binary tree, from the (padded) leaf level to the root level.
(define crypto-merkle-levels ((ph crypto-field-hasher-p) (level crypto-field-listp))
  :returns (levels true-list-listp)
  :measure (len level)
  (if (or (endp level) (endp (cdr level)))
      (list (true-list-fix level))
    (cons (true-list-fix level)
          (crypto-merkle-levels ph (crypto-merkle-pair-level ph level)))))

(define crypto-merkle-pad-root ((ph crypto-field-hasher-p)
                                (root fieldp)
                                (empty-hash fieldp)
                                (n natp))
  :returns (padded-root fieldp :hyp (and (crypto-field-hasher-p ph) (fieldp root)))
  (if (zp n)
      root
    (crypto-merkle-pad-root ph
                            (crypto-merkle-hash-children ph (list root empty-hash))
                            empty-hash
                            (1- n)))
  :guard-hints (("Goal" :in-theory (enable crypto-merkle-hash-p
                                           crypto-field-hasher-p
                                           crypto-keccak-hasher-p))))

; usize::checked_next_power_of_two (0 -> 1); its base-2 logarithm.
(define crypto-log2-next-power-of-two ((n natp))
  :returns (k natp :rule-classes :type-prescription)
  (if (zp n) 0 (integer-length (1- n))))

; snarkVM circuit/collections/src/merkle_tree/mod.rs: MerkleTree::new.
; The result is (list root tree empty-hash number-of-leaves), where tree
; holds the internal hashes from the root level down to the hashed leaves
; (the leaf level truncated to the leaves, plus one empty hash if their
; number is odd and above 1).
; Errors: DEPTH = 0, DEPTH > 64, overflow of next_power_of_two (more than 2^63
; leaves), or more than 2^DEPTH leaves.
(define crypto-merkle-tree-new ((lh crypto-field-hasher-p)
                                (ph crypto-field-hasher-p)
                                (depth natp)
                                (leaves true-listp))
  :guard (crypto-merkle-leaf-list-p lh leaves)
  :returns (tree (implies (not (reserrp tree)) (true-listp tree)))
  (b* ((depth (nfix depth))
       ((when (equal depth 0)) (spec-error))
       ((when (> depth 64)) (spec-error))
       (n (len leaves))
       ((when (> n (expt 2 63))) (spec-error))
       (tree-depth (crypto-log2-next-power-of-two n))
       ((when (> tree-depth depth)) (spec-error))
       (max-leaves (expt 2 tree-depth))
       (empty-hash (crypto-merkle-hash-empty ph))
       (leaf-hashes (crypto-merkle-hash-leaves lh leaves))
       (padded (append leaf-hashes (repeat (- max-leaves n) empty-hash)))
       (levels (crypto-merkle-levels ph padded))
       (num-leaf-nodes (if (equal n 0)
                           1
                         (+ n (if (> n 1) (mod n 2) 0))))
       (tree (append (acl2::flatten (rev (cdr levels)))
                     (take num-leaf-nodes padded)))
       (root (crypto-merkle-pad-root ph
                                     (car tree)
                                     empty-hash
                                     (- depth tree-depth))))
    (list root tree empty-hash n))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; K-ary Merkle paths (kary_merkle_tree).

; A k-ary Merkle path is (list leaf-index siblings),
; with leaf-index a u64 value and siblings a list of lists of hashes.
(define crypto-kary-merkle-path-p ((ph crypto-hasher-p) x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 2)
       (natp (first x))
       (< (first x) (expt 2 64))
       (crypto-merkle-hash-list-list-p ph (second x))))

(define crypto-kary-levels-have-len ((n natp) siblings)
  :returns (yes/no booleanp)
  (if (atom siblings)
      t
    (and (true-listp (car siblings))
         (equal (len (car siblings)) (nfix n))
         (crypto-kary-levels-have-len n (cdr siblings)))))

; snarkVM circuit/collections/src/kary_merkle_tree/mod.rs: KaryMerklePath::new (Inject).
; Halts if a level does not have ARITY - 1 (saturating) siblings
; or the number of levels is not DEPTH.
(define crypto-kary-merkle-path-new ((depth natp)
                                     (arity natp)
                                     (leaf-index natp)
                                     (siblings true-listp))
  :returns (path (implies (not (reserrp path)) (true-listp path)))
  (b* (((unless (crypto-kary-levels-have-len (nfix (- (nfix arity) 1)) siblings))
        (spec-error))
       ((unless (equal (len siblings) (nfix depth))) (spec-error)))
    (list leaf-index siblings)))

; The children of a level: the current hash inserted at the indicator
; position k among the siblings.  Mirrors the code: position 0 is
; (k == 0 ? current : s[0]), a middle position i is
; (i == k ? current : (i < k ? s[i] : s[i-1])), and position ARITY-1 is
; (k == ARITY-1 ? current : s[ARITY-2]).
(define crypto-kary-children ((i natp)
                              (arity natp)
                              (k natp)
                              current
                              (siblings true-listp))
  :returns (children true-listp)
  :measure (nfix (- (nfix arity) (nfix i)))
  (b* ((i (nfix i))
       ((when (>= i (nfix arity))) nil)
       (child (cond ((equal i (nfix k)) current)
                    ((< i (nfix k)) (nth i siblings))
                    (t (nth (1- i) siblings)))))
    (cons child (crypto-kary-children (1+ i) arity k current siblings))))

(define crypto-kary-merkle-path-loop ((ph crypto-hasher-p)
                                      (arity natp)
                                      (leaf-index natp)
                                      (level natp)
                                      siblings
                                      current)
  :guard (and (crypto-merkle-hash-list-list-p ph siblings)
              (crypto-merkle-hash-p ph current))
  :returns (root (implies (not (reserrp root)) (crypto-merkle-hash-p ph root))
                 :hyp (and (crypto-hasher-p ph)
                           (crypto-merkle-hash-p ph current)))
  (b* (((when (atom siblings)) current)
       (sibling-hashes (car siblings))
       (power (expt (nfix arity) (nfix level)))
       ((when (>= power (expt 2 64))) (spec-error))
       ((when (equal power 0)) (spec-error))
       ((when (zp arity)) (spec-error))
       (k (mod (floor (nfix leaf-index) power) (nfix arity)))
       ((when (endp sibling-hashes)) (spec-error))
       (children (crypto-kary-children 0 arity k current sibling-hashes))
       ((fty::ok current) (crypto-merkle-hash-children ph children)))
    (crypto-kary-merkle-path-loop ph arity leaf-index (1+ (nfix level))
                                  (cdr siblings) current))
  :measure (len siblings)
  :verify-guards nil)

; snarkVM circuit/collections/src/kary_merkle_tree/verify.rs: KaryMerklePath::verify.
; Halts if the leaf index is >= ARITY^DEPTH, the path length is not DEPTH,
; a level does not have ARITY - 1 (saturating) siblings, ARITY^i overflows u64
; for a level i (U64::pow on constants), or a level has no siblings
; (sibling_hashes[0], i.e. ARITY = 1).
; The indicator of level i is (leaf_index / ARITY^i) % ARITY.
(define crypto-kary-merkle-path-verify ((lh crypto-hasher-p)
                                        (ph crypto-hasher-p)
                                        (depth natp)
                                        (arity natp)
                                        path
                                        root
                                        leaf)
  :guard (and (crypto-kary-merkle-path-p ph path)
              (crypto-merkle-hash-p ph root)
              (crypto-merkle-leaf-p lh leaf))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (b* (((list leaf-index siblings) path)
       (leaf-index (nfix leaf-index))
       ((when (>= leaf-index (expt (nfix arity) (nfix depth)))) (spec-error))
       ((unless (equal (len siblings) (nfix depth))) (spec-error))
       ((unless (crypto-kary-levels-have-len (nfix (- (nfix arity) 1)) siblings))
        (spec-error))
       ((fty::ok current) (crypto-merkle-hash-leaf lh leaf))
       ((fty::ok current) (crypto-kary-merkle-path-loop ph arity leaf-index 0
                                                   siblings current)))
    (if (equal root current) 1 0))
  :verify-guards nil)
