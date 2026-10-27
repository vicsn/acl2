; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for the Keccak round and permutation against the hkec-g-
; circuit generators, on a state of input wires W1..W1600 (lane i is
; W(64i+1)..W(64i+64), little-endian). The generators list their constraints
; newest first and name the private variable of constraint k (hkec-var k);
; snarkVM allocates one variable per constraint too, so (hkec-var k) is
; W(1601+k) and the constraints are compared in order.

(include-book "check-lib")
(include-book "../fun-circuits/hkec-main")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun kec-wires (lo n)
  (if (zp n) nil (cons (list (list 1 (wv lo))) (kec-wires (1+ (nfix lo)) (1- n)))))

(defconst *kec-state* (kec-wires 1 1600))

; The constraints oldest first, with (hkec-var k) renamed to W(base+k).
(defun kec-rename-vec (vec base)
  (if (atom vec)
      nil
    (b* ((var (second (car vec))))
      (cons (list (first (car vec))
                  (if (keywordp var)
                      (wv (+ base (hkec-var-index var)))
                    var))
            (kec-rename-vec (cdr vec) base)))))

(defun kec-rename (constrs base acc)
  (if (atom constrs)
      acc
    (b* ((cn (car constrs)))
      (kec-rename (cdr constrs) base
                  (cons (r1cs::make-r1cs-constraint
                         :a (kec-rename-vec (r1cs::r1cs-constraint->a cn) base)
                         :b (kec-rename-vec (r1cs::r1cs-constraint->b cn) base)
                         :c (kec-rename-vec (r1cs::r1cs-constraint->c cn) base))
                        acc)))))

(defun kec-round-check (r)
  (b* (((mv & cs) (hkec-g-round (acl2::group 64 *kec-state*)
                                (nth r *hkec-round-constant-bits*) nil (base-prime))))
    (same-circuit (ext-run (acl2::circuits-h-keccak *fuel* 0 r))
                  (kec-rename cs 1601 nil) nil)))

; round covers rotate_left (rho, no constraint); the round constant only
; flips constant bits.
(defcheck keccak-round-extraction
  (and (kec-round-check 0) (kec-round-check 1) (kec-round-check 23)))

(defun kec-rounds-check (n)
  (b* (((mv & cs) (hkec-g-rounds (acl2::group 64 *kec-state*)
                                 (take n *hkec-round-constant-bits*) nil (base-prime))))
    (same-circuit (ext-run (acl2::circuits-h-keccak *fuel* 1 n))
                  (kec-rename cs 1601 nil) nil)))

; permutation_f with the 24 round constants.
(defcheck keccak-permutation-extraction
  (kec-rounds-check 24))

; pad_keccak and pad_sha3 push constant bits only.
(defcheck keccak-pad-extraction
  (and (equal (ext-run (acl2::circuits-h-keccak *fuel* 2 1)) nil)
       (equal (ext-run (acl2::circuits-h-keccak *fuel* 2 1087)) nil)
       (equal (ext-run (acl2::circuits-h-keccak *fuel* 2 1600)) nil)
       (equal (ext-run (acl2::circuits-h-keccak *fuel* 3 1)) nil)
       (equal (ext-run (acl2::circuits-h-keccak *fuel* 3 1084)) nil)
       (equal (ext-run (acl2::circuits-h-keccak *fuel* 3 1600)) nil)))

; PathHash::hash_children for Keccak: arity children of variant bits
; W1..W(arity * variant); the private variables follow them.
(defun kec-hash-children-check (arity variant type)
  (b* ((n (* arity variant))
       ((mv & cs) (hkec-g-hash-children (cons type variant)
                                        (kec-wires 1 n) (base-prime))))
    (same-circuit (ext-run (acl2::circuits-h-keccak-hash-children
                            *fuel* arity variant (equal type 1)))
                  (kec-rename cs (1+ n) nil) nil)))

(defcheck keccak-hash-children-extraction
  (and (kec-hash-children-check 2 256 0) (kec-hash-children-check 4 256 1)))
