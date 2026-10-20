; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keccak::hash of circuit/algorithms/src/keccak/hash.rs against the
; Keccak-family hash HKEC-KECCAK-FAMILY-HASH (FIPS 202 via kestrel sha-3),
; and Keccak PathHash::hash_children of circuit/collections/src/merkle_tree,
; which hashes the constant true wire followed by the children bits.

(in-package "ALEOVM")

(include-book "hkec-hash")
(include-book "hkec-sha3")

(defrule hkec-g-hash-sound-family
  (implies (and (primep p)
                (hkec-variant-p variant)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-hash variant input p)) asg p)
                (hkec-wires-p input asg p))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-hash variant input p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-hash variant input p)) asg p)
                       (hkec-keccak-family-hash variant (hkec-eval-list input asg p)))))
  :use hkec-g-hash-sound
  :disable hkec-g-hash-sound)

(defrule hkec-g-hash-complete-family
  (implies (and (primep p)
                (hkec-variant-p variant)
                (hkec-terms-ok input 0)
                (hkec-wires-p input asg p))
           (b* (((mv out cs) (hkec-g-hash variant input p))
                (asg2 (hkec-solve cs asg p)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-list input asg2 p)
                         (hkec-eval-list input asg p))
                  (equal (hkec-eval-list out asg2 p)
                         (hkec-keccak-family-hash variant (hkec-eval-list input asg p))))))
  :use hkec-g-hash-complete
  :disable hkec-g-hash-complete)

(defrule hkec-g-permutation-f-sound-keccak-p
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-permutation-f s cs p)) asg p)
                (hkec-wires-p s asg p)
                (true-listp s)
                (equal (len s) 1600))
           (equal (hkec-eval-list (mv-nth 0 (hkec-g-permutation-f s cs p)) asg p)
                  (sha3::keccak-p 1600 24 (hkec-eval-list s asg p))))
  :use (hkec-g-permutation-f-sound
        (:instance hkec-permutation-f-is-keccak-p (s (hkec-eval-list s asg p))))
  :disable (hkec-g-permutation-f-sound hkec-permutation-f-is-keccak-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PathHash::hash_children for Keccak: hash (true || children bits).

(define hkec-g-hash-children (variant children-bits p)
  :verify-guards nil
  (hkec-g-hash variant (cons 1 children-bits) p))

(defrule hkec-g-hash-children-sound
  (implies (and (primep p)
                (hkec-variant-p variant)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-hash-children variant children-bits p)) asg p)
                (hkec-wires-p children-bits asg p))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-hash-children variant children-bits p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-hash-children variant children-bits p)) asg p)
                       (hkec-keccak-family-hash
                        variant (cons 1 (hkec-eval-list children-bits asg p))))))
  :enable hkec-g-hash-children
  :use ((:instance hkec-g-hash-sound-family (input (cons 1 children-bits))))
  :disable hkec-g-hash-sound-family)

(defrule hkec-g-hash-children-complete
  (implies (and (primep p)
                (hkec-variant-p variant)
                (hkec-terms-ok children-bits 0)
                (hkec-wires-p children-bits asg p))
           (b* (((mv out cs) (hkec-g-hash-children variant children-bits p))
                (asg2 (hkec-solve cs asg p)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-list children-bits asg2 p)
                         (hkec-eval-list children-bits asg p))
                  (equal (hkec-eval-list out asg2 p)
                         (hkec-keccak-family-hash
                          variant (cons 1 (hkec-eval-list children-bits asg p)))))))
  :enable hkec-g-hash-children
  :use ((:instance hkec-g-hash-complete-family (input (cons 1 children-bits))))
  :disable hkec-g-hash-complete-family)
