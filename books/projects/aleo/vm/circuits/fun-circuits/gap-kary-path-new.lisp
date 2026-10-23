; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; KaryMerklePath::new (snarkVM circuit/collections/src/kary_merkle_tree/mod.rs),
; variable mode.  It emits U64::new on the leaf index (Integer::new: one
; boolean check per bit, the value is the weighted sum of the 64 bits) and
; Inject::new on every sibling.  A sibling is a PH::Hash: Field<E> for the
; BHP and Poseidon path hashers (Field::new, one wire, no constraint) and
; BooleanHash<E, VARIANT> for Keccak (Boolean::new on each of the VARIANT
; bits).  The arity and depth checks are host-side halts on the shape of
; the sibling list, so they appear as hypotheses on the wire shape.  No
; hash is computed.

(in-package "ALEOVM")

(include-book "int-new")
(include-book "../fun-specs/crypto-merkle")
(include-book "../r1cs/boolean-check")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A sibling's wires: a symbol (field hash) or a symbol list (Keccak bits).

(define gap-hash-wire-p ((ph crypto-hasher-p) w)
  :returns (yes/no booleanp)
  (if (crypto-keccak-hasher-p ph)
      (and (symbol-listp w)
           (equal (len w) (crypto-keccak-variant ph)))
    (and (symbolp w) t)))

(define gap-hash-wire-list-p ((ph crypto-hasher-p) ws)
  :returns (yes/no booleanp)
  (if (atom ws)
      (null ws)
    (and (gap-hash-wire-p ph (car ws))
         (gap-hash-wire-list-p ph (cdr ws)))))

(define gap-hash-wire-list-list-p ((ph crypto-hasher-p) wss)
  :returns (yes/no booleanp)
  (if (atom wss)
      (null wss)
    (and (gap-hash-wire-list-p ph (car wss))
         (gap-hash-wire-list-list-p ph (cdr wss)))))

(define gap-hash-binds ((ph crypto-hasher-p) w asg)
  :guard (r1cs::r1cs-valuationp asg 2)
  :verify-guards nil
  (if (crypto-keccak-hasher-p ph)
      (r1cs::valuation-binds-allp asg w)
    (r1cs::valuation-bindsp asg w)))

(define gap-hash-binds-list ((ph crypto-hasher-p) ws asg)
  :verify-guards nil
  (if (atom ws)
      t
    (and (gap-hash-binds ph (car ws) asg)
         (gap-hash-binds-list ph (cdr ws) asg))))

(define gap-hash-binds-list-list ((ph crypto-hasher-p) wss asg)
  :verify-guards nil
  (if (atom wss)
      t
    (and (gap-hash-binds-list ph (car wss) asg)
         (gap-hash-binds-list-list ph (cdr wss) asg))))

(define gap-hash-value ((ph crypto-hasher-p) w asg)
  :verify-guards nil
  (if (crypto-keccak-hasher-p ph)
      (lookup-equal-list w asg)
    (lookup-equal w asg)))

(define gap-hash-value-list ((ph crypto-hasher-p) ws asg)
  :verify-guards nil
  (if (atom ws)
      nil
    (cons (gap-hash-value ph (car ws) asg)
          (gap-hash-value-list ph (cdr ws) asg))))

(define gap-hash-value-list-list ((ph crypto-hasher-p) wss asg)
  :verify-guards nil
  (if (atom wss)
      nil
    (cons (gap-hash-value-list ph (car wss) asg)
          (gap-hash-value-list-list ph (cdr wss) asg))))

(define gap-hash-gadget ((ph crypto-hasher-p) w (p primep))
  :verify-guards nil
  :short "Inject::new of one sibling: nothing for a field, a boolean check
          per bit for a BooleanHash."
  (if (crypto-keccak-hasher-p ph)
      (boolean-check-gadget-list w p)
    nil))

(define gap-hash-gadget-list ((ph crypto-hasher-p) ws (p primep))
  :verify-guards nil
  (if (atom ws)
      nil
    (append (gap-hash-gadget ph (car ws) p)
            (gap-hash-gadget-list ph (cdr ws) p))))

(define gap-hash-gadget-list-list ((ph crypto-hasher-p) wss (p primep))
  :verify-guards nil
  (if (atom wss)
      nil
    (append (gap-hash-gadget-list ph (car wss) p)
            (gap-hash-gadget-list-list ph (cdr wss) p))))

(define gap-kary-path-new-gadget ((ph crypto-hasher-p)
                                  (idx symbol-listp)
                                  wss
                                  (p primep))
  :verify-guards nil
  :short "U64::new on the leaf index bits, then Inject::new on each sibling."
  (append (int-new-gadget idx p)
          (gap-hash-gadget-list-list ph wss p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled gap-hash-gadget-iff
  (implies (and (crypto-hasher-p ph)
                (gap-hash-wire-p ph w)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (gap-hash-binds ph w asg))
           (equal (r1cs::r1cs-constraints-holdp (gap-hash-gadget ph w p) asg p)
                  (crypto-merkle-hash-p ph (gap-hash-value ph w asg))))
  :enable (gap-hash-gadget gap-hash-wire-p gap-hash-binds gap-hash-value
           crypto-merkle-hash-p
           boolean-check-gadget-list-to-bit-listp
           len-of-lookup-equal-list
           fieldp))

(defruled gap-hash-gadget-list-iff
  (implies (and (crypto-hasher-p ph)
                (gap-hash-wire-list-p ph ws)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (gap-hash-binds-list ph ws asg))
           (equal (r1cs::r1cs-constraints-holdp
                   (gap-hash-gadget-list ph ws p) asg p)
                  (crypto-merkle-hash-list-p ph (gap-hash-value-list ph ws asg))))
  :induct (len ws)
  :enable (gap-hash-gadget-list gap-hash-wire-list-p gap-hash-binds-list
           gap-hash-value-list gap-hash-gadget-iff))

(defruled gap-hash-gadget-list-list-iff
  (implies (and (crypto-hasher-p ph)
                (gap-hash-wire-list-list-p ph wss)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (gap-hash-binds-list-list ph wss asg))
           (equal (r1cs::r1cs-constraints-holdp
                   (gap-hash-gadget-list-list ph wss p) asg p)
                  (crypto-merkle-hash-list-list-p
                   ph (gap-hash-value-list-list ph wss asg))))
  :induct (len wss)
  :enable (gap-hash-gadget-list-list gap-hash-wire-list-list-p
           gap-hash-binds-list-list gap-hash-value-list-list
           crypto-merkle-hash-list-list-p
           gap-hash-gadget-list-iff))

(defruled gap-len-of-gap-hash-value-list
  (equal (len (gap-hash-value-list ph ws asg)) (len ws))
  :induct (len ws)
  :enable gap-hash-value-list)

(defruled gap-len-of-gap-hash-value-list-list
  (equal (len (gap-hash-value-list-list ph wss asg)) (len wss))
  :induct (len wss)
  :enable gap-hash-value-list-list)

(defruled gap-levels-have-len-of-values
  (implies (gap-hash-wire-list-list-p ph wss)
           (equal (crypto-kary-levels-have-len
                   n (gap-hash-value-list-list ph wss asg))
                  (crypto-kary-levels-have-len n wss)))
  :induct (len wss)
  :enable (crypto-kary-levels-have-len gap-hash-value-list-list
           gap-len-of-gap-hash-value-list
           gap-hash-wire-list-list-p
           gap-true-listp-of-gap-hash-value-list
           gap-true-listp-when-wire-list-p)
  :prep-lemmas
  ((defrule gap-true-listp-when-wire-list-p
     (implies (gap-hash-wire-list-p ph ws) (true-listp ws))
     :induct (len ws)
     :enable gap-hash-wire-list-p)
   (defrule gap-true-listp-of-gap-hash-value-list
     (true-listp (gap-hash-value-list ph ws asg))
     :induct (len ws)
     :enable gap-hash-value-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness: from the wires, the leaf index is the u64 the 64 bits denote,
; every sibling is a hash of the hasher's type, the result is a k-ary
; Merkle path, and it is what the funspec returns.  The shape hypotheses
; are snarkVM's host-side arity and depth checks.

(defruled gap-kary-path-new-gadget-sound
  (implies (and (crypto-hasher-p ph)
                (symbol-listp idx)
                (equal (len idx) 64)
                (gap-hash-wire-list-list-p ph wss)
                (crypto-kary-levels-have-len (nfix (- (nfix arity) 1)) wss)
                (equal (len wss) (nfix depth))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg idx)
                (gap-hash-binds-list-list ph wss asg)
                (r1cs::r1cs-constraints-holdp
                 (gap-kary-path-new-gadget ph idx wss p) asg p))
           (b* ((leaf (lebits->int (lookup-equal-list idx asg) nil))
                (sibs (gap-hash-value-list-list ph wss asg))
                (path (list leaf sibs)))
             (and (crypto-kary-merkle-path-p ph path)
                  (equal (crypto-kary-merkle-path-new depth arity leaf sibs)
                         path))))
  :use ((:instance int-new-gadget-sound (xs idx) (signedp nil) (n 64))
        gap-hash-gadget-list-list-iff)
  :enable (gap-kary-path-new-gadget
           crypto-kary-merkle-path-p
           crypto-kary-merkle-path-new
           gap-levels-have-len-of-values
           gap-len-of-gap-hash-value-list-list
           int-valuep int-min int-max))

(defruled gap-kary-path-new-gadget-complete
  (implies (and (crypto-hasher-p ph)
                (symbol-listp idx)
                (equal (len idx) 64)
                (gap-hash-wire-list-list-p ph wss)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg idx)
                (gap-hash-binds-list-list ph wss asg)
                (natp leaf)
                (< leaf (expt 2 64))
                (equal (lookup-equal-list idx asg) (int->lebits leaf 64))
                (crypto-merkle-hash-list-list-p
                 ph (gap-hash-value-list-list ph wss asg)))
           (and (r1cs::r1cs-constraints-holdp
                 (gap-kary-path-new-gadget ph idx wss p) asg p)
                (equal (lebits->int (lookup-equal-list idx asg) nil) leaf)))
  :use ((:instance int-new-gadget-complete
         (xs idx) (signedp nil) (n 64) (x leaf))
        gap-hash-gadget-list-list-iff)
  :enable (gap-kary-path-new-gadget
           int-new-spec
           int-valuep int-min int-max))
