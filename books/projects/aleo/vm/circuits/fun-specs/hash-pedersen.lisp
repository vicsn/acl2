; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete Pedersen hash and commitment
; (snarkVM console/algorithms/src/pedersen).
;
; This book does not include base.lisp, so that base.lisp can include it.
;
; The bases are parameters.  snarkVM's Pedersen<E, NUM_BITS>::setup(message)
; takes G = Blake2Xs::hash_to_curve("Aleo.Pedersen.Base.{message}") and
; base_window[i] = 2^i G for i < NUM_BITS, and
; H = Blake2Xs::hash_to_curve("Aleo.Pedersen.RandomBase.{message}") and
; random_base_window[i] = 2^i H for i < 251 (Scalar::size_in_bits).  The
; network instances are setup("AleoPedersen64") (NUM_BITS = 64) and
; setup("AleoPedersen128") (NUM_BITS = 128).  hash_to_curve returns subgroup
; points, so the theorems below assume subgroup bases
; (hped-ped-r-point-listp) and nothing else.
;
; hash_uncompressed: inputs longer than NUM_BITS are an error; shorter inputs
; are padded with false bits; the result is the sum of the bases whose bit is
; set, from the zero point.  commit_uncompressed adds, to the hash, the random
; bases selected by the 251 little-endian bits of the randomizer.  commit is
; the x-coordinate of commit_uncompressed.

(in-package "ALEOVM")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "../edwards-order/bls12-points"))
(local (include-book "../edwards-assoc/edwards-bls12-associativity"))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subgroup closure.

(local
 (defruled hped-ped-curve-facts
   (and (ecurve::twisted-edwards-curve-completep (ecurve::edwards-bls12-curve))
        (dm::primep (ecurve::edwards-bls12-r)))
   :enable (ecurve::edwards-bls12-curve-completep)))

(local
 (defun hped-ped-nat-induct (n)
   (if (zp n) n (hped-ped-nat-induct (1- n)))))

(local
 (defruled hped-ped-mul-distrib-nat
   (implies (and (ecurve::edwards-bls12-pointp p1)
                 (ecurve::edwards-bls12-pointp p2)
                 (natp n))
            (equal (ecurve::edwards-bls12-mul n (ecurve::edwards-bls12-add p1 p2))
                   (ecurve::edwards-bls12-add (ecurve::edwards-bls12-mul n p1)
                                              (ecurve::edwards-bls12-mul n p2))))
   :induct (hped-ped-nat-induct n)
   :hints (("Subgoal *1/1"
            :in-theory (enable ecurve::edwards-bls12-add ecurve::edwards-bls12-mul
                               (:e ecurve::twisted-edwards-add)
                               (:e ecurve::edwards-bls12-curve)))
           ("Subgoal *1/2"
            :use ((:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point (ecurve::edwards-bls12-add p1 p2)))
                  (:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point p1))
                  (:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point p2))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p1) (point2 p2)
                             (point3 (ecurve::edwards-bls12-add
                                      (ecurve::edwards-bls12-mul (1- n) p1)
                                      (ecurve::edwards-bls12-mul (1- n) p2))))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p2)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point3 (ecurve::edwards-bls12-mul (1- n) p2)))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point2 p2)
                             (point3 (ecurve::edwards-bls12-mul (1- n) p2)))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p1)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point3 (ecurve::edwards-bls12-add
                                      p2 (ecurve::edwards-bls12-mul (1- n) p2))))
                  (:instance ecurve::twisted-edwards-add-commutative
                             (point1 p2)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (curve (ecurve::edwards-bls12-curve)))
                  hped-ped-curve-facts)
            :in-theory (e/d (ecurve::edwards-bls12-add ecurve::edwards-bls12-mul
                             ecurve::edwards-bls12-pointp)
                            (ecurve::edwards-bls12-add-associative
                             ecurve::twisted-edwards-add-commutative))))))

(local
 (defruled hped-ped-r-pointp-when-r-kills
   (implies (and (ecurve::edwards-bls12-pointp p1)
                 (equal (ecurve::edwards-bls12-mul (ecurve::edwards-bls12-r) p1)
                        (ecurve::twisted-edwards-zero)))
            (ecurve::edwards-bls12-r-pointp p1))
   :use (hped-ped-curve-facts
         (:instance ecurve::twisted-edwards-point-orderp-when-prime-kills
                    (point p1) (r (ecurve::edwards-bls12-r))
                    (curve (ecurve::edwards-bls12-curve))))
   :enable (ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-mul
            ecurve::edwards-bls12-pointp)))

(local
 (defruled hped-ped-r-kills-r-point
   (implies (ecurve::edwards-bls12-r-pointp p1)
            (equal (ecurve::edwards-bls12-mul (ecurve::edwards-bls12-r) p1)
                   (ecurve::twisted-edwards-zero)))
   :enable (ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-mul
            ecurve::twisted-edwards-point-orderp)))

(defrule hped-ped-r-pointp-of-add
  (implies (and (ecurve::edwards-bls12-r-pointp p1)
                (ecurve::edwards-bls12-r-pointp p2))
           (ecurve::edwards-bls12-r-pointp (ecurve::edwards-bls12-add p1 p2)))
  :use ((:instance hped-ped-mul-distrib-nat (n (ecurve::edwards-bls12-r)))
        (:instance hped-ped-r-pointp-when-r-kills
                   (p1 (ecurve::edwards-bls12-add p1 p2)))
        (:instance hped-ped-r-kills-r-point (p1 p1))
        (:instance hped-ped-r-kills-r-point (p1 p2)))
  :enable ((:e ecurve::edwards-bls12-add) (:e ecurve::twisted-edwards-zero)))

(defrule hped-ped-r-pointp-of-zero
  (ecurve::edwards-bls12-r-pointp (ecurve::twisted-edwards-zero))
  :enable ecurve::edwards-bls12-r-pointp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parameters.

(define hped-ped-r-point-listp (bases)
  :returns (yes/no booleanp)
  :short "A list of subgroup points (the Pedersen bases)."
  (if (atom bases)
      (null bases)
    (and (ecurve::edwards-bls12-r-pointp (car bases))
         (hped-ped-r-point-listp (cdr bases)))))

(define hped-ped-bases-p ((num-bits natp) bases rbases)
  :returns (yes/no booleanp)
  :short "Well-formed Pedersen parameters: @('NUM_BITS') subgroup bases
          and 251 subgroup random bases."
  (and (hped-ped-r-point-listp bases)
       (equal (len bases) (nfix num-bits))
       (hped-ped-r-point-listp rbases)
       (equal (len rbases) 251)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hped-ped-sum ((bits bit-listp) bases acc)
  :verify-guards nil
  :short "Add to @('acc'), in order, the bases whose bit is 1."
  (if (or (endp bits) (endp bases))
      acc
    (hped-ped-sum (cdr bits)
                  (cdr bases)
                  (if (equal (car bits) 1)
                      (ecurve::edwards-bls12-add acc (car bases))
                    acc)))
  ///
  (defrule hped-ped-r-pointp-of-sum
    (implies (and (hped-ped-r-point-listp bases)
                  (ecurve::edwards-bls12-r-pointp acc))
             (ecurve::edwards-bls12-r-pointp (hped-ped-sum bits bases acc)))
    :enable hped-ped-r-point-listp))

(define hped-ped-pad ((bits bit-listp) (n natp))
  :returns (padded bit-listp :hyp (bit-listp bits))
  :short "Pad with 0 bits to length @('n') (for @('len bits <= n'))."
  (append bits (repeat (nfix (- (lnfix n) (len bits))) 0)))

; console/algorithms/src/pedersen/hash_uncompressed.rs
(define hped-pedersen-hash-uncompressed ((num-bits natp) bases (input bit-listp))
  :verify-guards nil
  :short "@('Pedersen::hash_uncompressed'), or an error for long inputs."
  (if (> (len input) (lnfix num-bits))
      (reserr :input-too-long)
    (hped-ped-sum (hped-ped-pad input num-bits) bases (ecurve::twisted-edwards-zero)))
  ///
  (defrule hped-ped-r-pointp-of-hash-uncompressed
    (implies (and (hped-ped-r-point-listp bases)
                  (not (reserrp (hped-pedersen-hash-uncompressed num-bits bases input))))
             (ecurve::edwards-bls12-r-pointp
              (hped-pedersen-hash-uncompressed num-bits bases input)))))

(define hped-ped-randomizer-bits (randomizer)
  :returns (bits bit-listp)
  :verify-guards nil
  :short "@('Scalar::to_bits_le'): the 251 little-endian bits of the scalar."
  (acl2::nat=>lebits 251 (pfield::fep-fix randomizer (ecurve::edwards-bls12-r))))

; console/algorithms/src/pedersen/commit_uncompressed.rs
(define hped-pedersen-commit-uncompressed ((num-bits natp) bases rbases
                                           (input bit-listp) randomizer)
  :verify-guards nil
  :short "@('Pedersen::commit_uncompressed'), or an error for long inputs."
  (b* ((h (hped-pedersen-hash-uncompressed num-bits bases input))
       ((when (reserrp h)) h))
    (hped-ped-sum (hped-ped-randomizer-bits randomizer) rbases h))
  ///
  (defrule hped-ped-r-pointp-of-commit-uncompressed
    (implies (and (hped-ped-r-point-listp bases)
                  (hped-ped-r-point-listp rbases)
                  (not (reserrp (hped-pedersen-commit-uncompressed
                                 num-bits bases rbases input randomizer))))
             (ecurve::edwards-bls12-r-pointp
              (hped-pedersen-commit-uncompressed num-bits bases rbases input randomizer)))))

; console/algorithms/src/pedersen/commit.rs
(define hped-pedersen-commit ((num-bits natp) bases rbases (input bit-listp) randomizer)
  :verify-guards nil
  :short "@('Pedersen::commit'): the x-coordinate of the uncompressed commitment."
  (b* ((c (hped-pedersen-commit-uncompressed num-bits bases rbases input randomizer))
       ((when (reserrp c)) c))
    (ecurve::point-finite->x c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Total versions for base.lisp's stubs pedersen-hash-uncompressed and
;; pedersen-commit-uncompressed, which are groupp everywhere: the zero point
;; on long inputs.  (curve-network.lisp checks the length before calling them.)

(define hped-pedersen-hash-uncompressed-total ((num-bits natp) bases (input bit-listp))
  :verify-guards nil
  (b* ((h (hped-pedersen-hash-uncompressed num-bits bases input)))
    (if (reserrp h) (ecurve::twisted-edwards-zero) h))
  ///
  (defrule hped-ped-r-pointp-of-hash-uncompressed-total
    (implies (hped-ped-r-point-listp bases)
             (ecurve::edwards-bls12-r-pointp
              (hped-pedersen-hash-uncompressed-total num-bits bases input)))))

(define hped-pedersen-commit-uncompressed-total ((num-bits natp) bases rbases
                                                 (input bit-listp) randomizer)
  :verify-guards nil
  (b* ((c (hped-pedersen-commit-uncompressed num-bits bases rbases input randomizer)))
    (if (reserrp c) (ecurve::twisted-edwards-zero) c))
  ///
  (defrule hped-ped-r-pointp-of-commit-uncompressed-total
    (implies (and (hped-ped-r-point-listp bases)
                  (hped-ped-r-point-listp rbases))
             (ecurve::edwards-bls12-r-pointp
              (hped-pedersen-commit-uncompressed-total num-bits bases rbases input randomizer)))))
