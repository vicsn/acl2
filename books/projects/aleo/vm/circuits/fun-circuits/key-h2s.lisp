; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Aleo::hash_to_scalar_psd4 / psd8 (circuit/network/src/v0.rs) are
; Poseidon::hash_to_scalar on the AleoPoseidon4 / AleoPoseidon8 instances,
; i.e. hpos-c-hash-to-scalar with rate 4 / 8.  The output Scalar is the
; first 250 bit wires.  key-h2s-sound restates hpos-c-hash-to-scalar-sound
; with that scalar equal to aleo-hash-to-scalar-psd{4,8}-funspec and to
; values-hash-to-scalar-psd4 of the evaluated inputs.

(in-package "ALEOVM")

(include-book "hpos-hash-to-scalar")
(include-book "int-mulpow-wrapped")
(include-book "../fun-specs/curve-network")
(include-book "../fun-specs/values-helpers")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defruled key-poseidon-hash-is-hpos
  (implies (hpos-aleo-rate-p rate)
           (equal (poseidon-hash rate ins)
                  (hpos-poseidon-hash rate ins)))
  :enable (poseidon-hash poseidon-hash-many hpos-poseidon-hash hpos-aleo-rate-p))

(defruled key-curve-hash-to-scalar-psd-is-mod
  (implies (hpos-aleo-rate-p rate)
           (equal (curve-hash-to-scalar-psd rate ins)
                  (mod (nfix (hpos-poseidon-hash rate ins)) (expt 2 250))))
  :enable (curve-hash-to-scalar-psd curve-scalar-from-field-lossy
           key-poseidon-hash-is-hpos))

(defruled key-values-hash-to-scalar-psd4-is-mod
  (implies (pfield::fe-listp ins (base-prime))
           (equal (values-hash-to-scalar-psd4 ins)
                  (mod (nfix (hpos-poseidon-hash 4 ins)) (expt 2 250))))
  :enable (values-hash-to-scalar-psd4 values-scalar-from-field-lossy
           key-poseidon-hash-is-hpos hpos-aleo-rate-p fieldp pfield::fep)
  :use key-natp-of-hpos-poseidon-hash-4
  :prep-lemmas
  ((defrule key-values-field-listp-when-fe-listp
     (implies (pfield::fe-listp ins (base-prime))
              (values-field-listp ins))
     :enable (pfield::fe-listp fieldp values-field-listp)
     :induct (len ins))
   (defrule key-fieldp-of-hpos-poseidon-hash-4
     (fieldp (hpos-poseidon-hash 4 ins))
     :enable (hpos-poseidon-hash hpos-aleo-rate-p fieldp)
     :use (:instance fe-listp-of-poseidon-hash-many (rate 4) (inputs ins)
                     (num-outputs 1))
     :disable fe-listp-of-poseidon-hash-many)
   (defrule key-natp-of-hpos-poseidon-hash-4
     (natp (hpos-poseidon-hash 4 ins))
     :rule-classes (:rewrite :type-prescription)
     :use key-fieldp-of-hpos-poseidon-hash-4
     :in-theory (e/d (fieldp pfield::fep) (key-fieldp-of-hpos-poseidon-hash-4)))))

(defmacro key-h2s-hyps ()
  '(and (hpos-aleo-rate-p rate)
        (symbolp u)
        (symbolp x)
        (not (equal u x))
        (symbol-listp bs)
        (symbol-listp rs)
        (not (member-equal x bs))
        (not (member-equal x rs))
        (equal (len bs) (integer-length (base-prime)))
        (equal (len rs) (bits-lt-prime-rlen (base-prime)))
        (r1cs::r1cs-valuationp asgx (base-prime))
        (not (r1cs::valuation-bindsp asgx x))
        (r1cs::valuation-binds-allp asgx bs)
        (r1cs::valuation-binds-allp asgx rs)
        (r1cs::valuation-bindsp asgx u)
        (equal (lookup-equal u asgx) 1)
        (r1cs::r1cs-constraints-holdp cs asgx (base-prime))))

(defrule key-h2s-sound
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar rate xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many rate xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime))))
    (implies (key-h2s-hyps)
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (curve-hash-to-scalar-psd rate ins)))))
  :do-not-induct t
  :enable key-curve-hash-to-scalar-psd-is-mod
  :disable hpos-c-hash-to-scalar-sound
  :use (hpos-c-hash-to-scalar-sound
        (:instance int-mulpow-lebits=>nat-take-nthcdr
                   (h 250)
                   (b (lookup-equal-list
                       (mv-nth 0 (hpos-h2s-wires
                                  (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))
                       asgx)))))

(defrule key-fe-listp-of-hpos-lc-eval-list
  (implies (dm::primep p)
           (pfield::fe-listp (hpos-lc-eval-list xs asg p) p))
  :enable (hpos-lc-eval-list pfield::fe-listp)
  :induct (len xs))

(defrule key-h2s-psd4-sound
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar 4 xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many 4 xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime)))
       (sk (lebits=>nat (take 250 (lookup-equal-list bs asgx)))))
    (implies (let ((rate 4)) (key-h2s-hyps))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal sk (aleo-hash-to-scalar-psd4-funspec ins))
                  (equal sk (values-hash-to-scalar-psd4 ins)))))
  :do-not-induct t
  :enable (aleo-hash-to-scalar-psd4-funspec key-values-hash-to-scalar-psd4-is-mod
           key-curve-hash-to-scalar-psd-is-mod hpos-aleo-rate-p)
  :disable key-h2s-sound
  :use ((:instance key-h2s-sound (rate 4))
        hpos-primep-of-base))

(defrule key-h2s-psd8-sound
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar 8 xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many 8 xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime))))
    (implies (let ((rate 8)) (key-h2s-hyps))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (aleo-hash-to-scalar-psd8-funspec ins)))))
  :do-not-induct t
  :enable (aleo-hash-to-scalar-psd8-funspec hpos-aleo-rate-p)
  :disable key-h2s-sound
  :use (:instance key-h2s-sound (rate 8)))
