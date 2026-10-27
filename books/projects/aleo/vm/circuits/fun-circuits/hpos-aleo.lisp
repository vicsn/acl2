; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Poseidon circuits instantiated with the network parameters
; (Poseidon2/4/8, alpha 17, domains AleoPoseidon2/4/8), and Inject::new.
;
; Field::pow with a constant exponent walks exponent.to_bits_be(), i.e. the
; 253 big-endian bits of the field element 17.

(in-package "ALEOVM")

(include-book "hpos-sponge")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defund hpos-alpha-bits ()
  (declare (xargs :verify-guards nil))
  (append (repeat 248 0) (list 1 0 0 0 1)))

(defrule hpos-alpha-bits-val
  (equal (hpos-bits-val 0 (hpos-alpha-bits)) 17))

(defrule hpos-len-of-hpos-alpha-bits
  (equal (len (hpos-alpha-bits)) 253))

(in-theory (disable (:e hpos-alpha-bits)))

(defrule hpos-aleo-params-facts
  (implies (hpos-aleo-rate-p rate)
           (and (equal (hpos-params->prime (hpos-aleo-params rate))
                       primes::*bls12-377-scalar-field-prime*)
                (equal (hpos-params->alpha (hpos-aleo-params rate)) 17)
                (pfield::fep (hpos-aleo-domain rate)
                             primes::*bls12-377-scalar-field-prime*)))
  :enable hpos-aleo-rate-p)

(defrule hpos-primep-of-base
  (dm::primep primes::*bls12-377-scalar-field-prime*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inject::new for Mode::Constant: the parameters become constants and the
;; domain separator a constant field element; no constraints, no variables.

(defund hpos-c-new (rate)
  (declare (xargs :verify-guards nil))
  (mv (hpos-lc-const (hpos-aleo-domain rate)) (hpos-aleo-params rate) nil))

(defrule hpos-c-new-correct
  (b* (((mv domain params cs) (hpos-c-new rate)))
    (implies (hpos-aleo-rate-p rate)
             (and (hpos-lc-constp domain)
                  (equal (hpos-lc-eval domain asg primes::*bls12-377-scalar-field-prime*)
                         (hpos-aleo-domain rate))
                  (equal params (hpos-aleo-params rate))
                  (equal cs nil))))
  :enable (hpos-c-new hpos-lc-constp hpos-lc-const pfield::fep)
  :disable hpos-aleo-params-facts
  :use hpos-aleo-params-facts)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; HashMany::hash_many on the network instances.

(defund hpos-c-poseidon-hash-many (rate xs nout vs asg)
  (declare (xargs :verify-guards nil))
  (hpos-c-hash-many (hpos-aleo-domain rate) xs nout rate (hpos-aleo-params rate)
                    (hpos-alpha-bits) vs asg))

(defund hpos-poseidon-bound (rate nin nout)
  (declare (xargs :verify-guards nil))
  (hpos-hash-many-bound rate nin nout (hpos-aleo-params rate) (hpos-alpha-bits)))

(defrule hpos-c-poseidon-hash-many-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-poseidon-hash-many rate xs nout vs asg))))
  :enable hpos-c-poseidon-hash-many)

(hpos-def-mono hpos-c-poseidon-hash-many
               (hpos-c-poseidon-hash-many rate xs nout vs asg))

(defrule hpos-c-poseidon-hash-many-sound
  (b* (((mv outs cs & &) (hpos-c-poseidon-hash-many rate xs nout vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list outs asgx p)
                    (hpos-poseidon-hash-many rate (hpos-lc-eval-list xs asgx p) nout))))
  :enable (hpos-c-poseidon-hash-many hpos-poseidon-hash-many)
  :disable (hpos-c-hash-many-sound hpos-aleo-params-facts (:e dm::primep))
  :use (hpos-aleo-params-facts
        hpos-primep-of-base
        (:instance hpos-c-hash-many-sound
                   (domain (hpos-aleo-domain rate))
                   (params (hpos-aleo-params rate))
                   (bits (hpos-alpha-bits)))))

(defrule hpos-c-poseidon-hash-many-vs-len
  (b* (((mv & & vs2 &) (hpos-c-poseidon-hash-many rate xs nout vs asg)))
    (and (<= (- (len vs) (hpos-poseidon-bound rate (len xs) nout)) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable (hpos-c-poseidon-hash-many hpos-poseidon-bound))

(defrule hpos-c-poseidon-hash-many-complete
  (b* (((mv outs cs vs2 asg2) (hpos-c-poseidon-hash-many rate xs nout vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound rate (len xs) nout) (len vs))
                  (hpos-lc-list-boundp xs asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp outs asg2))))
  :enable (hpos-c-poseidon-hash-many hpos-poseidon-bound)
  :disable (hpos-c-hash-many-complete hpos-aleo-params-facts (:e dm::primep))
  :use (hpos-aleo-params-facts
        hpos-primep-of-base
        (:instance hpos-c-hash-many-complete
                   (domain (hpos-aleo-domain rate))
                   (params (hpos-aleo-params rate))
                   (bits (hpos-alpha-bits)))))

;; Poseidon::hash: the first output of hash_many with one output.

(defund hpos-c-poseidon-hash (rate xs vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv outs cs vs asg) (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
    (mv (car outs) cs vs asg)))
