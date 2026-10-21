; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Poseidon wrappers of snarkVM circuit/network/src/v0.rs:
;
;   hash_many_psdR(input, n)   = POSEIDON_R.hash_many(input, n)
;   hash_to_scalar_psdR(input) = POSEIDON_R.hash_to_scalar(input)
;   hash_to_group_psdR(input)  = POSEIDON_R.hash_to_group(input)
;
; for R = 2, 4, 8.  The POSEIDON_R instances are constants
; (Poseidon::setup("AleoPoseidonR")), so each wrapper emits exactly the
; certified gadget hpos-c-poseidon-hash-many, hpos-c-hash-to-scalar or
; hpos-c-hash-to-group at rate R; num_outputs is a synthesis-time u16.

(in-package "ALEOVM")

(include-book "hpos-hash-to-scalar")
(include-book "hpos-hash-to-group")
(include-book "int-mulpow-wrapped")
(include-book "../fun-specs/curve-network")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defruled net-psd-hash-many-is-funspec
  (implies (hpos-aleo-rate-p rate)
           (equal (curve-hash-many-psd rate ins nout)
                  (hpos-poseidon-hash-many rate ins nout)))
  :enable (curve-hash-many-psd poseidon-hash-many hpos-aleo-rate-p))

(defruled net-psd-poseidon-hash-is-hpos
  (implies (hpos-aleo-rate-p rate)
           (equal (poseidon-hash rate ins)
                  (hpos-poseidon-hash rate ins)))
  :enable (poseidon-hash poseidon-hash-many hpos-poseidon-hash hpos-aleo-rate-p))

(defruled net-psd-hash-to-scalar-is-mod
  (implies (hpos-aleo-rate-p rate)
           (equal (curve-hash-to-scalar-psd rate ins)
                  (mod (nfix (hpos-poseidon-hash rate ins)) (expt 2 250))))
  :enable (curve-hash-to-scalar-psd curve-scalar-from-field-lossy
           net-psd-poseidon-hash-is-hpos))

(defruledl net-psd-elligator2-encode-when-validp
  (implies (hped-elligator2-encode-validp h)
           (equal (elligator2-encode h) (hped-elligator2-encode h)))
  :enable (elligator2-encode hped-elligator2-encode-total))

(defruled net-psd-hash-to-group-is-funspec
  (implies (and (hpos-aleo-rate-p rate) (consp in))
           (and (iff (reserrp (curve-hash-to-group-psd rate in))
                     (not (hpos-hash-to-group-validp rate in)))
                (implies (hpos-hash-to-group-validp rate in)
                         (equal (curve-hash-to-group-psd rate in)
                                (hpos-hash-to-group-spec rate in)))))
  :use ((:instance net-psd-elligator2-encode-when-validp
                   (h (first (poseidon-hash-many rate in 2))))
        (:instance net-psd-elligator2-encode-when-validp
                   (h (second (poseidon-hash-many rate in 2)))))
  :in-theory (e/d (curve-hash-to-group-psd hpos-aleo-rate-p
                   hpos-hash-to-group-validp
                   hpos-hash-to-group-spec hpos-hash-to-group-fields
                   poseidon-hash-many group-add-funspec spec-error)
                  (hped-elligator2-encode-validp hped-elligator2-encode
                   elligator2-encode)))

(defun net-psd-sym (pre s n post)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string pre s (coerce (explode-nonnegative-integer n 10 nil) 'string) post)
   'net-psd-sym))

(defmacro net-psd-instance (n)
  (flet ((name (s n) (net-psd-sym "NET-" s n ""))
         (fn (s n) (net-psd-sym "ALEO-" s n "-FUNSPEC")))
    `(progn
       (defruled ,(name "HASH-MANY-PSD-SOUND-" n)
         (b* (((mv outs cs & &) (hpos-c-poseidon-hash-many ,n xs nout vs asg))
              (p primes::*bls12-377-scalar-field-prime*))
           (implies (r1cs::r1cs-constraints-holdp cs asgx p)
                    (equal (hpos-lc-eval-list outs asgx p)
                           (,(fn "HASH-MANY-PSD" n) (hpos-lc-eval-list xs asgx p) nout))))
         :use ((:instance hpos-c-poseidon-hash-many-sound (rate ,n))
               (:instance net-psd-hash-many-is-funspec
                          (rate ,n) (ins (hpos-lc-eval-list xs asgx
                                                            primes::*bls12-377-scalar-field-prime*))))
         :in-theory '(,(fn "HASH-MANY-PSD" n) (:e hpos-aleo-rate-p)))

       (defruled ,(name "HASH-MANY-PSD-COMPLETE-" n)
         (b* (((mv outs cs vs2 asg2) (hpos-c-poseidon-hash-many ,n xs nout vs asg))
              (p primes::*bls12-377-scalar-field-prime*))
           (implies (and (r1cs::r1cs-valuationp asg p)
                         (hpos-supply-okp vs asg)
                         (<= (hpos-poseidon-bound ,n (len xs) nout) (len vs))
                         (hpos-lc-list-boundp xs asg))
                    (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                         (hpos-lc-list-boundp outs asg2))))
         :use (:instance hpos-c-poseidon-hash-many-complete (rate ,n))
         :in-theory '((:e hpos-aleo-rate-p)))

       (defruled ,(name "HASH-TO-SCALAR-PSD-SOUND-" n)
         (b* (((mv bits cs & &) (hpos-c-hash-to-scalar ,n xs u vs asg))
              ((mv & & vs1 &) (hpos-c-poseidon-hash-many ,n xs 1 vs asg))
              ((mv bs rs x &) (hpos-h2s-wires vs1))
              (p (base-prime))
              (ins (hpos-lc-eval-list xs asgx p)))
           (implies (and (symbolp u)
                         (symbolp x)
                         (not (equal u x))
                         (symbol-listp bs)
                         (symbol-listp rs)
                         (not (member-equal x bs))
                         (not (member-equal x rs))
                         (equal (len bs) (integer-length p))
                         (equal (len rs) (bits-lt-prime-rlen p))
                         (r1cs::r1cs-valuationp asgx p)
                         (not (r1cs::valuation-bindsp asgx x))
                         (r1cs::valuation-binds-allp asgx bs)
                         (r1cs::valuation-binds-allp asgx rs)
                         (r1cs::valuation-bindsp asgx u)
                         (equal (lookup-equal u asgx) 1)
                         (r1cs::r1cs-constraints-holdp cs asgx p))
                    (and (equal bits (take 250 bs))
                         (bit-listp (lookup-equal-list bs asgx))
                         (scalarp (lebits=>nat (take 250 (lookup-equal-list bs asgx))))
                         (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                                (,(fn "HASH-TO-SCALAR-PSD" n) ins)))))
         :do-not-induct t
         :use ((:instance hpos-c-hash-to-scalar-sound (rate ,n))
               (:instance net-psd-hash-to-scalar-is-mod
                          (rate ,n) (ins (hpos-lc-eval-list xs asgx (base-prime))))
               (:instance scalarp-of-curve-hash-to-scalar-psd
                          (rate ,n) (inputs (hpos-lc-eval-list xs asgx (base-prime))))
               (:instance int-mulpow-lebits=>nat-take-nthcdr
                          (h 250)
                          (b (lookup-equal-list
                              (mv-nth 0 (hpos-h2s-wires
                                         (mv-nth 2 (hpos-c-poseidon-hash-many ,n xs 1 vs asg))))
                              asgx))))
         :in-theory (e/d (,(fn "HASH-TO-SCALAR-PSD" n) (:e hpos-aleo-rate-p))
                         (hpos-c-hash-to-scalar-sound)))

       (defruled ,(name "HASH-TO-SCALAR-PSD-COMPLETE-" n)
         (b* (((mv & cs & asg2) (hpos-c-hash-to-scalar ,n xs u vs asg))
              (p (base-prime)))
           (implies (and (r1cs::r1cs-valuationp asg p)
                         (hpos-supply-okp vs asg)
                         (<= (hpos-h2s-bound ,n (len xs)) (len vs))
                         (hpos-lc-list-boundp xs asg)
                         (symbolp u)
                         (r1cs::valuation-bindsp asg u)
                         (equal (lookup-equal u asg) 1))
                    (and (r1cs::r1cs-valuationp asg2 p)
                         (hpos-ext-p asg asg2)
                         (r1cs::r1cs-constraints-holdp cs asg2 p))))
         :use (:instance hpos-c-hash-to-scalar-complete (rate ,n))
         :in-theory '((:e hpos-aleo-rate-p)))

       (defruled ,(name "HASH-TO-GROUP-PSD-SOUND-" n)
         (b* (((mv g cs & &) (hpos-c-hash-to-group ,n xs u vs asg))
              (p primes::*bls12-377-scalar-field-prime*)
              (in (hpos-lc-eval-list xs asgx p)))
           (implies (and (consp xs)
                         (hpos-h2g-sound-hyps ,n xs u vs asg asgx)
                         (r1cs::r1cs-constraints-holdp cs asgx p))
                    (and (not (reserrp (,(fn "HASH-TO-GROUP-PSD" n) in)))
                         (ecurve::edwards-bls12-pointp (hpos-pt-eval g asgx))
                         (equal (hpos-pt-eval g asgx)
                                (,(fn "HASH-TO-GROUP-PSD" n) in)))))
         :do-not-induct t
         :use ((:instance hpos-c-hash-to-group-sound (rate ,n))
               (:instance net-psd-hash-to-group-is-funspec
                          (rate ,n)
                          (in (hpos-lc-eval-list xs asgx
                                                 primes::*bls12-377-scalar-field-prime*)))
               (:instance return-type-of-curve-hash-to-group-psd
                          (rate ,n)
                          (inputs (hpos-lc-eval-list xs asgx
                                                     primes::*bls12-377-scalar-field-prime*)))
               (:instance net-psd-consp-of-lc-eval-list
                          (p primes::*bls12-377-scalar-field-prime*)))
         :in-theory '(,(fn "HASH-TO-GROUP-PSD" n) (:e hpos-aleo-rate-p)))

       (defruled ,(name "HASH-TO-GROUP-PSD-COMPLETE-" n)
         (b* (((mv g cs & asg2) (hpos-c-hash-to-group ,n xs u vs asg))
              (p primes::*bls12-377-scalar-field-prime*))
           (implies (and (consp xs)
                         (r1cs::r1cs-valuationp asg p)
                         (hpos-supply-okp vs asg)
                         (<= (hpos-h2g-bound ,n (len xs)) (len vs))
                         (hpos-lc-list-boundp xs asg)
                         (symbolp u)
                         (r1cs::valuation-bindsp asg u)
                         (equal (lookup-equal u asg) 1)
                         (not (reserrp (,(fn "HASH-TO-GROUP-PSD" n)
                                        (hpos-lc-eval-list xs asg p)))))
                    (and (r1cs::r1cs-valuationp asg2 p)
                         (hpos-ext-p asg asg2)
                         (r1cs::r1cs-constraints-holdp cs asg2 p)
                         (hpos-pt-boundp g asg2))))
         :do-not-induct t
         :use ((:instance hpos-c-hash-to-group-complete (rate ,n))
               (:instance net-psd-hash-to-group-is-funspec
                          (rate ,n)
                          (in (hpos-lc-eval-list xs asg
                                                 primes::*bls12-377-scalar-field-prime*)))
               (:instance net-psd-consp-of-lc-eval-list
                          (asgx asg) (p primes::*bls12-377-scalar-field-prime*)))
         :in-theory '(,(fn "HASH-TO-GROUP-PSD" n) (:e hpos-aleo-rate-p))))))

(defruled net-psd-consp-of-lc-eval-list
  (implies (consp xs)
           (consp (hpos-lc-eval-list xs asgx p)))
  :enable hpos-lc-eval-list)

(net-psd-instance 2)
(net-psd-instance 4)
(net-psd-instance 8)
