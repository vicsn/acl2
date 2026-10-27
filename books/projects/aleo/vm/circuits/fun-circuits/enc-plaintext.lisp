; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::encrypt_with_randomizers, Plaintext::encrypt_symmetric
; (snarkVM circuit/program/src/data/plaintext/encrypt.rs) and
; Owner::<Plaintext>::encrypt (record/helpers/owner.rs).
;
; encrypt_with_randomizers: to_fields (the constraints of write_bits_le,
;   ptx-bits.lisp), then zip_eq with the randomizers (a host length check)
;   and Field::add per element, which builds the linear combination
;   chunk_i + r_i and emits no constraint; Ciphertext::from_fields checks
;   the length on the host.  The output value of element i is therefore
;   the field sum of the chunk value and the randomizer value.
; encrypt_symmetric: num_randomizers (size_in_fields, which runs
;   write_bits_le; the later to_fields reuses the cached bits and emits
;   nothing new), then hash_many_psd8([encryption_domain, key], n) with the
;   domain a constant (hpos-aleo.lisp), then encrypt_with_randomizers.
; Owner::encrypt: a public owner is returned unchanged; a private owner's
;   ciphertext is the linear combination address.x + r_0.  No constraint.

(in-package "ALEOVM")

(include-book "ptx-bits")
(include-book "hpos-aleo")
(include-book "grp-mul")
(include-book "../fun-specs/crypto-record")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers.

(defruled enc-base-prime-value
  (equal (base-prime) primes::*bls12-377-scalar-field-prime*)
  :enable (base-prime (:e ecurve::edwards-bls12-q)))

(defruled enc-values-field-listp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbol-listp xs)
                (r1cs::valuation-binds-allp asg xs))
           (values-field-listp (lookup-equal-list xs asg)))
  :induct (len xs)
  :enable (lookup-equal-list r1cs::valuation-binds-allp fieldp values-field-listp
           r1cs::fep-of-lookup-equal primep-of-base-prime))

(defrule enc-len-of-values-field-lists-add
  (implies (equal (len xs) (len ys))
           (equal (len (values-field-lists-add xs ys)) (len xs)))
  :enable values-field-lists-add)

(defruled enc-ciphertext-from-fields-when-short
  (implies (and (values-field-listp xs)
                (<= (len xs) (values-max-data-size-in-fields)))
           (equal (values-ciphertext-from-fields xs) xs))
  :enable values-ciphertext-from-fields)

(defruled enc-len-of-ptx-to-fields-out
  (implies (not (equal (ptx-to-fields-out terms) :error))
           (<= (len (ptx-to-fields-out terms)) (values-max-data-size-in-fields)))
  :enable ptx-to-fields-out)

(defruled enc-values-field-listp-of-plaintext-to-fields
  (implies (not (reserrp (plaintext-to-fields x)))
           (values-field-listp (plaintext-to-fields x)))
  :use (:instance values-field-list-resultp-of-plaintext-to-fields (pt x))
  :enable values-field-list-resultp)

(defrule enc-len-of-ptx-chunks-val
  (equal (len (ptx-chunks-val chunks asg)) (len chunks))
  :enable ptx-chunks-val)

(defthm enc-len-cong
  (implies (equal a b) (equal (len a) (len b)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Plaintext::encrypt_with_randomizers

(define enc-ptx-fields-out (wt)
  :short "The output linear combinations of Plaintext::to_fields."
  (ptx-to-fields-out (append (ptx-bits-out wt nil) (list 1))))

(define enc-halts (out (nrs natp))
  :short "Host halts of encrypt_with_randomizers: to_fields exceeds the size
          limit, or zip_eq sees a length mismatch."
  (or (equal out :error)
      (not (equal (len out) nrs))))

(defruled enc-ptx-encrypt-with-randomizers-vals
  (b* ((out (enc-ptx-fields-out wt))
       (spec (plaintext-encrypt-with-randomizers (ptx-val wt asg) rvals)))
    (implies (and (ptx-wtp wt)
                  (ptx-typed wt asg)
                  (values-field-listp rvals)
                  (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil)
                                                asg (base-prime)))
             (and (iff (enc-halts out (len rvals)) (reserrp spec))
                  (implies (not (enc-halts out (len rvals)))
                           (equal (values-field-lists-add
                                   (ptx-chunks-val out asg) rvals)
                                  spec)))))
  :do-not-induct t
  :use ((:instance ptx-to-fields-sound (p (base-prime)))
        (:instance ptx-write-bits-le-sound (p (base-prime)))
        (:instance enc-values-field-listp-of-plaintext-to-fields
                   (x (ptx-val wt asg)))
        (:instance enc-len-of-ptx-to-fields-out
                   (terms (append (ptx-bits-out wt nil) (list 1))))
        (:instance enc-len-cong
                   (a (ptx-chunks-val (ptx-to-fields-out
                                       (append (ptx-bits-out wt nil) (list 1)))
                                      asg))
                   (b (plaintext-to-fields (ptx-val wt asg))))
        (:instance enc-ciphertext-from-fields-when-short
                   (xs (values-field-lists-add
                        (plaintext-to-fields (ptx-val wt asg))
                        rvals))))
  :enable (plaintext-encrypt-with-randomizers enc-ptx-fields-out enc-halts
           primep-of-base-prime))

(defruled enc-ptx-encrypt-with-randomizers-sound
  :short "R1CS-SOUND of Plaintext::encrypt_with_randomizers, given
          Literal::new on each leaf (as Plaintext::to_fields): the
          ciphertext values (chunk + randomizer) are the funspec's result
          on the plaintext and randomizers the wires denote, and snarkVM
          halts exactly when the funspec fails."
  (b* ((out (enc-ptx-fields-out wt))
       (rvals (lookup-equal-list rs asg))
       (spec (plaintext-encrypt-with-randomizers (ptx-val wt asg) rvals)))
    (implies (and (ptx-wtp wt)
                  (ptx-typed wt asg)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (symbol-listp rs)
                  (r1cs::valuation-binds-allp asg rs)
                  (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil)
                                                asg (base-prime)))
             (and (plaintextp (ptx-val wt asg))
                  (iff (enc-halts out (len rs)) (reserrp spec))
                  (implies (not (enc-halts out (len rs)))
                           (equal (values-field-lists-add
                                   (ptx-chunks-val out asg) rvals)
                                  spec)))))
  :do-not-induct t
  :use ((:instance ptx-write-bits-le-sound (p (base-prime)))
        (:instance enc-values-field-listp-of-lookup (xs rs))
        (:instance enc-ptx-encrypt-with-randomizers-vals
                   (rvals (lookup-equal-list rs asg))))
  :enable primep-of-base-prime)

(defruled enc-ptx-encrypt-with-randomizers-complete
  :short "R1CS-COMPLETE of Plaintext::encrypt_with_randomizers: the leaf
          witnesses satisfy the constraints (those of to_fields)."
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (ptx-bits-witnessp wt nil asg p))
           (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
  :use (:instance ptx-write-bits-complete (bigp nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Plaintext::encrypt_symmetric

(defund enc-randomizer-inputs (key)
  (declare (xargs :verify-guards nil))
  (list (hpos-lc-const (values-encryption-domain)) (hpos-lc-var key)))

(defund enc-c-ptx-encrypt-symmetric (wt key vs asg)
  "Synthesis of Plaintext::encrypt_symmetric: returns
   (mv out rs cs vs asg) with out the to_fields chunks, rs the
   randomizer linear combinations and cs the constraints."
  (declare (xargs :verify-guards nil))
  (b* ((n (ptx-size-in-fields wt))
       ((mv rs cs vs asg)
        (hpos-c-poseidon-hash-many 8 (enc-randomizer-inputs key) (nfix n) vs asg)))
    (mv (enc-ptx-fields-out wt) rs (append (ptx-bits-gadget wt nil) cs) vs asg)))

(define enc-sym-halts (wt out rs)
  (or (equal (ptx-size-in-fields wt) :error)
      (enc-halts out (len rs))))

(defruled enc-eval-randomizer-inputs
  (implies (and (symbolp key)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg key))
           (equal (hpos-lc-eval-list (enc-randomizer-inputs key) asg
                                     primes::*bls12-377-scalar-field-prime*)
                  (list (values-encryption-domain) (lookup-equal key asg))))
  :use ((:instance r1cs::fep-of-lookup-equal (var key) (valuation asg) (prime (base-prime)))
        fieldp-of-values-encryption-domain)
  :enable (enc-randomizer-inputs hpos-lc-eval-list enc-base-prime-value
           fieldp pfield::fep))

(defruled enc-crypto-hash-many-psd-8
  (equal (crypto-hash-many-psd 8 inputs n)
         (hpos-poseidon-hash-many 8 inputs n))
  :enable (crypto-hash-many-psd poseidon-hash-many))

(defrule enc-len-of-hpos-poseidon-hash-many-8
  (equal (len (hpos-poseidon-hash-many 8 inputs n)) (nfix n))
  :use (:instance len-of-crypto-hash-many-psd (rate 8) (num-outputs n))
  :in-theory (e/d (enc-crypto-hash-many-psd-8) (len-of-crypto-hash-many-psd)))

(defrule enc-values-field-listp-of-hpos-poseidon-hash-many-8
  (values-field-listp (hpos-poseidon-hash-many 8 inputs n))
  :use (:instance crypto-field-listp-of-poseidon-hash-many
                  (rate 8) (num-outputs n))
  :in-theory (e/d (poseidon-hash-many) (crypto-field-listp-of-poseidon-hash-many)))

(defrule enc-ptx-size-in-fields-type
  (or (equal (ptx-size-in-fields wt) :error)
      (natp (ptx-size-in-fields wt)))
  :rule-classes ((:type-prescription :corollary
                  (or (equal (ptx-size-in-fields wt) :error)
                      (natp (ptx-size-in-fields wt)))))
  :enable ptx-size-in-fields)

(defruled enc-ptx-encrypt-symmetric-sound
  :short "R1CS-SOUND of Plaintext::encrypt_symmetric, given Literal::new on
          each leaf and a field key wire: in any assignment satisfying the
          constraints, the ciphertext values are the funspec's result, and
          snarkVM halts exactly when the funspec fails."
  (b* (((mv out rs cs & &) (enc-c-ptx-encrypt-symmetric wt key vs asg))
       (spec (plaintext-encrypt-symmetric (ptx-val wt asgx)
                                                 (lookup-equal key asgx))))
    (implies (and (ptx-wtp wt)
                  (ptx-typed wt asgx)
                  (r1cs::r1cs-valuationp asgx (base-prime))
                  (symbolp key)
                  (r1cs::valuation-bindsp asgx key)
                  (r1cs::r1cs-constraints-holdp cs asgx (base-prime)))
             (and (iff (enc-sym-halts wt out rs) (reserrp spec))
                  (implies (not (enc-sym-halts wt out rs))
                           (equal (values-field-lists-add
                                   (ptx-chunks-val out asgx)
                                   (hpos-lc-eval-list rs asgx (base-prime)))
                                  spec)))))
  :do-not-induct t
  :use ((:instance ptx-num-randomizers-sound (p (base-prime)) (asg asgx))
        (:instance r1cs::fep-of-lookup-equal (var key) (valuation asgx)
                   (prime (base-prime)))
        (:instance enc-ptx-encrypt-with-randomizers-vals
                   (asg asgx)
                   (rvals (hpos-lc-eval-list
                           (mv-nth 0 (hpos-c-poseidon-hash-many
                                      8 (enc-randomizer-inputs key)
                                      (nfix (ptx-size-in-fields wt)) vs asg))
                           asgx (base-prime))))
        (:instance hpos-c-poseidon-hash-many-sound
                   (rate 8) (xs (enc-randomizer-inputs key))
                   (nout (nfix (ptx-size-in-fields wt))))
        (:instance enc-len-cong
                   (a (hpos-lc-eval-list
                       (mv-nth 0 (hpos-c-poseidon-hash-many
                                  8 (enc-randomizer-inputs key)
                                  (nfix (ptx-size-in-fields wt)) vs asg))
                       asgx primes::*bls12-377-scalar-field-prime*))
                   (b (hpos-poseidon-hash-many
                       8 (hpos-lc-eval-list (enc-randomizer-inputs key) asgx
                                            primes::*bls12-377-scalar-field-prime*)
                       (nfix (ptx-size-in-fields wt)))))
        (:instance enc-eval-randomizer-inputs (asg asgx)))
  :enable (enc-c-ptx-encrypt-symmetric enc-sym-halts plaintext-encrypt-symmetric
           poseidon-hash-many enc-base-prime-value values-field-fix fieldp
           hpos-aleo-rate-p r1cs::r1cs-constraints-holdp-of-append))

(defrule enc-randomizer-inputs-boundp
  (implies (and (symbolp key) (r1cs::valuation-bindsp asg key))
           (hpos-lc-list-boundp (enc-randomizer-inputs key) asg))
  :enable (enc-randomizer-inputs hpos-lc-list-boundp hpos-lc-boundp
           hpos-lc-sv hpos-terms-sv hpos-sv-boundp hpos-lc-const hpos-lc-var
           hpos-pv))

(defrule enc-len-of-enc-randomizer-inputs
  (equal (len (enc-randomizer-inputs key)) 2)
  :enable enc-randomizer-inputs)

(defruled enc-hash-complete-step
  (b* (((mv & cs2 & asg2) (hpos-c-poseidon-hash-many
                            8 (enc-randomizer-inputs key) n vs asg)))
    (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound 8 2 n) (len vs))
                  (symbolp key)
                  (r1cs::valuation-bindsp asg key))
             (and (r1cs::r1cs-valuationp asg2 (base-prime))
                  (hpos-ext-p asg asg2)
                  (no-duplicatesp-equal (strip-cars asg2))
                  (r1cs::r1cs-constraints-holdp cs2 asg2 (base-prime)))))
  :use ((:instance hpos-c-poseidon-hash-many-complete
                   (rate 8) (xs (enc-randomizer-inputs key)) (nout n)))
  :in-theory (e/d (enc-base-prime-value hpos-aleo-rate-p hpos-wit-okp)
                  (hpos-c-poseidon-hash-many-complete)))

(defruled enc-ptx-encrypt-symmetric-complete
  :short "R1CS-COMPLETE of Plaintext::encrypt_symmetric: from an assignment
          with the leaf witnesses and the key, Poseidon witness generation
          yields an assignment satisfying all the constraints.  The leaf
          constraints are assumed to mention only wires bound in the
          starting assignment."
  (b* (((mv & & cs & asg2) (enc-c-ptx-encrypt-symmetric wt key vs asg)))
    (implies (and (ptx-wtp wt)
                  (ptx-typed wt asg)
                  (ptx-bits-witnessp wt nil asg (base-prime))
                  (hpos-cs-boundp (ptx-bits-gadget wt nil) asg)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound 8 2 (nfix (ptx-size-in-fields wt)))
                      (len vs))
                  (symbolp key)
                  (r1cs::valuation-bindsp asg key))
             (r1cs::r1cs-constraints-holdp cs asg2 (base-prime))))
  :do-not-induct t
  :use ((:instance ptx-write-bits-complete (p (base-prime)) (bigp nil))
        (:instance enc-hash-complete-step (n (nfix (ptx-size-in-fields wt))))
        (:instance hpos-holdp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many
                                   8 (enc-randomizer-inputs key)
                                   (nfix (ptx-size-in-fields wt)) vs asg)))
                   (cs (ptx-bits-gadget wt nil))
                   (p (base-prime))))
  :in-theory (e/d (enc-c-ptx-encrypt-symmetric
                   r1cs::r1cs-constraints-holdp-of-append primep-of-base-prime)
                  (hpos-holdp-when-ext-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Plaintext::encrypt: (address.to_group() * randomizer).to_x_coordinate()
; is the plaintext view key, then encrypt_symmetric.  The product is
; Group::mul_assign on the scalar's to_bits_be (grp-mul.lisp); its output
; x-coordinate wire is the key wire of encrypt_symmetric.

(defmacro enc-mul-hyps (asg)
  `(and (consp bits)
        (grp-bits-ok bits ,asg)
        (grp-steps-boundp steps ,asg)
        (equal (len steps) (len (cdr bits)))
        (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
        (r1cs::valuation-bindsp ,asg bx) (r1cs::valuation-bindsp ,asg by)
        (r1cs::valuation-bindsp ,asg ox) (r1cs::valuation-bindsp ,asg oy)
        (r1cs::r1cs-valuationp ,asg (base-prime))))

(defund enc-c-ptx-encrypt (wt bits ox oy steps bx by vs asg)
  "Synthesis of Plaintext::encrypt: (mv out rs cs vs asg)."
  (declare (xargs :verify-guards nil))
  (b* ((key (car (grp-mul-out bits ox oy steps)))
       ((mv out rs cs vs asg) (enc-c-ptx-encrypt-symmetric wt key vs asg)))
    (mv out rs (append (grp-mul-gadget bits ox oy steps bx by (base-prime)) cs)
        vs asg)))

(defruled enc-view-key-wire
  (b* ((out (grp-mul-out bits ox oy steps))
       (asg asgx))
    (implies (and (enc-mul-hyps asgx)
                  (groupp (grp-pt bx by))
                  (scalarp s)
                  (equal (grp-bit-vals bits asgx) (rev (scalar-bits-le s)))
                  (symbolp (first out)) (r1cs::valuation-bindsp asgx (first out))
                  (symbolp (second out)) (r1cs::valuation-bindsp asgx (second out))
                  (r1cs::r1cs-constraints-holdp
                   (grp-mul-gadget bits ox oy steps bx by (base-prime))
                   asgx (base-prime)))
             (equal (values-group-x (values-group-mul s (grp-pt bx by)))
                    (lookup-equal (first out) asgx))))
  :do-not-induct t
  :use ((:instance grp-mul-gadget-sound-funspec (asg asgx) (p (base-prime)))
        (:instance hbhp-r-pointp-of-mul (k s) (p1 (grp-pt bx by)))
        (:instance grp-point-coords
                   (x (lookup-equal (first (grp-mul-out bits ox oy steps)) asgx))
                   (y (lookup-equal (second (grp-mul-out bits ox oy steps)) asgx)))
        (:instance r1cs::fep-of-lookup-equal
                   (var (first (grp-mul-out bits ox oy steps))) (valuation asgx)
                   (prime (base-prime)))
        (:instance r1cs::fep-of-lookup-equal
                   (var (second (grp-mul-out bits ox oy steps))) (valuation asgx)
                   (prime (base-prime))))
  :in-theory (e/d (values-group-x values-group-mul values-to-group group-mul-funspec
                   values-scalar-fix values-group-fix groupp fieldp
                   ecurve::edwards-bls12-point->u primep-of-base-prime)
                  (grp-mul-gadget-sound-funspec hbhp-r-pointp-of-mul)))

(defruled enc-ptx-encrypt-sound
  :short "R1CS-SOUND of Plaintext::encrypt, given Literal::new on each leaf,
          Address::new on the address wires and Scalar::to_bits_be on the
          randomizer (the bit wires of mul_assign): the ciphertext values
          are plaintext-encrypt of the wire plaintext, address and scalar,
          and snarkVM halts exactly when it fails."
  (b* (((mv out rs cs & &) (enc-c-ptx-encrypt wt bits ox oy steps bx by vs asg))
       (kout (grp-mul-out bits ox oy steps))
       (spec (plaintext-encrypt (ptx-val wt asgx) (ecurve::point-finite
                                                  (lookup-equal bx asgx)
                                                  (lookup-equal by asgx))
                                s)))
    (implies (and (enc-mul-hyps asgx)
                  (groupp (ecurve::point-finite (lookup-equal bx asgx)
                                                (lookup-equal by asgx)))
                  (scalarp s)
                  (equal (grp-bit-vals bits asgx) (rev (scalar-bits-le s)))
                  (symbolp (first kout)) (r1cs::valuation-bindsp asgx (first kout))
                  (symbolp (second kout)) (r1cs::valuation-bindsp asgx (second kout))
                  (ptx-wtp wt)
                  (ptx-typed wt asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx (base-prime)))
             (and (iff (enc-sym-halts wt out rs) (reserrp spec))
                  (implies (not (enc-sym-halts wt out rs))
                           (equal (values-field-lists-add
                                   (ptx-chunks-val out asgx)
                                   (hpos-lc-eval-list rs asgx (base-prime)))
                                  spec)))))
  :do-not-induct t
  :use ((:instance enc-view-key-wire)
        (:instance enc-ptx-encrypt-symmetric-sound
                   (key (first (grp-mul-out bits ox oy steps)))))
  :in-theory (e/d (enc-c-ptx-encrypt plaintext-encrypt
                   r1cs::r1cs-constraints-holdp-of-append)
                  (enc-ptx-encrypt-symmetric-sound)))

(defruled enc-ptx-encrypt-complete
  :short "R1CS-COMPLETE of Plaintext::encrypt: with the mul_assign
          witnesses and the leaf witnesses in the starting assignment
          (whose constraints mention only its wires), Poseidon witness
          generation yields an assignment satisfying all the constraints."
  (b* (((mv & & cs & asg2) (enc-c-ptx-encrypt wt bits ox oy steps bx by vs asg))
       (kout (grp-mul-out bits ox oy steps)))
    (implies (and (r1cs::r1cs-constraints-holdp
                   (grp-mul-gadget bits ox oy steps bx by (base-prime))
                   asg (base-prime))
                  (hpos-cs-boundp (grp-mul-gadget bits ox oy steps bx by (base-prime))
                                  asg)
                  (ptx-wtp wt)
                  (ptx-typed wt asg)
                  (ptx-bits-witnessp wt nil asg (base-prime))
                  (hpos-cs-boundp (ptx-bits-gadget wt nil) asg)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound 8 2 (nfix (ptx-size-in-fields wt)))
                      (len vs))
                  (symbolp (first kout))
                  (r1cs::valuation-bindsp asg (first kout)))
             (r1cs::r1cs-constraints-holdp cs asg2 (base-prime))))
  :do-not-induct t
  :use ((:instance enc-ptx-encrypt-symmetric-complete
                   (key (first (grp-mul-out bits ox oy steps))))
        (:instance enc-hash-complete-step
                   (key (first (grp-mul-out bits ox oy steps)))
                   (n (nfix (ptx-size-in-fields wt))))
        (:instance hpos-holdp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many
                                   8 (enc-randomizer-inputs
                                      (first (grp-mul-out bits ox oy steps)))
                                   (nfix (ptx-size-in-fields wt)) vs asg)))
                   (cs (grp-mul-gadget bits ox oy steps bx by (base-prime)))
                   (p (base-prime))))
  :in-theory (e/d (enc-c-ptx-encrypt enc-c-ptx-encrypt-symmetric
                   r1cs::r1cs-constraints-holdp-of-append)
                  (hpos-holdp-when-ext-p enc-ptx-encrypt-symmetric-complete)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner::<Plaintext>::encrypt

(define enc-owner-encrypt-out ((publicp booleanp) ax ay (rs true-listp) asg)
  :short "The output of Owner::encrypt in variable mode: the public owner
          point unchanged, or the one-field ciphertext address.x + r_0.
          Returns :error where snarkVM halts (wrong randomizer count)."
  (if publicp
      (if (endp rs)
          (crypto-ciphertext-owner-public
           (ecurve::point-finite (lookup-equal ax asg) (lookup-equal ay asg)))
        :error)
    (if (equal (len rs) 1)
        (crypto-ciphertext-owner-private
         (list (pfield::add (lookup-equal ax asg) (lookup-equal (car rs) asg)
                            (base-prime))))
      :error)))

(define enc-owner-encrypt-gadget ()
  :short "Constraints of Owner::encrypt: none (linear combinations only)."
  nil)

(defruled enc-owner-encrypt-sound
  :short "R1CS-SOUND of Owner::encrypt, given Address::new on the owner
          (the wire point is groupp): the output is the funspec's result on
          the owner and randomizers the wires denote, and snarkVM halts
          exactly when the funspec fails."
  (b* ((pt (ecurve::point-finite (lookup-equal ax asg) (lookup-equal ay asg)))
       (owner (if publicp (owner-public pt) (owner-private pt)))
       (out (enc-owner-encrypt-out publicp ax ay rs asg))
       (spec (crypto-owner-encrypt owner (lookup-equal-list rs asg))))
    (implies (and (groupp pt)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (symbolp ax)
                  (r1cs::valuation-bindsp asg ax)
                  (symbol-listp rs)
                  (r1cs::valuation-binds-allp asg rs)
                  (r1cs::r1cs-constraints-holdp (enc-owner-encrypt-gadget)
                                                asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use ((:instance enc-values-field-listp-of-lookup (xs rs))
        (:instance r1cs::fep-of-lookup-equal (var ax) (valuation asg)
                   (prime (base-prime))))
  :expand ((lookup-equal-list rs asg))
  :enable (enc-owner-encrypt-out crypto-owner-encrypt crypto-field-add crypto-group-x
           crypto-edwards-bls12-pointp-when-groupp values-field-listp
           ecurve::edwards-bls12-point->u spec-error))

(defruled enc-owner-encrypt-complete
  (r1cs::r1cs-constraints-holdp (enc-owner-encrypt-gadget) asg p)
  :enable (enc-owner-encrypt-gadget r1cs::r1cs-constraints-holdp))
