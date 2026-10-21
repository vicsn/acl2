; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::encrypt_symmetric and Record::encrypt (snarkVM circuit/program/src/
; data/record/encrypt.rs):
;   A::assert_eq(nonce, A::g_scalar_multiply(randomizer))
;       net-gmul-gadget (Scalar::to_bits_le, cached as rbits, then the fixed
;       base fold), then two linear constraints nonce.x = out.x, nonce.y = out.y
;   record_view_key = (owner.to_group() * randomizer).to_x_coordinate()
;       grp-mul-gadget on Scalar::to_bits_be = the reverse of the cached rbits
;   encrypt_symmetric_unchecked(record_view_key)
; Record::encrypt is the first component.

(in-package "ALEOVM")

(include-book "enc-record-sym")
(include-book "net-gmul")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; E::assert_eq of a wire and a linear combination: (lc) (1) = (b).

(define enc-lc-eq-gadget (lc b)
  :verify-guards nil
  (list (r1cs::make-r1cs-constraint :a lc
                                    :b (list (list 1 1))
                                    :c (list (list 1 b)))))

(defruled enc-lc-eq-gadget-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbolp b)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp (enc-lc-eq-gadget lc b) asg p)
                  (equal (r1cs::dot-product lc asg p) (lookup-equal b asg))))
  :enable (enc-lc-eq-gadget r1cs::r1cs-constraint-holdsp r1cs::dot-product
           r1cs::fep-of-lookup-equal primep-of-base-prime))

(define enc-nonce-gadget (gout ng)
  :verify-guards nil
  (append (enc-lc-eq-gadget (car gout) (nth 0 ng))
          (enc-lc-eq-gadget (cdr gout) (nth 1 ng))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The to_bits_be wires are the reverse of the cached to_bits_le wires.

(defruled enc-grp-bit-vals-is-lookup-equal-list
  (equal (grp-bit-vals x asg) (lookup-equal-list x asg))
  :enable (grp-bit-vals lookup-equal-list))

(defruled enc-lookup-equal-list-of-append
  (equal (lookup-equal-list (append x y) asg)
         (append (lookup-equal-list x asg) (lookup-equal-list y asg)))
  :enable lookup-equal-list)

(defruled enc-lookup-equal-list-of-rev
  (equal (lookup-equal-list (rev x) asg) (rev (lookup-equal-list x asg)))
  :enable (rev lookup-equal-list enc-lookup-equal-list-of-append))

(defruled enc-grp-bits-ok-of-append
  (equal (grp-bits-ok (append x y) asg)
         (and (grp-bits-ok x asg) (grp-bits-ok y asg)))
  :enable grp-bits-ok)

(defruled enc-grp-bits-ok-of-rev
  (implies (grp-bits-ok x asg) (grp-bits-ok (rev x) asg))
  :enable (rev grp-bits-ok enc-grp-bits-ok-of-append))

(defruled enc-grp-bits-ok-when-bits
  (implies (and (symbol-listp x)
                (r1cs::valuation-binds-allp asg x)
                (bit-listp (lookup-equal-list x asg)))
           (grp-bits-ok x asg))
  :enable (grp-bits-ok lookup-equal-list r1cs::valuation-binds-allp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The view key of the spec is the x-coordinate of the values-level product.

(defruled enc-crypto-view-key-is-values
  (implies (and (groupp pt) (scalarp s))
           (equal (crypto-group-x (ecurve::edwards-bls12-mul (nfix s) pt))
                  (values-group-x (values-group-mul s pt))))
  :use (:instance hbhp-r-pointp-of-mul (k s) (p1 pt))
  :in-theory (e/d (crypto-group-x values-group-x values-group-mul values-to-group
                   values-scalar-fix values-group-fix groupp scalarp)
                  (hbhp-r-pointp-of-mul)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The circuit.

(define enc-rec-sym-prefix (og ng s rbits rs sts steps ox oy)
  :verify-guards nil
  (append (net-gmul-gadget s rbits rs sts (base-prime))
          (enc-nonce-gadget (net-gmul-out rbits sts (base-prime)) ng)
          (grp-mul-gadget (rev rbits) ox oy steps (nth 0 og) (nth 1 og)
                          (base-prime))))

(define enc-rec-sym-key (rbits ox oy steps)
  :verify-guards nil
  (car (grp-mul-out (rev rbits) ox oy steps)))

(defund enc-c-rec-sym (pubp og data ng s rbits rs sts steps ox oy vs asg)
  "Synthesis of Record::encrypt_symmetric: (mv rs key cs vs asg)."
  (declare (xargs :verify-guards nil))
  (b* ((key (enc-rec-sym-key rbits ox oy steps))
       ((mv prs cs vs asg) (enc-c-rec-sym-unchecked pubp data key vs asg)))
    (mv prs key
        (append (enc-rec-sym-prefix og ng s rbits rs sts steps ox oy) cs)
        vs asg)))

(defmacro enc-rec-sym-hyps ()
  '(and (net-gmul-hyps)
        (rec-record-new-hyps)
        (groupp (rec-point-of og asg))
        (groupp (rec-point-of ng asg))
        (grp-steps-boundp steps asg)
        (equal (len steps) 250)
        (symbolp ox) (symbolp oy)
        (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
        (symbolp (first (grp-mul-out (rev rbits) ox oy steps)))
        (r1cs::valuation-bindsp asg (first (grp-mul-out (rev rbits) ox oy steps)))
        (symbolp (second (grp-mul-out (rev rbits) ox oy steps)))
        (r1cs::valuation-bindsp asg (second (grp-mul-out (rev rbits) ox oy steps)))))

(defruled enc-nth-symbol-and-bound
  (implies (and (symbol-listp xs) (r1cs::valuation-binds-allp asg xs)
                (natp i) (< i (len xs)))
           (and (symbolp (nth i xs))
                (r1cs::valuation-bindsp asg (nth i xs))))
  :enable (nth r1cs::valuation-binds-allp))

(defruled enc-rec-sym-gmul-sound
  (implies (and (net-gmul-hyps)
                (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
           (b* ((sv (lookup-equal s asg))
                (out (net-gmul-out rbits sts p)))
             (and (scalarp sv)
                  (equal (lookup-equal-list rbits asg) (scalar-bits-le sv))
                  (bit-listp (lookup-equal-list rbits asg))
                  (equal (ecurve::point-finite (r1cs::dot-product (car out) asg p)
                                               (r1cs::dot-product (cdr out) asg p))
                         (crypto-g-scalar-multiply sv)))))
  :do-not-induct t
  :use (net-g-scalar-multiply-sound
        (:instance scalar-write-bits-le-gadget-sound (xs rbits) (acc nil)))
  :in-theory '(net-gmul-gadget r1cs::r1cs-constraints-holdp-of-append
               crypto-g-scalar-multiply crypto-generator-g-is-curve-generator-g
               aleo-g-scalar-multiply-funspec nfix lnfix (:e bit-listp)))

(defruled enc-rec-sym-nonce-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp ng) (equal (len ng) 14)
                (r1cs::valuation-binds-allp asg ng)
                (r1cs::r1cs-constraints-holdp (enc-nonce-gadget out ng) asg p))
           (equal (rec-point-of ng asg)
                  (ecurve::point-finite (r1cs::dot-product (car out) asg p)
                                        (r1cs::dot-product (cdr out) asg p))))
  :do-not-induct t
  :use ((:instance enc-nth-symbol-and-bound (xs ng) (i 0))
        (:instance enc-nth-symbol-and-bound (xs ng) (i 1))
        (:instance enc-lc-eq-gadget-holds (lc (car out)) (b (nth 0 ng)))
        (:instance enc-lc-eq-gadget-holds (lc (cdr out)) (b (nth 1 ng))))
  :in-theory '(enc-nonce-gadget rec-point-of r1cs::r1cs-constraints-holdp-of-append
               (:e natp) (:e <)))

(defruled enc-rec-sym-key-sound
  (implies (and (symbol-listp rbits) (equal (len rbits) 251)
                (r1cs::valuation-binds-allp asg rbits)
                (scalarp sv)
                (equal (lookup-equal-list rbits asg) (scalar-bits-le sv))
                (bit-listp (lookup-equal-list rbits asg))
                (symbol-listp og) (equal (len og) 14)
                (r1cs::valuation-binds-allp asg og)
                (groupp (rec-point-of og asg))
                (grp-steps-boundp steps asg)
                (equal (len steps) 250)
                (symbolp ox) (symbolp oy)
                (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
                (r1cs::r1cs-valuationp asg (base-prime))
                (symbolp (first (grp-mul-out (rev rbits) ox oy steps)))
                (r1cs::valuation-bindsp asg (first (grp-mul-out (rev rbits) ox oy steps)))
                (symbolp (second (grp-mul-out (rev rbits) ox oy steps)))
                (r1cs::valuation-bindsp asg (second (grp-mul-out (rev rbits) ox oy steps)))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-gadget (rev rbits) ox oy steps (nth 0 og) (nth 1 og)
                                 (base-prime))
                 asg (base-prime)))
           (equal (lookup-equal (enc-rec-sym-key rbits ox oy steps) asg)
                  (crypto-group-x
                   (ecurve::edwards-bls12-mul (nfix sv) (rec-point-of og asg)))))
  :do-not-induct t
  :use ((:instance enc-view-key-wire
                   (bits (rev rbits)) (bx (nth 0 og)) (by (nth 1 og))
                   (asgx asg) (s sv))
        (:instance enc-crypto-view-key-is-values (pt (rec-point-of og asg)) (s sv))
        (:instance enc-grp-bits-ok-when-bits (x rbits))
        (:instance enc-grp-bits-ok-of-rev (x rbits))
        (:instance enc-nth-symbol-and-bound (xs og) (i 0))
        (:instance enc-nth-symbol-and-bound (xs og) (i 1))
        (:instance acl2::consp-of-rev (x rbits))
        (:instance acl2::len-of-rev (x rbits)))
  :in-theory '(enc-rec-sym-key rec-point-of
               enc-grp-bit-vals-is-lookup-equal-list enc-lookup-equal-list-of-rev
               len (:e natp) (:e <) (:e len) (:e binary-+) (:e unary--)))

(defruled enc-rec-sym-prefix-sound
  (implies (and (enc-rec-sym-hyps)
                (r1cs::r1cs-constraints-holdp
                 (enc-rec-sym-prefix og ng s rbits rs sts steps ox oy)
                 asg p))
           (b* ((sv (lookup-equal s asg)))
             (and (scalarp sv)
                  (equal (rec-point-of ng asg) (crypto-g-scalar-multiply sv))
                  (equal (lookup-equal (enc-rec-sym-key rbits ox oy steps) asg)
                         (crypto-group-x
                          (ecurve::edwards-bls12-mul (nfix sv)
                                                     (rec-point-of og asg)))))))
  :do-not-induct t
  :use (enc-rec-sym-gmul-sound
        (:instance enc-rec-sym-nonce-sound (out (net-gmul-out rbits sts p)))
        (:instance enc-rec-sym-key-sound (sv (lookup-equal s asg))))
  :in-theory '(enc-rec-sym-prefix r1cs::r1cs-constraints-holdp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Soundness.

(defrule enc-not-reserrp-of-cons-ciphertext-record
  (implies (and (crypto-ciphertext-record-resultp c) (not (reserrp c)))
           (not (reserrp (cons c rest))))
  :enable (reserrp crypto-ciphertext-record-resultp crypto-ciphertext-recordp))

(defruled enc-record-encrypt-symmetric-sound
  :short "R1CS-SOUND of Record::encrypt_symmetric, given Record::new on the
          record wires (owner and nonce group points) and the bound wires of
          the randomizer, its to_bits_le and the two scalar multiplications:
          the outputs are crypto-record-encrypt-symmetric of the wire record
          and randomizer.  The nonce check is a constraint, so the spec never
          fails it when the constraints hold."
  (b* (((mv prs key cs & &)
        (enc-c-rec-sym pubp og data ng s rbits rs sts steps ox oy vs asg0))
       (out (enc-rec-sym-unchecked-out pubp og data ng vbits prs asg))
       (spec (crypto-record-encrypt-symmetric
              (rec-record-of-wires pubp og data ng vbits asg)
              (lookup-equal s asg))))
    (implies (and (enc-rec-sym-hyps)
                  (rec-record-data-typed data asg)
                  (r1cs::r1cs-constraints-holdp cs asg p))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (list out (lookup-equal key asg)) spec)))))
  :do-not-induct t
  :use (enc-rec-sym-prefix-sound
        (:instance enc-record-encrypt-symmetric-unchecked-sound
                   (key (enc-rec-sym-key rbits ox oy steps))))
  :in-theory (e/d (enc-c-rec-sym r1cs::r1cs-constraints-holdp-of-append
                   crypto-record-encrypt-symmetric rec-record-of-wires
                   crypto-owner-address enc-rec-sym-key)
                  (enc-rec-sym-prefix-sound
                   enc-record-encrypt-symmetric-unchecked-sound)))

(defruled enc-not-reserrp-when-ciphertext-recordp
  (implies (crypto-ciphertext-recordp c) (not (reserrp c)))
  :enable (reserrp crypto-ciphertext-recordp))

(defruled enc-record-encrypt-sound
  :short "R1CS-SOUND of Record::encrypt: the first output of
          Record::encrypt_symmetric."
  (b* (((mv prs & cs & &)
        (enc-c-rec-sym pubp og data ng s rbits rs sts steps ox oy vs asg0))
       (out (enc-rec-sym-unchecked-out pubp og data ng vbits prs asg))
       (spec (crypto-record-encrypt
              (rec-record-of-wires pubp og data ng vbits asg)
              (lookup-equal s asg))))
    (implies (and (enc-rec-sym-hyps)
                  (rec-record-data-typed data asg)
                  (r1cs::r1cs-constraints-holdp cs asg p))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use enc-record-encrypt-symmetric-sound
  :in-theory (e/d (crypto-record-encrypt enc-not-reserrp-when-ciphertext-recordp
                   return-type-of-crypto-record-encrypt-symmetric)
                  (enc-record-encrypt-symmetric-sound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Completeness.

(defrule enc-point-finite-coords-equal
  (implies (and (fieldp a) (fieldp b) (fieldp c) (fieldp d)
                (equal (ecurve::point-finite a b) (ecurve::point-finite c d)))
           (and (equal a c) (equal b d)))
  :use ((:instance grp-point-coords (x a) (y b))
        (:instance grp-point-coords (x c) (y d)))
  :in-theory nil
  :rule-classes nil)

(defruled enc-rec-sym-nonce-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp ng) (equal (len ng) 14)
                (r1cs::valuation-binds-allp asg ng)
                (equal (rec-point-of ng asg)
                       (ecurve::point-finite (r1cs::dot-product (car out) asg p)
                                             (r1cs::dot-product (cdr out) asg p))))
           (r1cs::r1cs-constraints-holdp (enc-nonce-gadget out ng) asg p))
  :do-not-induct t
  :use ((:instance enc-nth-symbol-and-bound (xs ng) (i 0))
        (:instance enc-nth-symbol-and-bound (xs ng) (i 1))
        (:instance enc-point-finite-coords-equal
                   (a (lookup-equal (nth 0 ng) asg))
                   (b (lookup-equal (nth 1 ng) asg))
                   (c (r1cs::dot-product (car out) asg p))
                   (d (r1cs::dot-product (cdr out) asg p)))
        (:instance r1cs::fep-of-lookup-equal (var (nth 0 ng)) (valuation asg) (prime p))
        (:instance r1cs::fep-of-lookup-equal (var (nth 1 ng)) (valuation asg) (prime p))
        (:instance enc-lc-eq-gadget-holds (lc (car out)) (b (nth 0 ng)))
        (:instance enc-lc-eq-gadget-holds (lc (cdr out)) (b (nth 1 ng))))
  :in-theory (e/d (enc-nonce-gadget rec-point-of r1cs::r1cs-constraints-holdp-of-append
                   fieldp primep-of-base-prime)
                  (enc-lc-eq-gadget-holds)))

(defruled enc-rec-sym-mul-complete
  (implies (and (symbol-listp rbits) (equal (len rbits) 251)
                (r1cs::valuation-binds-allp asg rbits)
                (bit-listp (lookup-equal-list rbits asg))
                (symbol-listp og) (equal (len og) 14)
                (r1cs::valuation-binds-allp asg og)
                (groupp (rec-point-of og asg))
                (grp-steps-boundp steps asg)
                (equal (len steps) 250)
                (symbolp ox) (symbolp oy)
                (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
                (r1cs::r1cs-valuationp asg (base-prime))
                (equal (lookup-equal ox asg)
                       (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                           (lookup-equal (nth 0 og) asg) 0))
                (equal (lookup-equal oy asg)
                       (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                           (lookup-equal (nth 1 og) asg) 1))
                (grp-steps-canonp (cdr (rev rbits)) steps (nth 0 og) (nth 1 og)
                                  ox oy asg))
           (r1cs::r1cs-constraints-holdp
            (grp-mul-gadget (rev rbits) ox oy steps (nth 0 og) (nth 1 og)
                            (base-prime))
            asg (base-prime)))
  :do-not-induct t
  :use ((:instance grp-mul-gadget-complete
                   (bits (rev rbits)) (bx (nth 0 og)) (by (nth 1 og))
                   (p (base-prime)))
        (:instance enc-grp-bits-ok-when-bits (x rbits))
        (:instance enc-grp-bits-ok-of-rev (x rbits))
        (:instance enc-nth-symbol-and-bound (xs og) (i 0))
        (:instance enc-nth-symbol-and-bound (xs og) (i 1))
        (:instance crypto-edwards-bls12-pointp-when-groupp (x (rec-point-of og asg)))
        (:instance acl2::consp-of-rev (x rbits))
        (:instance acl2::len-of-rev (x rbits)))
  :in-theory '(rec-point-of len (:e natp) (:e <) (:e len) (:e binary-+) (:e unary--)))

(defruled enc-rec-sym-prefix-complete
  (b* ((sv (lookup-equal s asg)))
    (implies (and (enc-rec-sym-hyps)
                  (scalarp sv)
                  (equal (lookup-equal-list rbits asg) (scalar-bits-le sv))
                  (equal (lookup-equal-list rs asg)
                         (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                                     (scalar-modulus-minus-one-bits)))
                  (net-gfold-canonp (cdr rbits) sts 1
                                    (ecurve::edwards-bls12-mul
                                     (lookup-equal (car rbits) asg)
                                     (curve-generator-g))
                                    asg)
                  (equal (rec-point-of ng asg) (crypto-g-scalar-multiply sv))
                  (equal (lookup-equal ox asg)
                         (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                             (lookup-equal (nth 0 og) asg) 0))
                  (equal (lookup-equal oy asg)
                         (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                             (lookup-equal (nth 1 og) asg) 1))
                  (grp-steps-canonp (cdr (rev rbits)) steps (nth 0 og) (nth 1 og)
                                    ox oy asg))
             (r1cs::r1cs-constraints-holdp
              (enc-rec-sym-prefix og ng s rbits rs sts steps ox oy) asg p)))
  :do-not-induct t
  :use (net-g-scalar-multiply-complete
        enc-rec-sym-gmul-sound
        (:instance enc-rec-sym-nonce-complete (out (net-gmul-out rbits sts p)))
        enc-rec-sym-mul-complete
        (:instance bit-listp-of-scalar-bits-le (a (lookup-equal s asg))))
  :in-theory '(enc-rec-sym-prefix r1cs::r1cs-constraints-holdp-of-append))

(defruled enc-record-encrypt-symmetric-complete
  :short "R1CS-COMPLETE of Record::encrypt_symmetric (and of Record::encrypt,
          the same circuit): from an assignment with the randomizer, its
          to_bits_le and range-check witnesses, the canonical witnesses of
          both scalar multiplications, a nonce equal to randomizer * G (the
          spec's precondition) and the entry leaf witnesses, Poseidon witness
          generation yields an assignment satisfying all the constraints.
          The prefix and entry constraints are assumed to mention only wires
          bound in the starting assignment."
  (b* ((sv (lookup-equal s asg))
       ((mv & & cs & asg2)
        (enc-c-rec-sym pubp og data ng s rbits rs sts steps ox oy vs asg)))
    (implies (and (enc-rec-sym-hyps)
                  (scalarp sv)
                  (equal (lookup-equal-list rbits asg) (scalar-bits-le sv))
                  (equal (lookup-equal-list rs asg)
                         (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                                     (scalar-modulus-minus-one-bits)))
                  (net-gfold-canonp (cdr rbits) sts 1
                                    (ecurve::edwards-bls12-mul
                                     (lookup-equal (car rbits) asg)
                                     (curve-generator-g))
                                    asg)
                  (equal (rec-point-of ng asg) (crypto-g-scalar-multiply sv))
                  (equal (lookup-equal ox asg)
                         (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                             (lookup-equal (nth 0 og) asg) 0))
                  (equal (lookup-equal oy asg)
                         (if (equal (lookup-equal (car (rev rbits)) asg) 1)
                             (lookup-equal (nth 1 og) asg) 1))
                  (grp-steps-canonp (cdr (rev rbits)) steps (nth 0 og) (nth 1 og)
                                    ox oy asg)
                  (hpos-cs-boundp (enc-rec-sym-prefix og ng s rbits rs sts steps ox oy)
                                  asg)
                  (rec-record-data-typed data asg)
                  (enc-rec-data-witnessp data asg (base-prime))
                  (hpos-cs-boundp (enc-rec-data-gadget data) asg)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-poseidon-bound
                       8 2 (nfix (rec-record-num-randomizers pubp data)))
                      (len vs)))
             (r1cs::r1cs-constraints-holdp cs asg2 p)))
  :do-not-induct t
  :use (enc-rec-sym-prefix-complete
        (:instance enc-record-encrypt-symmetric-unchecked-complete
                   (key (enc-rec-sym-key rbits ox oy steps)))
        (:instance enc-hash-complete-step
                   (key (enc-rec-sym-key rbits ox oy steps))
                   (n (nfix (rec-record-num-randomizers pubp data))))
        (:instance hpos-holdp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many
                                   8 (enc-randomizer-inputs
                                      (enc-rec-sym-key rbits ox oy steps))
                                   (nfix (rec-record-num-randomizers pubp data))
                                   vs asg)))
                   (cs (enc-rec-sym-prefix og ng s rbits rs sts steps ox oy))))
  :in-theory (e/d (enc-c-rec-sym enc-c-rec-sym-unchecked enc-rec-sym-key
                   r1cs::r1cs-constraints-holdp-of-append)
                  (hpos-holdp-when-ext-p enc-rec-sym-prefix-complete
                   enc-record-encrypt-symmetric-unchecked-complete
                   enc-hash-complete-step)))
