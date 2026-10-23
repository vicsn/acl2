; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ciphertext (snarkVM circuit/program/src/data/ciphertext): a vector of field
; elements.
;
; new:            Field::new on each element; a variable-mode Field::new adds a
;                 witness and no constraint.  The length check is on the host.
; write_bits_*:   Field::write_bits_* on each element, in order.
; is_equal:       lengths differ: constant false, no constraint.  Otherwise
;                 Boolean::constant(true) &= a_i.is_equal(b_i).  The first AND
;                 folds with the constant (no constraint) and leaves the
;                 linear combination 1 - r_0; the second is
;                 (1 - r_0) * (1 - r_1) = z_1 and later ones z * (1 - r_i) = z'.
; is_not_equal:   lengths differ: constant true.  Otherwise
;                 Boolean::constant(false) |= a_i.is_not_equal(b_i): r_0, then
;                 (1 - z) * (1 - r_i) = (1 - z') per element.
;
; The vector fold chains (rec-eq-chain, rec-neq-chain) are reused for any
; vector of field elements compared element-wise.

(in-package "ALEOVM")

(include-book "rec-leaves")
(include-book "prog-primitives")
(include-book "../fun-specs/crypto-record")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Element-level facts.

(defthm rec-neq-bit-when-constraints
  (implies (and (equal p (base-prime))
                (pfield::fep x p)
                (pfield::fep y p)
                (pfield::fep m p)
                (pfield::fep r p)
                (equal (pfield::mul (pfield::sub x y p) m p) r)
                (equal (pfield::mul (pfield::sub x y p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (equal (if (equal x y) 0 1) r))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d ()
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x y p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub (x x) (y y) (p p))
                 (:instance pfield::equal-of-0-and-sub (x 1) (y r) (p p))))))

(defruled rec-neq-gadget-bit
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (prog-field-neq-gadget x y m r (base-prime)) asg (base-prime)))
           (equal (lookup-equal r asg)
                  (if (equal (lookup-equal x asg) (lookup-equal y asg)) 0 1)))
  :use ((:instance prog-field-neq-gadget-to-spec (p (base-prime)))
        (:instance rec-neq-bit-when-constraints
                   (p (base-prime))
                   (x (lookup-equal x asg))
                   (y (lookup-equal y asg))
                   (m (lookup-equal m asg))
                   (r (lookup-equal r asg))))
  :enable (r1cs::fep-of-lookup-equal primep-of-base-prime))

(define rec-neq-mult ((x fieldp) (y fieldp))
  :guard-hints (("Goal" :in-theory (enable fieldp)))
  :short "snarkVM's multiplier witness of @('Field::is_not_equal')."
  (if (equal x y)
      1
    (pfield::inv (pfield::sub x y (base-prime)) (base-prime))))

(defruled rec-neq-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg) (lookup-equal y asg)) 0 1))
                (equal (lookup-equal m asg)
                       (rec-neq-mult (lookup-equal x asg) (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (prog-field-neq-gadget x y m r (base-prime)) asg (base-prime)))
  :use (:instance prog-field-neq-gadget-complete (p (base-prime)))
  :enable (rec-neq-mult fieldp r1cs::fep-of-lookup-equal primep-of-base-prime))

(defruled rec-and-step
  (implies (and (pfield::fep a (base-prime))
                (equal r (if c 0 1)))
           (equal (pfield::mul a (pfield::sub 1 r (base-prime)) (base-prime))
                  (if c a 0))))

(defruled rec-or-step
  (implies (and (pfield::fep a (base-prime))
                (pfield::fep z (base-prime))
                (equal r (if c 0 1)))
           (equal (equal (pfield::mul (pfield::sub 1 a (base-prime))
                                      (pfield::sub 1 r (base-prime))
                                      (base-prime))
                         (pfield::sub 1 z (base-prime)))
                  (equal z (if c a 1))))
  :hints (("Goal" :cases (c))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vector shapes and honest witnesses.

(define rec-chain-last ((acc symbolp) (zs symbol-listp))
  :returns (s symbolp :hyp :guard)
  :short "The wire holding the accumulator after the chain."
  (if (endp zs) acc (rec-chain-last (car zs) (cdr zs))))

(define rec-neq-witness-okp ((xs symbol-listp) (ys symbol-listp)
                             (ms symbol-listp) (rs symbol-listp)
                             (asg alistp))
  :short "Each element's is_not_equal bit and multiplier are snarkVM's witness."
  :verify-guards nil
  (or (endp xs)
      (and (consp ys) (consp ms) (consp rs)
           (b* ((x (lookup-equal (car xs) asg))
                (y (lookup-equal (car ys) asg)))
             (and (equal (lookup-equal (car rs) asg) (if (equal x y) 0 1))
                  (equal (lookup-equal (car ms) asg) (rec-neq-mult x y))))
           (rec-neq-witness-okp (cdr xs) (cdr ys) (cdr ms) (cdr rs) asg))))

(define rec-and-prefix (a (xs true-listp) (ys true-listp))
  :short "Accumulator values of the is_equal chain from @('a')."
  (if (or (endp xs) (endp ys))
      nil
    (b* ((a1 (if (equal (car xs) (car ys)) a 0)))
      (cons a1 (rec-and-prefix a1 (cdr xs) (cdr ys))))))

(define rec-or-prefix (a (xs true-listp) (ys true-listp))
  :short "Accumulator values of the is_not_equal chain from @('a')."
  (if (or (endp xs) (endp ys))
      nil
    (b* ((a1 (if (equal (car xs) (car ys)) a 1)))
      (cons a1 (rec-or-prefix a1 (cdr xs) (cdr ys))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; AND chain: per element, Field::is_not_equal then acc * (1 - r) = z.

(define rec-eq-chain ((acc symbolp)
                      (xs symbol-listp) (ys symbol-listp)
                      (ms symbol-listp) (rs symbol-listp)
                      (zs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp xs) (endp ys) (endp ms) (endp rs) (endp zs))
      nil
    (append (prog-field-neq-gadget (car xs) (car ys) (car ms) (car rs) (base-prime))
            (prog-and-var-eq-gadget acc (car rs) (car zs) (base-prime))
            (rec-eq-chain (car zs) (cdr xs) (cdr ys) (cdr ms) (cdr rs) (cdr zs)))))

(defmacro rec-chain-hyps ()
  '(and (symbolp acc)
        (symbol-listp xs) (symbol-listp ys) (symbol-listp ms)
        (symbol-listp rs) (symbol-listp zs)
        (equal (len ys) (len xs))
        (equal (len ms) (len xs))
        (equal (len rs) (len xs))
        (equal (len zs) (len xs))
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-bindsp asg acc)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg ms)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-binds-allp asg zs)))

(defruled rec-eq-chain-sound
  (implies (and (rec-chain-hyps)
                (pfield::fep (lookup-equal acc asg) (base-prime))
                (r1cs::r1cs-constraints-holdp
                 (rec-eq-chain acc xs ys ms rs zs) asg (base-prime)))
           (equal (lookup-equal (rec-chain-last acc zs) asg)
                  (if (equal (lookup-equal-list xs asg)
                             (lookup-equal-list ys asg))
                      (lookup-equal acc asg)
                    0)))
  :induct (rec-eq-chain acc xs ys ms rs zs)
  :enable (rec-eq-chain rec-chain-last lookup-equal-list
           r1cs::valuation-binds-allp
           r1cs::r1cs-constraints-holdp-of-append
           prog-and-var-eq-gadget-to-mul
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :hints (("Subgoal *1/2"
           :use ((:instance rec-neq-gadget-bit
                            (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
                 (:instance rec-and-step
                            (a (lookup-equal acc asg))
                            (r (lookup-equal (car rs) asg))
                            (c (equal (lookup-equal (car xs) asg)
                                      (lookup-equal (car ys) asg))))))))

(defruled rec-eq-chain-complete
  (implies (and (rec-chain-hyps)
                (pfield::fep (lookup-equal acc asg) (base-prime))
                (rec-neq-witness-okp xs ys ms rs asg)
                (equal (lookup-equal-list zs asg)
                       (rec-and-prefix (lookup-equal acc asg)
                                       (lookup-equal-list xs asg)
                                       (lookup-equal-list ys asg))))
           (r1cs::r1cs-constraints-holdp
            (rec-eq-chain acc xs ys ms rs zs) asg (base-prime)))
  :induct (rec-eq-chain acc xs ys ms rs zs)
  :enable (rec-eq-chain lookup-equal-list rec-and-prefix rec-neq-witness-okp
           r1cs::valuation-binds-allp
           r1cs::r1cs-constraints-holdp-of-append
           prog-and-var-eq-gadget-to-mul
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :hints (("Subgoal *1/2"
           :use ((:instance rec-neq-gadget-complete
                            (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
                 (:instance rec-and-step
                            (a (lookup-equal acc asg))
                            (r (lookup-equal (car rs) asg))
                            (c (equal (lookup-equal (car xs) asg)
                                      (lookup-equal (car ys) asg))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; OR chain: per element, Field::is_not_equal then (1 - acc) * (1 - r) = (1 - z).

(define rec-neq-chain ((acc symbolp)
                       (xs symbol-listp) (ys symbol-listp)
                       (ms symbol-listp) (rs symbol-listp)
                       (zs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp xs) (endp ys) (endp ms) (endp rs) (endp zs))
      nil
    (append (prog-field-neq-gadget (car xs) (car ys) (car ms) (car rs) (base-prime))
            (prog-bool-or-gadget acc (car rs) (car zs) (base-prime))
            (rec-neq-chain (car zs) (cdr xs) (cdr ys) (cdr ms) (cdr rs) (cdr zs)))))

(defruled rec-neq-chain-sound
  (implies (and (rec-chain-hyps)
                (r1cs::r1cs-constraints-holdp
                 (rec-neq-chain acc xs ys ms rs zs) asg (base-prime)))
           (equal (lookup-equal (rec-chain-last acc zs) asg)
                  (if (equal (lookup-equal-list xs asg)
                             (lookup-equal-list ys asg))
                      (lookup-equal acc asg)
                    1)))
  :induct (rec-neq-chain acc xs ys ms rs zs)
  :enable (rec-neq-chain rec-chain-last lookup-equal-list
           r1cs::valuation-binds-allp
           r1cs::r1cs-constraints-holdp-of-append
           prog-bool-or-gadget-to-mul
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :hints (("Subgoal *1/2"
           :use ((:instance rec-neq-gadget-bit
                            (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
                 (:instance rec-or-step
                            (a (lookup-equal acc asg))
                            (z (lookup-equal (car zs) asg))
                            (r (lookup-equal (car rs) asg))
                            (c (equal (lookup-equal (car xs) asg)
                                      (lookup-equal (car ys) asg))))))))

(defruled rec-neq-chain-complete
  (implies (and (rec-chain-hyps)
                (rec-neq-witness-okp xs ys ms rs asg)
                (equal (lookup-equal-list zs asg)
                       (rec-or-prefix (lookup-equal acc asg)
                                      (lookup-equal-list xs asg)
                                      (lookup-equal-list ys asg))))
           (r1cs::r1cs-constraints-holdp
            (rec-neq-chain acc xs ys ms rs zs) asg (base-prime)))
  :induct (rec-neq-chain acc xs ys ms rs zs)
  :enable (rec-neq-chain lookup-equal-list rec-or-prefix rec-neq-witness-okp
           r1cs::valuation-binds-allp
           r1cs::r1cs-constraints-holdp-of-append
           prog-bool-or-gadget-to-mul
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :hints (("Subgoal *1/2"
           :use ((:instance rec-neq-gadget-complete
                            (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
                 (:instance rec-or-step
                            (a (lookup-equal acc asg))
                            (z (lookup-equal (car zs) asg))
                            (r (lookup-equal (car rs) asg))
                            (c (equal (lookup-equal (car xs) asg)
                                      (lookup-equal (car ys) asg))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Wire values are field elements.

(defruled rec-values-field-listp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbol-listp xs)
                (r1cs::valuation-binds-allp asg xs))
           (values-field-listp (lookup-equal-list xs asg)))
  :induct (len xs)
  :enable (lookup-equal-list r1cs::valuation-binds-allp fieldp
           r1cs::fep-of-lookup-equal primep-of-base-prime))

(defruled rec-crypto-field-bits
  (implies (fieldp x)
           (and (equal (crypto-field-bits-le x) (field-bits-le x))
                (equal (crypto-field-bits-be x) (rev (field-bits-le x)))))
  :enable (crypto-field-bits-le crypto-field-bits-be
           crypto-nat->lebits crypto-nat->bebits
           acl2::nat=>bebits acl2::nat=>bendian acl2::nat=>lebits
           field-bits-le fieldp pfield::fep fb-base-prime-below-2-253))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::new

(define rec-ciphertext-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('Ciphertext::new') in variable mode: none.
          Each element is a fresh witness (Field::new)."
  nil)

(defruled rec-ciphertext-new-sound
  (b* ((vals (lookup-equal-list ws asg)))
    (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                  (symbol-listp ws)
                  (r1cs::valuation-binds-allp asg ws)
                  (<= (len ws) (crypto-max-data-size-in-fields))
                  (r1cs::r1cs-constraints-holdp (rec-ciphertext-new-gadget)
                                                asg (base-prime)))
             (and (values-field-listp vals)
                  (equal (crypto-ciphertext-new vals) vals))))
  :enable (crypto-ciphertext-new rec-values-field-listp-of-lookup))

(defruled rec-ciphertext-new-complete
  (r1cs::r1cs-constraints-holdp (rec-ciphertext-new-gadget) asg p)
  :enable (rec-ciphertext-new-gadget r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::write_bits_le / write_bits_be: Field::write_bits_* per element.

(define rec-bits-shapep ((xs symbol-listp) bitss rss)
  :short "Per element: 253 bit wires and the range-check wires."
  (or (endp xs)
      (and (consp bitss) (consp rss)
           (symbol-listp (car bitss))
           (symbol-listp (car rss))
           (equal (len (car bitss)) (integer-length (base-prime)))
           (equal (len (car rss)) (bits-lt-prime-rlen (base-prime)))
           (rec-bits-shapep (cdr xs) (cdr bitss) (cdr rss)))))

(define rec-bits-boundp ((asg alistp) (xs symbol-listp) bitss rss)
  :verify-guards nil
  (or (endp xs)
      (and (consp bitss) (consp rss)
           (r1cs::valuation-bindsp asg (car xs))
           (r1cs::valuation-binds-allp asg (car bitss))
           (r1cs::valuation-binds-allp asg (car rss))
           (rec-bits-boundp asg (cdr xs) (cdr bitss) (cdr rss)))))

(define rec-bits-witness-okp ((asg alistp) (xs symbol-listp) bitss rss)
  :short "Per element: the canonical bits and snarkVM's range-check witness."
  :verify-guards nil
  (or (endp xs)
      (and (consp bitss) (consp rss)
           (equal (lookup-equal-list (car bitss) asg)
                  (field-bits-le (lookup-equal (car xs) asg)))
           (equal (lookup-equal-list (car rss) asg)
                  (fb-bits-lte-const-witness
                   (lookup-equal-list (car bitss) asg)
                   (nat=>lebits* (1- (base-prime)))))
           (rec-bits-witness-okp asg (cdr xs) (cdr bitss) (cdr rss)))))

(define rec-fields-write-bits-gadget ((xs symbol-listp) bitss rss (u symbolp))
  :guard (rec-bits-shapep xs bitss rss)
  :guard-hints (("Goal" :in-theory (enable rec-bits-shapep)))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (symbol-listp xs) (symbolp u)
                              (rec-bits-shapep xs bitss rss))
                    :hints (("Goal" :in-theory (enable rec-bits-shapep))))
  :short "Constraints of writing the bits of a vector of field elements."
  (if (endp xs)
      nil
    (append (fb-field-write-bits-le-gadget (car xs) (car bitss) (car rss)
                                           u (base-prime))
            (rec-fields-write-bits-gadget (cdr xs) (cdr bitss) (cdr rss) u))))

(define rec-concat-le ((xs true-listp) bitss)
  :verify-guards nil
  :short "Output wires of write_bits_le: each element's bits in order."
  (if (endp xs) nil (append (car bitss) (rec-concat-le (cdr xs) (cdr bitss)))))

(define rec-concat-be ((xs true-listp) bitss)
  :verify-guards nil
  :short "Output wires of write_bits_be: each element's bits reversed, in order."
  (if (endp xs) nil (append (rev (car bitss)) (rec-concat-be (cdr xs) (cdr bitss)))))

(defmacro rec-bits-hyps ()
  '(and (symbol-listp xs) (symbolp u)
        (rec-bits-shapep xs bitss rss)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)
        (rec-bits-boundp asg xs bitss rss)))

(defruled rec-fields-write-bits-sound
  (b* ((xvals (lookup-equal-list xs asg)))
    (implies (and (rec-bits-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-write-bits-gadget xs bitss rss u) asg (base-prime)))
             (and (values-field-listp xvals)
                  (equal (lookup-equal-list (rec-concat-le xs bitss) asg)
                         (crypto-field-list-bits-le xvals))
                  (equal (lookup-equal-list (rec-concat-be xs bitss) asg)
                         (crypto-field-list-bits-be xvals)))))
  :induct (rec-fields-write-bits-gadget xs bitss rss u)
  :enable (rec-fields-write-bits-gadget rec-bits-shapep rec-bits-boundp
           rec-concat-le rec-concat-be lookup-equal-list
           lookup-equal-list-of-append lookup-equal-list-of-rev
           crypto-field-list-bits-le crypto-field-list-bits-be
           rec-crypto-field-bits
           r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use (:instance rec-field-bits-when-gadget
                           (x (car xs)) (bits (car bitss)) (rs (car rss))))))

(defruled rec-fields-write-bits-complete
  (implies (and (rec-bits-hyps)
                (rec-bits-witness-okp asg xs bitss rss))
           (r1cs::r1cs-constraints-holdp
            (rec-fields-write-bits-gadget xs bitss rss u) asg (base-prime)))
  :induct (rec-fields-write-bits-gadget xs bitss rss u)
  :enable (rec-fields-write-bits-gadget rec-bits-shapep rec-bits-boundp
           rec-bits-witness-okp
           r1cs::r1cs-constraints-holdp-of-append
           fieldp r1cs::fep-of-lookup-equal primep-of-base-prime)
  :hints (("Subgoal *1/2"
           :use (:instance rec-field-gadget-complete
                           (x (car xs)) (bits (car bitss)) (rs (car rss))))))

(defruled rec-ciphertext-write-bits-sound
  (b* ((xvals (lookup-equal-list xs asg)))
    (implies (and (rec-bits-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-write-bits-gadget xs bitss rss u) asg (base-prime)))
             (and (values-field-listp xvals)
                  (equal (lookup-equal-list (rec-concat-le xs bitss) asg)
                         (crypto-ciphertext-write-bits-le xvals))
                  (equal (lookup-equal-list (rec-concat-be xs bitss) asg)
                         (crypto-ciphertext-write-bits-be xvals)))))
  :enable (crypto-ciphertext-write-bits-le crypto-ciphertext-write-bits-be)
  :use rec-fields-write-bits-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::is_equal

(define rec-fields-is-equal-gadget ((xs symbol-listp) (ys symbol-listp)
                                    (ms symbol-listp) (rs symbol-listp)
                                    (zs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((not (equal (len xs) (len ys))) nil)
        ((or (endp xs) (endp ms) (endp rs)) nil)
        ((or (endp (cdr xs)) (endp (cdr ms)) (endp (cdr rs)) (endp zs))
         (prog-field-neq-gadget (car xs) (car ys) (car ms) (car rs) (base-prime)))
        (t (append
            (prog-field-neq-gadget (car xs) (car ys) (car ms) (car rs) (base-prime))
            (prog-field-neq-gadget (cadr xs) (cadr ys) (cadr ms) (cadr rs)
                                   (base-prime))
            (prog-eq-and-gadget (car rs) (cadr rs) (car zs) (base-prime))
            (rec-eq-chain (car zs) (cddr xs) (cddr ys) (cddr ms) (cddr rs)
                          (cdr zs))))))

(define rec-fields-is-equal-value ((xs symbol-listp) (ys symbol-listp)
                                   (rs symbol-listp) (zs symbol-listp)
                                   (asg alistp))
  :verify-guards nil
  :short "Value of the output boolean: a constant, the linear combination
          @($1 - r_0$), or the last AND wire."
  (cond ((not (equal (len xs) (len ys))) 0)
        ((endp xs) 1)
        ((endp (cdr xs)) (pfield::sub 1 (lookup-equal (car rs) asg) (base-prime)))
        (t (lookup-equal (rec-chain-last (car zs) (cdr zs)) asg))))

(defmacro rec-vec-hyps ()
  '(and (symbol-listp xs) (symbol-listp ys) (symbol-listp ms)
        (symbol-listp rs) (symbol-listp zs)
        (equal (len ms) (len xs))
        (equal (len rs) (len xs))
        (equal (len zs) (nfix (1- (len xs))))
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg ms)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-binds-allp asg zs)))

(defruled rec-eq-and-first
  (equal (pfield::mul (pfield::sub 1 (if c0 0 1) (base-prime))
                      (pfield::sub 1 (if c1 0 1) (base-prime))
                      (base-prime))
         (if (and c0 c1) 1 0)))

(defruled rec-lookup-equal-list-when-atom
  (implies (not (consp keys))
           (equal (lookup-equal-list keys asg) nil))
  :enable lookup-equal-list)

(defruled rec-equal-of-lookup-equal-lists
  (implies (and (consp xs) (consp ys))
           (equal (equal (lookup-equal-list xs asg) (lookup-equal-list ys asg))
                  (and (equal (lookup-equal (car xs) asg) (lookup-equal (car ys) asg))
                       (equal (lookup-equal-list (cdr xs) asg)
                              (lookup-equal-list (cdr ys) asg)))))
  :enable lookup-equal-list)

(defthm rec-len-cong
  (implies (equal a b) (equal (len a) (len b)))
  :rule-classes nil)

(defruled rec-not-equal-lookup-lists-when-len
  (implies (not (equal (len xs) (len ys)))
           (not (equal (lookup-equal-list xs asg) (lookup-equal-list ys asg))))
  :do-not-induct t
  :use ((:instance rec-len-cong
                   (a (lookup-equal-list xs asg)) (b (lookup-equal-list ys asg)))))

(defthm rec-consp-when-len-equal
  (implies (and (equal (len xs) (len ys)) (consp xs))
           (consp ys))
  :rule-classes nil)

(defruled rec-fields-is-equal-sound-2
  (implies (and (rec-vec-hyps)
                (equal (len xs) (len ys))
                (consp (cdr xs))
                (consp ys)
                (consp (cdr ys))
                (r1cs::r1cs-constraints-holdp
                 (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
           (equal (rec-fields-is-equal-value xs ys rs zs asg)
                  (if (equal (lookup-equal-list xs asg) (lookup-equal-list ys asg))
                      1 0)))
  :do-not-induct t
  :in-theory (e/d (rec-fields-is-equal-gadget rec-fields-is-equal-value
                   rec-equal-of-lookup-equal-lists
                   r1cs::r1cs-constraints-holdp-of-append
                   prog-eq-and-gadget-to-mul rec-eq-and-first
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  (lookup-equal-list))
  :use ((:instance rec-neq-gadget-bit
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
        (:instance rec-neq-gadget-bit
                   (x (cadr xs)) (y (cadr ys)) (m (cadr ms)) (r (cadr rs)))
        (:instance rec-eq-chain-sound
                   (acc (car zs)) (xs (cddr xs)) (ys (cddr ys))
                   (ms (cddr ms)) (rs (cddr rs)) (zs (cdr zs)))))

(defruled rec-fields-is-equal-sound-1
  (implies (and (rec-vec-hyps)
                (equal (len xs) (len ys))
                (consp xs)
                (not (consp (cdr xs)))
                (consp ys)
                (not (consp (cdr ys)))
                (r1cs::r1cs-constraints-holdp
                 (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
           (equal (rec-fields-is-equal-value xs ys rs zs asg)
                  (if (equal (lookup-equal-list xs asg) (lookup-equal-list ys asg))
                      1 0)))
  :do-not-induct t
  :in-theory (e/d (rec-fields-is-equal-gadget rec-fields-is-equal-value
                   rec-equal-of-lookup-equal-lists
                   rec-lookup-equal-list-when-atom
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  (lookup-equal-list))
  :use ((:instance rec-neq-gadget-bit
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))))

(defruled rec-fields-is-equal-sound
  (b* ((xvals (lookup-equal-list xs asg))
       (yvals (lookup-equal-list ys asg)))
    (implies (and (rec-vec-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
             (equal (rec-fields-is-equal-value xs ys rs zs asg)
                    (if (equal xvals yvals) 1 0))))
  :do-not-induct t
  :cases ((not (equal (len xs) (len ys)))
          (not (consp xs))
          (not (consp (cdr xs))))
  :in-theory (e/d (rec-fields-is-equal-value rec-not-equal-lookup-lists-when-len)
                  (lookup-equal-list))
  :hints (("Subgoal 2" :expand ((lookup-equal-list xs asg) (lookup-equal-list ys asg))))
  :use (rec-fields-is-equal-sound-1 rec-fields-is-equal-sound-2
        (:instance rec-consp-when-len-equal (xs xs) (ys ys))
        (:instance rec-consp-when-len-equal (xs (cdr xs)) (ys (cdr ys)))
        (:instance rec-consp-when-len-equal (xs (cdr ys)) (ys (cdr xs)))))

(defruled rec-ciphertext-is-equal-sound
  (b* ((xvals (lookup-equal-list xs asg))
       (yvals (lookup-equal-list ys asg)))
    (implies (and (rec-vec-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
             (and (values-field-listp xvals)
                  (values-field-listp yvals)
                  (equal (rec-fields-is-equal-value xs ys rs zs asg)
                         (crypto-ciphertext-is-equal xvals yvals)))))
  :do-not-induct t
  :in-theory (e/d (crypto-ciphertext-is-equal rec-values-field-listp-of-lookup
                   rec-not-equal-lookup-lists-when-len)
                  (lookup-equal-list))
  :use rec-fields-is-equal-sound)

(defruled rec-and-prefix-of-cons
  (equal (rec-and-prefix a (cons x xs) (cons y ys))
         (b* ((a1 (if (equal x y) a 0)))
           (cons a1 (rec-and-prefix a1 xs ys))))
  :enable rec-and-prefix)

(defruled rec-fields-is-equal-complete-2
  (implies (and (rec-vec-hyps)
                (equal (len xs) (len ys))
                (consp (cdr xs))
                (consp ys)
                (consp (cdr ys))
                (rec-neq-witness-okp xs ys ms rs asg)
                (equal (lookup-equal-list zs asg)
                       (rec-and-prefix (if (equal (lookup-equal (car xs) asg)
                                                  (lookup-equal (car ys) asg))
                                           1 0)
                                       (cdr (lookup-equal-list xs asg))
                                       (cdr (lookup-equal-list ys asg)))))
           (r1cs::r1cs-constraints-holdp
            (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
  :do-not-induct t
  :in-theory (e/d (rec-fields-is-equal-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   prog-eq-and-gadget-to-mul rec-eq-and-first
                   rec-and-prefix-of-cons
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  ())
  :expand ((rec-neq-witness-okp xs ys ms rs asg)
           (rec-neq-witness-okp (cdr xs) (cdr ys) (cdr ms) (cdr rs) asg)
           (lookup-equal-list xs asg) (lookup-equal-list ys asg)
           (lookup-equal-list (cdr xs) asg) (lookup-equal-list (cdr ys) asg)
           (lookup-equal-list zs asg))
  :use ((:instance rec-neq-gadget-complete
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
        (:instance rec-neq-gadget-complete
                   (x (cadr xs)) (y (cadr ys)) (m (cadr ms)) (r (cadr rs)))
        (:instance rec-eq-chain-complete
                   (acc (car zs)) (xs (cddr xs)) (ys (cddr ys))
                   (ms (cddr ms)) (rs (cddr rs)) (zs (cdr zs)))))

(defruled rec-fields-is-equal-complete-1
  (implies (and (rec-vec-hyps)
                (consp xs)
                (not (consp (cdr xs)))
                (rec-neq-witness-okp xs ys ms rs asg))
           (r1cs::r1cs-constraints-holdp
            (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
  :do-not-induct t
  :in-theory (enable rec-fields-is-equal-gadget)
  :expand ((rec-neq-witness-okp xs ys ms rs asg))
  :use ((:instance rec-neq-gadget-complete
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))))

(defruled rec-fields-is-equal-complete
  (implies (and (rec-vec-hyps)
                (rec-neq-witness-okp xs ys ms rs asg)
                (equal (lookup-equal-list zs asg)
                       (rec-and-prefix (if (equal (lookup-equal (car xs) asg)
                                                  (lookup-equal (car ys) asg))
                                           1 0)
                                       (cdr (lookup-equal-list xs asg))
                                       (cdr (lookup-equal-list ys asg)))))
           (r1cs::r1cs-constraints-holdp
            (rec-fields-is-equal-gadget xs ys ms rs zs) asg (base-prime)))
  :do-not-induct t
  :cases ((not (equal (len xs) (len ys)))
          (not (consp xs))
          (not (consp (cdr xs))))
  :in-theory (enable rec-fields-is-equal-gadget)
  :use (rec-fields-is-equal-complete-2 rec-fields-is-equal-complete-1
        (:instance rec-consp-when-len-equal (xs xs) (ys ys))
        (:instance rec-consp-when-len-equal (xs (cdr xs)) (ys (cdr ys)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Ciphertext::is_not_equal

(define rec-fields-is-not-equal-gadget ((xs symbol-listp) (ys symbol-listp)
                                        (ms symbol-listp) (rs symbol-listp)
                                        (zs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((not (equal (len xs) (len ys))) nil)
        ((or (endp xs) (endp ys) (endp ms) (endp rs)) nil)
        (t (append
            (prog-field-neq-gadget (car xs) (car ys) (car ms) (car rs) (base-prime))
            (rec-neq-chain (car rs) (cdr xs) (cdr ys) (cdr ms) (cdr rs) zs)))))

(define rec-fields-is-not-equal-value ((xs symbol-listp) (ys symbol-listp)
                                       (rs symbol-listp) (zs symbol-listp)
                                       (asg alistp))
  :verify-guards nil
  (cond ((not (equal (len xs) (len ys))) 1)
        ((endp xs) 0)
        (t (lookup-equal (rec-chain-last (car rs) zs) asg))))

(defruled rec-fields-is-not-equal-sound-1
  (implies (and (rec-vec-hyps)
                (equal (len xs) (len ys))
                (consp xs)
                (consp ys)
                (r1cs::r1cs-constraints-holdp
                 (rec-fields-is-not-equal-gadget xs ys ms rs zs) asg (base-prime)))
           (equal (rec-fields-is-not-equal-value xs ys rs zs asg)
                  (if (equal (lookup-equal-list xs asg) (lookup-equal-list ys asg))
                      0 1)))
  :do-not-induct t
  :in-theory (e/d (rec-fields-is-not-equal-gadget rec-fields-is-not-equal-value
                   rec-equal-of-lookup-equal-lists
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  (lookup-equal-list))
  :use ((:instance rec-neq-gadget-bit
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
        (:instance rec-neq-chain-sound
                   (acc (car rs)) (xs (cdr xs)) (ys (cdr ys))
                   (ms (cdr ms)) (rs (cdr rs)) (zs zs))))

(defruled rec-ciphertext-is-not-equal-sound
  (b* ((xvals (lookup-equal-list xs asg))
       (yvals (lookup-equal-list ys asg)))
    (implies (and (rec-vec-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-is-not-equal-gadget xs ys ms rs zs) asg (base-prime)))
             (and (values-field-listp xvals)
                  (values-field-listp yvals)
                  (equal (rec-fields-is-not-equal-value xs ys rs zs asg)
                         (crypto-ciphertext-is-not-equal xvals yvals)))))
  :do-not-induct t
  :cases ((not (equal (len xs) (len ys)))
          (not (consp xs)))
  :in-theory (e/d (crypto-ciphertext-is-not-equal crypto-ciphertext-is-equal
                   crypto-bit-not
                   rec-fields-is-not-equal-value
                   rec-values-field-listp-of-lookup
                   rec-lookup-equal-list-when-atom
                   rec-not-equal-lookup-lists-when-len)
                  (lookup-equal-list))
  :use (rec-fields-is-not-equal-sound-1
        (:instance rec-consp-when-len-equal (xs xs) (ys ys))
        (:instance rec-consp-when-len-equal (xs ys) (ys xs))))

(defruled rec-fields-is-not-equal-complete
  (implies (and (rec-vec-hyps)
                (rec-neq-witness-okp xs ys ms rs asg)
                (equal (lookup-equal-list zs asg)
                       (rec-or-prefix (if (equal (lookup-equal (car xs) asg)
                                                 (lookup-equal (car ys) asg))
                                          0 1)
                                      (cdr (lookup-equal-list xs asg))
                                      (cdr (lookup-equal-list ys asg)))))
           (r1cs::r1cs-constraints-holdp
            (rec-fields-is-not-equal-gadget xs ys ms rs zs) asg (base-prime)))
  :do-not-induct t
  :in-theory (e/d (rec-fields-is-not-equal-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  ())
  :expand ((rec-neq-witness-okp xs ys ms rs asg)
           (lookup-equal-list xs asg) (lookup-equal-list ys asg))
  :use ((:instance rec-neq-gadget-complete
                   (x (car xs)) (y (car ys)) (m (car ms)) (r (car rs)))
        (:instance rec-neq-chain-complete
                   (acc (car rs)) (xs (cdr xs)) (ys (cdr ys))
                   (ms (cdr ms)) (rs (cdr rs)) (zs zs))))
