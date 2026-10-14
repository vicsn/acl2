; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar comparisons.  When the operands are not both constant, snarkVM
; computes the linear combination 2*(a - b) and decomposes it.  The result
; of is_less_than is the least significant bit (the last bit of the
; big-endian decomposition, which is the first little-endian bit).
; is_greater_than swaps the operands.  The or-equal forms are boolean not
; of the opposite less-than, so they emit the same constraints and the
; result is the linear combination 1 - bit.
;
; The decomposition below is booleanity, the power-of-two sum of the
; linear combination, and the range check, matching field to_bits.
; For scalars, 2*(a-b) mod p is odd iff a < b, because 2r < p.
; The parity lemma and the four gadget soundness theorems are below.
; The 253-bit decomposition is not a lifted PFCS definition.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-scalar")
(include-book "../r1cs/field-to-bits")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/fep-fix" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-scalar-double-diff-to-bits-gadget ((a symbolp)
                                               (b symbolp)
                                               (bits symbol-listp)
                                               (rs symbol-listp)
                                               (u symbolp)
                                               (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :guard-hints (("Goal" :in-theory (disable bits-lt-prime-rlen integer-length)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Field decomposition of the linear combination @($2(a-b)$)."
  (append (boolean-check-gadget-list bits p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 2 a)
                          (list (- p 2) b))
                 :b (list (list 1 1))
                 :c (pow2sum-vector bits 0)))
          (bits-lt-prime-gadget bits rs p)
          (zero-unit-gadget (car (last rs)) u p)))

(define crv-scalar-is-less-than-gadget ((a symbolp)
                                        (b symbolp)
                                        (bits symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-scalar-double-diff-to-bits-gadget a b bits rs u p))

(define crv-scalar-is-greater-than-gadget ((a symbolp)
                                           (b symbolp)
                                           (bits symbol-listp)
                                           (rs symbol-listp)
                                           (u symbolp)
                                           (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "is_greater_than is is_less_than with the scalars swapped."
  (crv-scalar-is-less-than-gadget b a bits rs u p))

(define crv-scalar-is-greater-than-or-equal-gadget
  ((a symbolp) (b symbolp)
   (bits symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as is_less_than.  The result is @($1 - bit$)."
  (crv-scalar-is-less-than-gadget a b bits rs u p))

(define crv-scalar-is-less-than-or-equal-gadget
  ((a symbolp) (b symbolp)
   (bits symbol-listp) (rs symbol-listp) (u symbolp) (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-scalar-is-greater-than-or-equal-gadget b a bits rs u p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 2r < p, and p is odd, without leaving the prime expanded in later proofs.

(defrule crv-scalar-prime-below-base-prime
  (< (scalar-prime) (base-prime))
  :rule-classes (:rewrite (:linear :trigger-terms ((scalar-prime))))
  :in-theory '((:e scalar-prime) (:e base-prime) (:e <)))

(defrule crv-twice-scalar-prime-below-base-prime
  (< (* 2 (scalar-prime)) (base-prime))
  :rule-classes (:rewrite (:linear :trigger-terms ((scalar-prime))))
  :in-theory '((:e scalar-prime) (:e base-prime) (:e <) (:e *)))

(defrule crv-base-prime-oddp
  (oddp (base-prime))
  :in-theory '((:e base-prime) (:e oddp)))

(defrule crv-integer-length-of-base-prime
  (equal (integer-length (base-prime)) 253)
  :in-theory '((:e base-prime) (:e integer-length)))

(local (in-theory (disable base-prime
                           (:e base-prime)
                           scalar-prime
                           (:e scalar-prime)
                           ecurve::edwards-bls12-q
                           (:e ecurve::edwards-bls12-q)
                           ecurve::edwards-bls12-r
                           (:e ecurve::edwards-bls12-r)
                           primes::bls12-377-scalar-field-prime
                           (:e primes::bls12-377-scalar-field-prime))))

(defruled crv-fep-base-of-scalar
  (implies (and (equal p (base-prime))
                (scalarp s))
           (pfield::fep s p))
  :enable (scalarp pfield::fep)
  :disable (base-prime (:e base-prime)
            scalar-prime (:e scalar-prime)
            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
            primes::bls12-377-scalar-field-prime
            (:e primes::bls12-377-scalar-field-prime))
  :use crv-scalar-prime-below-base-prime)

(defruled crv-neg-of-nonzero-scalar
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp b)
                (not (equal b 0)))
           (equal (pfield::neg b p)
                  (- p b)))
  :enable (pfield::neg)
  :disable (base-prime (:e base-prime)
            scalar-prime (:e scalar-prime)
            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
            primes::bls12-377-scalar-field-prime
            (:e primes::bls12-377-scalar-field-prime))
  :use ((:instance crv-fep-base-of-scalar (s b))
        (:instance acl2::mod-when-<-of-0 (x (- b)) (y p))))

(defruled crv-sub-when-scalar-ge
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp a)
                (scalarp b)
                (<= b a))
           (equal (pfield::sub a b p)
                  (- a b)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (e/d (pfield::sub pfield::add pfield::neg pfield::fep scalarp)
                           (base-prime (:e base-prime)
                            scalar-prime (:e scalar-prime)
                            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
                            primes::bls12-377-scalar-field-prime
                            (:e primes::bls12-377-scalar-field-prime)
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mod-when-fep))
           :use (crv-scalar-prime-below-base-prime
                 (:instance crv-fep-base-of-scalar (s a))
                 (:instance crv-fep-base-of-scalar (s b))))))

(defruled crv-sub-when-scalar-lt
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp a)
                (scalarp b)
                (< a b))
           (equal (pfield::sub a b p)
                  (- p (- b a))))
  :hints (("Goal"
           :in-theory (e/d (pfield::sub pfield::add pfield::neg pfield::fep scalarp)
                           (base-prime (:e base-prime)
                            scalar-prime (:e scalar-prime)
                            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
                            primes::bls12-377-scalar-field-prime
                            (:e primes::bls12-377-scalar-field-prime)
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mod-when-fep))
           :use (crv-scalar-prime-below-base-prime
                 (:instance crv-fep-base-of-scalar (s a))
                 (:instance crv-fep-base-of-scalar (s b))))))

(defruled crv-mul-2-when-below-prime
  (implies (and (posp p)
                (natp k)
                (< (* 2 k) p))
           (equal (pfield::mul 2 k p)
                  (* 2 k)))
  :enable pfield::mul
  :use (:instance acl2::mod-when-< (x (* 2 k)) (y p)))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defruled crv-mul-2-of-complement
    (implies (and (posp p)
                  (natp d)
                  (< 0 d)
                  (< (* 2 d) p))
             (equal (pfield::mul 2 (- p d) p)
                    (- p (* 2 d))))
    :hints (("Goal" :in-theory (enable pfield::mul))))

  (defruled crv-mod-2-of-p-minus-even
    (implies (and (integerp p)
                  (oddp p)
                  (integerp e)
                  (evenp e)
                  (<= e p))
             (equal (mod (- p e) 2)
                    1))
    :hints (("Goal" :in-theory (enable oddp evenp))))

  (defruled crv-twice-scalar-diff-below-prime
    (implies (and (equal p (base-prime))
                  (scalarp x)
                  (scalarp y)
                  (<= y x))
             (< (* 2 (- x y)) p))
    :hints (("Goal"
             :in-theory (e/d (scalarp pfield::fep)
                             (base-prime (:e base-prime)
                              scalar-prime (:e scalar-prime)
                              ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
                              ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
                              primes::bls12-377-scalar-field-prime
                              (:e primes::bls12-377-scalar-field-prime)))
             :use (crv-twice-scalar-prime-below-base-prime
                   crv-scalar-prime-below-base-prime)))))

(defruled crv-mod-2-of-double
  (implies (integerp z)
           (equal (mod (* 2 z) 2) 0))
  :enable (acl2::evenp-of-*-when-evenp
           acl2::mod-of-2-when-evenp-cheap)
  :use (:instance acl2::evenp-of-*-when-evenp (x 2) (y z)))

(defruled crv-double-diff-even-when-ge
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp a)
                (scalarp b)
                (<= b a))
           (equal (mod (pfield::mul 2 (pfield::sub a b p) p) 2)
                  0))
  :hints (("Goal"
           :use ((:instance crv-sub-when-scalar-ge)
                 (:instance crv-mul-2-when-below-prime (k (- a b)))
                 (:instance crv-mod-2-of-double (z (- a b)))
                 (:instance crv-twice-scalar-diff-below-prime (x a) (y b)))
           :in-theory (e/d (scalarp pfield::fep)
                           (pfield::sub pfield::mul
                            base-prime (:e base-prime)
                            scalar-prime (:e scalar-prime)
                            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
                            primes::bls12-377-scalar-field-prime
                            (:e primes::bls12-377-scalar-field-prime))))))

(defruled crv-double-diff-odd-when-lt
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp a)
                (scalarp b)
                (< a b))
           (equal (mod (pfield::mul 2 (pfield::sub a b p) p) 2)
                  1))
  :hints (("Goal"
           :use ((:instance crv-sub-when-scalar-lt)
                 (:instance crv-mul-2-of-complement (d (- b a)))
                 (:instance crv-mod-2-of-p-minus-even (e (* 2 (- b a))))
                 (:instance crv-twice-scalar-diff-below-prime (x b) (y a)))
           :in-theory (e/d (scalarp pfield::fep)
                           (pfield::sub pfield::mul
                            base-prime (:e base-prime)
                            scalar-prime (:e scalar-prime)
                            ecurve::edwards-bls12-q (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-r (:e ecurve::edwards-bls12-r)
                            primes::bls12-377-scalar-field-prime
                            (:e primes::bls12-377-scalar-field-prime))))))

(defruled crv-scalar-double-diff-parity
  :short "For scalars, @($2(a-b)$) in the base field is odd iff @($a < b$)."
  (implies (and (equal p (base-prime))
                (primep p)
                (scalarp a)
                (scalarp b))
           (equal (mod (pfield::mul 2 (pfield::sub a b p) p) 2)
                  (if (< a b) 1 0)))
  :cases ((< a b))
  :enable (crv-double-diff-even-when-ge
           crv-double-diff-odd-when-lt)
  :disable (pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            (:definition pfield::sub)))

(defruled crv-car-is-mod-2-of-lebits
  (implies (and (bit-listp bits)
                (consp bits))
           (equal (car bits)
                  (mod (lebits=>nat bits) 2)))
  :enable (acl2::lebits=>nat-of-cons bitp bfix crv-mod-2-of-double))

(defruled crv-neg-2-mod-prime
  (implies (and (primep p)
                (< 2 p))
           (equal (mod (- p 2) p)
                  (pfield::neg 2 p)))
  :enable (pfield::neg)
  :use (:instance acl2::mod-of-+-same-arg2 (x -2) (y p)))

(defruled crv-double-diff-linear-combination
  (implies (and (primep p)
                (< 2 p)
                (pfield::fep a p)
                (pfield::fep b p))
           (equal (pfield::add (pfield::mul 2 a p)
                               (pfield::mul (mod (- p 2) p) b p)
                               p)
                  (pfield::mul 2 (pfield::sub a b p) p)))
  :enable (pfield::sub crv-neg-2-mod-prime))

(defruled crv-double-diff-constraint-to-mul
  (implies (and (symbolp a)
                (symbolp b)
                (symbol-listp bits)
                (primep p)
                (< 2 p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (list (list 2 a)
                             (list (- p 2) b))
                    :b (list (list 1 1))
                    :c (pow2sum-vector bits 0))
                   asg p)
                  (equal (pfield::mul 2
                                      (pfield::sub (lookup-equal a asg)
                                                   (lookup-equal b asg)
                                                   p)
                                      p)
                         (mod (lebits=>nat (lookup-equal-list bits asg))
                              p))))
  :hints (("Goal"
           :use (:instance crv-double-diff-linear-combination
                           (a (lookup-equal a asg))
                           (b (lookup-equal b asg)))
           :in-theory (e/d (r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            pow2sum-vector-to-mod-of-lebits=>nat
                            r1cs::fep-of-lookup-equal
                            crv-neg-2-mod-prime)
                           (pfield::mul-of-+-same-arg1-arg2
                            pfield::add-of-mul-and-mul-combine-constants-2
                            pfield::equal-of-add-move-negations-bind-free-2a
                            pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::add-commutative
                            pfield::add-commutative-2
                            (:definition pfield::sub))))))

(defruled crv-consp-when-len-253
  (implies (equal (len x) 253)
           (consp x))
  :cases ((consp x)))

(defruled crv-member-of-car-of-last
  (implies (consp x)
           (member-equal (car (last x)) x))
  :hints (("Goal" :in-theory (enable last member-equal))))

(defruled crv-scalar-double-diff-to-bits-to-value
  (implies (and (symbolp a) (symbolp b)
                (symbol-listp bits) (symbol-listp rs)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (primep p) (oddp p) (< 2 p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-double-diff-to-bits-gadget a b bits rs u p)
                 asg p))
           (b* ((bits$ (lookup-equal-list bits asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (and (bit-listp bits$)
                           (consp bits$)
                           (equal (pfield::mul 2
                                              (pfield::sub (lookup-equal a asg)
                                                           (lookup-equal b asg)
                                                           p)
                                              p)
                                  (lebits=>nat bits$))))))
  :use ((:instance bits-lt-prime-soundness (x a) (xs bits))
        (:instance crv-consp-when-len-253 (x bits)))
  :cases ((consp rs))
  :enable (crv-scalar-double-diff-to-bits-gadget
           boolean-check-gadget-list-to-bit-listp
           crv-double-diff-constraint-to-mul
           zero-unit-gadget-to-equal-0
           last-of-lookup-equal-list
           car-of-lookup-equal-list
           crv-integer-length-of-base-prime
           crv-member-of-car-of-last
           r1cs::valuation-bindsp-when-valuation-binds-allp
           acl2::mod-when-<)
  :disable (integer-length
            bits-lt-prime-rlen
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::add-of-mul-and-mul-combine-constants-2
            (:definition pfield::sub)))

(defruled crv-sub-1-of-bit
  (implies (and (equal p (base-prime))
                (bitp b))
           (equal (pfield::sub 1 b p)
                  (if (equal b 0) 1 0)))
  :cases ((equal b 0))
  :enable bitp
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1))

(defruled crv-scalar-is-less-than-gadget-sound
  (implies (and (symbolp a) (symbolp b)
                (symbol-listp bits) (symbol-listp rs)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (primep p) (oddp p) (< 2 p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-less-than-gadget a b bits rs u p)
                 asg p))
           (implies (equal (lookup-equal u asg) 1)
                    (equal (car (lookup-equal-list bits asg))
                           (scalar-is-less-than-funspec
                            (lookup-equal a asg)
                            (lookup-equal b asg)))))
  :hints (("Goal"
           :use ((:instance crv-scalar-double-diff-to-bits-to-value)
                 (:instance crv-scalar-double-diff-parity
                            (a (lookup-equal a asg))
                            (b (lookup-equal b asg)))
                 (:instance crv-car-is-mod-2-of-lebits
                            (bits (lookup-equal-list bits asg))))
           :in-theory (e/d (crv-scalar-is-less-than-gadget
                            scalar-is-less-than-funspec
                            scalarp
                            pfield::fep-fix-when-fep)
                           (crv-scalar-double-diff-to-bits-to-value
                            crv-scalar-double-diff-parity
                            crv-car-is-mod-2-of-lebits
                            base-prime (:e base-prime)
                            scalar-prime (:e scalar-prime)
                            ecurve::edwards-bls12-q
                            (:e ecurve::edwards-bls12-q)
                            ecurve::edwards-bls12-r
                            (:e ecurve::edwards-bls12-r)
                            primes::bls12-377-scalar-field-prime
                            (:e primes::bls12-377-scalar-field-prime))))))

(defruled crv-scalar-is-greater-than-gadget-sound
  (implies (and (symbolp a) (symbolp b)
                (symbol-listp bits) (symbol-listp rs)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (primep p) (oddp p) (< 2 p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-greater-than-gadget a b bits rs u p)
                 asg p))
           (implies (equal (lookup-equal u asg) 1)
                    (equal (car (lookup-equal-list bits asg))
                           (scalar-is-greater-than-funspec
                            (lookup-equal a asg)
                            (lookup-equal b asg)))))
  :hints (("Goal"
           :use (:instance crv-scalar-is-less-than-gadget-sound
                           (a b) (b a))
           :in-theory (e/d (crv-scalar-is-greater-than-gadget
                            scalar-is-greater-than-funspec
                            crv-integer-length-of-base-prime)
                           (integer-length
                            crv-scalar-is-less-than-gadget-sound)))))

(defruled crv-scalar-is-greater-than-or-equal-gadget-sound
  (implies (and (symbolp a) (symbolp b)
                (symbol-listp bits) (symbol-listp rs)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (primep p) (oddp p) (< 2 p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-greater-than-or-equal-gadget
                  a b bits rs u p)
                 asg p))
           (implies (equal (lookup-equal u asg) 1)
                    (equal (pfield::sub 1
                                        (car (lookup-equal-list bits asg))
                                        p)
                           (scalar-is-greater-than-or-equal-funspec
                            (lookup-equal a asg)
                            (lookup-equal b asg)))))
  :hints (("Goal"
           :use (:instance crv-scalar-is-less-than-gadget-sound)
           :in-theory (e/d (crv-scalar-is-greater-than-or-equal-gadget
                            crv-sub-1-of-bit
                            scalar-is-greater-than-or-equal-funspec
                            scalar-is-less-than-funspec
                            boolean-not-funspec
                            bitp
                            crv-integer-length-of-base-prime)
                           (integer-length
                            crv-scalar-is-less-than-gadget-sound
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1)))))

(defruled crv-scalar-is-less-than-or-equal-gadget-sound
  (implies (and (symbolp a) (symbolp b)
                (symbol-listp bits) (symbol-listp rs)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (primep p) (oddp p) (< 2 p) (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-less-than-or-equal-gadget
                  a b bits rs u p)
                 asg p))
           (implies (equal (lookup-equal u asg) 1)
                    (equal (pfield::sub 1
                                        (car (lookup-equal-list bits asg))
                                        p)
                           (scalar-is-less-than-or-equal-funspec
                            (lookup-equal a asg)
                            (lookup-equal b asg)))))
  :hints (("Goal"
           :use (:instance crv-scalar-is-greater-than-or-equal-gadget-sound
                           (a b) (b a))
           :in-theory (e/d (crv-scalar-is-less-than-or-equal-gadget
                            scalar-is-less-than-or-equal-funspec
                            crv-integer-length-of-base-prime)
                           (integer-length
                            crv-scalar-is-greater-than-or-equal-gadget-sound)))))
