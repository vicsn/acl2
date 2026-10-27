; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::from_field (circuit/types/scalar/src/helpers/from_field.rs).
;
; The body is Scalar::from_bits_le of Field::to_bits_le, with no truncation.
; size_in_bits is 251, size_in_data_bits is 250, and the base field is 253
; bits, so the 253-bit list is longer than both.
;
; Field::to_bits_le is field-to-bits-gadget: boolean checks, the power-of-two
; sum, bits-lt-prime-gadget, and zero-unit-gadget on (car (last rs)).
; field-to-bits-soundness yields bit-listp and x = lebits=>nat only when the
; unit wire is 1.  zero-unit-gadget does not force that wire.  The hypothesis
; (lookup-equal u asg) = 1 is the public one.
;
; from_bits_le then emits:
;   Boolean::assert_bits_are_zero on (nthcdr 251 xs).  One constraint: the
;   unweighted sum of those two bits, times 1, equals 0.
;   Boolean::assert_less_than_or_equal_constant of the first 251 bits against
;   the little-endian bits of r - 1.  That is bits-lte-const-gadget (rlen 250)
;   and a final assert that the comparison result wire is 0.
; The scalar is lebits=>nat of those 251 bit wires.  The weighted sum is a
; linear combination, not an assert_eq.
;
; bits-lte-const-soundness assumes bit-listp of the circuit bits.  That
; hypothesis is used only after field-to-bits-soundness has proved it.
; Completeness is not claimed: the bits-below-prime and bits-lte-const
; witnesses are not constructed.

(in-package "ALEOVM")

(include-book "../r1cs/field-to-bits")
(include-book "scalar-new-r1cs")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "../library-extensions/r1cses"))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled scalar-from-field-base-facts
  (and (primep (base-prime))
       (oddp (base-prime))
       (< 2 (base-prime))
       (equal (integer-length (base-prime)) 253))
  :in-theory '((:e base-prime)
               (:e primep)
               (:e oddp)
               (:e <)
               (:e integer-length)))

(defruled scalar-from-field-scalar-prime-posp
  (posp (scalar-prime))
  :in-theory '((:e scalar-prime) (:e posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl scalar-from-field-symbol-listp-of-nthcdr
  (implies (symbol-listp xs)
           (symbol-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr symbol-listp))))

(defruledl scalar-from-field-symbol-listp-of-take
  (implies (and (symbol-listp xs)
                (natp n)
                (<= n (len xs)))
           (symbol-listp (take n xs)))
  :hints (("Goal" :in-theory (enable take symbol-listp))))

(defruledl scalar-from-field-consp-when-len-250
  (implies (equal (len qs) 250)
           (consp qs))
  :hints (("Goal" :in-theory (enable len))))

(defruledl scalar-from-field-symbolp-car-last
  (implies (and (symbol-listp qs)
                (consp qs))
           (symbolp (car (last qs))))
  :hints (("Goal" :in-theory (enable last symbol-listp))))

(defruledl scalar-from-field-bindsp-car-last
  (implies (and (r1cs::valuation-binds-allp asg qs)
                (consp qs))
           (r1cs::valuation-bindsp asg (car (last qs))))
  :hints (("Goal" :in-theory (enable last r1cs::valuation-binds-allp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::assert_bits_are_zero.  Same shape as
; fb-boolean-assert-bits-are-zero-gadget: coefficients 1 on each bit,
; times the constant 1, equals 0.  That book has no certificate.

(define scalar-from-field-one-vector ((bits symbol-listp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (if (endp bits)
      nil
    (cons (list 1 (car bits))
          (scalar-from-field-one-vector (cdr bits)))))

(define scalar-from-field-excess-zero-gadget ((bits symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The one constraint of @('Boolean::assert_bits_are_zero')."
  (list (r1cs::make-r1cs-constraint
         :a (scalar-from-field-one-vector bits)
         :b (list (list 1 1))
         :c nil)))

(defruledl scalar-from-field-dot-product-of-one-vector
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::dot-product
                   (scalar-from-field-one-vector bits) asg p)
                  (bits-field-sum (lookup-equal-list bits asg))))
  :hints (("Goal"
           :in-theory (enable scalar-from-field-one-vector
                              r1cs::dot-product
                              bits-field-sum
                              lookup-equal-list
                              bitp
                              pfield::add
                              pfield::mul
                              acl2::bfix))))

(defruled scalar-from-field-excess-zero-to-funspec
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (scalar-from-field-excess-zero-gadget bits) asg p)
                  (boolean-assert-bits-are-zero-funspec
                   (lookup-equal-list bits asg))))
  :enable (scalar-from-field-excess-zero-gadget
           scalar-from-field-dot-product-of-one-vector
           boolean-assert-bits-are-zero-funspec
           assert-eq-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruledl scalar-from-field-pair-zero
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime))
                (equal (pfield::add a (pfield::add b 0 p) p) 0))
           (equal (cons a (cons b nil)) '(0 0)))
  :enable (bitp pfield::add scalar-from-field-base-facts)
  :disable ((:e base-prime)))

(defruledl scalar-from-field-sum-of-pair
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime)))
           (equal (bits-field-sum (cons a (cons b nil)))
                  (pfield::add a (pfield::add b 0 p) p)))
  :enable (bits-field-sum acl2::bfix bitp))

(defruledl scalar-from-field-len-2-as-cons
  (implies (and (true-listp bits)
                (equal (len bits) 2))
           (equal (cons (car bits) (cons (cadr bits) nil))
                  bits))
  :hints (("Goal" :in-theory (enable len true-listp))))

(defruledl scalar-from-field-nthcdr-two
  (implies (and (true-listp xs)
                (natp n)
                (equal (len xs) (+ 2 n)))
           (equal (nthcdr n xs)
                  (cons (nth n xs)
                        (cons (nth (+ 1 n) xs) nil))))
  :hints (("Goal" :in-theory (enable nthcdr nth len))))

(defruledl scalar-from-field-bitp-of-nth
  (implies (and (bit-listp xs)
                (natp i)
                (< i (len xs)))
           (bitp (nth i xs)))
  :hints (("Goal" :in-theory (enable nth bit-listp))))

(defruledl scalar-from-field-mod-of-sum
  (equal (mod (bits-field-sum bits) (base-prime))
         (bits-field-sum bits))
  :hints (("Goal"
           :use fieldp-of-bits-field-sum
           :in-theory (e/d (fieldp pfield::fep acl2::mod-when-<)
                           (fieldp-of-bits-field-sum
                            (:e base-prime))))))

; A left-to-right rewrite, restricted to the looked-up value list.
; nthcdr-two as a general rule also rewrites the symbol list inside the gadget.

(defruledl scalar-from-field-nthcdr-of-lookup
  (implies (and (equal (len xs) 253)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (nthcdr 251 (lookup-equal-list xs asg))
                  (list (nth 251 (lookup-equal-list xs asg))
                        (nth 252 (lookup-equal-list xs asg)))))
  :hints (("Goal"
           :use (:instance scalar-from-field-nthcdr-two
                           (xs (lookup-equal-list xs asg))
                           (n 251))
           :in-theory (e/d (len-of-lookup-equal-list)
                           (scalar-from-field-nthcdr-two)))))

(defruledl scalar-from-field-two-zero
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime))
                (equal (bits-field-sum (list a b)) 0))
           (equal (list a b) '(0 0)))
  :enable (scalar-from-field-sum-of-pair
           scalar-from-field-pair-zero)
  :disable (pfield::add-of-0-arg1-gen
            pfield::add-of-0-arg2-gen
            pfield::add-commutative-when-constant
            (:e base-prime)))

(defruled scalar-from-field-high-bits-zero
  :short "The excess-bit constraint forces the two high field bits to 0."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (equal (len xs) 253)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-excess-zero-gadget (nthcdr 251 xs))
                 asg p))
           (equal (nthcdr 251 (lookup-equal-list xs asg))
                  '(0 0)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (scalar-from-field-excess-zero-to-funspec
                            boolean-assert-bits-are-zero-funspec
                            assert-eq-funspec
                            enforce-funspec
                            scalar-from-field-two-zero
                            scalar-from-field-nthcdr-of-lookup
                            scalar-from-field-mod-of-sum
                            scalar-from-field-symbol-listp-of-nthcdr
                            lookup-equal-list-of-nthcdr
                            acl2::bit-listp-of-nthcdr
                            acl2::bitp-of-nth-when-bit-listp
                            acl2::len-of-nthcdr
                            len-of-lookup-equal-list
                            bitp)
                           (scalar-from-field-nthcdr-two
                            scalar-from-field-sum-of-pair
                            scalar-from-field-pair-zero
                            pfield::add-of-0-arg1-gen
                            pfield::add-of-0-arg2-gen
                            pfield::add-commutative-when-constant
                            (:e base-prime)
                            (:e scalar-prime))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled scalar-from-field-modulus-bits-same
  (equal (acl2::nat=>lebits 251 (1- (scalar-prime)))
         (scalar-modulus-minus-one-bits))
  :use ((:instance acl2::nat=>lebits-of-lebits=>nat
                   (digits (scalar-modulus-minus-one-bits)))
        scalar-modulus-minus-one-bits-value
        scalar-modulus-minus-one-bits-len)
  :enable acl2::bit-list-fix-when-bit-listp
  :disable (acl2::nat=>lebits-of-lebits=>nat
            (:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)
            (:e base-prime)))

(defruled scalar-from-field-lte-iff
  (implies (and (bit-listp low)
                (equal (len low) 251))
           (equal (boolean-assert-less-than-or-equal-constant-funspec
                   low
                   (acl2::nat=>lebits 251 (1- (scalar-prime))))
                  (<= (lebits=>nat low) (1- (scalar-prime)))))
  :enable (boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           assert-funspec
           enforce-funspec
           scalar-from-field-modulus-bits-same
           scalar-modulus-minus-one-bits-value
           scalar-modulus-minus-one-bits-len
           reserrp
           bitp)
  :disable ((:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)
            (:e base-prime)))

(defruledl scalar-from-field-zero-excess-ok
  (boolean-assert-bits-are-zero-funspec '(0 0))
  :enable (boolean-assert-bits-are-zero-funspec
           bits-field-sum
           assert-eq-funspec
           enforce-funspec
           pfield::add
           pfield::mul
           acl2::bfix))

(defruled scalar-from-field-bits-are-canonical
  (implies (and (fieldp x)
                (bit-listp xs)
                (equal (len xs) 253)
                (equal (lebits=>nat xs) x))
           (equal (field-bits-le x) xs))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits xs))
  :enable (field-bits-le
           base-field-size-in-bits
           fieldp
           pfield::fep
           pfield::fep-fix-when-fep
           acl2::bit-list-fix-when-bit-listp)
  :disable (acl2::nat=>lebits-of-lebits=>nat
            (:e base-prime)))

(defruledl scalar-from-field-lebits-of-two-zeros
  (equal (lebits=>nat '(0 0)) 0)
  :in-theory '((:e lebits=>nat)))

(defruledl scalar-from-field-drop-high
  (implies (and (equal (len xs) 253)
                (equal (nthcdr 251 xs) '(0 0)))
           (equal (lebits=>nat xs)
                  (lebits=>nat (take 251 xs))))
  :hints (("Goal"
           :in-theory (e/d (acl2::len-of-take
                            scalar-from-field-lebits-of-two-zeros)
                           (acl2::lebits=>nat-of-append
                            acl2::append-of-take-and-nthcdr))
           :use ((:instance acl2::lebits=>nat-of-append
                            (lodigits (take 251 xs))
                            (hidigits '(0 0)))
                 (:instance acl2::append-of-take-and-nthcdr
                            (n 251)
                            (x xs))))))

(defruledl scalar-from-field-nat-not-error
  (implies (natp s)
           (not (equal s (spec-error))))
  :enable (spec-error reserr reserrp))

(defruled scalar-from-field-values-are-funspec
  :short "Zero excess bits and a 251-bit value at most @($r - 1$) are
          @('scalar-from-field-funspec'), and that value is a scalar."
  (implies (and (fieldp x)
                (bit-listp xs)
                (equal (len xs) 253)
                (equal (lebits=>nat xs) x)
                (equal (nthcdr 251 xs) '(0 0))
                (<= (lebits=>nat (take 251 xs))
                    (1- (scalar-prime))))
           (b* ((low (take 251 xs))
                (s (lebits=>nat low)))
             (and (equal (len low) 251)
                  (bit-listp low)
                  (scalarp s)
                  (equal s x)
                  (not (equal (scalar-from-field-funspec x)
                              (spec-error)))
                  (equal s (scalar-from-field-funspec x)))))
  :do-not-induct t
  :enable (scalar-from-field-funspec
           scalar-from-bits-le-funspec
           scalar-from-field-bits-are-canonical
           scalar-from-field-lte-iff
           scalar-from-field-zero-excess-ok
           scalar-from-field-drop-high
           scalar-from-field-nat-not-error
           scalar-from-field-scalar-prime-posp
           scalar-field-size-in-bits
           base-field-size-in-bits
           scalarp
           pfield::fep
           fieldp
           acl2::len-of-take
           acl2::bit-listp-of-take
           spec-error)
  :disable ((:e scalar-prime)
            (:e base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-from-field-gadget ((x symbolp)
                                  (xs symbol-listp)
                                  (rs symbol-listp)
                                  (u symbolp)
                                  (qs symbol-listp)
                                  (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (integer-length p) 253)
              (equal (len rs) (bits-lt-prime-rlen p))
              (equal (len qs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory (enable
                                         scalar-from-field-symbol-listp-of-nthcdr
                                         scalar-from-field-symbol-listp-of-take
                                         scalar-from-field-consp-when-len-250
                                         scalar-from-field-symbolp-car-last
                                         scalar-modulus-minus-one-bits-len
                                         scalar-modulus-minus-one-bits-has-0
                                         scalar-modulus-minus-one-bits-msb
                                         scalar-modulus-minus-one-bits-rlen))))
  :short "Constraints of @('Scalar::from_field'): @('Field::to_bits_le'),
          then @('assert_bits_are_zero') of the two excess bits and
          @('assert_less_than_or_equal_constant') of the first 251 bits
          against the bits of @($r - 1$)."
  :guard-hints (("Goal"
                 :in-theory (enable
                             scalar-from-field-symbol-listp-of-nthcdr
                             scalar-from-field-symbol-listp-of-take
                             scalar-from-field-consp-when-len-250
                             scalar-from-field-symbolp-car-last
                             scalar-modulus-minus-one-bits-len
                             scalar-modulus-minus-one-bits-has-0
                             scalar-modulus-minus-one-bits-msb
                             scalar-modulus-minus-one-bits-rlen)))
  (append (field-to-bits-gadget x xs rs u p)
          (scalar-from-field-excess-zero-gadget (nthcdr 251 xs))
          (bits-lte-const-gadget (take 251 xs)
                                 (scalar-modulus-minus-one-bits)
                                 qs
                                 p)
          (scalar-new-assert-gadget (car (last qs)) p)))

(defruled scalar-from-field-low-below-modulus
  :short "After the bits are booleans, the comparator and the final assert
          put the low 251 bits at most @($r - 1$)."
  (implies (and (symbol-listp xs)
                (symbol-listp qs)
                (equal (len xs) 253)
                (equal (len qs) 250)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg qs)
                (bit-listp (lookup-equal-list xs asg))
                (r1cs::r1cs-constraints-holdp
                 (bits-lte-const-gadget (take 251 xs)
                                        (scalar-modulus-minus-one-bits)
                                        qs
                                        p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (scalar-new-assert-gadget (car (last qs)) p)
                 asg p))
           (<= (lebits=>nat (take 251 (lookup-equal-list xs asg)))
               (1- (scalar-prime))))
  :do-not-induct t
  :enable (scalar-modulus-minus-one-bits-value
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen
           scalar-new-assert-gadget-to-zero
           scalar-from-field-symbol-listp-of-take
           scalar-from-field-symbolp-car-last
           scalar-from-field-consp-when-len-250
           scalar-from-field-bindsp-car-last
           lookup-equal-list-of-take
           acl2::bit-listp-of-take
           acl2::len-of-take
           last-of-lookup-equal-list
           car-of-lookup-equal-list
           len-of-lookup-equal-list
           r1cs::valuation-binds-allp-of-take)
  :use (:instance bits-lte-const-soundness
                  (xs (take 251 xs))
                  (cs (scalar-modulus-minus-one-bits))
                  (rs qs)
                  (p p))
  :disable (bits-lte-const-soundness
            (:e scalar-prime)
            (:e base-prime)
            (:e scalar-modulus-minus-one-bits)))

(defruled scalar-from-field-gadget-sound
  :short "Wire soundness of @('Scalar::from_field').  The unit wire is
          the public one.  The scalar is @('lebits=>nat') of the first
          251 bit wires: a scalar, equal to @('scalar-from-field-funspec'),
          which is not @('(spec-error)')."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbol-listp qs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len qs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-gadget x xs rs u qs p) asg p))
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg))
                (low (take 251 xs$))
                (s (lebits=>nat low)))
             (and (bit-listp xs$)
                  (equal x$ (lebits=>nat xs$))
                  (fieldp x$)
                  (equal (nthcdr 251 xs$) '(0 0))
                  (scalarp s)
                  (not (equal (scalar-from-field-funspec x$)
                              (spec-error)))
                  (equal s (scalar-from-field-funspec x$)))))
  :do-not-induct t
  :enable (scalar-from-field-gadget
           scalar-from-field-base-facts
           fieldp
           pfield::fep
           r1cs::fep-of-lookup-equal)
  :use ((:instance field-to-bits-soundness
                   (x x) (xs xs) (rs rs) (u u) (p p))
        (:instance scalar-from-field-high-bits-zero
                   (xs xs) (asg asg) (p p))
        (:instance scalar-from-field-low-below-modulus
                   (xs xs) (qs qs) (asg asg) (p p))
        (:instance scalar-from-field-values-are-funspec
                   (x (lookup-equal x asg))
                   (xs (lookup-equal-list xs asg))))
  :disable (field-to-bits-soundness
            scalar-from-field-high-bits-zero
            scalar-from-field-low-below-modulus
            scalar-from-field-values-are-funspec
            (:e base-prime)
            (:e scalar-prime)))
