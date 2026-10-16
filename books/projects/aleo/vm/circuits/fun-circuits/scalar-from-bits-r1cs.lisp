; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS for snarkVM Scalar::from_bits_le, Scalar::from_bits_be, and
; Scalar::from_field (circuit/types/scalar/src/helpers/from_bits.rs and
; from_field.rs).  Scalar::from_field_lossy is a different circuit.
;
; from_bits_le of a list longer than 251 bits emits
; Boolean::assert_bits_are_zero on the excess (one linear sum), then the
; 251-bit case.  Longer than 250 bits: the first 251 bits are a linear
; combination, which adds no constraint, then
; Boolean::assert_less_than_or_equal_constant against the bits of r - 1.
; That comparator is bits-lte-const-gadget plus scalar-new-assert-gadget on
; the last fold wire (the assert that the result is 0).  A 251-bit input
; is 251 constraints and 250 private wires.  Bits that are already booleans
; are not checked again, and the weighted sum is not an assert_eq.
; At most 250 bits: pad with constant false up to 251 and the linear
; combination only.  No range check, and no constraint.
; from_bits_be reverses, then from_bits_le.  Reversal adds no constraint.
; from_field is Field::to_bits_le (field-to-bits-gadget, 253 bits) then
; from_bits_le of those bits.
;
; R1CS-SOUND stays 0 for from_bits_le and from_bits_be.  The constraints
; those functions emit do not force bit-listp: bits-lte-const-gadget and
; boolean-and/or do not, and the weighted sum is not a constraint.
; scalar-from-bits-le-gadget-implies-funspec and the be twin assume
; bit-listp of the wires.  from_field boolean-checks the 253 bits inside
; field-to-bits-gadget, so its soundness is over the wires.  zero-unit-gadget
; does not force the unit wire; the hypothesis (lookup-equal u asg) = 1 is
; the public unit input.

(in-package "ALEOVM")

(include-book "scalar-new-r1cs")
(include-book "crv-bits")
(include-book "../fun-specs/primitives-scalar")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../library-extensions/r1cses")
(include-book "../library-extensions/digits")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/append" :dir :system)

(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "std/lists/last" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e scalar-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-r)
                           (:e scalar-modulus-minus-one-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl sfb-scalar-field-size
  (equal (scalar-field-size-in-bits) 251)
  :in-theory '((:e scalar-field-size-in-bits)))

(defruledl sfb-base-field-size
  (equal (base-field-size-in-bits) 253)
  :in-theory '((:e base-field-size-in-bits)))

(defruledl sfb-scalar-length
  (equal (integer-length (scalar-prime)) 251)
  :in-theory '((:e scalar-prime)
               (:e integer-length)
               (:e ecurve::edwards-bls12-r)))

(defruledl sfb-posp-scalar
  (posp (scalar-prime))
  :in-theory '((:e scalar-prime)
               (:e posp)
               (:e ecurve::edwards-bls12-r)))

(defruledl sfb-base-posp
  (and (posp (base-prime))
       (< 2 (base-prime))
       (oddp (base-prime)))
  :in-theory '((:e base-prime)
               (:e posp)
               (:e <)
               (:e oddp)
               (:e ecurve::edwards-bls12-q)))

;; oddp is disabled, and oddp-when-primep-cheap rewrites it to
;; (not (equal p 2)).  This executable fact discharges that.
(defruledl sfb-base-prime-not-two
  (not (equal (base-prime) 2))
  :in-theory '((:e base-prime)
               (:e ecurve::edwards-bls12-q)
               (:e equal)
               (:e not)))

(defruledl sfb-oddp-of-base-prime
  (oddp (base-prime))
  :in-theory '((:e base-prime)
               (:e ecurve::edwards-bls12-q)
               (:e oddp)))

(defruledl sfb-prime-when-base
  (implies (equal p (base-prime))
           (and (primep p)
                (oddp p)
                (equal (integer-length p) 253)
                (equal (bits-lt-prime-rlen p) 252)))
  :use (crv-base-prime-integer-length
        crv-bits-lt-prime-rlen-is-252
        sfb-base-posp
        primep-of-base-prime)
  :disable (crv-base-prime-integer-length
            crv-bits-lt-prime-rlen-is-252
            primep-of-base-prime))

(defruledl sfb-mod-consts
  (implies (equal p (base-prime))
           (and (equal (mod 0 p) 0)
                (equal (mod 1 p) 1)
                (equal (mod 2 p) 2)))
  :hints (("Goal" :in-theory (enable (:e base-prime) (:e mod)))))

(defruledl sfb-coeff-neg-one
  (implies (equal p (base-prime))
           (equal (mod (1- p) p) (pfield::neg 1 p)))
  :hints (("Goal"
           :in-theory (enable (:e base-prime)
                              (:e ecurve::edwards-bls12-q)
                              pfield::neg))))

(defruledl sfb-modulus-tail
  (and (equal (len (cdr (scalar-modulus-minus-one-bits))) 250)
       (consp (cdr (scalar-modulus-minus-one-bits))))
  :in-theory '((:e scalar-modulus-minus-one-bits)
               (:e len)
               (:e cdr)
               (:e consp)))

(defruledl sfb-pm1-bits-rlen
  (equal (bits-lte-const-rlen (nat=>lebits* (1- (base-prime)))) 252)
  :enable bits-lt-prime-rlen
  :use crv-bits-lt-prime-rlen-is-252
  :disable (crv-bits-lt-prime-rlen-is-252
            (:definition bits-lte-const-rlen)
            (:e base-prime)
            (:e nat=>lebits*)))

(defruledl sfb-pm1-tail
  (and (equal (len (nat=>lebits* (1- (base-prime)))) 253)
       (equal (len (cdr (nat=>lebits* (1- (base-prime))))) 252)
       (consp (cdr (nat=>lebits* (1- (base-prime))))))
  :in-theory '((:e nat=>lebits*)
               (:e acl2::nat=>lendian*)
               (:e base-prime)
               (:e ecurve::edwards-bls12-q)
               (:e len)
               (:e cdr)
               (:e consp)
               (:e binary-+)
               (:e unary--)))

(defruledl sfb-modulus-bits-same
  (equal (acl2::nat=>lebits 251 (1- (scalar-prime)))
         (scalar-modulus-minus-one-bits))
  :use ((:instance acl2::nat=>lebits-of-lebits=>nat
                   (digits (scalar-modulus-minus-one-bits)))
        scalar-modulus-minus-one-bits-value
        scalar-modulus-minus-one-bits-len)
  :enable acl2::bit-list-fix-when-bit-listp
  :disable ((:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)
            (:e base-prime)
            acl2::nat=>lebits-of-lebits=>nat))

(defruledl sfb-symbol-listp-of-take
  (implies (and (symbol-listp xs)
                (natp n)
                (<= n (len xs)))
           (symbol-listp (take n xs)))
  :hints (("Goal" :in-theory (enable take symbol-listp))))

(defruledl sfb-symbol-listp-of-nthcdr
  (implies (symbol-listp xs)
           (symbol-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr symbol-listp))))

(defruledl sfb-bit-listp-of-take
  (implies (and (bit-listp xs)
                (natp n)
                (<= n (len xs)))
           (bit-listp (take n xs)))
  :hints (("Goal" :in-theory (enable take bit-listp))))

(defruledl sfb-symbolp-of-nth
  (implies (and (symbol-listp xs)
                (natp i)
                (< i (len xs)))
           (symbolp (nth i xs)))
  :hints (("Goal" :in-theory (enable nth symbol-listp))))

(defruledl sfb-bindsp-of-nth
  (implies (and (r1cs::valuation-binds-allp asg xs)
                (natp i)
                (< i (len xs)))
           (r1cs::valuation-bindsp asg (nth i xs)))
  :hints (("Goal" :in-theory (enable nth r1cs::valuation-binds-allp))))

(defruledl sfb-nthcdr-two
  (implies (and (true-listp xs)
                (natp n)
                (equal (len xs) (+ 2 n)))
           (equal (nthcdr n xs)
                  (list (nth n xs) (nth (+ 1 n) xs))))
  :hints (("Goal"
           :induct (nthcdr n xs)
           :in-theory (enable nthcdr nth len true-listp))))

(defruledl sfb-take-all
  (implies (and (true-listp xs)
                (equal (len xs) 251))
           (equal (take 251 xs) xs))
  :hints (("Goal"
           :use (:instance acl2::take-of-len (x xs))
           :in-theory (enable acl2::list-fix-when-true-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::assert_bits_are_zero.  One sum, then assert_eq with 0.
; The same constraint as fb-boolean-assert-bits-are-zero-gadget; that book
; does not certify, so the gadget is copied under this name.

(define scalar-from-bits-one-vector ((bits symbol-listp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (if (endp bits)
      nil
    (cons (list 1 (car bits))
          (scalar-from-bits-one-vector (cdr bits)))))

(define scalar-from-bits-excess-zero-gadget ((bits symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The one constraint of @('Boolean::assert_bits_are_zero')."
  (list (r1cs::make-r1cs-constraint
         :a (scalar-from-bits-one-vector bits)
         :b (list (list 1 1))
         :c nil)))

(defruledl sfb-dot-product-of-one-vector
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::dot-product
                   (scalar-from-bits-one-vector bits) asg p)
                  (bits-field-sum (lookup-equal-list bits asg))))
  :hints (("Goal"
           :in-theory (enable scalar-from-bits-one-vector
                              r1cs::dot-product
                              bits-field-sum
                              lookup-equal-list
                              bitp
                              pfield::add
                              pfield::mul
                              acl2::bfix))))

(defruled scalar-from-bits-excess-zero-gadget-to-funspec
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-excess-zero-gadget bits) asg p)
                  (boolean-assert-bits-are-zero-funspec
                   (lookup-equal-list bits asg))))
  :enable (scalar-from-bits-excess-zero-gadget
           sfb-dot-product-of-one-vector
           boolean-assert-bits-are-zero-funspec
           assert-eq-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruledl sfb-add-of-bits
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime)))
           (equal (pfield::add a b p)
                  (if (and (equal a 1) (equal b 1))
                      2
                    (+ a b))))
  :hints (("Goal"
           :in-theory (enable bitp pfield::add)
           :use sfb-base-posp)))

(defruledl sfb-two-bits-sum-zero
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime))
                (equal (pfield::add a (pfield::add b 0 p) p) 0))
           (equal (list a b) '(0 0)))
  :use (sfb-add-of-bits sfb-base-posp)
  :enable (pfield::add bitp)
  :disable (sfb-add-of-bits (:e base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sfb-low-bits ((bits true-listp))
  :returns (low true-listp :hyp (true-listp bits))
  (if (> (len bits) 251)
      (take 251 bits)
    bits)
  ///
  (defret len-of-sfb-low-bits
    (implies (> (len bits) 250)
             (equal (len low) 251))
    :hints (("Goal" :in-theory (enable sfb-low-bits)))))

(define sfb-value ((bits bit-listp))
  :returns (v natp :rule-classes :type-prescription)
  (lebits=>nat (sfb-low-bits bits))
  :guard-hints (("Goal" :in-theory (enable sfb-low-bits
                                           sfb-bit-listp-of-take))))

(defruledl sfb-short-is-scalar
  (implies (and (bit-listp bits)
                (<= (len bits) 250))
           (and (equal (scalar-from-bits-le-funspec bits)
                       (lebits=>nat bits))
                (equal (sfb-value bits) (lebits=>nat bits))
                (scalarp (lebits=>nat bits))
                (not (reserrp (scalar-from-bits-le-funspec bits)))))
  :use ((:instance lebits=>nat-less-when-len-less
                   (p (scalar-prime))
                   (bs bits))
        sfb-posp-scalar
        sfb-scalar-length)
  :rule-classes ((:rewrite) (:forward-chaining))
  :enable (scalar-from-bits-le-funspec
           sfb-scalar-field-size
           sfb-value
           sfb-low-bits
           scalarp
           pfield::fep
           reserrp)
  :disable (lebits=>nat-less-when-len-less
            (:e scalar-prime)
            (:e base-prime)))

(defruledl sfb-lte-iff
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
           sfb-modulus-bits-same
           scalar-modulus-minus-one-bits-value
           scalar-modulus-minus-one-bits-len
           reserrp
           bitp)
  :disable ((:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)
            (:e base-prime)))

(defruledl sfb-funspec-long
  (implies (and (bit-listp bits)
                (> (len bits) 250)
                (implies (> (len bits) 251)
                         (boolean-assert-bits-are-zero-funspec
                          (nthcdr 251 bits)))
                (<= (lebits=>nat (sfb-low-bits bits))
                    (1- (scalar-prime))))
           (and (equal (scalar-from-bits-le-funspec bits)
                       (sfb-value bits))
                (scalarp (sfb-value bits))
                (not (reserrp (scalar-from-bits-le-funspec bits)))))
  :rule-classes ((:rewrite) (:forward-chaining))
  :enable (scalar-from-bits-le-funspec
           sfb-scalar-field-size
           sfb-value
           sfb-low-bits
           sfb-lte-iff
           sfb-bit-listp-of-take
           crv-bit-listp-of-nthcdr
           scalarp
           pfield::fep)
  :disable ((:e scalar-prime)
            (:e base-prime)))

(defruledl sfb-funspec-success-checks
  (implies (and (bit-listp bits)
                (not (reserrp (scalar-from-bits-le-funspec bits))))
           (and (implies (> (len bits) 251)
                         (boolean-assert-bits-are-zero-funspec
                          (nthcdr 251 bits)))
                (implies (> (len bits) 250)
                         (<= (lebits=>nat (sfb-low-bits bits))
                             (1- (scalar-prime))))
                (equal (scalar-from-bits-le-funspec bits)
                       (sfb-value bits))))
  :enable (scalar-from-bits-le-funspec
           sfb-scalar-field-size
           sfb-value
           sfb-low-bits
           sfb-lte-iff
           sfb-bit-listp-of-take
           crv-bit-listp-of-nthcdr
           reserrp)
  :disable ((:e scalar-prime)
            (:e base-prime)
            (:e scalar-modulus-minus-one-bits)))

(defruledl sfb-above-modulus-errors
  (implies (and (bit-listp bits)
                (> (len bits) 250)
                (< (1- (scalar-prime))
                   (lebits=>nat (sfb-low-bits bits))))
           (reserrp (scalar-from-bits-le-funspec bits)))
  :use sfb-funspec-success-checks
  :disable (sfb-funspec-success-checks
            (:e scalar-prime)
            (:e base-prime)))

(defruledl sfb-lebits-of-two-zeros
  (equal (lebits=>nat '(0 0)) 0)
  :in-theory '((:e lebits=>nat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-from-bits-le-gadget ((xs symbol-listp)
                                    (rs symbol-listp)
                                    (p primep))
  :guard (or (<= (len xs) 250)
             (equal (len rs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory (enable sfb-symbol-listp-of-take
                                                sfb-symbol-listp-of-nthcdr
                                                crv-symbolp-of-car-of-last
                                                scalar-modulus-minus-one-bits-len
                                                scalar-modulus-minus-one-bits-has-0
                                                scalar-modulus-minus-one-bits-msb
                                                scalar-modulus-minus-one-bits-rlen))))
  :short "Constraints of @('Scalar::from_bits_le')."
  :guard-hints (("Goal"
                 :in-theory (enable sfb-symbol-listp-of-take
                                    sfb-symbol-listp-of-nthcdr
                                    crv-symbolp-of-car-of-last
                                    scalar-modulus-minus-one-bits-len
                                    scalar-modulus-minus-one-bits-has-0
                                    scalar-modulus-minus-one-bits-msb
                                    scalar-modulus-minus-one-bits-rlen)))
  (if (<= (len xs) 250)
      nil
    (append (if (> (len xs) 251)
                (scalar-from-bits-excess-zero-gadget (nthcdr 251 xs))
              nil)
            (bits-lte-const-gadget (take 251 xs)
                                   (scalar-modulus-minus-one-bits)
                                   rs
                                   p)
            (scalar-new-assert-gadget (car (last rs)) p))))

(define scalar-from-bits-be-gadget ((xs symbol-listp)
                                    (rs symbol-listp)
                                    (p primep))
  :guard (or (<= (len xs) 250)
             (equal (len rs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Scalar::from_bits_be'): reverse, then
          @('from_bits_le').  Reversal adds no constraint."
  :guard-hints (("Goal" :in-theory (enable crv-symbol-listp-of-rev)))
  (scalar-from-bits-le-gadget (rev xs) rs p))

(define scalar-from-field-gadget ((x symbolp)
                                  (xs symbol-listp)
                                  (frs symbol-listp)
                                  (u symbolp)
                                  (srs symbol-listp)
                                  (p primep))
  :guard (and (equal p (base-prime))
              (equal (len xs) 253)
              (equal (len frs) 252)
              (equal (len srs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal"
                             :do-not-induct t
                             :use ((:instance
                                    r1cs-constraint-listp-of-field-to-bits-gadget
                                    (rs frs)))
                             :in-theory (enable crv-base-prime-integer-length
                                                crv-bits-lt-prime-rlen-is-252
                                                sfb-prime-when-base
                                                sfb-oddp-of-base-prime
                                                sfb-base-prime-not-two))))
  :short "Constraints of @('Scalar::from_field'): @('Field::to_bits_le')
          then @('Scalar::from_bits_le') of the 253 bits."
  :guard-hints (("Goal"
                 :use sfb-prime-when-base
                 :in-theory (enable crv-base-prime-integer-length
                                    crv-bits-lt-prime-rlen-is-252)))
  (append (field-to-bits-gadget x xs frs u p)
          (scalar-from-bits-le-gadget xs srs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl sfb-le-hold-split
  (implies (> (len xs) 250)
           (equal (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-le-gadget xs rs p) asg p)
                  (and (or (not (> (len xs) 251))
                           (r1cs::r1cs-constraints-holdp
                            (scalar-from-bits-excess-zero-gadget
                             (nthcdr 251 xs))
                            asg p))
                       (r1cs::r1cs-constraints-holdp
                        (bits-lte-const-gadget
                         (take 251 xs)
                         (scalar-modulus-minus-one-bits)
                         rs p)
                        asg p)
                       (r1cs::r1cs-constraints-holdp
                        (scalar-new-assert-gadget (car (last rs)) p)
                        asg p))))
  :enable scalar-from-bits-le-gadget)

(defruledl sfb-low-of-lookup
  (implies (and (symbol-listp xs)
                (equal (len xs) (len bits))
                (> (len bits) 250))
           (equal (sfb-low-bits bits)
                  (if (equal (len xs) 251)
                      bits
                    (take 251 bits))))
  :enable (sfb-low-bits sfb-take-all))

(defruledl sfb-consp-len-250
  (implies (equal (len x) 250)
           (and (consp x)
                (consp (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defruledl sfb-consp-when-len-250
  (implies (equal (len x) 250)
           (consp x)))

(defruledl sfb-last-lookup-zero
  (implies (and (symbol-listp rs)
                (consp rs)
                (equal (car (lookup-equal-list (last rs) asg)) 0))
           (equal (lookup-equal (car (last rs)) asg) 0))
  :hints (("Goal"
           :do-not-induct t
           :use crv-lookup-of-car-of-last
           :in-theory (e/d (last-of-lookup-equal-list)
                           (car-of-lookup-equal-list
                            crv-lookup-of-car-of-last
                            (:definition last)
                            (:definition lookup-equal-list))))))

(defruledl sfb-lookup-zero-to-last
  (implies (and (symbol-listp rs)
                (consp rs)
                (equal (lookup-equal (car (last rs)) asg) 0))
           (equal (car (lookup-equal-list (last rs) asg)) 0))
  :hints (("Goal"
           :do-not-induct t
           :use crv-lookup-of-car-of-last
           :in-theory (e/d (last-of-lookup-equal-list)
                           (car-of-lookup-equal-list
                            crv-lookup-of-car-of-last
                            (:definition last)
                            (:definition lookup-equal-list))))))

(defruledl sfb-le-gadget-short-holds
  (implies (<= (len xs) 250)
           (r1cs::r1cs-constraints-holdp
            (scalar-from-bits-le-gadget xs rs p) asg p))
  :enable scalar-from-bits-le-gadget)

(defruledl sfb-le-witness-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len rs) 250)
                (> (len xs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (sfb-low-bits (lookup-equal-list xs asg))
                        (scalar-modulus-minus-one-bits)))
                (not (reserrp (scalar-from-bits-le-funspec
                               (lookup-equal-list xs asg)))))
           (r1cs::r1cs-constraints-holdp
            (scalar-from-bits-le-gadget xs rs p) asg p))
  :do-not-induct t
  :cases ((equal (len xs) 251))
  :enable (sfb-le-hold-split
           sfb-funspec-success-checks
           sfb-above-modulus-errors
           sfb-low-of-lookup
           sfb-low-bits
           scalar-from-bits-excess-zero-gadget-to-funspec
           scalar-new-assert-gadget-to-zero
           scalar-modulus-minus-one-bits-value
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen
           sfb-symbol-listp-of-take
           sfb-symbol-listp-of-nthcdr
           sfb-bit-listp-of-take
           crv-bit-listp-of-nthcdr
           crv-symbolp-of-car-of-last
           crv-bindsp-of-car-of-last
           sfb-consp-len-250
           sfb-last-lookup-zero
           crv-bits-lte-const-witness-satisfies
           lookup-equal-list-of-nthcdr
           lookup-equal-list-of-take
           sfb-take-all
           last-of-lookup-equal-list
           len-of-lookup-equal-list
           primep-of-base-prime)
  :use ((:instance bits-lte-const-soundness
                   (xs (take 251 xs))
                   (cs (scalar-modulus-minus-one-bits))
                   (rs rs)
                   (p p)))
  :disable (bits-lte-const-soundness
            car-of-lookup-equal-list
            crv-lookup-of-car-of-last
            (:definition last)
            (:definition lookup-equal-list)
            (:e scalar-prime)
            (:e base-prime)
            (:e scalar-modulus-minus-one-bits)))

; R1CS-SOUND stays 0.  bit-listp is assumed, not derived from the constraints.

(defruled scalar-from-bits-le-gadget-implies-funspec
  :short "Under @('bit-listp') of the bit wires, a satisfying assignment of
          @('Scalar::from_bits_le') returns @('sfb-value') of those wires,
          and that value is a scalar.  R1CS-SOUND stays 0: the circuit does
          not boolean-check the bits."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)))
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-bits-le-gadget xs rs p) asg p))
           (b* ((bits (lookup-equal-list xs asg))
                (s (sfb-value bits)))
             (and (not (reserrp (scalar-from-bits-le-funspec bits)))
                  (equal (scalar-from-bits-le-funspec bits) s)
                  (scalarp s))))
  :do-not-induct t
  :cases ((<= (len xs) 250))
  :enable (sfb-short-is-scalar
           sfb-funspec-long
           sfb-le-hold-split
           sfb-low-of-lookup
           sfb-low-bits
           scalar-from-bits-excess-zero-gadget-to-funspec
           scalar-new-assert-gadget-to-zero
           scalar-modulus-minus-one-bits-value
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen
           sfb-symbol-listp-of-take
           sfb-symbol-listp-of-nthcdr
           sfb-bit-listp-of-take
           crv-bit-listp-of-nthcdr
           crv-symbolp-of-car-of-last
           crv-bindsp-of-car-of-last
           sfb-consp-len-250
           sfb-lookup-zero-to-last
           lookup-equal-list-of-nthcdr
           lookup-equal-list-of-take
           sfb-take-all
           last-of-lookup-equal-list
           len-of-lookup-equal-list
           primep-of-base-prime
           scalar-from-bits-le-gadget)
  :use ((:instance bits-lte-const-soundness
                   (xs (take 251 xs))
                   (cs (scalar-modulus-minus-one-bits))
                   (rs rs)
                   (p p))
        (:instance sfb-funspec-long
                   (bits (lookup-equal-list xs asg)))
        (:instance sfb-short-is-scalar
                   (bits (lookup-equal-list xs asg))))
  :disable (bits-lte-const-soundness
            sfb-funspec-long
            sfb-short-is-scalar
            car-of-lookup-equal-list
            crv-lookup-of-car-of-last
            (:definition last)
            (:definition lookup-equal-list)
            (:e scalar-prime)
            (:e base-prime)
            (:e scalar-modulus-minus-one-bits)))

(defruled scalar-from-bits-le-gadget-rejects-error
  :short "R1CS-COMPLETE, error half: a bit list whose funspec is
          @('(spec-error)') satisfies no assignment of these wires."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)))
                (reserrp (scalar-from-bits-le-funspec
                          (lookup-equal-list xs asg))))
           (not (r1cs::r1cs-constraints-holdp
                 (scalar-from-bits-le-gadget xs rs p) asg p)))
  :use scalar-from-bits-le-gadget-implies-funspec
  :disable scalar-from-bits-le-gadget-implies-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sfb-bind ((keys symbol-listp) (vals))
  :guard (equal (len keys) (len vals))
  :verify-guards nil
  :returns (asg alistp)
  (if (endp keys)
      nil
    (cons (cons (car keys) (car vals))
          (sfb-bind (cdr keys) (cdr vals))))
  ///
  (defret len-of-sfb-bind
    (equal (len asg) (len keys))
    :hints (("Goal" :in-theory (enable sfb-bind)))))

(defruledl sfb-strip-cars
  (implies (and (true-listp keys)
                (equal (len keys) (len vals)))
           (equal (strip-cars (sfb-bind keys vals)) keys))
  :hints (("Goal" :in-theory (enable sfb-bind))))

(defruledl sfb-lookup-list-of-bind
  (implies (and (symbol-listp keys)
                (no-duplicatesp-eq keys)
                (equal (len keys) (len vals))
                (true-listp vals))
           (equal (lookup-equal-list keys (sfb-bind keys vals))
                  vals))
  :hints (("Goal"
           :in-theory (enable sfb-bind
                              lookup-equal-list
                              no-duplicatesp-eq
                              symbol-listp))))

(defruledl sfb-lookup-skip
  (implies (not (member-equal k (strip-cars a)))
           (equal (lookup-equal k (append a b))
                  (lookup-equal k b)))
  :hints (("Goal" :in-theory (enable lookup-equal append member-equal))))

(defruledl sfb-lookup-list-skip
  (implies (not (intersectp-eq keys (strip-cars a)))
           (equal (lookup-equal-list keys (append a b))
                  (lookup-equal-list keys b)))
  :hints (("Goal"
           :in-theory (enable lookup-equal-list
                              intersectp-eq
                              sfb-lookup-skip))))

(defruledl sfb-lookup-rs-from-append
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (no-duplicatesp-equal rs)
                (equal (len xs) (len bits))
                (equal (len rs) (len wits))
                (true-listp wits)
                (not (intersectp-equal xs rs)))
           (equal (lookup-equal-list
                   rs
                   (append (sfb-bind xs bits)
                           (sfb-bind rs wits)))
                  wits))
  :hints (("Goal"
           :in-theory (enable sfb-lookup-list-skip
                              sfb-lookup-list-of-bind
                              sfb-strip-cars
                              sfb-bind
                              lookup-equal-list
                              no-duplicatesp-eq
                              no-duplicatesp-equal
                              intersectp-eq
                              intersectp-equal
                              member-eq
                              member-equal))))

(defruledl sfb-lookup-list-first
  (implies (and (symbol-listp keys)
                (no-duplicatesp-eq keys)
                (equal (len keys) (len vals))
                (true-listp vals))
           (equal (lookup-equal-list keys
                                     (append (sfb-bind keys vals) other))
                  vals))
  :hints (("Goal"
           :in-theory (enable sfb-bind
                              lookup-equal-list
                              no-duplicatesp-eq
                              symbol-listp))))

(defruledl sfb-bit-is-fep
  (implies (and (bitp x) (equal p (base-prime)))
           (pfield::fep x p))
  :hints (("Goal"
           :in-theory (enable bitp)
           :use (sfb-base-posp
                 (:instance pfield::fep-of-0 (p (base-prime)))
                 (:instance pfield::fep-of-1 (p (base-prime)))))))

(defruledl sfb-fe-listp-when-bit-listp
  (implies (and (bit-listp xs) (equal p (base-prime)))
           (pfield::fe-listp xs p))
  :hints (("Goal"
           :in-theory (enable pfield::fe-listp
                              bit-listp
                              sfb-bit-is-fep))))

(defruledl sfb-no-dups-append
  (implies (and (symbol-listp a)
                (symbol-listp b)
                (no-duplicatesp-eq a)
                (no-duplicatesp-eq b)
                (not (intersectp-eq a b)))
           (no-duplicatesp-eq (append a b)))
  :hints (("Goal"
           :in-theory (enable no-duplicatesp-eq
                              append
                              intersectp-eq
                              symbol-listp))))

(defruledl sfb-bind-valuation
  (implies (and (equal p (base-prime))
                (symbol-listp keys)
                (no-duplicatesp-eq keys)
                (bit-listp vals)
                (equal (len keys) (len vals)))
           (r1cs::r1cs-valuationp (sfb-bind keys vals) p))
  :enable (r1cs::r1cs-valuationp
           r1cs::var-listp
           sfb-strip-cars
           sfb-fe-listp-when-bit-listp
           sfb-bind)
  :disable ((:e base-prime)))

(defruledl sfb-binds-of-bind
  (implies (and (symbol-listp keys)
                (equal (len keys) (len vals)))
           (r1cs::valuation-binds-allp (sfb-bind keys vals) keys))
  :hints (("Goal"
           :in-theory (enable sfb-bind
                              r1cs::valuation-binds-allp
                              r1cs::valuation-bindsp
                              sfb-strip-cars
                              symbol-listp))))

(defruledl sfb-binds-of-append-left
  (implies (r1cs::valuation-binds-allp a vars)
           (r1cs::valuation-binds-allp (append a b) vars))
  :hints (("Goal"
           :in-theory (enable r1cs::valuation-binds-allp
                              r1cs::valuation-bindsp
                              append))))

(defruledl sfb-binds-of-append-right
  (implies (r1cs::valuation-binds-allp b vars)
           (r1cs::valuation-binds-allp (append a b) vars))
  :hints (("Goal"
           :in-theory (enable r1cs::valuation-binds-allp
                              r1cs::valuation-bindsp
                              append))))

(defruledl sfb-alistp-of-append
  (implies (and (alistp a) (alistp b))
           (alistp (append a b)))
  :hints (("Goal" :in-theory (enable alistp append))))

(defruledl sfb-strip-cars-of-append
  (equal (strip-cars (append a b))
         (append (strip-cars a) (strip-cars b)))
  :hints (("Goal" :in-theory (enable strip-cars append))))

(defruledl sfb-strip-cdrs-of-append
  (equal (strip-cdrs (append a b))
         (append (strip-cdrs a) (strip-cdrs b)))
  :hints (("Goal" :in-theory (enable strip-cdrs append))))

(defruledl sfb-symbol-listp-of-append
  (implies (and (symbol-listp a) (symbol-listp b))
           (symbol-listp (append a b)))
  :hints (("Goal" :in-theory (enable symbol-listp append))))

(defruledl sfb-fe-listp-of-append
  (implies (and (pfield::fe-listp a p)
                (pfield::fe-listp b p))
           (pfield::fe-listp (append a b) p))
  :hints (("Goal" :in-theory (enable pfield::fe-listp append))))

(defruledl sfb-append-valuation
  (implies (and (r1cs::r1cs-valuationp a p)
                (r1cs::r1cs-valuationp b p)
                (not (intersectp-eq (strip-cars a) (strip-cars b))))
           (r1cs::r1cs-valuationp (append a b) p))
  :enable (r1cs::r1cs-valuationp
           r1cs::var-listp
           sfb-no-dups-append
           sfb-alistp-of-append
           sfb-strip-cars-of-append
           sfb-strip-cdrs-of-append
           sfb-symbol-listp-of-append
           sfb-fe-listp-of-append)
  :disable ((:e base-prime)))

(defruledl sfb-witness-bit-listp
  (implies (and (bit-listp bits)
                (equal (len bits) 251))
           (bit-listp (crv-bits-lte-const-witness
                       bits (scalar-modulus-minus-one-bits))))
  :enable (scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb)
  :disable ((:e scalar-modulus-minus-one-bits)))

(defruled scalar-from-bits-le-gadget-complete
  :short "R1CS-COMPLETE, success half: the bits together with the canonical
          @('bits-lte-const') fold witness satisfy @('Scalar::from_bits_le')
          whenever the funspec returns a value."
  (implies (and (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp rs)
                (no-duplicatesp-eq xs)
                (bit-listp bits)
                (equal (len xs) (len bits))
                (not (reserrp (scalar-from-bits-le-funspec bits)))
                (if (<= (len bits) 250)
                    t
                  (and (equal (len rs) 250)
                       (no-duplicatesp-eq rs)
                       (not (intersectp-eq xs rs)))))
           (b* ((wits (and (> (len bits) 250)
                           (crv-bits-lte-const-witness
                            (sfb-low-bits bits)
                            (scalar-modulus-minus-one-bits))))
                (asg (if (<= (len bits) 250)
                         (sfb-bind xs bits)
                       (append (sfb-bind xs bits)
                               (sfb-bind rs wits)))))
             (and (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg xs)
                  (implies (> (len bits) 250)
                           (r1cs::valuation-binds-allp asg rs))
                  (equal (lookup-equal-list xs asg) bits)
                  (implies (> (len bits) 250)
                           (equal (lookup-equal-list rs asg) wits))
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-le-gadget xs rs p) asg p))))
  :do-not-induct t
  :cases ((<= (len bits) 250))
  :enable (sfb-short-is-scalar
           sfb-le-witness-holds
           sfb-le-gadget-short-holds
           sfb-bind-valuation
           sfb-binds-of-bind
           sfb-binds-of-append-left
           sfb-binds-of-append-right
           sfb-lookup-list-of-bind
           sfb-lookup-list-first
           sfb-lookup-list-skip
           sfb-lookup-rs-from-append
           sfb-strip-cars
           sfb-fe-listp-when-bit-listp
           sfb-witness-bit-listp
           sfb-append-valuation
           primep-of-base-prime
           sfb-low-bits
           sfb-bit-listp-of-take
           len-of-lookup-equal-list
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen)
  :disable ((:definition scalar-from-bits-le-gadget)
            (:e base-prime)
            (:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)))

(defruledl sfb-nat-not-error
  (implies (natp s)
           (not (reserrp s)))
  :enable (reserr reserrp))

(defruled scalar-from-bits-le-gadget-spec
  :short "R1CS-SPEC of @('Scalar::from_bits_le').  The bit wires are a
          @('bit-listp').  Past 250 bits the fold wires are the canonical
          @('crv-bits-lte-const-witness').  The constraints hold iff the
          funspec returns @('sfb-value') of the wires and that value is
          a scalar."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)
                              (equal (lookup-equal-list rs asg)
                                     (crv-bits-lte-const-witness
                                      (sfb-low-bits
                                       (lookup-equal-list xs asg))
                                      (scalar-modulus-minus-one-bits))))))
           (b* ((bits (lookup-equal-list xs asg))
                (s (sfb-value bits)))
             (equal (r1cs::r1cs-constraints-holdp
                     (scalar-from-bits-le-gadget xs rs p) asg p)
                    (and (equal (scalar-from-bits-le-funspec bits) s)
                         (scalarp s)))))
  :do-not-induct t
  :cases ((<= (len xs) 250))
  :use (scalar-from-bits-le-gadget-implies-funspec
        sfb-le-witness-holds
        sfb-short-is-scalar)
  :enable (sfb-value
           sfb-nat-not-error
           sfb-le-gadget-short-holds)
  :disable (scalar-from-bits-le-gadget-implies-funspec
            sfb-le-witness-holds
            sfb-short-is-scalar
            (:e base-prime)
            (:e scalar-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled scalar-from-bits-be-gadget-implies-funspec
  :short "Under @('bit-listp') of the bit wires, a satisfying assignment of
          @('Scalar::from_bits_be') returns the little-endian value of the
          reversed wires.  R1CS-SOUND stays 0, as for @('from_bits_le')."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)))
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-bits-be-gadget xs rs p) asg p))
           (b* ((bits (rev (lookup-equal-list xs asg)))
                (s (sfb-value bits)))
             (and (not (reserrp (scalar-from-bits-be-funspec
                                 (lookup-equal-list xs asg))))
                  (equal (scalar-from-bits-be-funspec
                          (lookup-equal-list xs asg))
                         s)
                  (scalarp s))))
  :do-not-induct t
  :use ((:instance scalar-from-bits-le-gadget-implies-funspec
                   (xs (rev xs))))
  :enable (scalar-from-bits-be-gadget
           scalar-from-bits-be-funspec
           lookup-equal-list-of-rev
           crv-symbol-listp-of-rev
           crv-bit-listp-of-rev
           crv-valuation-binds-allp-of-rev
           acl2::len-of-rev)
  :disable (scalar-from-bits-le-gadget-implies-funspec
            (:e base-prime)
            (:e scalar-prime)))

(defruled scalar-from-bits-be-gadget-rejects-error
  :short "R1CS-COMPLETE, error half, of @('Scalar::from_bits_be')."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)))
                (reserrp (scalar-from-bits-be-funspec
                          (lookup-equal-list xs asg))))
           (not (r1cs::r1cs-constraints-holdp
                 (scalar-from-bits-be-gadget xs rs p) asg p)))
  :use scalar-from-bits-be-gadget-implies-funspec
  :disable scalar-from-bits-be-gadget-implies-funspec)

(defruled scalar-from-bits-be-gadget-complete
  :short "R1CS-COMPLETE, success half, of @('Scalar::from_bits_be').
          The fold witness is for the reversed bits."
  (implies (and (equal p (base-prime))
                (symbol-listp xs)
                (symbol-listp rs)
                (no-duplicatesp-eq xs)
                (bit-listp bits)
                (equal (len xs) (len bits))
                (not (reserrp (scalar-from-bits-be-funspec bits)))
                (if (<= (len bits) 250)
                    t
                  (and (equal (len rs) 250)
                       (no-duplicatesp-eq rs)
                       (not (intersectp-eq xs rs)))))
           (b* ((rbits (rev bits))
                (wits (and (> (len bits) 250)
                           (crv-bits-lte-const-witness
                            (sfb-low-bits rbits)
                            (scalar-modulus-minus-one-bits))))
                (asg (if (<= (len bits) 250)
                         (sfb-bind xs bits)
                       (append (sfb-bind xs bits)
                               (sfb-bind rs wits)))))
             (and (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal-list xs asg) bits)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-be-gadget xs rs p) asg p))))
  :do-not-induct t
  :cases ((<= (len bits) 250))
  :use ((:instance sfb-le-witness-holds
                   (xs (rev xs))
                   (p (base-prime))
                   (asg (if (<= (len bits) 250)
                            (sfb-bind xs bits)
                          (append (sfb-bind xs bits)
                                  (sfb-bind rs
                                            (crv-bits-lte-const-witness
                                             (sfb-low-bits (rev bits))
                                             (scalar-modulus-minus-one-bits))))))))
  :enable (scalar-from-bits-be-gadget
           scalar-from-bits-be-funspec
           sfb-le-witness-holds
           sfb-le-gadget-short-holds
           sfb-short-is-scalar
           crv-bit-listp-of-rev
           crv-symbol-listp-of-rev
           crv-valuation-binds-allp-of-rev
           lookup-equal-list-of-rev
           sfb-bind-valuation
           sfb-binds-of-bind
           sfb-binds-of-append-left
           sfb-binds-of-append-right
           sfb-lookup-list-of-bind
           sfb-lookup-list-first
           sfb-lookup-list-skip
           sfb-lookup-rs-from-append
           sfb-strip-cars
           sfb-witness-bit-listp
           sfb-bit-listp-of-take
           sfb-append-valuation
           sfb-no-dups-append
           primep-of-base-prime
           acl2::len-of-rev
           sfb-low-bits
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen)
  :disable ((:definition scalar-from-bits-le-gadget)
            (:e base-prime)
            (:e scalar-prime)
            (:e scalar-modulus-minus-one-bits)
            sfb-le-witness-holds))

(defruled scalar-from-bits-be-gadget-spec
  :short "R1CS-SPEC of @('Scalar::from_bits_be'), under @('bit-listp') and,
          past 250 bits, the canonical fold witness of the reversed wires."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp rs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (implies (> (len xs) 250)
                         (and (equal (len rs) 250)
                              (r1cs::valuation-binds-allp asg rs)
                              (equal (lookup-equal-list rs asg)
                                     (crv-bits-lte-const-witness
                                      (sfb-low-bits
                                       (rev (lookup-equal-list xs asg)))
                                      (scalar-modulus-minus-one-bits))))))
           (b* ((bits (lookup-equal-list xs asg))
                (s (sfb-value (rev bits))))
             (equal (r1cs::r1cs-constraints-holdp
                     (scalar-from-bits-be-gadget xs rs p) asg p)
                    (and (equal (scalar-from-bits-be-funspec bits) s)
                         (scalarp s)))))
  :do-not-induct t
  :cases ((<= (len xs) 250))
  :use (scalar-from-bits-be-gadget-implies-funspec
        (:instance sfb-le-witness-holds (xs (rev xs)))
        (:instance sfb-short-is-scalar
                   (bits (rev (lookup-equal-list xs asg)))))
  :enable (scalar-from-bits-be-gadget
           scalar-from-bits-be-funspec
           sfb-value
           sfb-nat-not-error
           sfb-le-gadget-short-holds
           lookup-equal-list-of-rev
           crv-symbol-listp-of-rev
           crv-bit-listp-of-rev
           crv-valuation-binds-allp-of-rev
           acl2::len-of-rev)
  :disable (scalar-from-bits-be-gadget-implies-funspec
            sfb-le-witness-holds
            sfb-short-is-scalar
            (:e base-prime)
            (:e scalar-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl sfb-bits-are-field-bits
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bit-listp xs)
                (equal (len xs) 253)
                (equal (lebits=>nat xs) x))
           (equal (field-bits-le x) xs))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits xs))
  :enable (field-bits-le
           sfb-base-field-size
           fieldp
           pfield::fep
           pfield::fep-fix-when-fep
           acl2::bit-list-fix-when-bit-listp)
  :disable (acl2::nat=>lebits-of-lebits=>nat
            (:e base-prime)
            (:e scalar-prime)))

(defruledl sfb-two-excess-zero
  (implies (and (bitp a)
                (bitp b)
                (equal p (base-prime))
                (boolean-assert-bits-are-zero-funspec (list a b)))
           (equal (list a b) '(0 0)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal a 1))
           :in-theory (e/d (boolean-assert-bits-are-zero-funspec
                            assert-eq-funspec
                            enforce-funspec
                            bits-field-sum
                            bitp
                            pfield::add
                            pfield::mul
                            sfb-two-bits-sum-zero
                            sfb-add-of-bits)
                           ((:e base-prime)
                            (:e scalar-prime))))
          ("Subgoal 2" :cases ((equal b 1)))
          ("Subgoal 1" :cases ((equal b 1)))))

(defruledl sfb-high-two-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (equal (len xs) 253)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-bits-excess-zero-gadget (nthcdr 251 xs))
                 asg p))
           (equal (nthcdr 251 (lookup-equal-list xs asg))
                  '(0 0)))
  :do-not-induct t
  :use ((:instance scalar-from-bits-excess-zero-gadget-to-funspec
                   (bits (nthcdr 251 xs))
                   (p (base-prime)))
        (:instance sfb-two-excess-zero
                   (a (nth 251 (lookup-equal-list xs asg)))
                   (b (nth 252 (lookup-equal-list xs asg)))
                   (p (base-prime))))
  :enable (lookup-equal-list-of-nthcdr
           sfb-symbol-listp-of-nthcdr
           sfb-symbolp-of-nth
           sfb-bindsp-of-nth
           sfb-nthcdr-two
           crv-bit-listp-of-nthcdr
           bitp
           len-of-lookup-equal-list)
  :disable (scalar-from-bits-excess-zero-gadget-to-funspec
            sfb-two-excess-zero
            boolean-assert-bits-are-zero-funspec
            bits-field-sum
            pfield::mul
            pfield::add
            (:e base-prime)))

(defruledl sfb-drop-high-zeros
  (implies (and (bit-listp xs)
                (equal (len xs) 253)
                (equal (nthcdr 251 xs) '(0 0)))
           (equal (lebits=>nat xs)
                  (lebits=>nat (take 251 xs))))
  :use ((:instance acl2::lebits=>nat-of-append
                   (lodigits (take 251 xs))
                   (hidigits (nthcdr 251 xs)))
        (:instance acl2::append-of-take-and-nthcdr
                   (n 251)
                   (x xs))
        sfb-lebits-of-two-zeros)
  :disable (acl2::lebits=>nat-of-append
            acl2::append-of-take-and-nthcdr))

(defruled scalar-from-field-gadget-sound
  :short "R1CS-SOUND of @('Scalar::from_field').  The unit wire is the
          public one: @('(equal (lookup-equal u asg) 1)').  The scalar is
          the value of the low 251 bit wires."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp frs)
                (symbolp u)
                (symbol-listp srs)
                (equal (len xs) 253)
                (equal (len frs) 252)
                (equal (len srs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-gadget x xs frs u srs p) asg p))
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg))
                (s (lebits=>nat (take 251 xs$))))
             (and (bit-listp xs$)
                  (equal x$ (lebits=>nat xs$))
                  (fieldp x$)
                  (equal s (sfb-value xs$))
                  (scalarp s)
                  (equal x$ s)
                  (equal s (scalar-from-field-funspec x$)))))
  :do-not-induct t
  :enable (scalar-from-field-gadget
           scalar-from-field-funspec
           sfb-prime-when-base
           sfb-bits-are-field-bits
           sfb-le-hold-split
           sfb-value
           sfb-low-bits
           fieldp
           pfield::fep
           r1cs::fep-of-lookup-equal)
  :use ((:instance field-to-bits-soundness
                   (x x) (xs xs) (rs frs) (u u) (p p))
        (:instance scalar-from-bits-le-gadget-implies-funspec
                   (xs xs) (rs srs) (p p))
        (:instance sfb-high-two-zero (xs xs) (p p))
        (:instance sfb-drop-high-zeros
                   (xs (lookup-equal-list xs asg))))
  :disable (field-to-bits-soundness
            scalar-from-bits-le-gadget-implies-funspec
            sfb-high-two-zero
            sfb-drop-high-zeros
            (:e base-prime)
            (:e scalar-prime)))

(defruled scalar-from-field-gadget-rejects-error
  :short "R1CS-COMPLETE, error half, of @('Scalar::from_field').  The unit
          wire is the public one."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp frs)
                (symbolp u)
                (symbol-listp srs)
                (equal (len xs) 253)
                (equal (len frs) 252)
                (equal (len srs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs)
                (equal (lookup-equal u asg) 1)
                (fieldp (lookup-equal x asg))
                (reserrp (scalar-from-field-funspec (lookup-equal x asg))))
           (not (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-gadget x xs frs u srs p) asg p)))
  :use scalar-from-field-gadget-sound
  :disable scalar-from-field-gadget-sound)

(defruled scalar-from-field-gadget-complete
  :short "R1CS-COMPLETE, success half, of @('Scalar::from_field'): canonical
          field bits, the public unit 1, and both fold witnesses."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp frs)
                (symbolp u)
                (symbol-listp srs)
                (equal (len xs) 253)
                (equal (len frs) 252)
                (equal (len srs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs)
                (fieldp (lookup-equal x asg))
                (not (reserrp (scalar-from-field-funspec
                               (lookup-equal x asg))))
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list frs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list srs asg)
                       (crv-bits-lte-const-witness
                        (take 251 (lookup-equal-list xs asg))
                        (scalar-modulus-minus-one-bits)))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (scalar-from-field-gadget x xs frs u srs p) asg p))
  :do-not-induct t
  :enable (scalar-from-field-gadget
           scalar-from-field-funspec
           sfb-prime-when-base
           sfb-base-field-size
           sfb-le-witness-holds
           sfb-bits-are-field-bits
           field-bits-le
           fieldp
           pfield::fep
           pfield::fep-fix-when-fep
           len-of-field-bits-le
           crv-bit-listp-of-canonical
           crv-base-prime-integer-length
           crv-bits-lt-prime-rlen-is-252
           sfb-low-bits
           sfb-bit-listp-of-take)
  :use ((:instance crv-field-to-bits-gadget-complete
                   (x x) (xs xs) (rs frs) (u u) (p p))
        (:instance crv-bit-listp-of-canonical
                   (x (lookup-equal x asg)))
        (:instance sfb-le-witness-holds
                   (xs xs) (rs srs) (p (base-prime))))
  :disable (crv-field-to-bits-gadget-complete
            sfb-le-witness-holds
            crv-bit-listp-of-canonical
            sfb-bits-are-field-bits
            (:e base-prime)
            (:e scalar-prime)
            (:e nat=>lebits*)
            integer-length))

(defruled scalar-from-field-gadget-spec
  :short "R1CS-SPEC of @('Scalar::from_field').  The unit wire is the public
          one, and the fold wires are the two canonical witnesses.  The
          scalar is the value of the low 251 bit wires."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp frs)
                (symbolp u)
                (symbol-listp srs)
                (equal (len xs) 253)
                (equal (len frs) 252)
                (equal (len srs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs)
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list frs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list srs asg)
                       (crv-bits-lte-const-witness
                        (take 251 (lookup-equal-list xs asg))
                        (scalar-modulus-minus-one-bits))))
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg))
                (s (lebits=>nat (take 251 xs$))))
             (equal (r1cs::r1cs-constraints-holdp
                     (scalar-from-field-gadget x xs frs u srs p) asg p)
                    (and (bit-listp xs$)
                         (equal x$ (lebits=>nat xs$))
                         (equal s (sfb-value xs$))
                         (equal s (scalar-from-field-funspec x$))
                         (scalarp s)))))
  :do-not-induct t
  :use (scalar-from-field-gadget-sound
        scalar-from-field-gadget-complete)
  :enable (sfb-bits-are-field-bits
           sfb-value
           sfb-low-bits
           fieldp
           pfield::fep)
  :disable (scalar-from-field-gadget-sound
            scalar-from-field-gadget-complete
            (:e base-prime)
            (:e scalar-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS.  Each gate that has a fixed shape is a parse-def.  The power-of-two
; sum and a variable-length excess sum are the relations of those single
; linear constraints, written by hand the way Scalar::new's weighted sum is.
; A list of at most 250 bits emits no constraint, so PFCS-SPEC stays 0 there.

(define sfb-and-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "sfb_and(x, y, z) := { (x) * (y) == (z) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-and-circuit) :pred sfb-and-pred :prime p)

(defruledl sfb-and-pred-to-mul
  (implies (equal p (base-prime))
           (equal (sfb-and-pred x y z p)
                  (equal (pfield::mul x y p) z)))
  :enable sfb-and-pred)

(defruledl sfb-and-gadget-to-mul
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-and-gadget x y z) asg p)
                  (equal (pfield::mul (lookup-equal x asg)
                                      (lookup-equal y asg) p)
                         (lookup-equal z asg))))
  :hints (("Goal"
           :in-theory (e/d (boolean-and-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           (pfield::mul-commutative)))))

(defruledl sfb-and-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (sfb-and-pred (lookup-equal x asg)
                                (lookup-equal y asg)
                                (lookup-equal z asg)
                                p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-and-gadget x y z) asg p)))
  :enable (sfb-and-pred-to-mul
           sfb-and-gadget-to-mul
           sfb-prime-when-base))

(define sfb-or-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "sfb_or(x, y, z) := { (1 - x) * (1 - y) == (1 - z) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-or-circuit) :pred sfb-or-pred :prime p)

(defruledl sfb-or-pred-to-eq
  (implies (equal p (base-prime))
           (equal (sfb-or-pred x y z p)
                  (equal (pfield::mul (pfield::sub 1 x p)
                                      (pfield::sub 1 y p)
                                      p)
                         (pfield::sub 1 z p))))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(sfb-or-pred
                         sfb-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruledl sfb-or-gadget-to-eq
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget x y z p) asg p)
                  (equal (pfield::mul (pfield::sub 1 (lookup-equal x asg) p)
                                      (pfield::sub 1 (lookup-equal y asg) p)
                                      p)
                         (pfield::sub 1 (lookup-equal z asg) p))))
  :hints (("Goal"
           :in-theory (e/d (boolean-or-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            sfb-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruledl sfb-or-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (sfb-or-pred (lookup-equal x asg)
                               (lookup-equal y asg)
                               (lookup-equal z asg)
                               p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget x y z p) asg p)))
  :enable (sfb-or-pred-to-eq sfb-or-gadget-to-eq))

(define sfb-assert-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "sfb_assert(r) := { (1 - r) * (1) == (1) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-assert-circuit) :pred sfb-assert-pred :prime p)

(defruledl sfb-assert-pred-to-eq
  (implies (and (equal p (base-prime))
                (pfield::fep r p))
           (equal (sfb-assert-pred r p)
                  (equal r 0)))
  :hints (("Goal"
           :in-theory (e/d (sfb-assert-pred
                            sfb-mod-consts
                            sfb-prime-when-base)
                           (pfield::mul-commutative)))))

(defruledl sfb-assert-pred-to-r1cs
  (implies (and (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg r))
           (equal (sfb-assert-pred (lookup-equal r asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-new-assert-gadget r p) asg p)))
  :enable (sfb-assert-pred-to-eq
           scalar-new-assert-gadget-to-zero
           r1cs::fep-of-lookup-equal
           sfb-prime-when-base))

(define sfb-bool-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "sfb_bool(b) := { (1 - b) * (b) == (0) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-bool-circuit) :pred sfb-bool-pred :prime p)

(defruledl sfb-bool-pred-to-bitp
  (implies (and (equal p (base-prime))
                (pfield::fep b p))
           (equal (sfb-bool-pred b p)
                  (bitp b)))
  :enable (sfb-bool-pred bitp sfb-mod-consts sfb-prime-when-base)
  :disable (pfield::mul-commutative))

(defruledl sfb-bool-pred-to-r1cs
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (sfb-bool-pred (lookup-equal b asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget b p) asg p)))
  :enable (sfb-bool-pred-to-bitp
           boolean-check-gadget-to-bitp
           r1cs::fep-of-lookup-equal
           sfb-prime-when-base))

(defund sfb-bools-pred (xs asg p)
  (if (endp xs)
      t
    (and (sfb-bool-pred (lookup-equal (car xs) asg) p)
         (sfb-bools-pred (cdr xs) asg p))))

(defruledl sfb-bools-pred-to-r1cs
  (implies (and (symbol-listp xs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (sfb-bools-pred xs asg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget-list xs p) asg p)))
  :hints (("Goal"
           :in-theory (enable sfb-bools-pred
                              boolean-check-gadget-list
                              sfb-bool-pred-to-r1cs
                              r1cs::r1cs-constraints-holdp-of-append
                              symbol-listp
                              r1cs::valuation-binds-allp))))

(define sfb-zero-unit-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "sfb_zero_unit(u, r) := { (u - r) * (1) == (1) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-zero-unit-circuit) :pred sfb-zero-unit-pred :prime p)

(defruledl sfb-zero-unit-pred-to-eq
  (implies (and (equal p (base-prime))
                (pfield::fep u p)
                (pfield::fep r p))
           (equal (sfb-zero-unit-pred u r p)
                  (equal (pfield::sub u r p) 1)))
  :hints (("Goal"
           :use sfb-base-posp
           :in-theory (e/d (sfb-zero-unit-pred
                            pfield::sub
                            sfb-mod-consts)
                           (pfield::mul-commutative
                            pfield::equal-of-add-of-neg
                            pfield::equal-of-add-of-neg-simple)))))

(defruledl sfb-zero-unit-gadget-to-eq
  (implies (and (symbolp u)
                (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraints-holdp
                   (zero-unit-gadget r u p) asg p)
                  (equal (pfield::sub (lookup-equal u asg)
                                      (lookup-equal r asg)
                                      p)
                         1)))
  :hints (("Goal"
           :in-theory (e/d (zero-unit-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            sfb-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruledl sfb-zero-unit-pred-to-r1cs
  (implies (and (symbolp u)
                (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg r))
           (equal (sfb-zero-unit-pred (lookup-equal u asg)
                                      (lookup-equal r asg)
                                      p)
                  (r1cs::r1cs-constraints-holdp
                   (zero-unit-gadget r u p) asg p)))
  :enable (sfb-zero-unit-pred-to-eq
           sfb-zero-unit-gadget-to-eq
           r1cs::fep-of-lookup-equal))

(define sfb-excess2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for the two excess bits of @('Scalar::from_field')."
  (pfcs::parse-def
   "sfb_excess2(b0, b1) := { (b0 + b1) * (1) == (0) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (sfb-excess2-circuit) :pred sfb-excess2-pred :prime p)

(defruledl sfb-excess2-pred-to-eq
  (implies (and (equal p (base-prime))
                (pfield::fep b0 p)
                (pfield::fep b1 p))
           (equal (sfb-excess2-pred b0 b1 p)
                  (equal (pfield::add b0 b1 p) 0)))
  :hints (("Goal"
           :use sfb-base-posp
           :in-theory (e/d (sfb-excess2-pred
                            sfb-mod-consts)
                           (pfield::mul-commutative)))))

(defund sfb-field-sum (bits p)
  (if (endp bits)
      0
    (pfield::add (car bits)
                 (sfb-field-sum (cdr bits) p)
                 p)))

(defund sfb-excess-pred (vars asg p)
  (equal (sfb-field-sum (lookup-equal-list vars asg) p) 0))

(defruledl sfb-fep-of-field-sum
  (implies (posp p)
           (pfield::fep (sfb-field-sum bits p) p))
  :hints (("Goal" :in-theory (enable sfb-field-sum))))

(defruledl sfb-dot-of-one-vector-any
  (implies (and (symbol-listp bits)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits))
           (equal (r1cs::dot-product
                   (scalar-from-bits-one-vector bits) asg p)
                  (sfb-field-sum (lookup-equal-list bits asg) p)))
  :hints (("Goal"
           :in-theory (enable scalar-from-bits-one-vector
                              sfb-field-sum
                              r1cs::dot-product
                              lookup-equal-list
                              r1cs::valuation-binds-allp
                              r1cs::fep-of-lookup-equal
                              symbol-listp))))

(defruledl sfb-excess-pred-to-r1cs
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits))
           (equal (sfb-excess-pred bits asg p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-excess-zero-gadget bits) asg p)))
  :do-not-induct t
  :use sfb-base-posp
  :enable (sfb-excess-pred
           scalar-from-bits-excess-zero-gadget
           sfb-dot-of-one-vector-any
           sfb-fep-of-field-sum
           sfb-prime-when-base
           pfield::mod-when-fep
           r1cs::r1cs-constraint-holdsp)
  :expand ((:free (q) (r1cs::dot-product '((1 1)) asg q))
           (:free (q) (r1cs::dot-product nil asg q)))
  :disable (r1cs::dot-product))

(defruledl sfb-excess2-pred-to-r1cs
  (implies (and (symbolp b0)
                (symbolp b1)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1))
           (equal (sfb-excess2-pred (lookup-equal b0 asg)
                                    (lookup-equal b1 asg)
                                    p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-excess-zero-gadget (list b0 b1))
                   asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use sfb-base-posp
           :in-theory (e/d (sfb-excess2-pred-to-eq
                            scalar-from-bits-excess-zero-gadget
                            scalar-from-bits-one-vector
                            r1cs::r1cs-constraint-holdsp
                            r1cs::fep-of-lookup-equal
                            pfield::mod-when-fep
                            sfb-mod-consts)
                           (pfield::mul-commutative
                            r1cs::dot-product))
           :expand ((:free (q)
                           (r1cs::dot-product (list (list 1 b0)
                                                    (list 1 b1))
                                              asg q))
                    (:free (q)
                           (r1cs::dot-product (list (list 1 b1)) asg q))
                    (:free (q) (r1cs::dot-product '((1 1)) asg q))
                    (:free (q) (r1cs::dot-product nil asg q))))))

(defund sfb-pow2-sum (bits i p)
  (if (endp bits)
      0
    (pfield::add (pfield::mul (expt 2 (nfix i)) (car bits) p)
                 (sfb-pow2-sum (cdr bits) (1+ (nfix i)) p)
                 p)))

(defund sfb-pow2sum-pred (s bits p)
  (equal (pfield::mul s 1 p)
         (sfb-pow2-sum bits 0 p)))

(defruledl sfb-fep-of-pow2-sum
  (implies (posp p)
           (pfield::fep (sfb-pow2-sum bits i p) p))
  :hints (("Goal" :in-theory (enable sfb-pow2-sum))))

(defruledl sfb-pow2-sum-to-dot-product
  (implies (and (symbol-listp xs)
                (natp i))
           (equal (sfb-pow2-sum (lookup-equal-list xs asg) i p)
                  (r1cs::dot-product (pow2sum-vector xs i) asg p)))
  :hints (("Goal"
           :induct (pow2sum-vector xs i)
           :in-theory (enable sfb-pow2-sum
                              pow2sum-vector
                              r1cs::dot-product
                              lookup-equal-list))))

(defruledl sfb-pow2sum-pred-to-r1cs
  (implies (and (symbolp s)
                (symbol-listp xs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s))
           (equal (sfb-pow2sum-pred (lookup-equal s asg)
                                    (lookup-equal-list xs asg)
                                    p)
                  (r1cs::r1cs-constraints-holdp
                   (pow2sum-gadget s xs) asg p)))
  :do-not-induct t
  :use sfb-base-posp
  :enable (sfb-pow2sum-pred
           sfb-pow2-sum-to-dot-product
           sfb-fep-of-pow2-sum
           pow2sum-gadget
           pfield::mod-when-fep
           r1cs::r1cs-constraint-holdsp
           r1cs::fep-of-lookup-equal
           sfb-prime-when-base)
  :expand ((:free (q) (r1cs::dot-product (list (list 1 s)) asg q))
           (:free (q) (r1cs::dot-product '((1 1)) asg q))
           (:free (q) (r1cs::dot-product nil asg q)))
  :disable (r1cs::dot-product))

(defund sfb-chain-pred (xs cs rs asg p)
  (declare (xargs :measure (len cs) :guard t :verify-guards nil))
  (b* ((x (lookup-equal (car xs) asg))
       (r (lookup-equal (car rs) asg)))
    (cond ((endp (cdr cs))
           (if (equal (car cs) 0)
               (sfb-or-pred x (lookup-equal (cadr xs) asg) r p)
             (sfb-and-pred x (lookup-equal (cadr xs) asg) r p)))
          (t (and (if (equal (car cs) 0)
                      (sfb-or-pred x (lookup-equal (cadr rs) asg) r p)
                    (sfb-and-pred x (lookup-equal (cadr rs) asg) r p))
                  (sfb-chain-pred (cdr xs) (cdr cs) (cdr rs) asg p))))))

(defruledl sfb-chain-len-facts
  (and (implies (and (equal (len a) (len b)) (consp b))
                (consp a))
       (implies (and (equal (len a) (len b)) (consp (cdr b)))
                (consp (cdr a)))
       (implies (equal (len a) (len b))
                (equal (equal (len (cdr a)) (len (cdr b))) t))
       (implies (and (equal (len a) (+ 1 (len b))) (consp b))
                (and (consp a)
                     (consp (cdr a))
                     (equal (equal (len (cdr a)) (+ 1 (len (cdr b)))) t))))
  :enable len)

(defruledl sfb-chain-pred-to-r1cs
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (1+ (len cs)))
                (equal (len rs) (len cs))
                (consp cs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs))
           (equal (sfb-chain-pred xs cs rs asg p)
                  (r1cs::r1cs-constraints-holdp
                   (bits-lte-const-gadget-aux xs cs rs p) asg p)))
  :hints (("Goal"
           :induct (sfb-chain-pred xs cs rs asg p)
           :expand ((:free (q) (bits-lte-const-gadget-aux xs cs rs q)))
           :in-theory (e/d (sfb-chain-pred
                            bits-lte-const-gadget-aux
                            sfb-or-pred-to-r1cs
                            sfb-and-pred-to-r1cs
                            r1cs::r1cs-constraints-holdp-of-append
                            sfb-chain-len-facts
                            symbol-listp
                            r1cs::valuation-binds-allp)
                           (len)))))

(defruledl sfb-scalar-range-to-chain
  (implies (and (equal (len xs) 251)
                (equal (len rs) 250))
           (equal (r1cs::r1cs-constraints-holdp
                   (bits-lte-const-gadget
                    xs (scalar-modulus-minus-one-bits) rs p)
                   asg p)
                  (r1cs::r1cs-constraints-holdp
                   (bits-lte-const-gadget-aux
                    (rev xs)
                    (rev (cdr (scalar-modulus-minus-one-bits)))
                    (rev rs)
                    p)
                   asg p)))
  :enable (bits-lte-const-gadget
           scalar-modulus-minus-one-bits-rlen
           scalar-modulus-minus-one-bits-len
           nthcdr
           r1cs::r1cs-constraints-holdp-of-rev))

(defruledl sfb-field-range-to-chain
  (implies (and (equal p (base-prime))
                (equal (len xs) 253)
                (equal (len rs) 252))
           (equal (r1cs::r1cs-constraints-holdp
                   (bits-lt-prime-gadget xs rs p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (bits-lte-const-gadget-aux
                    (rev xs)
                    (rev (cdr (nat=>lebits* (1- p))))
                    (rev rs)
                    p)
                   asg p)))
  :do-not-induct t
  :enable (bits-lt-prime-gadget
           bits-lte-const-gadget
           sfb-pm1-bits-rlen
           crv-pm1-len-is-253
           nthcdr
           r1cs::r1cs-constraints-holdp-of-rev)
  :disable (base-prime
            (:e base-prime)
            (:e nat=>lebits*)
            (:definition bits-lte-const-rlen)
            integer-length))

(defruledl sfb-last-bind
  (implies (and (symbol-listp rs)
                (consp rs)
                (r1cs::valuation-binds-allp asg rs))
           (and (symbolp (car (last rs)))
                (r1cs::valuation-bindsp asg (car (last rs)))))
  :enable (crv-symbolp-of-car-of-last crv-bindsp-of-car-of-last))

(defund scalar-from-bits-le-pred (xs rs asg p)
  (and (or (not (> (len xs) 251))
           (sfb-excess-pred (nthcdr 251 xs) asg p))
       (sfb-chain-pred (rev (take 251 xs))
                       (rev (cdr (scalar-modulus-minus-one-bits)))
                       (rev rs)
                       asg p)
       (sfb-assert-pred (lookup-equal (car (last rs)) asg) p)))

(defruled scalar-from-bits-le-pfcs-iff-r1cs
  :short "PFCS-SPEC of @('Scalar::from_bits_le') when the list is longer
          than 250 bits.  At most 250 bits emits nothing, so PFCS-SPEC
          stays 0 for that case."
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (> (len xs) 250)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs))
           (equal (scalar-from-bits-le-pred xs rs asg p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-le-gadget xs rs p) asg p)))
  :do-not-induct t
  :enable (scalar-from-bits-le-pred
           scalar-from-bits-le-gadget
           sfb-le-hold-split
           sfb-excess-pred-to-r1cs
           sfb-assert-pred-to-r1cs
           sfb-scalar-range-to-chain
           sfb-modulus-tail
           sfb-symbol-listp-of-take
           sfb-symbol-listp-of-nthcdr
           crv-symbol-listp-of-rev
           crv-valuation-binds-allp-of-rev
           crv-valuation-binds-allp-of-nthcdr
           r1cs::valuation-binds-allp-of-take
           sfb-last-bind
           sfb-consp-when-len-250
           crv-symbolp-of-car-of-last
           acl2::len-of-rev
           acl2::len-of-take)
  :use ((:instance sfb-chain-pred-to-r1cs
                   (xs (rev (take 251 xs)))
                   (cs (rev (cdr (scalar-modulus-minus-one-bits))))
                   (rs (rev rs))))
  :disable ((:definition bits-lte-const-gadget)
            (:e scalar-modulus-minus-one-bits)
            (:e base-prime)))

(defund scalar-from-bits-be-pred (xs rs asg p)
  (scalar-from-bits-le-pred (rev xs) rs asg p))

(defruled scalar-from-bits-be-pfcs-iff-r1cs
  :short "PFCS-SPEC of @('Scalar::from_bits_be') when the list is longer
          than 250 bits.  Reversal adds no constraint.  At most 250 bits
          emits nothing, so PFCS-SPEC stays 0 for that case."
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (> (len xs) 250)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs))
           (equal (scalar-from-bits-be-pred xs rs asg p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-bits-be-gadget xs rs p) asg p)))
  :do-not-induct t
  :enable (scalar-from-bits-be-pred
           scalar-from-bits-be-gadget
           scalar-from-bits-le-pfcs-iff-r1cs
           crv-symbol-listp-of-rev
           crv-valuation-binds-allp-of-rev
           acl2::len-of-rev))

(defund scalar-from-field-pred (x xs frs u srs asg p)
  (and (sfb-bools-pred xs asg p)
       (sfb-pow2sum-pred (lookup-equal x asg)
                         (lookup-equal-list xs asg)
                         p)
       (sfb-chain-pred (rev xs)
                       (rev (cdr (nat=>lebits* (1- p))))
                       (rev frs)
                       asg p)
       (sfb-zero-unit-pred (lookup-equal u asg)
                           (lookup-equal (car (last frs)) asg)
                           p)
       (sfb-excess2-pred (lookup-equal (nth 251 xs) asg)
                         (lookup-equal (nth 252 xs) asg)
                         p)
       (sfb-chain-pred (rev (take 251 xs))
                       (rev (cdr (scalar-modulus-minus-one-bits)))
                       (rev srs)
                       asg p)
       (sfb-assert-pred (lookup-equal (car (last srs)) asg) p)))

(defruled scalar-from-field-pfcs-iff-r1cs
  :short "PFCS-SPEC of @('Scalar::from_field'): boolean checks, the
          power-of-two sum, the field range chain, the unit check, the
          two-bit excess sum, the scalar range chain, and the final assert."
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp frs)
                (symbolp u)
                (symbol-listp srs)
                (equal (len xs) 253)
                (equal (len frs) 252)
                (equal (len srs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs))
           (equal (scalar-from-field-pred x xs frs u srs asg p)
                  (r1cs::r1cs-constraints-holdp
                   (scalar-from-field-gadget x xs frs u srs p) asg p)))
  :do-not-induct t
  :enable (scalar-from-field-pred
           scalar-from-field-gadget
           field-to-bits-gadget
           scalar-from-bits-le-gadget
           sfb-bools-pred-to-r1cs
           sfb-pow2sum-pred-to-r1cs
           sfb-field-range-to-chain
           sfb-zero-unit-pred-to-r1cs
           sfb-excess2-pred-to-r1cs
           sfb-scalar-range-to-chain
           sfb-assert-pred-to-r1cs
           sfb-pm1-tail
           crv-pm1-len-is-253
           sfb-modulus-tail
           sfb-symbol-listp-of-take
           sfb-symbolp-of-nth
           sfb-bindsp-of-nth
           sfb-nthcdr-two
           crv-symbol-listp-of-rev
           crv-valuation-binds-allp-of-rev
           r1cs::valuation-binds-allp-of-take
           sfb-last-bind
           sfb-consp-when-len-250
           crv-consp-when-len-252
           crv-symbolp-of-car-of-last
           acl2::len-of-rev
           acl2::len-of-take
           r1cs::r1cs-constraints-holdp-of-append)
  :use ((:instance sfb-chain-pred-to-r1cs
                   (xs (rev xs))
                   (cs (rev (cdr (nat=>lebits* (1- p)))))
                   (rs (rev frs)))
        (:instance sfb-chain-pred-to-r1cs
                   (xs (rev (take 251 xs)))
                   (cs (rev (cdr (scalar-modulus-minus-one-bits))))
                   (rs (rev srs)))
        (:instance sfb-excess2-pred-to-r1cs
                   (b0 (nth 251 xs))
                   (b1 (nth 252 xs))))
  :disable ((:definition bits-lte-const-gadget)
            (:definition bits-lt-prime-gadget)
            (:e base-prime)
            (:e scalar-modulus-minus-one-bits)
            (:e nat=>lebits*)))
