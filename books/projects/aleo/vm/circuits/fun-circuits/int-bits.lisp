; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FromBits::from_bits_le and from_bits_be.
;
; from_bits_le of at most n bits only pads with constant false and adds
; no constraint.  Extra bits are checked by Boolean::assert_bits_are_zero,
; which is one constraint: the sum of the excess linear combinations is 0.
; For bits, that sum is 0 iff every excess bit is 0, which is exactly
; int-from-bits-le-spec's error case.
;
; from_bits_be reverses the list and calls from_bits_le.  Reversal is not
; a constraint.  The funspecs agree via lebits=>nat of rev = bebits=>nat.

(in-package "ALEOVM")

(include-book "int-support")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/lists/rev" :dir :system)

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-excess-sum-vector ((xs symbol-listp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (if (endp xs)
      nil
    (cons (list 1 (car xs))
          (int-excess-sum-vector (cdr xs)))))

(define int-from-bits-le-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single @('assert_bits_are_zero') constraint, or none."
  (if (endp excess)
      nil
    (list (r1cs::make-r1cs-constraint
           :a (int-excess-sum-vector excess)
           :b (list (list 1 1))
           :c nil))))

(define int-from-bits-be-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraint, applied to the leading bits after reversal."
  (int-from-bits-le-gadget excess))

(defruled int-from-bits-be-gadget-is-le
  (equal (int-from-bits-be-gadget excess)
         (int-from-bits-le-gadget excess))
  :enable (int-from-bits-be-gadget int-from-bits-le-gadget))

(defruled int-from-bits-be-spec-is-le-of-rev
  (equal (int-from-bits-be-spec bits signedp n)
         (int-from-bits-le-spec (rev bits) signedp n))
  :enable (int-from-bits-be-spec
           int-from-bits-le-spec
           acl2::lebits=>nat-of-rev))

(defruled int-from-bits-le-gadget-empty-sound
  (implies (and (bit-listp bits)
                (<= (len bits) n)
                (integer-widthp n)
                (posp n))
           (and (not (equal (int-from-bits-le-spec bits signedp n)
                            (spec-error)))
                (equal (int-from-bits-le-spec bits signedp n)
                       (int-wrap (lebits=>nat bits) signedp n))
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget nil) asg p)))
  :enable (int-from-bits-le-gadget
           int-from-bits-le-spec
           r1cs::r1cs-constraints-holdp))

(defruled int-from-bits-le-gadget-empty-complete
  (implies (and (bit-listp bits)
                (<= (len bits) n)
                (posp n))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget nil) asg p))
  :enable (int-from-bits-le-gadget r1cs::r1cs-constraints-holdp))

; assert_bits_are_zero is one constraint: the unweighted sum of the excess
; bits is 0 in the field.  For a list of bits shorter than the prime, that
; sum is 0 iff every bit is 0.

(define int-bit-sum ((xs true-listp))
  :returns (s natp :rule-classes :type-prescription)
  (if (endp xs)
      0
    (+ (nfix (car xs))
       (int-bit-sum (cdr xs))))
  ///
  (defruled int-bit-sum-of-cons
    (equal (int-bit-sum (cons x xs))
           (+ (nfix x) (int-bit-sum xs)))))

(defruled int-bit-sum-bound
  (implies (bit-listp xs)
           (<= (int-bit-sum xs) (len xs)))
  :rule-classes :linear
  :enable (int-bit-sum bit-listp))

(defthm int-bit-sum-zero-all-zero
  (implies (and (bit-listp xs)
                (equal (int-bit-sum xs) 0))
           (equal xs (repeat (len xs) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable int-bit-sum repeat bit-listp))))

(defruled int-bit-listp-of-nthcdr
  (implies (bit-listp bits)
           (bit-listp (nthcdr n bits)))
  :hints (("Goal" :in-theory (enable bit-listp nthcdr))))

(defruled lebits=>nat-of-repeat-0
  (implies (natp n)
           (equal (lebits=>nat (repeat n 0)) 0))
  :hints (("Goal" :in-theory (enable repeat acl2::lebits=>nat-of-cons))))

(defruled int-bit-sum-of-repeat-0
  (implies (natp n)
           (equal (int-bit-sum (repeat n 0)) 0))
  :hints (("Goal" :in-theory (enable int-bit-sum repeat))))

(define int-excess-field-sum ((vals nat-listp) (p primep))
  :verify-guards nil
  :returns (s natp :rule-classes :type-prescription)
  (if (endp vals)
      0
    (pfield::add (nfix (car vals))
                 (int-excess-field-sum (cdr vals) p)
                 p))
  ///
  (defruled int-excess-field-sum-is-bit-sum
    (implies (and (primep p)
                  (bit-listp vals)
                  (< (len vals) p))
             (equal (int-excess-field-sum vals p)
                    (int-bit-sum vals)))
    :enable (int-excess-field-sum
             int-bit-sum
             int-bit-sum-bound
             pfield::add
             bit-listp)))

(defruledl int-excess-dot-product-is-field-sum
  (implies (and (primep p)
                (symbol-listp xs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::dot-product (int-excess-sum-vector xs) asg p)
                  (int-excess-field-sum (lookup-equal-list xs asg) p)))
  :hints (("Goal"
           :in-theory (enable int-excess-sum-vector
                              int-excess-field-sum
                              lookup-equal-list
                              r1cs::dot-product
                              r1cs::valuation-binds-allp
                              pfield::add
                              pfield::mul))))

(defruled int-excess-bits-sum-forces-all-zero
  :short "A satisfying @('assert_bits_are_zero') sum forces every excess bit to 0."
  (implies (and (primep p)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget excess) asg p))
           (equal (lookup-equal-list excess asg)
                  (repeat (len excess) 0)))
  :enable (int-from-bits-le-gadget
           int-excess-dot-product-is-field-sum
           int-excess-field-sum-is-bit-sum
           int-bit-sum-bound
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add)
  :use (:instance int-bit-sum-zero-all-zero
                  (xs (lookup-equal-list excess asg))))

(defruled int-excess-zero-implies-constraint
  (implies (and (primep p)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (repeat (len excess) 0)))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget excess) asg p))
  :do-not-induct t
  :enable (int-from-bits-le-gadget
           int-excess-dot-product-is-field-sum
           int-excess-field-sum-is-bit-sum
           int-bit-sum-of-repeat-0
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add))

(defruled int-from-bits-le-gadget-iff-all-zero
  (implies (and (primep p)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (< (len excess) p))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-from-bits-le-gadget excess) asg p)
                  (equal (lookup-equal-list excess asg)
                         (repeat (len excess) 0))))
  :do-not-induct t
  :use (int-excess-bits-sum-forces-all-zero
        int-excess-zero-implies-constraint))

(defruledl int-lebits-below-pow2-when-short
  (implies (and (bit-listp bits)
                (natp n)
                (<= (len bits) n))
           (< (lebits=>nat bits) (expt 2 n)))
  :hints (("Goal"
           :use (:instance acl2::lebits=>nat-upper-bound (digits bits))
           :in-theory (disable acl2::lebits=>nat-upper-bound))))

(defruled int-lebits-below-pow2-when-excess-zero
  (implies (and (bit-listp bits)
                (natp n)
                (equal (nthcdr n bits)
                       (repeat (len (nthcdr n bits)) 0)))
           (< (lebits=>nat bits) (expt 2 n)))
  :hints (("Goal"
           :cases ((<= n (len bits)))
           :in-theory (e/d (int-lebits-below-pow2-when-short
                            acl2::lebits=>nat-of-append
                            lebits=>nat-of-repeat-0
                            acl2::append-of-take-and-nthcdr)
                           (acl2::lebits=>nat-upper-bound)))
          ("Subgoal 1"
           :use ((:instance acl2::lebits=>nat-of-append
                            (lodigits (take n bits))
                            (hidigits (nthcdr n bits)))
                 (:instance acl2::lebits=>nat-upper-bound
                            (digits (take n bits)))))))

(local
 (defthm int-product-ge-factor
   (implies (and (integerp k)
                 (<= 1 k)
                 (rationalp e)
                 (< 0 e))
            (<= e (* k e)))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance acl2::<-of-*-and-*-cancel
                            (x1 k)
                            (x2 1)
                            (y e))
            :in-theory (disable acl2::<-of-*-and-*-cancel)
            :do-not-induct t))))

(local
 (defthm int-nat-high-zero-when-sum-below
   (implies (and (natp lo)
                 (natp hi)
                 (posp n)
                 (< lo (expt 2 n))
                 (< (+ lo (* hi (expt 2 n))) (expt 2 n)))
            (equal hi 0))
   :rule-classes nil
   :hints (("Goal"
            :cases ((equal hi 0))
            :do-not-induct t)
           ("Subgoal 1"
            :use (:instance int-product-ge-factor
                            (k hi)
                            (e (expt 2 n)))
            :do-not-induct t)
           ("Subgoal 2"
            :use (:instance int-product-ge-factor
                            (k hi)
                            (e (expt 2 n)))
            :do-not-induct t))))

(defruledl int-nthcdr-when-len-not-greater
  (implies (and (natp n)
                (true-listp xs)
                (<= (len xs) n))
           (equal (nthcdr n xs) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defruled int-excess-zero-when-lebits-below
  (implies (and (bit-listp bits)
                (natp n)
                (< (lebits=>nat bits) (expt 2 n)))
           (equal (nthcdr n bits)
                  (repeat (len (nthcdr n bits)) 0)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((<= (len bits) n))
           :in-theory (e/d (int-nthcdr-when-len-not-greater
                            lebits=>nat-of-repeat-0
                            acl2::repeat-when-zp
                            acl2::bit-list-fix-when-bit-listp)
                           (acl2::lebits=>nat nthcdr repeat)))
          ("Subgoal 2"
           :use ((:instance acl2::append-of-take-and-nthcdr
                            (n n) (x bits))
                 (:instance acl2::lebits=>nat-of-append
                            (lodigits (take n bits))
                            (hidigits (nthcdr n bits)))
                 (:instance acl2::lebits=>nat-upper-bound
                            (digits (take n bits)))
                 (:instance int-nat-high-zero-when-sum-below
                            (lo (lebits=>nat (take n bits)))
                            (hi (lebits=>nat (nthcdr n bits))))
                 (:instance acl2::lebits=>nat-injectivity
                            (digits1 (nthcdr n bits))
                            (digits2 (repeat (len (nthcdr n bits)) 0))))
           :in-theory (e/d (lebits=>nat-of-repeat-0
                            acl2::bit-list-fix-when-bit-listp
                            acl2::bit-listp-of-nthcdr
                            acl2::len-of-take
                            int-bit-listp-of-nthcdr)
                           (acl2::lebits=>nat nthcdr repeat
                            acl2::lebits=>nat-upper-bound
                            acl2::lebits=>nat-of-append
                            acl2::lebits=>nat-injectivity)))))

(local
 (defthm int-len-of-equal-lists
   (implies (equal a b)
            (equal (len a) (len b)))
   :rule-classes nil))

(defruled int-len-nthcdr-is-len-excess
  (implies (equal (lookup-equal-list excess asg)
                  (nthcdr n bits))
           (equal (len (nthcdr n bits))
                  (len excess)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (acl2::len-of-nthcdr)
                           (nthcdr lookup-equal-list
                                   acl2::open-small-nthcdr))
           :use ((:instance len-of-lookup-equal-list
                            (keys excess)
                            (alist asg))
                 (:instance int-len-of-equal-lists
                            (a (lookup-equal-list excess asg))
                            (b (nthcdr n bits)))))))

(defruled int-excess-nthcdr-is-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (natp n)
                (bit-listp bits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg) (nthcdr n bits))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget excess) asg p))
           (equal (nthcdr n bits)
                  (repeat (len (nthcdr n bits)) 0)))
  :do-not-induct t
  :hints (("Goal"
           :use (int-excess-bits-sum-forces-all-zero
                 int-len-nthcdr-is-len-excess)
           :in-theory (e/d (int-bit-listp-of-nthcdr
                            int-len-nthcdr-is-len-excess)
                           (nthcdr lookup-equal-list
                                   acl2::open-small-nthcdr
                                   acl2::len-of-nthcdr
                                   acl2::repeat-of-nfix
                                   int-excess-bits-sum-forces-all-zero)))))

(defruled int-from-bits-le-not-error-implies-below
  (implies (and (bit-listp bits)
                (integer-widthp n)
                (not (equal (int-from-bits-le-spec bits signedp n)
                            (spec-error))))
           (< (lebits=>nat bits) (expt 2 n)))
  :do-not-induct t
  :enable (int-from-bits-le-spec
           not-spec-error-when-integerp
           posp-when-integer-widthp)
  :disable ((:e expt) integer-widthp))

(defruled int-from-bits-le-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (bit-listp bits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg) (nthcdr n bits))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget excess) asg p))
           (and (not (equal (int-from-bits-le-spec bits signedp n)
                            (spec-error)))
                (equal (int-from-bits-le-spec bits signedp n)
                       (int-wrap (lebits=>nat bits) signedp n))))
  :do-not-induct t
  :hints (("Goal"
           :use (int-excess-nthcdr-is-zero
                 int-lebits-below-pow2-when-excess-zero)
           :in-theory (e/d (int-from-bits-le-spec
                            int-wrap
                            not-spec-error-when-integerp
                            posp-when-integer-widthp
                            acl2::mod-when-<)
                           (integer-widthp
                            (:e expt)
                            nthcdr
                            acl2::open-small-nthcdr
                            acl2::len-of-nthcdr
                            acl2::repeat-of-nfix
                            mod floor)))))

(defruled int-from-bits-le-gadget-complete
  (implies (and (primep p)
                (integer-widthp n)
                (bit-listp bits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg) (nthcdr n bits))
                (< (len excess) p)
                (not (equal (int-from-bits-le-spec bits signedp n)
                            (spec-error))))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget excess) asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (int-from-bits-le-not-error-implies-below
                 int-excess-zero-when-lebits-below
                 int-from-bits-le-gadget-iff-all-zero
                 int-len-nthcdr-is-len-excess)
           :in-theory (e/d (int-bit-listp-of-nthcdr
                            int-len-nthcdr-is-len-excess
                            posp-when-integer-widthp)
                           (nthcdr lookup-equal-list
                                   acl2::open-small-nthcdr
                                   acl2::len-of-nthcdr
                                   acl2::repeat-of-nfix
                                   integer-widthp
                                   (:e expt))))))

(defruledl int-bit-listp-of-rev
  (implies (bit-listp xs)
           (bit-listp (rev xs)))
  :hints (("Goal" :in-theory (enable bit-listp rev))))

(defruled int-from-bits-be-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (bit-listp bits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr n (rev bits)))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-be-gadget excess) asg p))
           (and (not (equal (int-from-bits-be-spec bits signedp n)
                            (spec-error)))
                (equal (int-from-bits-be-spec bits signedp n)
                       (int-from-bits-le-spec (rev bits) signedp n))))
  :do-not-induct t
  :use (:instance int-from-bits-le-gadget-sound
                  (bits (rev bits)))
  :enable (int-from-bits-be-gadget-is-le
           int-from-bits-be-spec-is-le-of-rev
           int-bit-listp-of-rev))

(defruled int-from-bits-be-gadget-complete
  (implies (and (primep p)
                (integer-widthp n)
                (bit-listp bits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr n (rev bits)))
                (< (len excess) p)
                (not (equal (int-from-bits-be-spec bits signedp n)
                            (spec-error))))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-be-gadget excess) asg p))
  :do-not-induct t
  :use (:instance int-from-bits-le-gadget-complete
                  (bits (rev bits)))
  :enable (int-from-bits-be-gadget-is-le
           int-from-bits-be-spec-is-le-of-rev
           int-bit-listp-of-rev))

(defconst *int-from-bits-le-sample*
  '((e0 . 0) (e1 . 0)))

(defruled int-from-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-from-bits-le-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-from-bits-le-gadget
                                     int-excess-sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-from-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-from-bits-be-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-from-bits-be-gadget-is-le
           int-from-bits-le-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-from-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_from_bits_le(e0, e1) := {
    (e0 + e1) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-from-bits-le-circuit)
            :pred int-from-bits-le-pred
            :prime prime)

(local
 (defthm int-nthcdr-of-len-append
   (implies (and (true-listp low)
                 (natp n)
                 (equal (len low) n))
            (equal (nthcdr n (append low more))
                   more))
   :hints (("Goal" :in-theory (enable nthcdr append)))))

(defruled int-from-bits-le-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp e0)
                (bitp e1)
                (bit-listp low)
                (equal (len low) 8)
                (integer-widthp 8))
           (equal (int-from-bits-le-pred e0 e1 prime)
                  (not (equal (int-from-bits-le-spec
                               (append low (list e0 e1)) nil 8)
                              (spec-error)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-lebits-below-pow2-when-excess-zero
                            (bits (append low (list e0 e1)))
                            (n 8))
                 (:instance int-excess-zero-when-lebits-below
                            (bits (append low (list e0 e1)))
                            (n 8)))
           :in-theory (e/d (int-from-bits-le-pred
                            int-from-bits-le-spec
                            int-nthcdr-of-len-append
                            not-spec-error-when-integerp
                            pfield::add
                            pfield::mul
                            acl2::mod-when-<
                            bitp)
                           (acl2::lebits=>nat
                            nthcdr
                            acl2::open-small-nthcdr
                            acl2::len-of-nthcdr
                            mod floor)))))

(define int-from-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_from_bits_be(e0, e1) := {
    (e0 + e1) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-from-bits-be-circuit)
            :pred int-from-bits-be-pred
            :prime prime)

(defruled int-from-bits-be-pred-is-le-pred
  (equal (int-from-bits-be-pred e0 e1 prime)
         (int-from-bits-le-pred e0 e1 prime))
  :enable (int-from-bits-be-pred int-from-bits-le-pred))
