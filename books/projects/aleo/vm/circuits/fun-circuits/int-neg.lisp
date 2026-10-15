; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Neg::neg.
;
; Unsigned negation halts in the host.  The funspec is spec-error and there
; is no successful witness.  That is a completeness fact: every valid output
; (there are none) is witnessed.
;
; Signed negation is one.add_checked(!self).  Boolean not is a linear
; combination.  The resulting constraints are r1cs/signed-small-neg, which
; is wrapped subtraction from zero plus a check that the operand and the
; result are not both negative (the signed minimum).

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-add")
(include-book "../r1cs/signed-small-neg")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-neg-signed-gadget ((xs symbol-listp)
                               (ys symbol-listp)
                               (carry symbolp)
                               (both-neg symbolp)
                               (one symbolp)
                               (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-neg-gadget xs ys carry both-neg one p))

(defruled int-neg-unsigned-spec-error
  (implies (not signedp)
           (equal (int-neg-spec x signedp n) (spec-error)))
  :enable int-neg-spec)

(defruled int-neg-unsigned-complete
  :short "No valid unsigned output exists, so none fails to be witnessed."
  (implies (and (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (equal (int-neg-spec x nil n) (spec-error)))
  :enable int-neg-spec)

(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(defruledl int-lebits=>int-of-signed-int->lebits
  (implies (and (posp n)
                (int-valuep x t n))
           (equal (lebits=>int (int->lebits x n))
                  (ifix x)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance lebits->int-of-int->lebits (signedp t))
                 (:instance lebits->int-is-lebits=>int
                            (bits (int->lebits x n))))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit)
                           (lebits=>int lebits->int)))))

(defruledl int-lebits=>int-in-signed-range
  (implies (and (bit-listp bits)
                (posp n)
                (equal (len bits) n))
           (and (<= (- (expt 2 (1- n))) (lebits=>int bits))
                (< (lebits=>int bits) (expt 2 (1- n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-valuep-of-lebits->int (signedp t))
                 (:instance lebits->int-is-lebits=>int (bits bits)))
           :in-theory (e/d (int-valuep int-min int-max)
                           (lebits=>int lebits->int
                            int-valuep-of-lebits->int)))))

(defruledl int-neg-spec-is-negation
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep (- (ifix x)) t n))
           (equal (int-neg-spec x t n)
                  (- (ifix x))))
  :enable int-neg-spec)

(defruled int-neg-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbolp carry) (symbolp both-neg) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg both-neg)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-neg-signed-gadget xs ys carry both-neg one p)
                 asg p))
           (equal (lebits=>int (lookup-equal-list ys asg))
                  (int-neg-spec x t n)))
  :do-not-induct t
  :enable (int-neg-signed-gadget
           int-neg-spec-is-negation
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           posp-when-integer-widthp
           int-lebits=>int-of-signed-int->lebits
           int-lebits=>int-in-signed-range
           bit-listp-of-int->lebits-explicit
           len-of-lookup-equal-list
           len-of-int->lebits
           int-valuep
           int-min
           int-max
           acl2::ifix-when-integerp
           acl2::pos-fix-when-posp
           not-spec-error-when-integerp)
  :use ((:instance signed-small-neg-gadget-soundness)
        (:instance int-lebits=>int-in-signed-range
                   (bits (lookup-equal-list ys asg))
                   (n (len ys)))))

(local (in-theory (disable int-neg-spec-is-negation
                           int-lebits=>int-of-signed-int->lebits
                           int-lebits=>int-in-signed-range
                           int-valuep
                           int-min
                           int-max
                           integer-length-of-base-prime
                           int-width-add-fits
                           integer-widthp
                           acl2::ifix-when-integerp
                           acl2::pos-fix-when-posp
                           not-spec-error-when-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed completeness.  Negation is wrapped subtraction from zero, plus
; a check that the operand and the result are not both negative.  The
; product of the sign bits is 0 whenever the funspec is not spec-error
; (the signed minimum is the only failure).  Unsigned negation is a host
; halt: the funspec is spec-error, so there is no circuit witness.

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(deflabel int-neg-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (current-theory 'int-neg-before-mod)))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "../library-extensions/bit-lists"))

(defruledl int-valuep-of-zero-signed
  (implies (posp n)
           (int-valuep 0 t n))
  :enable (int-valuep int-min int-max))

(defruledl bit-listp-of-repeat-0
  (bit-listp (repeat n 0))
  :hints (("Goal" :in-theory (enable bit-listp repeat bitp))))

(defruledl int-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

(defruledl int-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

(defruledl int-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruled int-neg-spec-when-not-error
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error))))
           (equal (int-neg-spec x t n)
                  (- (ifix x))))
  :enable int-neg-spec)

(defruledl int-integerp-when-int-valuep
  (implies (int-valuep x signedp n)
           (integerp x))
  :rule-classes :forward-chaining
  :enable int-valuep)

(local (in-theory (disable int-valuep)))

(defruledl int-neg-value-in-range
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error))))
           (int-valuep (- x) t n))
  :enable (int-neg-spec
           int-integerp-when-int-valuep
           acl2::ifix-when-integerp))

(defruledl int-neg-result-msb
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error))))
           (equal (car (last (int->lebits (- x) n)))
                  (if (< (- x) 0) 1 0)))
  :do-not-induct t
  :enable (int-neg-value-in-range
           int-integerp-when-int-valuep
           acl2::ifix-when-integerp)
  :hints (("Goal"
           :use (:instance int-signed-msb
                           (x (- x))
                           (n n))
           :in-theory (disable int-valuep int-min int-max int-neg-spec))))

(defruled int-neg-sign-and-is-zero
  :short "The operand and its negation are not both negative when
          negation stays in range.  That is the bit the circuit forces to 0."
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error))))
           (equal (bitand (car (last (int->lebits x n)))
                          (car (last (int->lebits (- (ifix x)) n))))
                  0))
  :do-not-induct t
  :enable (int-neg-result-msb
           int-integerp-when-int-valuep
           bitand
           acl2::ifix-when-integerp)
  :hints (("Goal"
           :use ((:instance int-signed-msb (x x) (n n))
                 (:instance int-neg-result-msb))
           :cases ((< x 0)))))

(defruledl int-zero-sub-nat-equation
  (implies (and (posp n)
                (int-valuep x t n))
           (equal (+ (* (int-sub-carry 0 x n) (expt 2 n))
                     (lebits=>nat (int->lebits (- x) n)))
                  (+ (expt 2 n)
                     (- (lebits=>nat (int->lebits x n))))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-sub-carry-on-lebits
                           (x 0) (y x) (n n))
           :in-theory (enable lebits=>nat-of-int->lebits
                              int-valuep-of-zero-signed
                              int-valuep
                              acl2::ifix-when-integerp
                              acl2::mod-of-0-arg1))))

(defruledl lebits=>nat-of-bits-and-carry
  (implies (and (bit-listp bits)
                (bitp c))
           (equal (lebits=>nat (append bits (list c)))
                  (+ (lebits=>nat bits)
                     (* c (expt 2 (len bits))))))
  :enable (acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           int-lebits=>nat-of-nil
           acl2::bfix-when-bitp))

(defruledl int-zero-minus-var-constraints-hold
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp zs)
                (symbolp carry)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (- (ifix x)) n))
                (equal (lookup-equal carry asg) (int-sub-carry 0 x n)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-const-var-gadget
             (repeat n 0) xs (append zs (list carry)) one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-zero-sub-nat-equation (n n) (x x))))
  :enable (unsigned-small-sub-const-var-gadget-correct
           bit-listp-of-repeat-0
           int-valuep
           int-valuep-of-zero-signed
           int-zero-sub-nat-equation
           lebits=>nat-of-bits-and-carry
           int-valuation-binds-allp-of-nil
           int-lookup-equal-list-of-nil
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           acl2::lebits=>nat-of-all-zero-constant
           symbol-listp-of-append-of-symbol
           bit-listp-of-append-of-bit
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           len-of-append-of-singleton
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruledl int-neg-sign-and-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp both-neg)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg both-neg)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal both-neg asg)
                       (bitand (car (last (lookup-equal-list xs asg)))
                               (car (last (lookup-equal-list ys asg))))))
           (r1cs::r1cs-constraints-holdp
            (boolean-and-gadget (car (last xs))
                                (car (last ys))
                                both-neg)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-and-gadget-to-bitand
                   (x (car (last xs)))
                   (y (car (last ys)))
                   (z both-neg))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars ys)
                   (var (car (last ys))))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance member-equal-of-car-of-last (xs xs))
        (:instance member-equal-of-car-of-last (xs ys)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :disable bitp)

(defruled int-neg-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp carry)
                (symbolp both-neg)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg both-neg)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg)
                       (int->lebits (int-neg-spec x t n) n))
                (equal (lookup-equal carry asg) (int-sub-carry 0 x n))
                (equal (lookup-equal both-neg asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-neg-signed-gadget xs ys carry both-neg one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-zero-minus-var-constraints-hold
                            (zs ys))
                 (:instance int-neg-sign-and-holds)
                 (:instance int-neg-sign-and-is-zero))))
  :enable (int-neg-signed-gadget
           signed-small-neg-gadget
           signed-small-sub-wrapped-const-var-gadget
           unsigned-small-sub-wrapped-const-var-gadget
           int-zero-minus-var-constraints-hold
           int-neg-sign-and-holds
           int-neg-sign-and-is-zero
           int-neg-spec-when-not-error
           acl2::ifix-when-integerp
           zero-gadget-to-equal-0
           lookup-equal-of-car
           lookup-equal-list-of-last
           member-equal-of-car-of-last
           symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           integer-widthp
           posp-when-integer-widthp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

; -1 at width 2.  Bits of 1 are (1 0); bits of -1 are (1 1).
; The library gadget is a wrapped subtraction from zero, so this sample
; only records a satisfying boolean-and of the sign bits being zero
; together with a zero constraint.  The full subtraction sample is the
; sub-wrapped gadget; here both-neg = 0 and the sign of the result is 1
; while the sign of the input 1 is 0, so their and is 0.

(defconst *int-neg-sample*
  '((sx . 0) (sy . 1) (both . 0)))

(defruled int-neg-sample-holds
  (r1cs::r1cs-constraints-holdp
   (append (boolean-and-gadget 'sx 'sy 'both)
           (zero-gadget 'both))
   *int-neg-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     boolean-and-gadget
                                     zero-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-neg-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The both-negative check.  The subtraction is int_sub_checked."
  (pfcs::parse-def
   "int_neg_sign(sx, sy, both) := {
    (sx) * (sy) == (both),
    (both) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-neg-circuit) :pred int-neg-pred :prime prime)

(defruled int-neg-pred-to-funspec
  :short "Both sign bits are clear of the product, and the product is 0.
          This is the signed-minimum check, not the whole negation."
  (implies (and (equal prime (base-prime))
                (bitp sx)
                (bitp sy)
                (pfield::fep both prime))
           (equal (int-neg-pred sx sy both prime)
                  (and (equal both 0)
                       (equal (bitand sx sy) 0))))
  :enable (int-neg-pred bitand))
