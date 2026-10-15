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

; Signed negation as a PFCS.  Wrapped subtraction from zero, then the
; check that the operand and the result are not both negative.  Unsigned
; negation is a host halt (spec-error) and is not this circuit.

(local (in-theory (enable acl2::mod-when-<
                           acl2::mod-when-<-of-0
                           acl2::mod-of-+-of-constant
                           acl2::mod-of-minus-arg1
                           acl2::mod-when-equal-of-mod-and-0-free-cheap
                           acl2::mod-when-integerp-of-quotient
                           acl2::mod-of-0-arg1
                           acl2::equal-of-mod-of-+-cancel
                           acl2::equal-of-mod-same-arg1
                           acl2::<-of-mod-same-arg2
                           acl2::<-of-mod-and-0
                           acl2::ifix-when-integerp
                           acl2::ifix-of--
                           acl2::ifix-of-ifix
                           acl2::ifix-of-+-when-integerp-arg1
                           acl2::pos-fix-when-posp
                           acl2::expt-when-not-integerp-arg1-cheap
                           acl2::<-of-0-and-expt
                           acl2::<-of-expt-and-0
                           acl2::<-of-expt-and-expt-same-base
                           acl2::integerp-of-expt-when-natp
                           acl2::fold-consts-in-+)))


(define int-neg-signed-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Signed negation: wrapped subtraction from zero, then the
          both-negative check.  Unsigned negation is a host halt and
          is not this circuit."
  (pfcs::parse-def
   "int_neg_signed(xu, zu, carry, n2, sx, sy, both) := {
    (carry) * (n2) == (n2 - xu - zu),
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

(pfcs::lift (int-neg-signed-circuit)
            :pred int-neg-signed-pred
            :prime prime)

(defruledl int-neg-mod-when-inside
  (implies (and (integerp a)
                (integerp p)
                (< 0 p)
                (< (- p) a)
                (< a p))
           (equal (mod a p)
                  (if (< a 0) (+ a p) a)))
  :hints (("Goal"
           :cases ((< a 0))
           :in-theory (e/d (acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defruledl int-neg-sub-mod-iff
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp xu) (< xu (expt 2 n))
                (natp zu) (< zu (expt 2 n))
                (bitp carry)
                (equal n2 (expt 2 n)))
           (equal (equal (mod (* carry n2) prime)
                         (mod (+ n2 (- xu) (- zu)) prime))
                  (equal (+ n2 (- xu))
                         (+ zu (* carry n2)))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)
                   (equal carry 0)
                   (< (+ n2 (- xu) (- zu)) 0))
           :in-theory (e/d (int-neg-mod-when-inside
                            bitp
                            integer-widthp
                            base-prime
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defruledl int-neg-sign-pred-iff
  (implies (and (equal prime (base-prime))
                (bitp sx)
                (bitp sy)
                (bitp both))
           (equal (and (equal (pfield::mul sx sy prime) both)
                       (equal (pfield::mul both (mod 1 prime) prime)
                              (mod 0 prime)))
                  (and (equal both 0)
                       (equal (* sx sy) 0))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal sx 0) (equal sy 0) (equal both 0))
           :in-theory (e/d (pfield::mul
                            bitp
                            base-prime
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            acl2::ifix-when-integerp
                            acl2::pos-fix-when-posp
                            acl2::mod-when-<)
                           (mod floor)))))

(defruledl int-neg-signed-pred-is-constraints
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp xu) (< xu (expt 2 n))
                (natp zu) (< zu (expt 2 n))
                (bitp carry)
                (bitp sx) (bitp sy) (bitp both)
                (equal n2 (expt 2 n)))
           (equal (int-neg-signed-pred xu zu carry n2 sx sy both prime)
                  (and (equal (+ n2 (- xu))
                              (+ zu (* carry n2)))
                       (equal both 0)
                       (equal (* sx sy) 0))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-neg-sub-mod-iff)
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (int-neg-signed-pred
                            int-neg-sign-pred-iff
                            pfield::add
                            pfield::mul
                            pfield::neg
                            pfield::sub
                            bitp
                            integer-widthp
                            base-prime
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            acl2::ifix-when-integerp
                            acl2::pos-fix-when-posp
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0
                            acl2::mod-of-+-same-arg1
                            acl2::mod-of-+-same-arg2)
                           (mod floor
                            int-neg-sub-mod-iff
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants
                            (:elim acl2::floor-mod-elim-rule))))))

(defruledl int-neg-nfix-of-width
  (implies (integer-widthp n)
           (equal (nfix n) n))
  :enable integer-widthp)

(defruledl int-neg-spec-unsigned-is-mod
  (implies (integer-widthp n)
           (equal (int-spec-unsigned x n)
                  (mod (ifix x) (expt 2 n))))
  :enable (int-spec-unsigned int-neg-nfix-of-width))

(defruledl int-neg-msb-of-small-nat
  (implies (and (posp n)
                (natp z)
                (< z (expt 2 n)))
           (equal (car (last (int->lebits z n)))
                  (if (< z (expt 2 (1- n))) 0 1)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-signed-msb
                            (x (int-wrap z t n)))
                 (:instance int->lebits-of-int-wrap
                            (x z)
                            (signedp t)))
           :in-theory (e/d (int-wrap
                            int-valuep
                            int-min
                            int-max
                            acl2::mod-when-<
                            acl2::ifix-when-integerp
                            len-of-int->lebits)
                           (int-signed-msb
                            int->lebits)))))

(local
 (defthm int-neg-split-unique
   (implies (and (natp zu)
                 (natp z0)
                 (bitp c)
                 (bitp c0)
                 (posp m)
                 (< zu m)
                 (< z0 m)
                 (equal (+ zu (* c m))
                        (+ z0 (* c0 m))))
            (and (equal zu z0)
                 (equal c c0)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable bitp)
            :cases ((equal c 0) (equal c 1)
                    (equal c0 0) (equal c0 1))))))

(defruledl int-neg-zero-sub-equation
  (implies (and (integer-widthp n)
                (int-valuep x t n))
           (equal (+ (expt 2 n)
                     (- (int-spec-unsigned x n)))
                  (+ (mod (- (ifix x)) (expt 2 n))
                     (* (int-sub-carry 0 x n)
                        (expt 2 n)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-sub-carry-equation (x 0) (y x))
           :in-theory (e/d (int-neg-spec-unsigned-is-mod
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            acl2::mod-when-<)
                           (int-spec-unsigned
                            int-sub-carry
                            mod floor)))))

(defruledl int-neg-bitand-is-product
  (implies (and (bitp a) (bitp b))
           (equal (bitand a b) (* a b)))
  :hints (("Goal"
           :cases ((equal a 0) (equal b 0))
           :in-theory (enable bitand bitp))))

(defruledl int-neg-mod-in-range
  (implies (and (integerp a)
                (posp m))
           (and (natp (mod a m))
                (< (mod a m) m)))
  :hints (("Goal"
           :in-theory (e/d (natp
                            acl2::<-of-mod-same-arg2)
                           (mod floor)))))

(defruledl int-neg-spec-unsigned-below
  (implies (integer-widthp n)
           (< (int-spec-unsigned x n) (expt 2 n)))
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (int-spec-unsigned
                            integer-widthp
                            acl2::ifix-when-integerp
                            acl2::<-of-mod-same-arg2)
                           (mod floor)))))

(defruledl int-neg-equation-iff-canonical
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (natp zu)
                (< zu (expt 2 n))
                (bitp carry))
           (equal (equal (+ (expt 2 n)
                            (- (int-spec-unsigned x n)))
                         (+ zu (* carry (expt 2 n))))
                  (and (equal zu (mod (- (ifix x)) (expt 2 n)))
                       (equal carry (int-sub-carry 0 x n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-neg-zero-sub-equation)
                 (:instance int-neg-split-unique
                            (m (expt 2 n))
                            (z0 (mod (- (ifix x)) (expt 2 n)))
                            (c0 (int-sub-carry 0 x n))
                            (c carry))
                 (:instance int-neg-mod-in-range
                            (a (- (ifix x)))
                            (m (expt 2 n))))
           :in-theory (e/d (integer-widthp
                            posp-when-integer-widthp
                            bitp
                            (:t int-sub-carry)
                            (:t expt))
                           (int-spec-unsigned
                            int-sub-carry
                            mod floor)))))
(defruledl int-neg-unsigned-of-spec
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error))))
           (equal (int-spec-unsigned (int-neg-spec x t n) n)
                  (mod (- (ifix x)) (expt 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :use int-neg-spec-when-not-error
           :in-theory (e/d (int-neg-spec-unsigned-is-mod
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            acl2::ifix-of--)
                           (int-neg-spec
                            int-spec-unsigned
                            int-neg-spec-when-not-error
                            mod floor)))))

(defruledl int-neg-spec-error-iff-min
  (implies (and (integer-widthp n)
                (int-valuep x t n))
           (iff (equal (int-neg-spec x t n) (spec-error))
                (equal x (- (expt 2 (1- n))))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)
                   (equal x (- (expt 2 (1- n)))))
           :in-theory (e/d (int-neg-spec
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            not-spec-error-when-integerp
                            acl2::ifix-when-integerp
                            acl2::pos-fix-when-posp)
                           (mod floor)))))

(defruledl int-neg-min-residues
  (implies (and (integer-widthp n)
                (equal x (- (expt 2 (1- n)))))
           (and (equal (mod (ifix x) (expt 2 n))
                       (expt 2 (1- n)))
                (equal (mod (- (ifix x)) (expt 2 n))
                       (expt 2 (1- n)))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (integer-widthp
                            acl2::ifix-when-integerp
                            acl2::ifix-of--
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (mod floor)))))

(defruledl int-neg-lebits-same-mod
  (implies (and (integer-widthp n)
                (equal (mod (ifix a) (expt 2 n))
                       (mod (ifix b) (expt 2 n))))
           (equal (int->lebits a n)
                  (int->lebits b n)))
  :enable (int->lebits int-neg-nfix-of-width))

(defruledl int-neg-bitp-of-sign-bit
  (implies (integer-widthp n)
           (bitp (car (last (int->lebits x n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance bitp-of-car-of-last-when-bit-listp
                            (bits (int->lebits x n)))
                 (:instance len-of-int->lebits))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            integer-widthp
                            posp-when-integer-widthp
                            len)
                           (int->lebits
                            bitp
                            bitp-of-car-of-last-when-bit-listp
                            len-of-int->lebits)))))

(defruledl int-neg-min-product-is-one
  (implies (and (integer-widthp n)
                (equal x (- (expt 2 (1- n))))
                (equal sx (car (last (int->lebits x n))))
                (equal zu (mod (- (ifix x)) (expt 2 n)))
                (equal sy (car (last (int->lebits zu n)))))
           (equal (* sx sy) 1))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-neg-min-residues)
                 (:instance int-neg-msb-of-small-nat
                            (z (expt 2 (1- n))))
                 (:instance int-neg-lebits-same-mod
                            (a x)
                            (b (expt 2 (1- n))))
                 (:instance int-neg-lebits-same-mod
                            (a zu)
                            (b (expt 2 (1- n)))))
           :in-theory (e/d (integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp)
                           (int->lebits
                            int-neg-msb-of-small-nat
                            int-neg-min-residues
                            int-neg-lebits-same-mod
                            mod floor)))))

(defruledl int-neg-lebits-of-residue
  (implies (and (integer-widthp n)
                (natp zu)
                (< zu (expt 2 n))
                (equal zu (mod (- (ifix x)) (expt 2 n))))
           (equal (int->lebits zu n)
                  (int->lebits (- (ifix x)) n)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int->lebits
                            int-neg-nfix-of-width
                            integer-widthp
                            acl2::mod-when-<
                            acl2::ifix-when-integerp
                            acl2::ifix-of--)
                           (mod floor)))))

(defruledl int-neg-sign-product-zero-when-ok
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (not (equal (int-neg-spec x t n) (spec-error)))
                (equal sx (car (last (int->lebits x n))))
                (natp zu)
                (< zu (expt 2 n))
                (equal zu (mod (- (ifix x)) (expt 2 n)))
                (equal sy (car (last (int->lebits zu n)))))
           (equal (* sx sy) 0))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-neg-sign-and-is-zero)
                 (:instance int-neg-lebits-of-residue)
                 (:instance int-neg-bitp-of-sign-bit (x x))
                 (:instance int-neg-bitp-of-sign-bit
                            (x (- (ifix x))))
                 (:instance int-neg-bitand-is-product
                            (a (car (last (int->lebits x n))))
                            (b (car (last (int->lebits
                                           (- (ifix x)) n))))))
           :in-theory (e/d (posp-when-integer-widthp)
                           (int-neg-spec
                            int->lebits
                            bitp
                            mod floor
                            acl2::mod-of-minus-arg1
                            (:elim acl2::floor-mod-elim-rule)
                            int-neg-sign-and-is-zero
                            int-neg-lebits-of-residue
                            int-neg-bitp-of-sign-bit
                            int-neg-bitand-is-product)))))

(defruledl int-neg-error-unsat
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (equal (int-neg-spec x t n) (spec-error))
                (equal xu (int-spec-unsigned x n))
                (equal sx (car (last (int->lebits x n))))
                (natp zu)
                (< zu (expt 2 n))
                (bitp carry)
                (equal sy (car (last (int->lebits zu n))))
                (equal n2 (expt 2 n)))
           (not (and (equal (+ n2 (- xu))
                            (+ zu (* carry n2)))
                     (equal (* sx sy) 0))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-neg-equation-iff-canonical)
                 (:instance int-neg-min-product-is-one))
           :in-theory (e/d (int-neg-spec-error-iff-min)
                           (int-neg-spec
                            int->lebits
                            int-spec-unsigned
                            int-sub-carry
                            bitp
                            ifix
                            mod floor
                            (:e spec-error)
                            acl2::mod-of-minus-arg1
                            (:elim acl2::floor-mod-elim-rule)
                            int-neg-equation-iff-canonical
                            int-neg-min-product-is-one)))))

(defruledl int-neg-constraints-iff-spec
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (equal xu (int-spec-unsigned x n))
                (equal sx (car (last (int->lebits x n))))
                (natp zu)
                (< zu (expt 2 n))
                (bitp carry)
                (bitp sy)
                (bitp both)
                (equal sy (car (last (int->lebits zu n))))
                (equal n2 (expt 2 n)))
           (equal (and (equal (+ n2 (- xu))
                              (+ zu (* carry n2)))
                       (equal both 0)
                       (equal (* sx sy) 0))
                  (and (not (equal (int-neg-spec x t n) (spec-error)))
                       (equal zu
                              (int-spec-unsigned
                               (int-neg-spec x t n)
                               n))
                       (equal carry (int-sub-carry 0 x n))
                       (equal both 0))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal (int-neg-spec x t n) (spec-error)))
           :use ((:instance int-neg-error-unsat)
                 (:instance int-neg-equation-iff-canonical)
                 (:instance int-neg-unsigned-of-spec)
                 (:instance int-neg-sign-product-zero-when-ok))
           :in-theory (e/d (int-neg-spec-error-iff-min)
                          (int-neg-spec
                           int->lebits
                           int-spec-unsigned
                           int-sub-carry
                           bitp
                           ifix
                           mod floor
                           (:e spec-error)
                           acl2::mod-of-minus-arg1
                           (:elim acl2::floor-mod-elim-rule)
                           int-neg-error-unsat
                           int-neg-equation-iff-canonical
                           int-neg-unsigned-of-spec
                           int-neg-sign-product-zero-when-ok)))))

(defruled int-neg-signed-pred-to-funspec
  :short "Signed negation's wrapped subtraction from zero, together
          with the both-negative check, is int-neg-spec for every
          integer width, including 128.  Unsigned negation is not
          this circuit."
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x t n)
                (equal xu (int-spec-unsigned x n))
                (equal sx (car (last (int->lebits x n))))
                (natp zu)
                (< zu (expt 2 n))
                (bitp carry)
                (bitp sy)
                (bitp both)
                (equal sy (car (last (int->lebits zu n))))
                (equal n2 (expt 2 n)))
           (equal (int-neg-signed-pred xu zu carry n2 sx sy both prime)
                  (and (not (equal (int-neg-spec x t n) (spec-error)))
                       (equal zu
                              (int-spec-unsigned
                               (int-neg-spec x t n)
                               n))
                       (equal carry (int-sub-carry 0 x n))
                       (equal both 0))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-neg-signed-pred-is-constraints)
                 (:instance int-neg-constraints-iff-spec)
                 (:instance int-neg-bitp-of-sign-bit (x x))
                 (:instance int-neg-bitp-of-sign-bit (x zu)))
           :in-theory (e/d (int-neg-spec-unsigned-below)
                           (int-neg-signed-pred
                            int-neg-signed-pred-is-constraints
                            int-neg-constraints-iff-spec
                            int-neg-bitp-of-sign-bit
                            bitp
                            int-neg-spec
                            int-spec-unsigned
                            int-sub-carry
                            int->lebits
                            mod floor)))))
