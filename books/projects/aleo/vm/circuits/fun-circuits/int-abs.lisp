; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; AbsChecked and AbsWrapped.
;
; Unsigned absolute value is the identity: no constraints, and the funspec
; is the input (it is in range).
;
; Signed abs_checked is ternary(msb, zero.sub_checked(self), self).
; Signed abs_wrapped is ternary(msb, zero.sub_wrapped(self), self).
; Those are r1cs/signed-small-abs-checked and signed-small-abs-wrapped.
; The signed minimum fails abs_checked and wraps to itself under abs_wrapped,
; matching the funspecs.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/signed-small-abs-checked")
(include-book "../r1cs/signed-small-abs-wrapped")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(deflabel int-abs-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (current-theory 'int-abs-before-mod)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-abs-checked-unsigned-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(define int-abs-wrapped-unsigned-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(define int-abs-checked-signed-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (minus-xs symbol-listp)
                                       (carry symbolp)
                                       (diff-sign symbolp)
                                       (overflow symbolp)
                                       (one symbolp)
                                       (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len minus-xs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-abs-checked-gadget xs ys minus-xs carry
                                   diff-sign overflow one p))

(define int-abs-wrapped-signed-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (minus-xs symbol-listp)
                                       (carry symbolp)
                                       (one symbolp)
                                       (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len minus-xs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-abs-wrapped-gadget xs ys minus-xs carry one p))

(defruled int-abs-checked-unsigned-sound
  (implies (and (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (and (equal (int-abs-checked-spec x nil n) x)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-checked-unsigned-gadget) asg p)))
  :enable (int-abs-checked-spec
           int-abs-checked-unsigned-gadget
           int-valuep
           int-min
           int-max
           r1cs::r1cs-constraints-holdp))

(defruled int-abs-checked-unsigned-complete
  (implies (and (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (r1cs::r1cs-constraints-holdp
            (int-abs-checked-unsigned-gadget) asg p))
  :enable (int-abs-checked-unsigned-gadget
           r1cs::r1cs-constraints-holdp))

(defruled int-abs-wrapped-unsigned-sound
  (implies (and (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (and (equal (int-abs-wrapped-spec x nil n) x)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-unsigned-gadget) asg p)))
  :enable (int-abs-wrapped-spec
           int-abs-wrapped-unsigned-gadget
           int-wrap
           int-valuep
           int-min
           int-max
           posp-when-integer-widthp
           acl2::mod-when-<
           acl2::pos-fix-when-posp
           r1cs::r1cs-constraints-holdp))

(local (in-theory (disable acl2::mod-when-<)))

(defruled int-abs-wrapped-unsigned-complete
  (implies (and (not signedp)
                (int-valuep x nil n))
           (r1cs::r1cs-constraints-holdp
            (int-abs-wrapped-unsigned-gadget) asg p))
  :enable (int-abs-wrapped-unsigned-gadget
           r1cs::r1cs-constraints-holdp))

(deflabel int-abs-before-signed-sound)
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (in-theory (current-theory 'int-abs-before-signed-sound)))

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

(defruledl int-abs-checked-spec-when-nonneg
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (<= 0 (ifix x)))
           (equal (int-abs-checked-spec x t n)
                  (ifix x)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (enable int-abs-checked-spec
                              abs
                              int-valuep
                              int-min
                              int-max
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              acl2::ifix-when-integerp))))

(defruledl int-abs-checked-spec-when-neg
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (< (ifix x) 0)
                (int-valuep (- (ifix x)) t n))
           (equal (int-abs-checked-spec x t n)
                  (- (ifix x))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (enable int-abs-checked-spec
                              abs
                              int-valuep
                              int-min
                              int-max
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              acl2::ifix-when-integerp))))

(defruled int-abs-checked-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry) (symbolp diff-sign)
                (symbolp overflow) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len minus-xs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg diff-sign)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-abs-checked-signed-gadget
                  xs ys minus-xs carry diff-sign overflow one p)
                 asg p))
           (equal (lebits=>int (lookup-equal-list ys asg))
                  (int-abs-checked-spec x t n)))
  :do-not-induct t
  :enable (int-abs-checked-signed-gadget
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           posp-when-integer-widthp
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-lookup-equal-list
           len-of-int->lebits
           int-lebits=>int-of-signed-int->lebits
           int-lebits=>int-in-signed-range
           int-abs-checked-spec-when-nonneg
           int-abs-checked-spec-when-neg
           int-valuep
           int-min
           int-max
           acl2::pos-fix-when-posp
           acl2::ifix-when-integerp
           not-spec-error-when-integerp)
  :use ((:instance signed-small-abs-checked-gadget-soundness
                   (over/under-flow overflow))
        (:instance int-lebits=>int-in-signed-range
                   (bits (lookup-equal-list ys asg))
                   (n (len ys)))))

(local (in-theory (disable int-abs-checked-spec-when-nonneg
                           int-abs-checked-spec-when-neg
                           int-lebits=>int-of-signed-int->lebits
                           int-lebits=>int-in-signed-range
                           acl2::ifix-when-integerp)))

(defruledl int-spec-unsigned-of-abs-wrapped
  (implies (and (integer-widthp n)
                (int-valuep x t n))
           (equal (int-spec-unsigned (int-abs-wrapped-spec x t n) n)
                  (abs (ifix x))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (enable int-abs-wrapped-spec
                              int-wrap
                              int-spec-unsigned
                              abs
                              int-valuep
                              int-min
                              int-max
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              acl2::ifix-when-integerp
                              acl2::mod-when-<
                              acl2::mod-when-<-of-0
                              acl2::mod-of-mod-same-arg2)
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)))))

(defruled int-abs-wrapped-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len minus-xs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget
                  xs ys minus-xs carry one p)
                 asg p))
           (equal (mod (lebits=>int (lookup-equal-list ys asg))
                       (expt 2 n))
                  (int-spec-unsigned (int-abs-wrapped-spec x t n) n)))
  :enable (int-abs-wrapped-signed-gadget
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           bit-listp-of-int->lebits-explicit
           int-lebits=>int-of-signed-int->lebits
           int-spec-unsigned-of-abs-wrapped
           acl2::ifix-when-integerp)
  :do-not-induct t
  :use signed-small-abs-wrapped-gadget-soundness)

(local (in-theory (disable int-spec-unsigned-of-abs-wrapped
                           int-lebits=>int-of-signed-int->lebits
                           acl2::ifix-when-integerp
                           abs
                           acl2::mod-when-<
                           acl2::mod-when-<-of-0
                           acl2::mod-of-mod-same-arg2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness witnesses.
;
; Checked absolute value subtracts the operand from the constant 0 and
; selects that negation when the sign bit is set.  The subtraction's
; overflow bit is the and of the operand sign with the negation of the
; xor of the two signs.  That bit is 0 whenever abs_checked is not
; spec-error, including at width 128.
;
; Wrapped absolute value is the same subtraction without the overflow
; check.  The signed minimum wraps to itself, and the same carry still
; witnesses 0 - x.

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
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

(defruled int-abs-checked-spec-when-not-error
  (implies (and (int-valuep x t n)
                (not (equal (int-abs-checked-spec x t n) (spec-error))))
           (equal (int-abs-checked-spec x t n)
                  (abs (ifix x))))
  :enable (int-abs-checked-spec abs))

(defruledl int-abs-checked-neg-in-range
  (implies (and (posp n)
                (int-valuep x t n)
                (< x 0)
                (not (equal (int-abs-checked-spec x t n) (spec-error))))
           (int-valuep (- (ifix x)) t n))
  :enable (int-abs-checked-spec abs int-valuep))

(defruled int-abs-checked-overflow-is-zero
  :short "The checked-abs overflow bit is 0 whenever @('|x|') is in range."
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-abs-checked-spec x t n) (spec-error))))
           (equal (if (and (equal (car (last (int->lebits x n))) 1)
                           (equal (bitxor (car (last (int->lebits
                                                      (- (ifix x)) n)))
                                          (car (last (int->lebits x n))))
                                  0))
                      1
                    0)
                  0))
  :do-not-induct t
  :enable (int-signed-msb
           bitxor
           int-abs-checked-neg-in-range
           int-abs-checked-spec
           abs
           int-valuep
           int-min
           int-max
           acl2::ifix-when-integerp)
  :hints (("Goal" :cases ((< (ifix x) 0)))))

(defruled int-abs-checked-result-bits
  :short "Bits of a successful checked absolute value are the operand
          when it is nonnegative and the bits of its negation otherwise."
  (implies (and (posp n)
                (int-valuep x t n)
                (not (equal (int-abs-checked-spec x t n) (spec-error))))
           (equal (int->lebits (int-abs-checked-spec x t n) n)
                  (if (equal (car (last (int->lebits x n))) 1)
                      (int->lebits (- (ifix x)) n)
                    (int->lebits x n))))
  :do-not-induct t
  :enable (int-abs-checked-spec-when-not-error
           int-signed-msb
           abs
           int-valuep
           acl2::ifix-when-integerp)
  :hints (("Goal" :cases ((< x 0)))))

(defruled int-abs-wrapped-result-bits
  :short "Bits of a wrapped absolute value, including the signed minimum."
  (implies (and (posp n)
                (int-valuep x t n))
           (equal (int->lebits (int-abs-wrapped-spec x t n) n)
                  (if (equal (car (last (int->lebits x n))) 1)
                      (int->lebits (- (ifix x)) n)
                    (int->lebits x n))))
  :do-not-induct t
  :enable (int-abs-wrapped-spec
           int->lebits-of-int-wrap
           int-signed-msb
           abs
           int-valuep
           acl2::ifix-when-integerp)
  :hints (("Goal" :cases ((< x 0)))))

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

(defruledl int-msb-xor-constraint-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal z asg)
                       (bitxor (car (last (lookup-equal-list xs asg)))
                               (car (last (lookup-equal-list ys asg))))))
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last xs))
                                (car (last ys))
                                z
                                p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs)))
                   (y (car (last ys))))
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

(defruledl int-abs-and-notright-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (consp xs)
                (symbolp diff-sign)
                (symbolp overflow)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg diff-sign)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list xs asg))
                (bitp (lookup-equal diff-sign asg))
                (equal (lookup-equal overflow asg)
                       (if (and (equal (car (last (lookup-equal-list xs asg)))
                                       1)
                                (equal (lookup-equal diff-sign asg) 0))
                           1
                         0)))
           (r1cs::r1cs-constraints-holdp
            (boolean-and-notright-gadget (car (last xs))
                                         diff-sign
                                         overflow
                                         one
                                         p)
            asg p))
  :do-not-induct t
  :enable (boolean-and-notright-gadget-to-booland-boolnot
           symbolp-of-car-of-last
           member-equal-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :use ((:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance member-equal-of-car-of-last (xs xs)))
  :disable bitp)

(defruledl int-abs-ternary-holds
  (implies (and (primep p)
                (symbol-listp minus-xs)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (equal (len minus-xs) (len xs))
                (equal (len ys) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list ys asg)
                       (if (equal (car (last (lookup-equal-list xs asg))) 1)
                           (lookup-equal-list minus-xs asg)
                         (lookup-equal-list xs asg))))
           (r1cs::r1cs-constraints-holdp
            (integer-ternary-gadget (car (last xs)) minus-xs xs ys p)
            asg p))
  :do-not-induct t
  :enable (integer-ternary-gadget-correctness
           symbolp-of-car-of-last
           member-equal-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :use ((:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance member-equal-of-car-of-last (xs xs)))
  :disable bitp)

(defruled int-abs-checked-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry)
                (symbolp diff-sign)
                (symbolp overflow)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len minus-xs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg diff-sign)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (not (equal (int-abs-checked-spec x t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg)
                       (int->lebits (int-abs-checked-spec x t n) n))
                (equal (lookup-equal-list minus-xs asg)
                       (int->lebits (- (ifix x)) n))
                (equal (lookup-equal carry asg) (int-sub-carry 0 x n))
                (equal (lookup-equal diff-sign asg)
                       (bitxor (car (last (int->lebits (- (ifix x)) n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-abs-checked-signed-gadget
             xs ys minus-xs carry diff-sign overflow one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-zero-minus-var-constraints-hold
                            (zs minus-xs))
                 (:instance int-msb-xor-constraint-holds
                            (xs minus-xs)
                            (ys xs)
                            (z diff-sign))
                 (:instance int-abs-and-notright-holds)
                 (:instance int-abs-ternary-holds)
                 (:instance int-abs-checked-overflow-is-zero))))
  :enable (int-abs-checked-signed-gadget
           signed-small-abs-checked-gadget
           signed-small-sub-checked-const-var-gadget
           unsigned-small-sub-wrapped-const-var-gadget
           int-zero-minus-var-constraints-hold
           int-msb-xor-constraint-holds
           int-abs-and-notright-holds
           int-abs-ternary-holds
           int-abs-checked-overflow-is-zero
           int-abs-checked-result-bits
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

(defruled int-abs-wrapped-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len minus-xs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg)
                       (int->lebits (int-abs-wrapped-spec x t n) n))
                (equal (lookup-equal-list minus-xs asg)
                       (int->lebits (- (ifix x)) n))
                (equal (lookup-equal carry asg) (int-sub-carry 0 x n)))
           (r1cs::r1cs-constraints-holdp
            (int-abs-wrapped-signed-gadget
             xs ys minus-xs carry one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-zero-minus-var-constraints-hold
                           (zs minus-xs))))
  :enable (int-abs-wrapped-signed-gadget
           signed-small-abs-wrapped-gadget
           signed-small-sub-wrapped-const-var-gadget
           unsigned-small-sub-wrapped-const-var-gadget
           int-zero-minus-var-constraints-hold
           int-abs-ternary-holds
           int-abs-wrapped-result-bits
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

(defconst *int-abs-sample* nil)

(defruled int-abs-checked-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-abs-checked-unsigned-gadget)
   *int-abs-sample*
   (base-prime))
  :enable (int-abs-checked-unsigned-gadget
           r1cs::r1cs-constraints-holdp))

(defruled int-abs-wrapped-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-abs-wrapped-unsigned-gadget)
   *int-abs-sample*
   (base-prime))
  :enable (int-abs-wrapped-unsigned-gadget
           r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-abs-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned absolute value adds nothing."
  (pfcs::parse-def
   "int_abs(x) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-abs-circuit) :pred int-abs-pred :prime prime)

(defruled int-abs-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (and (int-abs-pred x prime)
                (equal (int-abs-checked-spec x nil n) x)
                (equal (int-abs-wrapped-spec x nil n) x)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (enable int-abs-pred
                              int-abs-checked-spec
                              int-abs-wrapped-spec
                              int-wrap
                              int-valuep
                              int-min
                              int-max
                              abs
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              acl2::ifix-when-integerp
                              acl2::mod-when-<)
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)))))
