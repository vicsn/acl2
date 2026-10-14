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
           r1cs::r1cs-constraints-holdp))

(defruled int-abs-wrapped-unsigned-complete
  (implies (and (not signedp)
                (int-valuep x nil n))
           (r1cs::r1cs-constraints-holdp
            (int-abs-wrapped-unsigned-gadget) asg p))
  :enable (int-abs-wrapped-unsigned-gadget
           r1cs::r1cs-constraints-holdp))

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
  :enable (int-abs-checked-signed-gadget
           int-width-add-fits
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-abs-checked-gadget-soundness)

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
           int-abs-wrapped-spec
           int-wrap
           int-spec-unsigned
           int-width-add-fits
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-abs-wrapped-gadget-soundness)

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
                (equal x (int-abs-checked-spec x nil n))
                (equal x (int-abs-wrapped-spec x nil n))))
  :enable (int-abs-pred
           int-abs-checked-spec
           int-abs-wrapped-spec
           int-wrap
           int-valuep
           int-min
           int-max))
