; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier-byte validation (circuit/types/string identifier_literal/mod.rs).
;
; Boolean not is the linear combination 1 - x.
; and / or / xor are the usual single constraints.
; validate_byte is assert_eq(b7, 0), the shared ByteValidationData gates,
; and the four category enforces (products equal to 0).  The first byte
; also asserts the letter bit.
; validate_trailing_nulls is the chain
;   (flag[i-1]) * (1 - flag[i]) = 0.
; validate_identifier_bytes is validate_byte on each byte (the first one
; flagged) followed by that chain.  snarkVM passes the 31 bytes of the
; literal; the gadget is the same loop for any byte count.

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "environment-r1cs")
(include-book "../fun-specs/values-string")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-xor")
(include-book "../library-extensions/lookup-equal-list")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled values-b-and-is-bitand
  (implies (and (bitp a) (bitp b))
           (equal (values-b-and a b) (bitand a b)))
  :enable (values-b-and bitand))

(defruled values-b-or-is-bitor
  (implies (and (bitp a) (bitp b))
           (equal (values-b-or a b) (bitor a b)))
  :enable (values-b-or bitor))

(defruled values-b-xor-is-bitxor
  (implies (and (bitp a) (bitp b))
           (equal (values-b-xor a b) (bitxor a b)))
  :enable (values-b-xor bitxor))

(defruled values-b-not-is-sub
  (implies (and (bitp a) (equal p (base-prime)))
           (equal (values-b-not a) (pfield::sub 1 a p)))
  :enable (values-b-not))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_invalid_digit_offset = b3 & (b2 | b1)

(define is-invalid-digit-offset-gadget ((b1 symbolp) (b2 symbolp) (b3 symbolp)
                                        (w symbolp) (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-or-gadget b2 b1 w p)
          (boolean-and-gadget b3 w out)))

(defruled is-invalid-digit-offset-gadget-sound
  (implies (and (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp w) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-digit-offset-gadget b1 b2 b3 w out p) asg p))
           (equal (lookup-equal out asg)
                  (is-invalid-digit-offset (lookup-equal b1 asg)
                                           (lookup-equal b2 asg)
                                           (lookup-equal b3 asg))))
  :enable (is-invalid-digit-offset-gadget
           is-invalid-digit-offset
           boolean-or-gadget-to-bitor
           boolean-and-gadget-to-bitand
           values-b-or-is-bitor
           values-b-and-is-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defruled is-invalid-digit-offset-gadget-complete
  (implies (and (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp w) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (equal (lookup-equal w asg)
                       (bitor (lookup-equal b2 asg) (lookup-equal b1 asg)))
                (equal (lookup-equal out asg)
                       (bitand (lookup-equal b3 asg) (lookup-equal w asg))))
           (r1cs::r1cs-constraints-holdp
            (is-invalid-digit-offset-gadget b1 b2 b3 w out p) asg p))
  :enable (is-invalid-digit-offset-gadget
           boolean-or-gadget-to-bitor
           boolean-and-gadget-to-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defconst *is-invalid-digit-offset-sample*
  '((b1 . 0) (b2 . 1) (b3 . 1) (w . 1) (out . 1)))

(defruled is-invalid-digit-offset-sample-holds
  (r1cs::r1cs-constraints-holdp
   (is-invalid-digit-offset-gadget 'b1 'b2 'b3 'w 'out (base-prime))
   *is-invalid-digit-offset-sample*
   (base-prime))
  :enable (is-invalid-digit-offset-gadget
           boolean-or-gadget
           boolean-and-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define is-invalid-digit-offset-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "is_invalid_digit_offset(b1, b2, b3, w, out) := {
    (1 - b2) * (1 - b1) == (1 - w),
    (b3) * (w) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (is-invalid-digit-offset-circuit)
            :pred is-invalid-digit-offset-pred
            :prime prime)

(defruled is-invalid-digit-offset-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b1) (bitp b2) (bitp b3) (bitp w) (bitp out)
                (equal w (values-b-or b2 b1))
                (is-invalid-digit-offset-pred b1 b2 b3 w out prime))
           (equal out (is-invalid-digit-offset b1 b2 b3)))
  :enable (is-invalid-digit-offset-pred
           is-invalid-digit-offset
           values-b-and
           values-b-or))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_invalid_uppercase_offset = b4b3 & (b2 xor b1b0)

(define is-invalid-uppercase-offset-gadget ((b4b3 symbolp) (b1b0 symbolp)
                                            (b2 symbolp)
                                            (x symbolp) (out symbolp)
                                            (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-xor-gadget b2 b1b0 x p)
          (boolean-and-gadget b4b3 x out)))

(defruled is-invalid-uppercase-offset-gadget-sound
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2)
                (symbolp x) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b4b3 asg))
                (bitp (lookup-equal b1b0 asg))
                (bitp (lookup-equal b2 asg))
                (byte-validation-datap data)
                (equal (byte-validation-data->b4b3 data) (lookup-equal b4b3 asg))
                (equal (byte-validation-data->b1b0 data) (lookup-equal b1b0 asg))
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-uppercase-offset-gadget b4b3 b1b0 b2 x out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (is-invalid-uppercase-offset data (lookup-equal b2 asg))))
  :enable (is-invalid-uppercase-offset-gadget
           is-invalid-uppercase-offset
           boolean-xor-gadget-to-bitxor
           boolean-and-gadget-to-bitand
           values-b-xor-is-bitxor
           values-b-and-is-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defruled is-invalid-uppercase-offset-gadget-complete
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2)
                (symbolp x) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b4b3 asg))
                (bitp (lookup-equal b1b0 asg))
                (bitp (lookup-equal b2 asg))
                (equal (lookup-equal x asg)
                       (bitxor (lookup-equal b2 asg) (lookup-equal b1b0 asg)))
                (equal (lookup-equal out asg)
                       (bitand (lookup-equal b4b3 asg) (lookup-equal x asg))))
           (r1cs::r1cs-constraints-holdp
            (is-invalid-uppercase-offset-gadget b4b3 b1b0 b2 x out p) asg p))
  :enable (is-invalid-uppercase-offset-gadget
           boolean-xor-gadget-to-bitxor
           boolean-and-gadget-to-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defconst *is-invalid-uppercase-offset-sample*
  '((b4b3 . 1) (b1b0 . 1) (b2 . 0) (x . 1) (out . 1)))

(defruled is-invalid-uppercase-offset-sample-holds
  (r1cs::r1cs-constraints-holdp
   (is-invalid-uppercase-offset-gadget 'b4b3 'b1b0 'b2 'x 'out (base-prime))
   *is-invalid-uppercase-offset-sample*
   (base-prime))
  :enable (is-invalid-uppercase-offset-gadget
           boolean-xor-gadget
           boolean-and-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define is-invalid-uppercase-offset-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "is_invalid_uppercase_offset(b4b3, b1b0, b2, x, out) := {
    (2 * b2) * (b1b0) == (b2 + b1b0 - x),
    (b4b3) * (x) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (is-invalid-uppercase-offset-circuit)
            :pred is-invalid-uppercase-offset-pred
            :prime prime)

(defruled is-invalid-uppercase-offset-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b4b3) (bitp b1b0) (bitp b2) (bitp x) (bitp out)
                (equal x (values-b-xor b2 b1b0))
                (byte-validation-datap data)
                (equal (byte-validation-data->b4b3 data) b4b3)
                (equal (byte-validation-data->b1b0 data) b1b0)
                (is-invalid-uppercase-offset-pred b4b3 b1b0 b2 x out prime))
           (equal out (is-invalid-uppercase-offset data b2)))
  :enable (is-invalid-uppercase-offset-pred
           is-invalid-uppercase-offset
           values-b-and
           values-b-xor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_invalid_lowercase_offset = b4b3 & (b2 | b1b0)

(define is-invalid-lowercase-offset-gadget ((b4b3 symbolp) (b1b0 symbolp)
                                            (b2 symbolp)
                                            (w symbolp) (out symbolp)
                                            (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-or-gadget b2 b1b0 w p)
          (boolean-and-gadget b4b3 w out)))

(defruled is-invalid-lowercase-offset-gadget-sound
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2)
                (symbolp w) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b4b3 asg))
                (bitp (lookup-equal b1b0 asg))
                (bitp (lookup-equal b2 asg))
                (byte-validation-datap data)
                (equal (byte-validation-data->b4b3 data) (lookup-equal b4b3 asg))
                (equal (byte-validation-data->b1b0 data) (lookup-equal b1b0 asg))
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-lowercase-offset-gadget b4b3 b1b0 b2 w out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (is-invalid-lowercase-offset data (lookup-equal b2 asg))))
  :enable (is-invalid-lowercase-offset-gadget
           is-invalid-lowercase-offset
           boolean-or-gadget-to-bitor
           boolean-and-gadget-to-bitand
           values-b-or-is-bitor
           values-b-and-is-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defruled is-invalid-lowercase-offset-gadget-complete
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2)
                (symbolp w) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal b4b3 asg))
                (bitp (lookup-equal b1b0 asg))
                (bitp (lookup-equal b2 asg))
                (equal (lookup-equal w asg)
                       (bitor (lookup-equal b2 asg) (lookup-equal b1b0 asg)))
                (equal (lookup-equal out asg)
                       (bitand (lookup-equal b4b3 asg) (lookup-equal w asg))))
           (r1cs::r1cs-constraints-holdp
            (is-invalid-lowercase-offset-gadget b4b3 b1b0 b2 w out p) asg p))
  :enable (is-invalid-lowercase-offset-gadget
           boolean-or-gadget-to-bitor
           boolean-and-gadget-to-bitand
           r1cs::r1cs-constraints-holdp-of-append))

(defconst *is-invalid-lowercase-offset-sample*
  '((b4b3 . 1) (b1b0 . 0) (b2 . 1) (w . 1) (out . 1)))

(defruled is-invalid-lowercase-offset-sample-holds
  (r1cs::r1cs-constraints-holdp
   (is-invalid-lowercase-offset-gadget 'b4b3 'b1b0 'b2 'w 'out (base-prime))
   *is-invalid-lowercase-offset-sample*
   (base-prime))
  :enable (is-invalid-lowercase-offset-gadget
           boolean-or-gadget
           boolean-and-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define is-invalid-lowercase-offset-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "is_invalid_lowercase_offset(b4b3, b1b0, b2, w, out) := {
    (1 - b2) * (1 - b1b0) == (1 - w),
    (b4b3) * (w) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (is-invalid-lowercase-offset-circuit)
            :pred is-invalid-lowercase-offset-pred
            :prime prime)

(defruled is-invalid-lowercase-offset-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b4b3) (bitp b1b0) (bitp b2) (bitp w) (bitp out)
                (equal w (values-b-or b2 b1b0))
                (byte-validation-datap data)
                (equal (byte-validation-data->b4b3 data) b4b3)
                (equal (byte-validation-data->b1b0 data) b1b0)
                (is-invalid-lowercase-offset-pred b4b3 b1b0 b2 w out prime))
           (equal out (is-invalid-lowercase-offset data b2)))
  :enable (is-invalid-lowercase-offset-pred
           is-invalid-lowercase-offset
           values-b-and
           values-b-or))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ByteValidationData::new
;   b4b3 = b4 & b3
;   b1b0 = b1 & b0
;   sum  = b0+b1+b2+b3+b4          (linear combination)
;   all_zero_5 = is_equal(sum, 0) = 1 - r

(define byte-validation-data-new-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp)
                                         (b3 symbolp) (b4 symbolp)
                                         (b4b3 symbolp) (b1b0 symbolp)
                                         (m symbolp) (r symbolp)
                                         (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-and-gadget b4 b3 b4b3)
          (boolean-and-gadget b1 b0 b1b0)
          (list (r1cs::make-r1cs-constraint
                 :a (val-sum-lc (list b0 b1 b2 b3 b4))
                 :b (list (list 1 m))
                 :c (list (list 1 r)))
                (r1cs::make-r1cs-constraint
                 :a (val-sum-lc (list b0 b1 b2 b3 b4))
                 :b (val-not-lc r p)
                 :c nil))))

(defruled byte-validation-data-new-gadget-to-spec
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3) (symbolp b4)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((b0$ (lookup-equal b0 asg))
                (b1$ (lookup-equal b1 asg))
                (b2$ (lookup-equal b2 asg))
                (b3$ (lookup-equal b3 asg))
                (b4$ (lookup-equal b4 asg))
                (sum (+ b0$ b1$ b2$ b3$ b4$)))
             (equal (r1cs::r1cs-constraints-holdp
                     (byte-validation-data-new-gadget
                      b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
                     asg p)
                    (and (equal (lookup-equal b4b3 asg)
                                (pfield::mul b4$ b3$ p))
                         (equal (lookup-equal b1b0 asg)
                                (pfield::mul b1$ b0$ p))
                         (equal (pfield::mul sum (lookup-equal m asg) p)
                                (lookup-equal r asg))
                         (equal (pfield::mul sum
                                             (pfield::sub 1 (lookup-equal r asg) p)
                                             p)
                                0)))))
  :enable (byte-validation-data-new-gadget
           boolean-and-gadget
           val-sum-lc
           val-not-lc
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled byte-validation-data-new-gadget-sound
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3) (symbolp b4)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (bitp (lookup-equal b4 asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (byte-validation-data-new-gadget
                  b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
                 asg p))
           (equal (make-byte-validation-data
                   :b4b3 (lookup-equal b4b3 asg)
                   :b1b0 (lookup-equal b1b0 asg)
                   :all-zero-5 (pfield::sub 1 (lookup-equal r asg) p))
                  (byte-validation-data-new (lookup-equal b0 asg)
                                           (lookup-equal b1 asg)
                                           (lookup-equal b2 asg)
                                           (lookup-equal b3 asg)
                                           (lookup-equal b4 asg))))
  :enable (byte-validation-data-new-gadget-to-spec
           byte-validation-data-new
           values-b-and
           values-bool-to-bit
           bitand
           values-b-and-is-bitand
           field-is-zero-funspec))

(defruled byte-validation-data-new-gadget-complete
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3) (symbolp b4)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (bitp (lookup-equal b4 asg))
                (equal (lookup-equal b4b3 asg)
                       (values-b-and (lookup-equal b4 asg) (lookup-equal b3 asg)))
                (equal (lookup-equal b1b0 asg)
                       (values-b-and (lookup-equal b1 asg) (lookup-equal b0 asg)))
                (equal (lookup-equal r asg)
                       (if (equal (+ (lookup-equal b0 asg)
                                     (lookup-equal b1 asg)
                                     (lookup-equal b2 asg)
                                     (lookup-equal b3 asg)
                                     (lookup-equal b4 asg))
                                  0)
                           0
                         1))
                (equal (lookup-equal m asg)
                       (if (equal (+ (lookup-equal b0 asg)
                                     (lookup-equal b1 asg)
                                     (lookup-equal b2 asg)
                                     (lookup-equal b3 asg)
                                     (lookup-equal b4 asg))
                                  0)
                           0
                         (pfield::inv (+ (lookup-equal b0 asg)
                                         (lookup-equal b1 asg)
                                         (lookup-equal b2 asg)
                                         (lookup-equal b3 asg)
                                         (lookup-equal b4 asg))
                                      p))))
           (r1cs::r1cs-constraints-holdp
            (byte-validation-data-new-gadget
             b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
            asg p))
  :enable (byte-validation-data-new-gadget-to-spec
           values-b-and
           bitand))

(defconst *byte-validation-data-new-sample*
  ;; 'A' low 5 bits are 00001, so b0=1 and the rest 0.  sum=1, r=1, m=1.
  '((b0 . 1) (b1 . 0) (b2 . 0) (b3 . 0) (b4 . 0)
    (b4b3 . 0) (b1b0 . 0) (m . 1) (r . 1)))

(defruled byte-validation-data-new-sample-holds
  (r1cs::r1cs-constraints-holdp
   (byte-validation-data-new-gadget
    'b0 'b1 'b2 'b3 'b4 'b4b3 'b1b0 'm 'r (base-prime))
   *byte-validation-data-new-sample*
   (base-prime))
  :enable (byte-validation-data-new-gadget
           boolean-and-gadget
           val-sum-lc
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define byte-validation-data-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "byte_validation_data_new(b0, b1, b2, b3, b4, b4b3, b1b0, m, r) := {
    (b4) * (b3) == (b4b3),
    (b1) * (b0) == (b1b0),
    (b0 + b1 + b2 + b3 + b4) * (m) == (r),
    (b0 + b1 + b2 + b3 + b4) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (byte-validation-data-new-circuit)
            :pred byte-validation-data-new-pred
            :prime prime)

(defruled byte-validation-data-new-pred-to-gadget
  (implies (and (equal prime (base-prime))
                (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (bitp b4b3) (bitp b1b0) (bitp r)
                (pfield::fep m prime))
           (equal (byte-validation-data-new-pred
                   b0 b1 b2 b3 b4 b4b3 b1b0 m r prime)
                  (and (equal b4b3 (values-b-and b4 b3))
                       (equal b1b0 (values-b-and b1 b0))
                       (equal (pfield::mul (+ b0 b1 b2 b3 b4) m prime) r)
                       (equal (pfield::mul (+ b0 b1 b2 b3 b4)
                                           (pfield::sub 1 r prime)
                                           prime)
                              0))))
  :enable (byte-validation-data-new-pred values-b-and))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1 - x) * (1 - y) = z.  AND of two negations, each a linear combination.

(define val-and-nots-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (val-not-lc x p)
         :b (val-not-lc y p)
         :c (list (list 1 z)))))

(defruled val-and-nots-gadget-to-spec
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (val-and-nots-gadget x y z p) asg p)
                  (equal (pfield::mul (pfield::sub 1 (lookup-equal x asg) p)
                                      (pfield::sub 1 (lookup-equal y asg) p)
                                      p)
                         (lookup-equal z asg))))
  :enable (val-and-nots-gadget
           val-not-lc
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

; b6 * (1 - u) = z

(define val-and-not-right-gadget ((x symbolp) (u symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (val-not-lc u p)
         :c (list (list 1 z)))))

; (a - b) * (1 - c + d) = 0

(define val-diff-times-sum-gadget ((a symbolp) (b symbolp)
                                   (c symbolp) (d symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a)
                  (list (1- p) b))
         :b (list (list 1 1)
                  (list (1- p) c)
                  (list 1 d))
         :c nil)))

; x * (1 - r + d) = 0

(define val-times-sum-gadget ((x symbolp) (r symbolp) (d symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1)
                  (list (1- p) r)
                  (list 1 d))
         :c nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; validate_byte, not the first byte.
; null is the returned flag.  any_low5 is r, because all_zero_5 is 1 - r
; and not of that linear combination is r.

(define validate-byte-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp) (b3 symbolp)
                              (b4 symbolp) (b5 symbolp) (b6 symbolp) (b7 symbolp)
                              (b4b3 symbolp) (b1b0 symbolp)
                              (m symbolp) (r symbolp)
                              (lower symbolp) (null symbolp)
                              (or-d symbolp) (inv-d symbolp)
                              (xor-u symbolp) (bad-u symbolp)
                              (or-l symbolp) (bad-l symbolp)
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('validate_byte') when the byte is not first."
  (append (assert-zero-gadget b7)
          (byte-validation-data-new-gadget b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
          (val-and-nots-gadget b6 b5 null p)
          (boolean-and-gadget b6 b5 lower)
          (is-invalid-digit-offset-gadget b1 b2 b3 or-d inv-d p)
          (is-invalid-uppercase-offset-gadget b4b3 b1b0 b2 xor-u bad-u p)
          (is-invalid-lowercase-offset-gadget b4b3 b1b0 b2 or-l bad-l p)
          ;; null * any_low5 = 0, and any_low5 is r.
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 null))
                 :b (list (list 1 r))
                 :c nil))
          ;; digit_lc * ((1 - b4) + invalid_digit) = 0
          (val-diff-times-sum-gadget b5 lower b4 inv-d p)
          ;; upper_lc * (all_zero_5 + bad_upper) = 0, all_zero_5 = 1 - r
          (val-diff-times-sum-gadget b6 lower r bad-u p)
          ;; lower * (all_zero_5 + bad_lower) = 0
          (val-times-sum-gadget lower r bad-l p)))

(defruled validate-byte-gadget-to-pieces
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (symbolp lower) (symbolp null)
                (symbolp or-d) (symbolp inv-d)
                (symbolp xor-u) (symbolp bad-u)
                (symbolp or-l) (symbolp bad-l)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b7)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg null)
                (r1cs::valuation-bindsp asg or-d)
                (r1cs::valuation-bindsp asg inv-d)
                (r1cs::valuation-bindsp asg xor-u)
                (r1cs::valuation-bindsp asg bad-u)
                (r1cs::valuation-bindsp asg or-l)
                (r1cs::valuation-bindsp asg bad-l))
           (equal (r1cs::r1cs-constraints-holdp
                   (validate-byte-gadget b0 b1 b2 b3 b4 b5 b6 b7
                                        b4b3 b1b0 m r lower null
                                        or-d inv-d xor-u bad-u or-l bad-l p)
                   asg p)
                  (and (equal (lookup-equal b7 asg) 0)
                       (r1cs::r1cs-constraints-holdp
                        (byte-validation-data-new-gadget
                         b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
                        asg p)
                       (equal (pfield::mul (pfield::sub 1 (lookup-equal b6 asg) p)
                                           (pfield::sub 1 (lookup-equal b5 asg) p)
                                           p)
                              (lookup-equal null asg))
                       (equal (lookup-equal lower asg)
                              (pfield::mul (lookup-equal b6 asg)
                                           (lookup-equal b5 asg)
                                           p))
                       (r1cs::r1cs-constraints-holdp
                        (is-invalid-digit-offset-gadget b1 b2 b3 or-d inv-d p)
                        asg p)
                       (r1cs::r1cs-constraints-holdp
                        (is-invalid-uppercase-offset-gadget
                         b4b3 b1b0 b2 xor-u bad-u p)
                        asg p)
                       (r1cs::r1cs-constraints-holdp
                        (is-invalid-lowercase-offset-gadget
                         b4b3 b1b0 b2 or-l bad-l p)
                        asg p)
                       (equal (pfield::mul (lookup-equal null asg)
                                           (lookup-equal r asg)
                                           p)
                              0)
                       (equal (pfield::mul
                               (pfield::sub (lookup-equal b5 asg)
                                            (lookup-equal lower asg)
                                            p)
                               (pfield::add
                                (pfield::sub 1 (lookup-equal b4 asg) p)
                                (lookup-equal inv-d asg)
                                p)
                               p)
                              0)
                       (equal (pfield::mul
                               (pfield::sub (lookup-equal b6 asg)
                                            (lookup-equal lower asg)
                                            p)
                               (pfield::add
                                (pfield::sub 1 (lookup-equal r asg) p)
                                (lookup-equal bad-u asg)
                                p)
                               p)
                              0)
                       (equal (pfield::mul
                               (lookup-equal lower asg)
                               (pfield::add
                                (pfield::sub 1 (lookup-equal r asg) p)
                                (lookup-equal bad-l asg)
                                p)
                               p)
                              0))))
  :enable (validate-byte-gadget
           assert-zero-gadget-to-eq
           val-and-nots-gadget-to-spec
           boolean-and-gadget
           val-diff-times-sum-gadget
           val-times-sum-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled validate-byte-gadget-sound
  :short "R1CS-SOUND for a non-first byte: the null witness is validate-byte."
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (symbolp lower) (symbolp null)
                (symbolp or-d) (symbolp inv-d)
                (symbolp xor-u) (symbolp bad-u)
                (symbolp or-l) (symbolp bad-l)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b7)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg null)
                (r1cs::valuation-bindsp asg or-d)
                (r1cs::valuation-bindsp asg inv-d)
                (r1cs::valuation-bindsp asg xor-u)
                (r1cs::valuation-bindsp asg bad-u)
                (r1cs::valuation-bindsp asg or-l)
                (r1cs::valuation-bindsp asg bad-l)
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (bitp (lookup-equal b4 asg))
                (bitp (lookup-equal b5 asg))
                (bitp (lookup-equal b6 asg))
                (bitp (lookup-equal b7 asg))
                (bitp (lookup-equal r asg))
                (bitp (lookup-equal null asg))
                (r1cs::r1cs-constraints-holdp
                 (validate-byte-gadget b0 b1 b2 b3 b4 b5 b6 b7
                                      b4b3 b1b0 m r lower null
                                      or-d inv-d xor-u bad-u or-l bad-l p)
                 asg p))
           (equal (lookup-equal null asg)
                  (validate-byte (list (lookup-equal b0 asg)
                                       (lookup-equal b1 asg)
                                       (lookup-equal b2 asg)
                                       (lookup-equal b3 asg)
                                       (lookup-equal b4 asg)
                                       (lookup-equal b5 asg)
                                       (lookup-equal b6 asg)
                                       (lookup-equal b7 asg))
                                 nil)))
  :enable (validate-byte-gadget-to-pieces
           validate-byte
           byte-validation-data-new
           is-invalid-digit-offset
           is-invalid-uppercase-offset
           is-invalid-lowercase-offset
           values-b-and
           values-b-or
           values-b-xor
           values-b-not
           values-bool-to-bit))

(defruled validate-byte-gadget-complete
  :short "R1CS-COMPLETE: the canonical gate witnesses satisfy validate_byte."
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (symbolp lower) (symbolp null)
                (symbolp or-d) (symbolp inv-d)
                (symbolp xor-u) (symbolp bad-u)
                (symbolp or-l) (symbolp bad-l)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b7)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg null)
                (r1cs::valuation-bindsp asg or-d)
                (r1cs::valuation-bindsp asg inv-d)
                (r1cs::valuation-bindsp asg xor-u)
                (r1cs::valuation-bindsp asg bad-u)
                (r1cs::valuation-bindsp asg or-l)
                (r1cs::valuation-bindsp asg bad-l)
                (equal (lookup-equal b7 asg) 0)
                (r1cs::r1cs-constraints-holdp
                 (byte-validation-data-new-gadget
                  b0 b1 b2 b3 b4 b4b3 b1b0 m r p)
                 asg p)
                (equal (lookup-equal null asg)
                       (pfield::mul (pfield::sub 1 (lookup-equal b6 asg) p)
                                    (pfield::sub 1 (lookup-equal b5 asg) p)
                                    p))
                (equal (lookup-equal lower asg)
                       (pfield::mul (lookup-equal b6 asg)
                                    (lookup-equal b5 asg)
                                    p))
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-digit-offset-gadget b1 b2 b3 or-d inv-d p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-uppercase-offset-gadget
                  b4b3 b1b0 b2 xor-u bad-u p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (is-invalid-lowercase-offset-gadget
                  b4b3 b1b0 b2 or-l bad-l p)
                 asg p)
                (equal (pfield::mul (lookup-equal null asg)
                                    (lookup-equal r asg)
                                    p)
                       0)
                (equal (pfield::mul
                        (pfield::sub (lookup-equal b5 asg)
                                     (lookup-equal lower asg)
                                     p)
                        (pfield::add (pfield::sub 1 (lookup-equal b4 asg) p)
                                     (lookup-equal inv-d asg)
                                     p)
                        p)
                       0)
                (equal (pfield::mul
                        (pfield::sub (lookup-equal b6 asg)
                                     (lookup-equal lower asg)
                                     p)
                        (pfield::add (pfield::sub 1 (lookup-equal r asg) p)
                                     (lookup-equal bad-u asg)
                                     p)
                        p)
                       0)
                (equal (pfield::mul (lookup-equal lower asg)
                                    (pfield::add
                                     (pfield::sub 1 (lookup-equal r asg) p)
                                     (lookup-equal bad-l asg)
                                     p)
                                    p)
                       0))
           (r1cs::r1cs-constraints-holdp
            (validate-byte-gadget b0 b1 b2 b3 b4 b5 b6 b7
                                 b4b3 b1b0 m r lower null
                                 or-d inv-d xor-u bad-u or-l bad-l p)
            asg p))
  :enable validate-byte-gadget-to-pieces)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; First byte: the non-first constraints, plus
;   partial = b4b3 & b1b0
;   underscore = partial & b2
;   letter = b6 & !underscore
;   assert letter.

(define validate-first-byte-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp)
                                    (b3 symbolp) (b4 symbolp) (b5 symbolp)
                                    (b6 symbolp) (b7 symbolp)
                                    (b4b3 symbolp) (b1b0 symbolp)
                                    (m symbolp) (r symbolp)
                                    (lower symbolp) (null symbolp)
                                    (or-d symbolp) (inv-d symbolp)
                                    (xor-u symbolp) (bad-u symbolp)
                                    (or-l symbolp) (bad-l symbolp)
                                    (partial symbolp) (uscore symbolp)
                                    (letter symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (validate-byte-gadget b0 b1 b2 b3 b4 b5 b6 b7
                               b4b3 b1b0 m r lower null
                               or-d inv-d xor-u bad-u or-l bad-l p)
          (boolean-and-gadget b4b3 b1b0 partial)
          (boolean-and-gadget partial b2 uscore)
          (val-and-not-right-gadget b6 uscore letter p)
          (assert-gadget letter)))

(defruled validate-first-byte-gadget-sound
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (symbolp lower) (symbolp null)
                (symbolp or-d) (symbolp inv-d)
                (symbolp xor-u) (symbolp bad-u)
                (symbolp or-l) (symbolp bad-l)
                (symbolp partial) (symbolp uscore) (symbolp letter)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b7)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg null)
                (r1cs::valuation-bindsp asg or-d)
                (r1cs::valuation-bindsp asg inv-d)
                (r1cs::valuation-bindsp asg xor-u)
                (r1cs::valuation-bindsp asg bad-u)
                (r1cs::valuation-bindsp asg or-l)
                (r1cs::valuation-bindsp asg bad-l)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg letter)
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal b3 asg))
                (bitp (lookup-equal b4 asg))
                (bitp (lookup-equal b5 asg))
                (bitp (lookup-equal b6 asg))
                (bitp (lookup-equal b7 asg))
                (bitp (lookup-equal r asg))
                (bitp (lookup-equal null asg))
                (bitp (lookup-equal letter asg))
                (r1cs::r1cs-constraints-holdp
                 (validate-first-byte-gadget
                  b0 b1 b2 b3 b4 b5 b6 b7 b4b3 b1b0 m r lower null
                  or-d inv-d xor-u bad-u or-l bad-l partial uscore letter p)
                 asg p))
           (equal (lookup-equal null asg)
                  (validate-byte (list (lookup-equal b0 asg)
                                       (lookup-equal b1 asg)
                                       (lookup-equal b2 asg)
                                       (lookup-equal b3 asg)
                                       (lookup-equal b4 asg)
                                       (lookup-equal b5 asg)
                                       (lookup-equal b6 asg)
                                       (lookup-equal b7 asg))
                                 t)))
  :enable (validate-first-byte-gadget
           validate-byte-gadget-sound
           assert-gadget-to-funspec
           boolean-and-gadget-to-bitand
           val-and-not-right-gadget
           validate-byte
           values-b-and
           values-b-not))

(defruled validate-first-byte-gadget-complete
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp b4b3) (symbolp b1b0) (symbolp m) (symbolp r)
                (symbolp lower) (symbolp null)
                (symbolp or-d) (symbolp inv-d)
                (symbolp xor-u) (symbolp bad-u)
                (symbolp or-l) (symbolp bad-l)
                (symbolp partial) (symbolp uscore) (symbolp letter)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg letter)
                (r1cs::r1cs-constraints-holdp
                 (validate-byte-gadget b0 b1 b2 b3 b4 b5 b6 b7
                                      b4b3 b1b0 m r lower null
                                      or-d inv-d xor-u bad-u or-l bad-l p)
                 asg p)
                (equal (lookup-equal partial asg)
                       (pfield::mul (lookup-equal b4b3 asg)
                                    (lookup-equal b1b0 asg)
                                    p))
                (equal (lookup-equal uscore asg)
                       (pfield::mul (lookup-equal partial asg)
                                    (lookup-equal b2 asg)
                                    p))
                (equal (lookup-equal letter asg)
                       (pfield::mul (lookup-equal b6 asg)
                                    (pfield::sub 1 (lookup-equal uscore asg) p)
                                    p))
                (equal (lookup-equal letter asg) 1))
           (r1cs::r1cs-constraints-holdp
            (validate-first-byte-gadget
             b0 b1 b2 b3 b4 b5 b6 b7 b4b3 b1b0 m r lower null
             or-d inv-d xor-u bad-u or-l bad-l partial uscore letter p)
            asg p))
  :enable (validate-first-byte-gadget
           boolean-and-gadget
           val-and-not-right-gadget
           val-not-lc
           assert-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

; ASCII 'A' = 0x41.  Little-endian bits 1,0,0,0,0,0,1,0.
; null = 0, lower = 0, sum = 1 so r = 1 and m = 1, letter = 1.

(defconst *validate-byte-sample*
  '((b0 . 1) (b1 . 0) (b2 . 0) (b3 . 0) (b4 . 0) (b5 . 0) (b6 . 1) (b7 . 0)
    (b4b3 . 0) (b1b0 . 0) (m . 1) (r . 1)
    (lower . 0) (null . 0)
    (or-d . 0) (inv-d . 0)
    (xor-u . 0) (bad-u . 0)
    (or-l . 0) (bad-l . 0)
    (partial . 0) (uscore . 0) (letter . 1)))

(defruled validate-byte-sample-holds
  (r1cs::r1cs-constraints-holdp
   (validate-first-byte-gadget
    'b0 'b1 'b2 'b3 'b4 'b5 'b6 'b7
    'b4b3 'b1b0 'm 'r 'lower 'null
    'or-d 'inv-d 'xor-u 'bad-u 'or-l 'bad-l
    'partial 'uscore 'letter
    (base-prime))
   *validate-byte-sample*
   (base-prime))
  :enable (validate-first-byte-gadget
           validate-byte-gadget
           assert-zero-gadget
           byte-validation-data-new-gadget
           boolean-and-gadget
           boolean-or-gadget
           boolean-xor-gadget
           is-invalid-digit-offset-gadget
           is-invalid-uppercase-offset-gadget
           is-invalid-lowercase-offset-gadget
           val-and-nots-gadget
           val-and-not-right-gadget
           val-diff-times-sum-gadget
           val-times-sum-gadget
           val-not-lc
           val-sum-lc
           assert-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define validate-byte-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "validate_byte(b0, b1, b2, b3, b4, b5, b6, b7, b4b3, b1b0, m, r, lower, null, or_d, inv_d, xor_u, bad_u, or_l, bad_l) := {
    (b7) * (1) == (0),
    (b4) * (b3) == (b4b3),
    (b1) * (b0) == (b1b0),
    (b0 + b1 + b2 + b3 + b4) * (m) == (r),
    (b0 + b1 + b2 + b3 + b4) * (1 - r) == (0),
    (1 - b6) * (1 - b5) == (null),
    (b6) * (b5) == (lower),
    (1 - b2) * (1 - b1) == (1 - or_d),
    (b3) * (or_d) == (inv_d),
    (2 * b2) * (b1b0) == (b2 + b1b0 - xor_u),
    (b4b3) * (xor_u) == (bad_u),
    (1 - b2) * (1 - b1b0) == (1 - or_l),
    (b4b3) * (or_l) == (bad_l),
    (null) * (r) == (0),
    (b5 - lower) * (1 - b4 + inv_d) == (0),
    (b6 - lower) * (1 - r + bad_u) == (0),
    (lower) * (1 - r + bad_l) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (validate-byte-circuit)
            :pred validate-byte-pred
            :prime prime)

(defruled validate-byte-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (bitp b4b3) (bitp b1b0) (bitp r) (bitp lower) (bitp null)
                (bitp or-d) (bitp inv-d) (bitp xor-u) (bitp bad-u)
                (bitp or-l) (bitp bad-l)
                (pfield::fep m prime)
                (validate-byte-pred b0 b1 b2 b3 b4 b5 b6 b7
                                   b4b3 b1b0 m r lower null
                                   or-d inv-d xor-u bad-u or-l bad-l
                                   prime))
           (equal null
                  (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) nil)))
  :enable (validate-byte-pred
           validate-byte
           byte-validation-data-new
           is-invalid-digit-offset
           is-invalid-uppercase-offset
           is-invalid-lowercase-offset
           values-b-and
           values-b-or
           values-b-xor
           values-b-not
           values-bool-to-bit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; validate_trailing_nulls: for each consecutive pair,
; (flag[i]) * (1 - flag[i+1]) = 0.

(define validate-trailing-nulls-gadget ((flags symbol-listp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp flags) (endp (cdr flags)))
      nil
    (append (list (r1cs::make-r1cs-constraint
                   :a (list (list 1 (car flags)))
                   :b (val-not-lc (cadr flags) p)
                   :c nil))
            (validate-trailing-nulls-gadget (cdr flags) p))))

(define val-trailing-nulls-eqs ((bits true-listp) (p primep))
  :returns (yes/no booleanp)
  (if (or (endp bits) (endp (cdr bits)))
      t
    (and (equal (pfield::mul (car bits)
                             (pfield::sub 1 (cadr bits) p)
                             p)
                0)
         (val-trailing-nulls-eqs (cdr bits) p))))

(defruled validate-trailing-nulls-gadget-to-eqs
  (implies (and (symbol-listp flags)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg flags))
           (equal (r1cs::r1cs-constraints-holdp
                   (validate-trailing-nulls-gadget flags p) asg p)
                  (val-trailing-nulls-eqs (lookup-equal-list flags asg) p)))
  :enable (validate-trailing-nulls-gadget
           val-trailing-nulls-eqs
           val-not-lc
           lookup-equal-list
           r1cs::valuation-binds-allp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled val-trailing-nulls-eqs-iff-funspec
  (implies (and (bit-listp bits)
                (equal p (base-prime)))
           (equal (val-trailing-nulls-eqs bits p)
                  (equal (validate-trailing-nulls bits) t)))
  :hints (("Goal"
           :in-theory (enable val-trailing-nulls-eqs
                              validate-trailing-nulls
                              values-b-not
                              bfix))))

(defruled validate-trailing-nulls-gadget-sound
  (implies (and (symbol-listp flags)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg flags)
                (bit-listp (lookup-equal-list flags asg))
                (r1cs::r1cs-constraints-holdp
                 (validate-trailing-nulls-gadget flags p) asg p))
           (equal (validate-trailing-nulls (lookup-equal-list flags asg)) t))
  :enable (validate-trailing-nulls-gadget-to-eqs
           val-trailing-nulls-eqs-iff-funspec))

(defruled validate-trailing-nulls-gadget-complete
  (implies (and (symbol-listp flags)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg flags)
                (bit-listp (lookup-equal-list flags asg))
                (equal (validate-trailing-nulls (lookup-equal-list flags asg)) t))
           (r1cs::r1cs-constraints-holdp
            (validate-trailing-nulls-gadget flags p) asg p))
  :enable (validate-trailing-nulls-gadget-to-eqs
           val-trailing-nulls-eqs-iff-funspec))

(defconst *validate-trailing-nulls-sample*
  '((f0 . 0) (f1 . 1) (f2 . 1)))

(defruled validate-trailing-nulls-sample-holds
  (r1cs::r1cs-constraints-holdp
   (validate-trailing-nulls-gadget '(f0 f1 f2) (base-prime))
   *validate-trailing-nulls-sample*
   (base-prime))
  :enable (validate-trailing-nulls-gadget
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define validate-trailing-nulls-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "One link of the trailing-null chain.  The R1CS gadget repeats it."
  (pfcs::parse-def
   "validate_trailing_nulls(f0, f1) := {
    (f0) * (1 - f1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (validate-trailing-nulls-circuit)
            :pred validate-trailing-nulls-pred
            :prime prime)

(defruled validate-trailing-nulls-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp f0) (bitp f1)
                (validate-trailing-nulls-pred f0 f1 prime))
           (equal (validate-trailing-nulls (list f0 f1)) t))
  :enable (validate-trailing-nulls-pred
           validate-trailing-nulls
           values-b-not))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; validate_identifier_bytes is validate_byte on each byte, the first one
; with the letter assert, then validate_trailing_nulls on the null flags.
; The two-byte gadget below is the loop; snarkVM instantiates it at 31.

(define validate-identifier-bytes-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp)
                                         (b3 symbolp) (b4 symbolp) (b5 symbolp)
                                         (b6 symbolp) (b7 symbolp)
                                         (c0 symbolp) (c1 symbolp) (c2 symbolp)
                                         (c3 symbolp) (c4 symbolp) (c5 symbolp)
                                         (c6 symbolp) (c7 symbolp)
                                         (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Two-byte instance of the identifier validation loop.
          snarkVM runs the same loop on the 31 literal bytes."
  (append (validate-first-byte-gadget
           b0 b1 b2 b3 b4 b5 b6 b7
           'b4b3 'b1b0 'm 'r 'lower 'n0
           'or-d 'inv-d 'xor-u 'bad-u 'or-l 'bad-l
           'partial 'uscore 'letter p)
          (validate-byte-gadget
           c0 c1 c2 c3 c4 c5 c6 c7
           'c4b3 'c1b0 'cm 'cr 'clower 'n1
           'cor-d 'cinv-d 'cxor-u 'cbad-u 'cor-l 'cbad-l p)
          (validate-trailing-nulls-gadget '(n0 n1) p)))

(defruled validate-identifier-bytes-gadget-sound
  :short "The loop's constraints are the first-byte check, each later byte, and the null chain."
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3)
                (symbolp b4) (symbolp b5) (symbolp b6) (symbolp b7)
                (symbolp c0) (symbolp c1) (symbolp c2) (symbolp c3)
                (symbolp c4) (symbolp c5) (symbolp c6) (symbolp c7)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-identifier-bytes-gadget
                  b0 b1 b2 b3 b4 b5 b6 b7
                  c0 c1 c2 c3 c4 c5 c6 c7 p)
                 asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (validate-first-byte-gadget
                  b0 b1 b2 b3 b4 b5 b6 b7
                  'b4b3 'b1b0 'm 'r 'lower 'n0
                  'or-d 'inv-d 'xor-u 'bad-u 'or-l 'bad-l
                  'partial 'uscore 'letter p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-byte-gadget
                  c0 c1 c2 c3 c4 c5 c6 c7
                  'c4b3 'c1b0 'cm 'cr 'clower 'n1
                  'cor-d 'cinv-d 'cxor-u 'cbad-u 'cor-l 'cbad-l p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-trailing-nulls-gadget '(n0 n1) p)
                 asg p)))
  :enable validate-identifier-bytes-gadget)

(defconst *validate-identifier-bytes-sample*
  ;; 'A' followed by a null byte.  Flags 0, 1.
  '((b0 . 1) (b1 . 0) (b2 . 0) (b3 . 0) (b4 . 0) (b5 . 0) (b6 . 1) (b7 . 0)
    (b4b3 . 0) (b1b0 . 0) (m . 1) (r . 1)
    (lower . 0) (n0 . 0)
    (or-d . 0) (inv-d . 0) (xor-u . 0) (bad-u . 0) (or-l . 0) (bad-l . 0)
    (partial . 0) (uscore . 0) (letter . 1)
    (c0 . 0) (c1 . 0) (c2 . 0) (c3 . 0) (c4 . 0) (c5 . 0) (c6 . 0) (c7 . 0)
    (c4b3 . 0) (c1b0 . 0) (cm . 0) (cr . 0)
    (clower . 0) (n1 . 1)
    (cor-d . 0) (cinv-d . 0) (cxor-u . 0) (cbad-u . 0) (cor-l . 0) (cbad-l . 0)))

(defruled validate-identifier-bytes-sample-holds
  (r1cs::r1cs-constraints-holdp
   (validate-identifier-bytes-gadget
    'b0 'b1 'b2 'b3 'b4 'b5 'b6 'b7
    'c0 'c1 'c2 'c3 'c4 'c5 'c6 'c7
    (base-prime))
   *validate-identifier-bytes-sample*
   (base-prime))
  :enable (validate-identifier-bytes-gadget
           validate-byte-sample-holds
           validate-trailing-nulls-gadget
           validate-byte-gadget
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define validate-identifier-bytes-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The trailing-null link used after each validate_byte."
  (validate-trailing-nulls-circuit))

(defruled validate-identifier-bytes-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp f0) (bitp f1)
                (validate-trailing-nulls-pred f0 f1 prime))
           (equal (validate-trailing-nulls (list f0 f1)) t))
  :enable validate-trailing-nulls-pred-to-funspec)

(defruled validate-identifier-bytes-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-first-byte-gadget
                  'b0 'b1 'b2 'b3 'b4 'b5 'b6 'b7
                  'b4b3 'b1b0 'm 'r 'lower 'n0
                  'or-d 'inv-d 'xor-u 'bad-u 'or-l 'bad-l
                  'partial 'uscore 'letter p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-byte-gadget
                  'c0 'c1 'c2 'c3 'c4 'c5 'c6 'c7
                  'c4b3 'c1b0 'cm 'cr 'clower 'n1
                  'cor-d 'cinv-d 'cxor-u 'cbad-u 'cor-l 'cbad-l p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (validate-trailing-nulls-gadget '(n0 n1) p)
                 asg p))
           (r1cs::r1cs-constraints-holdp
            (validate-identifier-bytes-gadget
             'b0 'b1 'b2 'b3 'b4 'b5 'b6 'b7
             'c0 'c1 'c2 'c3 'c4 'c5 'c6 'c7 p)
            asg p))
  :enable (validate-identifier-bytes-gadget))
