; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; to_field, to_fields, to_scalar, from_field, from_field_lossy.
;
; to_field is Field::from_bits_le of at most 128 bits.  That is a linear
; combination and adds no constraint.  The field element is the unsigned
; bit pattern, which is int-to-field-spec.  to_fields is the singleton list
; of that element.  to_scalar is the same linear combination into the
; scalar; the value is int-to-scalar-spec and again no constraint.
;
; from_field is Field::to_lower_bits_le(n): boolean-check the n bits and
; one powers-of-two constraint.  It is unsatisfiable when the field element
; is not below 2^n.
;
; from_field_lossy is Field::to_bits_le sliced to n bits, i.e.
; r1cs/field-to-bits.  Soundness is field-to-bits-soundness plus the low
; n bits.  Completeness needs the bits-lt-prime witness, which this book
; does not construct; see bugs-int.txt.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")
(include-book "../r1cs/field-to-bits")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-to-field-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints.  The field is the weighted sum of the bits."
  nil)

(define int-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  (int-to-field-gadget))

(define int-to-scalar-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled int-to-field-gadget-sound
  (implies (and (int-valuep x signedp n)
                (integer-widthp n))
           (and (equal (int-to-field-spec x signedp n)
                       (int-spec-unsigned x n))
                (r1cs::r1cs-constraints-holdp
                 (int-to-field-gadget) asg p)))
  :enable (int-to-field-gadget
           int-to-field-spec
           int-spec-unsigned
           r1cs::r1cs-constraints-holdp))

(defruled int-to-field-gadget-complete
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (equal u (int-to-field-spec x signedp n)))
           (and (equal u (int-spec-unsigned x n))
                (r1cs::r1cs-constraints-holdp
                 (int-to-field-gadget) asg p)))
  :enable (int-to-field-gadget
           int-to-field-spec
           int-spec-unsigned
           r1cs::r1cs-constraints-holdp))

(defruled int-to-fields-spec-agrees
  (equal (int-to-fields-spec x signedp n)
         (list (int-to-field-spec x signedp n)))
  :enable int-to-fields-spec)

(defruled int-to-fields-gadget-sound
  (implies (and (int-valuep x signedp n)
                (integer-widthp n))
           (and (equal (int-to-fields-spec x signedp n)
                       (list (int-to-field-spec x signedp n)))
                (r1cs::r1cs-constraints-holdp
                 (int-to-fields-gadget) asg p)))
  :enable (int-to-fields-gadget
           int-to-fields-spec-agrees
           int-to-field-gadget-sound))

(defruled int-to-fields-gadget-complete
  (implies (and (int-valuep x signedp n)
                (integer-widthp n))
           (r1cs::r1cs-constraints-holdp
            (int-to-fields-gadget) asg p))
  :enable (int-to-fields-gadget int-to-field-gadget-complete))

(defruled int-to-scalar-gadget-sound
  (implies (and (int-valuep x signedp n)
                (integer-widthp n))
           (and (equal (int-to-scalar-spec x signedp n)
                       (int-spec-unsigned x n))
                (r1cs::r1cs-constraints-holdp
                 (int-to-scalar-gadget) asg p)))
  :enable (int-to-scalar-gadget
           int-to-scalar-spec
           int-spec-unsigned
           r1cs::r1cs-constraints-holdp))

(defruled int-to-scalar-gadget-complete
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (equal s (int-to-scalar-spec x signedp n)))
           (and (equal s (int-spec-unsigned x n))
                (r1cs::r1cs-constraints-holdp
                 (int-to-scalar-gadget) asg p)))
  :enable (int-to-scalar-gadget
           int-to-scalar-spec
           int-spec-unsigned
           r1cs::r1cs-constraints-holdp))

(defconst *int-to-field-sample* nil)

(defruled int-to-field-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-to-field-gadget) *int-to-field-sample* (base-prime))
  :enable (int-to-field-gadget r1cs::r1cs-constraints-holdp))

(defruled int-to-fields-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-to-fields-gadget) *int-to-field-sample* (base-prime))
  :enable (int-to-fields-gadget int-to-field-sample-holds))

(defruled int-to-scalar-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-to-scalar-gadget) *int-to-field-sample* (base-prime))
  :enable (int-to-scalar-gadget r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-from-field-gadget ((f symbolp)
                               (xs symbol-listp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('Field::to_lower_bits_le') of width @('(len xs)')."
  (append (boolean-check-gadget-list xs p)
          (pow2sum-gadget f xs)))

(defruled int-from-field-gadget-to-bits
  (implies (and (symbolp f)
                (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-from-field-gadget f xs p) asg p)
                  (and (bit-listp (lookup-equal-list xs asg))
                       (equal (lookup-equal f asg)
                              (mod (lebits=>nat (lookup-equal-list xs asg))
                                   p)))))
  :enable (int-from-field-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           r1cs::r1cs-constraints-holdp-of-append))

(defruled int-from-field-gadget-sound
  (implies (and (equal p (base-prime))
                (symbolp f)
                (symbol-listp xs)
                (equal n (len xs))
                (integer-widthp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (fieldp (lookup-equal f asg))
                (r1cs::r1cs-constraints-holdp
                 (int-from-field-gadget f xs p) asg p))
           (b* ((f$ (lookup-equal f asg))
                (bits (lookup-equal-list xs asg)))
             (and (not (equal (int-from-field-spec f$ signedp n)
                              (spec-error)))
                  (equal (lebits->int bits signedp)
                         (int-from-field-spec f$ signedp n)))))
  :enable (int-from-field-gadget-to-bits
           int-from-field-spec
           int-wrap
           int-width-lt-prime-bits
           lebits->int-when-unsigned
           lebits->int-is-lebits=>int
           fieldp))

(defruled int-from-field-gadget-complete
  (implies (and (equal p (base-prime))
                (symbolp f)
                (symbol-listp xs)
                (equal n (len xs))
                (integer-widthp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (fieldp (lookup-equal f asg))
                (not (equal (int-from-field-spec (lookup-equal f asg)
                                                 signedp n)
                            (spec-error)))
                (equal (lookup-equal-list xs asg)
                       (int->lebits (lookup-equal f asg) n)))
           (r1cs::r1cs-constraints-holdp
            (int-from-field-gadget f xs p) asg p))
  :enable (int-from-field-gadget-to-bits
           int-from-field-spec
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           int-width-lt-prime-bits
           fieldp))

(defconst *int-from-field-sample*
  '((f . 1) (b0 . 1) (b1 . 0)))

(defruled int-from-field-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-from-field-gadget 'f '(b0 b1) (base-prime))
   *int-from-field-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-from-field-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     pow2sum-gadget
                                     pow2sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-from-field-lossy-gadget ((f symbolp)
                                     (xs symbol-listp)
                                     (rs symbol-listp)
                                     (u symbolp)
                                     (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Full field-to-bits.  The integer is the first @('n') bits."
  (field-to-bits-gadget f xs rs u p))

(defruled int-from-field-lossy-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp f)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (integer-widthp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-from-field-lossy-gadget f xs rs u p) asg p))
           (b* ((bits (take n (lookup-equal-list xs asg)))
                (f$ (lookup-equal f asg)))
             (equal (lebits=>nat bits)
                    (mod f$ (expt 2 n)))))
  :enable (int-from-field-lossy-gadget
           field-to-bits-soundness
           integer-length-of-base-prime)
  :use (:instance acl2::lebits=>nat-of-append
                  (lodigits (take n (lookup-equal-list xs asg)))
                  (hidigits (nthcdr n (lookup-equal-list xs asg)))))

; No completeness theorem: the bits-lt-prime witness is not constructed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-to-field-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Empty: @('to_field') adds no constraint."
  (pfcs::parse-def
   "int_to_field(x) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-to-field-circuit) :pred int-to-field-pred :prime prime)

(defruled int-to-field-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (int-valuep x signedp n)
                (integer-widthp n)
                (equal u (int-spec-unsigned x n)))
           (and (int-to-field-pred x prime)
                (equal u (int-to-field-spec x signedp n))))
  :enable (int-to-field-pred
           int-to-field-spec
           int-spec-unsigned))

(define int-from-field-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_from_field(f, b0, b1) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (f) * (1) == (b0 + 2 * b1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-from-field-circuit)
            :pred int-from-field-pred
            :prime prime)

(defruled int-from-field-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1)
                (fieldp f)
                (equal f (+ b0 (* 2 b1))))
           (and (int-from-field-pred f b0 b1 prime)
                (equal (lebits->int (list b0 b1) nil)
                       (int-from-field-spec f nil 2))))
  :enable (int-from-field-pred
           int-from-field-spec
           int-wrap
           lebits->int
           lebits=>nat))
