; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; StringType::new and StringType::inject_size_in_bytes.
;
; Both host-check the u32 bound (and inject_size also host-checks byte
; alignment) and then assert_eq a constant size against a private witness.
; When the mode is constant both sides are constant, the host checks
; equality, and no constraint is added.  The gadget is the constraint
; added in every other case: (k) * (1) = (size).
;
; from_bits_le / from_bits_be call inject_size_in_bytes and then pack
; bytes.  U8::from_bits_* is an abstract integer injection; the only
; constraint this function adds is the size assert_eq.

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "../fun-specs/values-string")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-type-new-gadget ((k natp) (size symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "StringType::new asserts the size witness equals the constant length."
  (const-assert-eq-gadget k size))

(defruled string-type-new-gadget-sound
  (implies (and (string-typep s)
                (natp k)
                (< k (expt 2 32))
                (< k (base-prime))
                (equal k (len (string-type->bytes s)))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::r1cs-constraints-holdp
                 (string-type-new-gadget k size) asg p))
           (and (equal (lookup-equal size asg) k)
                (equal (string-type-new s) (string-type-fix s))))
  :enable (string-type-new-gadget
           const-assert-eq-gadget-to-eq
           string-type-new))

(defruled string-type-new-gadget-complete
  (implies (and (string-typep s)
                (natp k)
                (< k (expt 2 32))
                (< k (base-prime))
                (equal k (len (string-type->bytes s)))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (equal (lookup-equal size asg) k))
           (and (equal (string-type-new s) (string-type-fix s))
                (r1cs::r1cs-constraints-holdp
                 (string-type-new-gadget k size) asg p)))
  :enable (string-type-new-gadget
           const-assert-eq-gadget-to-eq
           string-type-new))

(defconst *string-type-new-sample*
  '((size . 3)))

(defruled string-type-new-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-type-new-gadget 3 'size)
   *string-type-new-sample*
   (base-prime))
  :enable (string-type-new-gadget
           const-assert-eq-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define string-type-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_type_new(k, size) := {
    (k) * (1) == (size)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-type-new-circuit)
            :pred string-type-new-pred
            :prime prime)

(defruled string-type-new-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (string-typep s)
                (fieldp k)
                (fieldp size)
                (< k (expt 2 32))
                (equal k (len (string-type->bytes s)))
                (string-type-new-pred k size prime))
           (equal (string-type-new s) (string-type-fix s)))
  :enable (string-type-new-pred
           string-type-new
           enforce-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-type-inject-size-gadget ((k natp) (size symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "inject_size_in_bytes asserts the size witness equals n/8."
  (const-assert-eq-gadget k size))

(defruled string-type-inject-size-gadget-sound
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::r1cs-constraints-holdp
                 (string-type-inject-size-gadget k size) asg p))
           (and (equal (lookup-equal size asg) k)
                (equal (string-type-inject-size-in-bytes bits) k)))
  :enable (string-type-inject-size-gadget
           const-assert-eq-gadget-to-eq
           string-type-inject-size-in-bytes))

(defruled string-type-inject-size-gadget-complete
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (equal (lookup-equal size asg) k))
           (and (equal (string-type-inject-size-in-bytes bits) k)
                (r1cs::r1cs-constraints-holdp
                 (string-type-inject-size-gadget k size) asg p)))
  :enable (string-type-inject-size-gadget
           const-assert-eq-gadget-to-eq
           string-type-inject-size-in-bytes))

(defconst *string-type-inject-size-sample*
  '((size . 2)))

(defruled string-type-inject-size-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-type-inject-size-gadget 2 'size)
   *string-type-inject-size-sample*
   (base-prime))
  :enable (string-type-inject-size-gadget
           const-assert-eq-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define string-type-inject-size-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_type_inject_size(k, size) := {
    (k) * (1) == (size)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-type-inject-size-circuit)
            :pred string-type-inject-size-pred
            :prime prime)

(defruled string-type-inject-size-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (fieldp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (fieldp size)
                (string-type-inject-size-pred k size prime))
           (equal (string-type-inject-size-in-bytes bits) k))
  :enable (string-type-inject-size-pred
           string-type-inject-size-in-bytes
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-type-from-bits-le-gadget ((k natp) (size symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "from_bits_le adds the inject_size_in_bytes assert_eq."
  (string-type-inject-size-gadget k size))

(defruled string-type-from-bits-le-gadget-sound
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::r1cs-constraints-holdp
                 (string-type-from-bits-le-gadget k size) asg p))
           (equal (string-type-from-bits-le bits)
                  (make-string-type :bytes (values-lebits-to-bytes bits))))
  :enable (string-type-from-bits-le
           string-type-inject-size-in-bytes))

(defruled string-type-from-bits-le-gadget-complete
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (equal (lookup-equal size asg) k))
           (r1cs::r1cs-constraints-holdp
            (string-type-from-bits-le-gadget k size) asg p))
  :enable (string-type-from-bits-le-gadget
           string-type-inject-size-gadget-complete))

(defconst *string-type-from-bits-le-sample* *string-type-inject-size-sample*)

(defruled string-type-from-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-type-from-bits-le-gadget 2 'size)
   *string-type-from-bits-le-sample*
   (base-prime))
  :enable (string-type-from-bits-le-gadget
           string-type-inject-size-sample-holds))

(define string-type-from-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_type_from_bits_le(k, size) := {
    (k) * (1) == (size)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-type-from-bits-le-circuit)
            :pred string-type-from-bits-le-pred
            :prime prime)

(defruled string-type-from-bits-le-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (fieldp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (fieldp size)
                (string-type-from-bits-le-pred k size prime))
           (equal (string-type-from-bits-le bits)
                  (make-string-type :bytes (values-lebits-to-bytes bits))))
  :enable (string-type-from-bits-le-pred
           string-type-from-bits-le
           string-type-inject-size-in-bytes
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-type-from-bits-be-gadget ((k natp) (size symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "from_bits_be adds the same size assert_eq as from_bits_le."
  (string-type-inject-size-gadget k size))

(defruled string-type-from-bits-be-gadget-sound
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::r1cs-constraints-holdp
                 (string-type-from-bits-be-gadget k size) asg p))
           (equal (string-type-from-bits-be bits)
                  (make-string-type :bytes (values-bebits-to-bytes bits))))
  :enable (string-type-from-bits-be
           string-type-inject-size-in-bytes))

(defruled string-type-from-bits-be-gadget-complete
  (implies (and (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (natp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (< k (base-prime))
                (symbolp size)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (equal (lookup-equal size asg) k))
           (r1cs::r1cs-constraints-holdp
            (string-type-from-bits-be-gadget k size) asg p))
  :enable (string-type-from-bits-be-gadget
           string-type-inject-size-gadget-complete))

(defconst *string-type-from-bits-be-sample* *string-type-inject-size-sample*)

(defruled string-type-from-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-type-from-bits-be-gadget 2 'size)
   *string-type-from-bits-be-sample*
   (base-prime))
  :enable (string-type-from-bits-be-gadget
           string-type-inject-size-sample-holds))

(define string-type-from-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_type_from_bits_be(k, size) := {
    (k) * (1) == (size)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-type-from-bits-be-circuit)
            :pred string-type-from-bits-be-pred
            :prime prime)

(defruled string-type-from-bits-be-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bit-listp bits)
                (equal (mod (len bits) 8) 0)
                (fieldp k)
                (equal k (floor (len bits) 8))
                (< k (expt 2 32))
                (fieldp size)
                (string-type-from-bits-be-pred k size prime))
           (equal (string-type-from-bits-be bits)
                  (make-string-type :bytes (values-bebits-to-bytes bits))))
  :enable (string-type-from-bits-be-pred
           string-type-from-bits-be
           string-type-inject-size-in-bytes
           fieldp))
