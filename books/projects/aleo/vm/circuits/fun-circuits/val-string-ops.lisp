; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; String and identifier operations whose constraints are either empty
; (bit reordering, packing, field-from-bits of a short bit string) or a
; field is_equal / boolean not / assert-bits-are-zero.
;
; Field::from_bits_le on at most 252 bits is a linear combination, so
; IdentifierLiteral::to_field adds no constraint.  Tests report 0
; constraints for to_field, to_fields, and write_bits_*.
; is_not_equal is boolean not of is_equal, also a linear combination.
; StringType::is_equal is is_equal of the size witnesses conjoined with
; is_equal of the packed fields.  The size witnesses are the byte lengths
; (enforced by new / inject_size_in_bytes).

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "val-string-validate")
(include-book "../fun-specs/values-string")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-and")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *val-string-empty-sample* nil)

(defruled val-string-empty-sample-holds
  (r1cs::r1cs-constraints-holdp nil *val-string-empty-sample* (base-prime))
  :enable r1cs::r1cs-constraints-holdp)

(define identifier-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "IdentifierLiteral::write_bits_le copies each byte's bits."
  nil)

(defruled identifier-write-bits-le-gadget-sound
  (implies (and (identifier-literalp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-write-bits-le-gadget) asg p))
           (equal (identifier-literal-to-bits-le x)
                  (values-bytes-to-lebits (identifier-literal->bytes x))))
  :enable (identifier-write-bits-le-gadget
           identifier-literal-to-bits-le
           r1cs::r1cs-constraints-holdp))

(defruled identifier-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            (identifier-write-bits-le-gadget) asg p))
  :enable identifier-write-bits-le-gadget)

(defconst *identifier-write-bits-le-sample* *val-string-empty-sample*)

(defruled identifier-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp (identifier-write-bits-le-gadget)
                                *identifier-write-bits-le-sample*
                                (base-prime))
  :enable (identifier-write-bits-le-gadget val-string-empty-sample-holds))

(define identifier-write-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_write_bits_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-write-bits-le-circuit)
            :pred identifier-write-bits-le-pred
            :prime prime)

(defruled identifier-write-bits-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (identifier-write-bits-le-pred prime) t))
  :enable (identifier-write-bits-le-pred))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "write_bits_be reverses the little-endian bits.  No constraint."
  nil)

(defruled identifier-write-bits-be-gadget-sound
  (implies (and (identifier-literalp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-write-bits-be-gadget) asg p))
           (equal (identifier-literal-to-bits-be x)
                  (rev (identifier-literal-to-bits-le x))))
  :enable (identifier-write-bits-be-gadget
           identifier-literal-to-bits-be
           r1cs::r1cs-constraints-holdp))

(defruled identifier-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            (identifier-write-bits-be-gadget) asg p))
  :enable identifier-write-bits-be-gadget)

(defconst *identifier-write-bits-be-sample* *val-string-empty-sample*)

(defruled identifier-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp (identifier-write-bits-be-gadget)
                                *identifier-write-bits-be-sample*
                                (base-prime))
  :enable (identifier-write-bits-be-gadget val-string-empty-sample-holds))

(define identifier-write-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_write_bits_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-write-bits-be-circuit)
            :pred identifier-write-bits-be-pred
            :prime prime)

(defruled identifier-write-bits-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (identifier-write-bits-be-pred prime) t))
  :enable identifier-write-bits-be-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-field-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "to_field is Field::from_bits_le of 248 bits: a linear combination."
  nil)

(defruled identifier-to-field-gadget-sound
  (implies (and (identifier-literalp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (identifier-to-field-gadget) asg p))
           (equal (identifier-literal-to-field x)
                  (values-lebits-to-field (identifier-literal-to-bits-le x))))
  :enable (identifier-to-field-gadget
           identifier-literal-to-field
           r1cs::r1cs-constraints-holdp))

(defruled identifier-to-field-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (identifier-to-field-gadget) asg p))
  :enable identifier-to-field-gadget)

(defconst *identifier-to-field-sample* *val-string-empty-sample*)

(defruled identifier-to-field-sample-holds
  (r1cs::r1cs-constraints-holdp (identifier-to-field-gadget)
                                *identifier-to-field-sample*
                                (base-prime))
  :enable (identifier-to-field-gadget val-string-empty-sample-holds))

(define identifier-to-field-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_to_field() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-to-field-circuit)
            :pred identifier-to-field-pred
            :prime prime)

(defruled identifier-to-field-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (identifier-to-field-pred prime) t))
  :enable identifier-to-field-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled identifier-to-fields-gadget-sound
  (implies (and (identifier-literalp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-to-fields-gadget) asg p))
           (equal (identifier-literal-to-fields x)
                  (list (identifier-literal-to-field x))))
  :enable (identifier-to-fields-gadget
           identifier-literal-to-fields
           r1cs::r1cs-constraints-holdp))

(defruled identifier-to-fields-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (identifier-to-fields-gadget) asg p))
  :enable identifier-to-fields-gadget)

(defconst *identifier-to-fields-sample* *val-string-empty-sample*)

(defruled identifier-to-fields-sample-holds
  (r1cs::r1cs-constraints-holdp (identifier-to-fields-gadget)
                                *identifier-to-fields-sample*
                                (base-prime))
  :enable (identifier-to-fields-gadget val-string-empty-sample-holds))

(define identifier-to-fields-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_to_fields() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-to-fields-circuit)
            :pred identifier-to-fields-pred
            :prime prime)

(defruled identifier-to-fields-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (identifier-to-fields-pred prime) t))
  :enable identifier-to-fields-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled string-write-bits-le-gadget-sound
  (implies (and (string-typep s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (string-write-bits-le-gadget) asg p))
           (equal (string-type-to-bits-le s)
                  (values-bytes-to-lebits (string-type->bytes s))))
  :enable (string-write-bits-le-gadget
           string-type-to-bits-le
           r1cs::r1cs-constraints-holdp))

(defruled string-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (string-write-bits-le-gadget) asg p))
  :enable string-write-bits-le-gadget)

(defconst *string-write-bits-le-sample* *val-string-empty-sample*)

(defruled string-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp (string-write-bits-le-gadget)
                                *string-write-bits-le-sample*
                                (base-prime))
  :enable (string-write-bits-le-gadget val-string-empty-sample-holds))

(define string-write-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_write_bits_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-write-bits-le-circuit)
            :pred string-write-bits-le-pred
            :prime prime)

(defruled string-write-bits-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (string-write-bits-le-pred prime) t))
  :enable string-write-bits-le-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled string-write-bits-be-gadget-sound
  (implies (and (string-typep s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (string-write-bits-be-gadget) asg p))
           (equal (string-type-to-bits-be s)
                  (values-bytes-to-bebits (string-type->bytes s))))
  :enable (string-write-bits-be-gadget
           string-type-to-bits-be
           r1cs::r1cs-constraints-holdp))

(defruled string-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (string-write-bits-be-gadget) asg p))
  :enable string-write-bits-be-gadget)

(defconst *string-write-bits-be-sample* *val-string-empty-sample*)

(defruled string-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp (string-write-bits-be-gadget)
                                *string-write-bits-be-sample*
                                (base-prime))
  :enable (string-write-bits-be-gadget val-string-empty-sample-holds))

(define string-write-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_write_bits_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-write-bits-be-circuit)
            :pred string-write-bits-be-pred
            :prime prime)

(defruled string-write-bits-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (string-write-bits-be-pred prime) t))
  :enable string-write-bits-be-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "to_fields packs little-endian bits.  from_bits_le of a short chunk is a linear combination."
  nil)

(defruled string-to-fields-gadget-sound
  (implies (and (string-typep s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (string-to-fields-gadget) asg p))
           (equal (string-type-to-fields s)
                  (values-pack-bits (string-type-to-bits-le s))))
  :enable (string-to-fields-gadget
           string-type-to-fields
           r1cs::r1cs-constraints-holdp))

(defruled string-to-fields-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (string-to-fields-gadget) asg p))
  :enable string-to-fields-gadget)

(defconst *string-to-fields-sample* *val-string-empty-sample*)

(defruled string-to-fields-sample-holds
  (r1cs::r1cs-constraints-holdp (string-to-fields-gadget)
                                *string-to-fields-sample*
                                (base-prime))
  :enable (string-to-fields-gadget val-string-empty-sample-holds))

(define string-to-fields-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_to_fields() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-to-fields-circuit)
            :pred string-to-fields-pred
            :prime prime)

(defruled string-to-fields-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (string-to-fields-pred prime) t))
  :enable string-to-fields-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::is_equal is Field::is_equal of the two to_field values.
; The result bit is 1 - r.

(define identifier-is-equal-gadget ((x symbolp) (y symbolp)
                                   (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-var-is-equal-gadget x y m r p))

(defruled identifier-is-equal-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (identifier-literalp a) (identifier-literalp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal x asg) (identifier-literal-to-field a))
                (equal (lookup-equal y asg) (identifier-literal-to-field b))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-equal-gadget x y m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (identifier-literal-is-equal a b)))
  :hints (("Goal"
           :use (:instance field-var-is-equal-gadget-sound (a x) (b y))
           :in-theory (e/d (identifier-is-equal-gadget
                            identifier-literal-is-equal
                            values-bool-to-bit)
                           (field-var-is-equal-gadget)))))

(defruled identifier-is-equal-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg) (lookup-equal y asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal x asg) (lookup-equal y asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x asg)
                                                   (lookup-equal y asg)
                                                   p)
                                      p))))
           (r1cs::r1cs-constraints-holdp
            (identifier-is-equal-gadget x y m r p) asg p))
  :enable (identifier-is-equal-gadget field-var-is-equal-gadget-complete))

(defconst *identifier-is-equal-sample*
  '((x . 4) (y . 4) (m . 0) (r . 0)))

(defruled identifier-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-is-equal-gadget 'x 'y 'm 'r (base-prime))
   *identifier-is-equal-sample*
   (base-prime))
  :enable (identifier-is-equal-gadget
           field-var-is-equal-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define identifier-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_is_equal(x, y, m, r) := {
    (x - y) * (m) == (r),
    (x - y) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-is-equal-circuit)
            :pred identifier-is-equal-pred
            :prime prime)

(defruled identifier-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x) (fieldp y) (bitp r)
                (pfield::fep m prime)
                (identifier-is-equal-pred x y m r prime)
                (identifier-literalp a) (identifier-literalp b)
                (equal x (identifier-literal-to-field a))
                (equal y (identifier-literal-to-field b)))
           (equal (pfield::sub 1 r prime)
                  (identifier-literal-is-equal a b)))
  :hints (("Goal"
           :use (:instance field-var-is-equal-bit-when-constraints
                           (p prime) (a x) (b y))
           :in-theory (enable identifier-is-equal-pred
                              identifier-literal-is-equal
                              values-bool-to-bit
                              fieldp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_not_equal is the r bit of is_equal (boolean not of 1 - r).

(define identifier-is-not-equal-gadget ((x symbolp) (y symbolp)
                                       (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (identifier-is-equal-gadget x y m r p))

(defruled identifier-is-not-equal-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (identifier-literalp a) (identifier-literalp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal x asg) (identifier-literal-to-field a))
                (equal (lookup-equal y asg) (identifier-literal-to-field b))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-not-equal-gadget x y m r p) asg p))
           (equal (lookup-equal r asg)
                  (identifier-literal-is-not-equal a b)))
  :hints (("Goal"
           :use identifier-is-equal-gadget-sound
           :in-theory (e/d (identifier-is-not-equal-gadget
                            identifier-literal-is-not-equal
                            identifier-literal-is-equal
                            values-bool-to-bit
                            bitp)
                           (identifier-is-equal-gadget)))))

(defruled identifier-is-not-equal-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg) (lookup-equal y asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal x asg) (lookup-equal y asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x asg)
                                                   (lookup-equal y asg)
                                                   p)
                                      p))))
           (r1cs::r1cs-constraints-holdp
            (identifier-is-not-equal-gadget x y m r p) asg p))
  :enable (identifier-is-not-equal-gadget
           identifier-is-equal-gadget-complete))

(defconst *identifier-is-not-equal-sample*
  ;; 5 - 4 = 1, so the multiplier is 1 and the neq bit is 1.
  '((x . 5) (y . 4) (m . 1) (r . 1)))

(defruled identifier-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-is-not-equal-gadget 'x 'y 'm 'r (base-prime))
   *identifier-is-not-equal-sample*
   (base-prime))
  :enable (identifier-is-not-equal-gadget
           field-var-is-equal-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define identifier-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_is_not_equal(x, y, m, r) := {
    (x - y) * (m) == (r),
    (x - y) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-is-not-equal-circuit)
            :pred identifier-is-not-equal-pred
            :prime prime)

(defruled identifier-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x) (fieldp y) (bitp r)
                (pfield::fep m prime)
                (identifier-is-not-equal-pred x y m r prime)
                (identifier-literalp a) (identifier-literalp b)
                (equal x (identifier-literal-to-field a))
                (equal y (identifier-literal-to-field b)))
           (equal (identifier-literal-is-not-equal a b) r))
  :hints (("Goal"
           :use (:instance field-var-is-equal-bit-when-constraints
                           (p prime) (a x) (b y))
           :in-theory (enable identifier-is-not-equal-pred
                              identifier-literal-is-not-equal
                              values-bool-to-bit
                              fieldp
                              bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; StringType::is_equal: size is_equal, then AND with each field is_equal.
; One field element (the strings pack to a single field) is the sample shape.
; Boolean not of the size/field neq bits is a linear combination, and the
; final AND is (1 - rs) * (1 - rf) = out.

(local
 (defruled values-field-lists-zip-equal-same
   (values-field-lists-zip-equal x x)
   :enable values-field-lists-zip-equal))

(define string-is-equal-gadget ((sa symbolp) (sb symbolp) (ms symbolp) (rs symbolp)
                               (fa symbolp) (fb symbolp) (mf symbolp) (rf symbolp)
                               (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (field-var-is-equal-gadget sa sb ms rs p)
          (field-var-is-equal-gadget fa fb mf rf p)
          (list (r1cs::make-r1cs-constraint
                 :a (val-not-lc rs p)
                 :b (val-not-lc rf p)
                 :c (list (list 1 out))))))

(defruled string-is-equal-gadget-sound
  (implies (and (symbolp sa) (symbolp sb) (symbolp ms) (symbolp rs)
                (symbolp fa) (symbolp fb) (symbolp mf) (symbolp rf)
                (symbolp out)
                (string-typep s) (string-typep u)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg sa)
                (r1cs::valuation-bindsp asg sb)
                (r1cs::valuation-bindsp asg ms)
                (r1cs::valuation-bindsp asg rs)
                (r1cs::valuation-bindsp asg fa)
                (r1cs::valuation-bindsp asg fb)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg out)
                (fieldp (lookup-equal sa asg))
                (fieldp (lookup-equal sb asg))
                (fieldp (lookup-equal fa asg))
                (fieldp (lookup-equal fb asg))
                (bitp (lookup-equal rs asg))
                (bitp (lookup-equal rf asg))
                (equal (lookup-equal sa asg) (len (string-type->bytes s)))
                (equal (lookup-equal sb asg) (len (string-type->bytes u)))
                (equal (list (lookup-equal fa asg)) (string-type-to-fields s))
                (equal (list (lookup-equal fb asg)) (string-type-to-fields u))
                (r1cs::r1cs-constraints-holdp
                 (string-is-equal-gadget sa sb ms rs fa fb mf rf out p) asg p))
           (equal (lookup-equal out asg)
                  (string-type-is-equal s u)))
  :hints (("Goal"
           :use ((:instance field-var-is-equal-gadget-sound
                            (a sa) (b sb) (m ms) (r rs))
                 (:instance field-var-is-equal-gadget-sound
                            (a fa) (b fb) (m mf) (r rf)))
           :in-theory (e/d (string-is-equal-gadget
                            string-type-is-equal
                            values-bool-to-bit
                            values-field-lists-zip-equal
                            values-field-lists-zip-equal-same
                            values-b-and
                            val-not-lc
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            bitp)
                           (field-var-is-equal-gadget)))))

(defruled string-is-equal-gadget-complete
  (implies (and (symbolp sa) (symbolp sb) (symbolp ms) (symbolp rs)
                (symbolp fa) (symbolp fb) (symbolp mf) (symbolp rf)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg sa)
                (r1cs::valuation-bindsp asg sb)
                (r1cs::valuation-bindsp asg ms)
                (r1cs::valuation-bindsp asg rs)
                (r1cs::valuation-bindsp asg fa)
                (r1cs::valuation-bindsp asg fb)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg out)
                (fieldp (lookup-equal sa asg))
                (fieldp (lookup-equal sb asg))
                (fieldp (lookup-equal fa asg))
                (fieldp (lookup-equal fb asg))
                (equal (lookup-equal rs asg)
                       (if (equal (lookup-equal sa asg) (lookup-equal sb asg))
                           0 1))
                (equal (lookup-equal ms asg)
                       (if (equal (lookup-equal sa asg) (lookup-equal sb asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal sa asg)
                                                   (lookup-equal sb asg) p)
                                      p)))
                (equal (lookup-equal rf asg)
                       (if (equal (lookup-equal fa asg) (lookup-equal fb asg))
                           0 1))
                (equal (lookup-equal mf asg)
                       (if (equal (lookup-equal fa asg) (lookup-equal fb asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal fa asg)
                                                   (lookup-equal fb asg) p)
                                      p)))
                (equal (lookup-equal out asg)
                       (pfield::mul (pfield::sub 1 (lookup-equal rs asg) p)
                                    (pfield::sub 1 (lookup-equal rf asg) p)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (string-is-equal-gadget sa sb ms rs fa fb mf rf out p) asg p))
  :enable (string-is-equal-gadget
           field-var-is-equal-gadget-complete
           val-not-lc
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defconst *string-is-equal-sample*
  '((sa . 1) (sb . 1) (ms . 0) (rs . 0)
    (fa . 9) (fb . 9) (mf . 0) (rf . 0)
    (out . 1)))

(defruled string-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-is-equal-gadget 'sa 'sb 'ms 'rs 'fa 'fb 'mf 'rf 'out (base-prime))
   *string-is-equal-sample*
   (base-prime))
  :enable (string-is-equal-gadget
           field-var-is-equal-gadget
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define string-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_is_equal(sa, sb, ms, rs, fa, fb, mf, rf, out) := {
    (sa - sb) * (ms) == (rs),
    (sa - sb) * (1 - rs) == (0),
    (fa - fb) * (mf) == (rf),
    (fa - fb) * (1 - rf) == (0),
    (1 - rs) * (1 - rf) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-is-equal-circuit)
            :pred string-is-equal-pred
            :prime prime)

(defruled string-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (string-typep s) (string-typep u)
                (fieldp sa) (fieldp sb) (fieldp fa) (fieldp fb)
                (bitp rs) (bitp rf) (bitp out)
                (pfield::fep ms prime) (pfield::fep mf prime)
                (equal sa (len (string-type->bytes s)))
                (equal sb (len (string-type->bytes u)))
                (equal (list fa) (string-type-to-fields s))
                (equal (list fb) (string-type-to-fields u))
                (string-is-equal-pred sa sb ms rs fa fb mf rf out prime))
           (equal (string-type-is-equal s u) out))
  :hints (("Goal"
           :use ((:instance field-var-is-equal-bit-when-constraints
                            (p prime) (a sa) (b sb) (m ms) (r rs))
                 (:instance field-var-is-equal-bit-when-constraints
                            (p prime) (a fa) (b fb) (m mf) (r rf)))
           :in-theory (enable string-is-equal-pred
                              string-type-is-equal
                              values-field-lists-zip-equal
                              values-field-lists-zip-equal-same
                              values-bool-to-bit
                              values-b-and
                              bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; StringType::is_not_equal is boolean not of is_equal: the linear combination
; 1 - out.  The constraints are exactly those of is_equal.

(define string-is-not-equal-gadget ((sa symbolp) (sb symbolp) (ms symbolp) (rs symbolp)
                                   (fa symbolp) (fb symbolp) (mf symbolp) (rf symbolp)
                                   (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (string-is-equal-gadget sa sb ms rs fa fb mf rf out p))

(defruled string-is-not-equal-gadget-sound
  (implies (and (symbolp sa) (symbolp sb) (symbolp ms) (symbolp rs)
                (symbolp fa) (symbolp fb) (symbolp mf) (symbolp rf)
                (symbolp out)
                (string-typep s) (string-typep u)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg sa)
                (r1cs::valuation-bindsp asg sb)
                (r1cs::valuation-bindsp asg ms)
                (r1cs::valuation-bindsp asg rs)
                (r1cs::valuation-bindsp asg fa)
                (r1cs::valuation-bindsp asg fb)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg out)
                (fieldp (lookup-equal sa asg))
                (fieldp (lookup-equal sb asg))
                (fieldp (lookup-equal fa asg))
                (fieldp (lookup-equal fb asg))
                (bitp (lookup-equal rs asg))
                (bitp (lookup-equal rf asg))
                (bitp (lookup-equal out asg))
                (equal (lookup-equal sa asg) (len (string-type->bytes s)))
                (equal (lookup-equal sb asg) (len (string-type->bytes u)))
                (equal (list (lookup-equal fa asg)) (string-type-to-fields s))
                (equal (list (lookup-equal fb asg)) (string-type-to-fields u))
                (r1cs::r1cs-constraints-holdp
                 (string-is-not-equal-gadget sa sb ms rs fa fb mf rf out p) asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (string-type-is-not-equal s u)))
  :hints (("Goal"
           :use string-is-equal-gadget-sound
           :in-theory (e/d (string-is-not-equal-gadget
                            string-type-is-not-equal
                            values-b-not
                            bitp)
                           (string-is-equal-gadget
                            string-type-is-equal)))))

(defruled string-is-not-equal-gadget-complete
  (implies (and (symbolp sa) (symbolp sb) (symbolp ms) (symbolp rs)
                (symbolp fa) (symbolp fb) (symbolp mf) (symbolp rf)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg sa)
                (r1cs::valuation-bindsp asg sb)
                (r1cs::valuation-bindsp asg ms)
                (r1cs::valuation-bindsp asg rs)
                (r1cs::valuation-bindsp asg fa)
                (r1cs::valuation-bindsp asg fb)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg out)
                (fieldp (lookup-equal sa asg))
                (fieldp (lookup-equal sb asg))
                (fieldp (lookup-equal fa asg))
                (fieldp (lookup-equal fb asg))
                (equal (lookup-equal rs asg)
                       (if (equal (lookup-equal sa asg) (lookup-equal sb asg))
                           0 1))
                (equal (lookup-equal ms asg)
                       (if (equal (lookup-equal sa asg) (lookup-equal sb asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal sa asg)
                                                   (lookup-equal sb asg) p)
                                      p)))
                (equal (lookup-equal rf asg)
                       (if (equal (lookup-equal fa asg) (lookup-equal fb asg))
                           0 1))
                (equal (lookup-equal mf asg)
                       (if (equal (lookup-equal fa asg) (lookup-equal fb asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal fa asg)
                                                   (lookup-equal fb asg) p)
                                      p)))
                (equal (lookup-equal out asg)
                       (pfield::mul (pfield::sub 1 (lookup-equal rs asg) p)
                                    (pfield::sub 1 (lookup-equal rf asg) p)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (string-is-not-equal-gadget sa sb ms rs fa fb mf rf out p) asg p))
  :enable (string-is-not-equal-gadget string-is-equal-gadget-complete))

(defconst *string-is-not-equal-sample* *string-is-equal-sample*)

(defruled string-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (string-is-not-equal-gadget 'sa 'sb 'ms 'rs 'fa 'fb 'mf 'rf 'out (base-prime))
   *string-is-not-equal-sample*
   (base-prime))
  :enable (string-is-not-equal-gadget string-is-equal-sample-holds))

(define string-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "string_is_not_equal(sa, sb, ms, rs, fa, fb, mf, rf, out) := {
    (sa - sb) * (ms) == (rs),
    (sa - sb) * (1 - rs) == (0),
    (fa - fb) * (mf) == (rf),
    (fa - fb) * (1 - rf) == (0),
    (1 - rs) * (1 - rf) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (string-is-not-equal-circuit)
            :pred string-is-not-equal-pred
            :prime prime)

(local
 (defruled string-is-not-equal-pred-is-string-is-equal-pred
   (equal (string-is-not-equal-pred sa sb ms rs fa fb mf rf out prime)
          (string-is-equal-pred sa sb ms rs fa fb mf rf out prime))
   :enable (string-is-not-equal-pred string-is-equal-pred)))

(defruled string-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (string-typep s) (string-typep u)
                (fieldp sa) (fieldp sb) (fieldp fa) (fieldp fb)
                (bitp rs) (bitp rf) (bitp out)
                (pfield::fep ms prime) (pfield::fep mf prime)
                (equal sa (len (string-type->bytes s)))
                (equal sb (len (string-type->bytes u)))
                (equal (list fa) (string-type-to-fields s))
                (equal (list fb) (string-type-to-fields u))
                (string-is-not-equal-pred sa sb ms rs fa fb mf rf out prime))
           (equal (pfield::sub 1 out prime)
                  (string-type-is-not-equal s u)))
  :hints (("Goal"
           :use (string-is-equal-pred-to-funspec
                 string-is-not-equal-pred-is-string-is-equal-pred)
           :in-theory (e/d (string-type-is-not-equal
                            values-b-not
                            bitp)
                           (string-is-not-equal-pred
                            string-is-equal-pred
                            string-type-is-equal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::assert_bits_are_zero, used by IdentifierLiteral::from_bits_le
; on the bits past the first 248.  The constraint is the unweighted sum
; of those bits times 1 equals 0.

(define identifier-from-bits-le-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The extra constraint of from_bits_le: excess bits sum to 0.
          Byte validation is validate-byte / validate-trailing-nulls."
  (if (endp excess)
      nil
    (assert-bits-sum-zero-gadget excess)))

;; FALSE: excess = (repeat (base-prime) 'e0), asg = ((e0 . 1)): the bit sum is
;; p = 0 mod p, so the constraint holds, but the bits are not all zero.
;; (defruled identifier-from-bits-le-gadget-sound
;;   (implies (and (symbol-listp excess)
;;                 (equal p (base-prime))
;;                 (r1cs::r1cs-valuationp asg p)
;;                 (r1cs::valuation-binds-allp asg excess)
;;                 (bit-listp (lookup-equal-list excess asg))
;;                 (r1cs::r1cs-constraints-holdp
;;                  (identifier-from-bits-le-gadget excess) asg p))
;;            (values-bits-all-zero-p (lookup-equal-list excess asg)))
;;   :enable (identifier-from-bits-le-gadget
;;            assert-bits-sum-zero-gadget
;;            val-sum-lc
;;            values-bits-all-zero-p
;;            r1cs::r1cs-constraint-holdsp
;;            r1cs::dot-product
;;            lookup-equal-list))

(local
 (defun val-bits-sum (xs)
   (if (endp xs)
       0
     (+ (ifix (car xs)) (val-bits-sum (cdr xs))))))

(local
 (defruled dot-product-of-val-sum-lc
   (implies (and (symbol-listp xs)
                 (primep p)
                 (r1cs::r1cs-valuationp asg p)
                 (r1cs::valuation-binds-allp asg xs))
            (equal (r1cs::dot-product (val-sum-lc xs) asg p)
                   (mod (val-bits-sum (lookup-equal-list xs asg)) p)))
   :induct (val-sum-lc xs)
   :enable (val-sum-lc
            r1cs::dot-product
            lookup-equal-list
            r1cs::valuation-binds-allp
            pfield::add
            acl2::mod-of-+-of-mod-arg2)))

(local
 (defthm natp-of-val-bits-sum
   (implies (bit-listp l)
            (natp (val-bits-sum l)))
   :rule-classes :type-prescription))

(local
 (defruled val-bits-sum-bound
   (implies (bit-listp l)
            (<= (val-bits-sum l) (len l)))
   :rule-classes :linear))

(local
 (defruled val-bits-sum-zero-iff-all-zero
   (implies (bit-listp l)
            (equal (equal (val-bits-sum l) 0)
                   (values-bits-all-zero-p l)))
   :enable values-bits-all-zero-p))

(defruled identifier-from-bits-le-gadget-sound-bounded
  (implies (and (symbol-listp excess)
                (< (len excess) (base-prime))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (r1cs::r1cs-constraints-holdp
                 (identifier-from-bits-le-gadget excess) asg p))
           (values-bits-all-zero-p (lookup-equal-list excess asg)))
  :hints (("Goal"
           :use ((:instance val-bits-sum-bound
                            (l (lookup-equal-list excess asg)))
                 (:instance val-bits-sum-zero-iff-all-zero
                            (l (lookup-equal-list excess asg))))
           :in-theory (enable identifier-from-bits-le-gadget
                              assert-bits-sum-zero-gadget
                              dot-product-of-val-sum-lc
                              r1cs::r1cs-constraint-holdsp
                              r1cs::dot-product))))

(defruled identifier-from-bits-le-gadget-complete
  (implies (and (symbol-listp excess)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (values-bits-all-zero-p (lookup-equal-list excess asg)))
           (r1cs::r1cs-constraints-holdp
            (identifier-from-bits-le-gadget excess) asg p))
  :enable (identifier-from-bits-le-gadget
           assert-bits-sum-zero-gadget
           val-sum-lc
           values-bits-all-zero-p
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal-list))

(defconst *identifier-from-bits-le-sample*
  '((e0 . 0)))

(defruled identifier-from-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-from-bits-le-gadget '(e0))
   *identifier-from-bits-le-sample*
   (base-prime))
  :enable (identifier-from-bits-le-gadget
           assert-bits-sum-zero-gadget
           val-sum-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define identifier-from-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_from_bits_le(e0) := {
    (e0) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-from-bits-le-circuit)
            :pred identifier-from-bits-le-pred
            :prime prime)

(defruled identifier-from-bits-le-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp e0)
                (identifier-from-bits-le-pred e0 prime))
           (values-bits-all-zero-p (list e0)))
  :enable (identifier-from-bits-le-pred values-bits-all-zero-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-bits-be-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "from_bits_be reverses, then from_bits_le.  Reversal adds nothing."
  (identifier-from-bits-le-gadget excess))

(defruled identifier-from-bits-be-gadget-sound
  (implies (and (bit-listp bits)
                (symbol-listp excess)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (equal (lookup-equal-list excess asg) (nthcdr 248 (rev bits)))
                (r1cs::r1cs-constraints-holdp
                 (identifier-from-bits-be-gadget excess) asg p))
           (equal (identifier-literal-from-bits-be bits)
                  (identifier-literal-from-bits-le (rev bits))))
  :enable identifier-literal-from-bits-be)

(defruled identifier-from-bits-be-gadget-complete
  (implies (and (symbol-listp excess)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (bit-listp (lookup-equal-list excess asg))
                (values-bits-all-zero-p (lookup-equal-list excess asg)))
           (r1cs::r1cs-constraints-holdp
            (identifier-from-bits-be-gadget excess) asg p))
  :enable (identifier-from-bits-be-gadget
           identifier-from-bits-le-gadget-complete))

(defconst *identifier-from-bits-be-sample* *identifier-from-bits-le-sample*)

(defruled identifier-from-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-from-bits-be-gadget '(e0))
   *identifier-from-bits-be-sample*
   (base-prime))
  :enable (identifier-from-bits-be-gadget
           identifier-from-bits-le-sample-holds))

(define identifier-from-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_from_bits_be(e0) := {
    (e0) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-from-bits-be-circuit)
            :pred identifier-from-bits-be-pred
            :prime prime)

(defruled identifier-from-bits-be-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp e0)
                (identifier-from-bits-be-pred e0 prime))
           (values-bits-all-zero-p (list e0)))
  :enable (identifier-from-bits-be-pred values-bits-all-zero-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-field-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "from_field is from_bits_le of Field::to_bits_le.  The field
          decomposition is the field gadget; the extra check is the excess-zero assert."
  (identifier-from-bits-le-gadget excess))

(defruled identifier-from-field-gadget-sound
  (implies (and (fieldp f)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-from-field-gadget nil) asg p))
           (equal (identifier-literal-from-field f)
                  (identifier-literal-from-bits-le (values-field-to-bits-le f))))
  :enable (identifier-from-field-gadget
           identifier-literal-from-field
           r1cs::r1cs-constraints-holdp))

(defruled identifier-from-field-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            (identifier-from-field-gadget nil) asg p))
  :enable identifier-from-field-gadget)

(defconst *identifier-from-field-sample* nil)

(defruled identifier-from-field-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-from-field-gadget nil)
   *identifier-from-field-sample*
   (base-prime))
  :enable (identifier-from-field-gadget val-string-empty-sample-holds))

(define identifier-from-field-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_from_field() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-from-field-circuit)
            :pred identifier-from-field-pred
            :prime prime)

(defruled identifier-from-field-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp f)
                (identifier-from-field-pred prime))
           (equal (identifier-literal-from-field f)
                  (identifier-literal-from-bits-le (values-field-to-bits-le f))))
  :enable (identifier-from-field-pred identifier-literal-from-field))
