; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier and program-id constructors, program-id field packing,
; program-id to address (hash abstracted), and OutputID constructors.

(in-package "ALEOVM")

(include-book "prog-primitives")
(include-book "prog-equal")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/crypto-response")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-public-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: @('Identifier::public') is @('Field::new') of the
          same field element."
  nil)

(defruled identifier-public-gadget-sound
  (implies (and (identifierp id)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (identifier-public-gadget) asg p))
           (equal (identifier-public id) (identifier-fix id)))
  :enable (identifier-public-gadget identifier-public))

(defruled identifier-public-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            (identifier-public-gadget) asg p))
  :enable identifier-public-gadget)

(defconst *identifier-public-sample-asg* nil)

(defruled identifier-public-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-public-gadget) *identifier-public-sample-asg* 5)
  :enable (identifier-public-gadget r1cs::r1cs-constraints-holdp))

(define identifier-public-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_public() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-public-circuit)
            :pred identifier-public-pred
            :prime prime)

(defruled identifier-public-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (identifierp id))
           (and (identifier-public-pred prime)
                (equal (identifier-public id) (identifier-fix id))))
  :enable (identifier-public-pred identifier-public))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-public-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: both identifiers are injected as public fields."
  nil)

(defruled program-id-public-gadget-sound
  (implies (and (program-idp id)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (program-id-public-gadget) asg p))
           (equal (program-id-public id)
                  (make-program-id
                   :name (identifier-public (program-id->name id))
                   :network (identifier-public (program-id->network id)))))
  :enable (program-id-public-gadget program-id-public))

(defruled program-id-public-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (program-id-public-gadget) asg p))
  :enable program-id-public-gadget)

(defconst *program-id-public-sample-asg* nil)

(defruled program-id-public-sample-holds
  (r1cs::r1cs-constraints-holdp
   (program-id-public-gadget) *program-id-public-sample-asg* 5)
  :enable (program-id-public-gadget r1cs::r1cs-constraints-holdp))

(define program-id-public-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "program_id_public() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (program-id-public-circuit)
            :pred program-id-public-pred
            :prime prime)

(defruled program-id-public-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (program-idp id))
           (and (program-id-public-pred prime)
                (equal (program-id-public id)
                       (make-program-id
                        :name (identifier-public (program-id->name id))
                        :network (identifier-public (program-id->network id))))))
  :enable (program-id-public-pred program-id-public))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: @('to_field') on an identifier is its field element."
  nil)

(defruled program-id-to-fields-gadget-sound
  (implies (and (program-idp id)
                (symbolp n) (symbolp w)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg n)
                (r1cs::valuation-bindsp asg w)
                (equal (lookup-equal n asg)
                       (identifier->field (program-id->name id)))
                (equal (lookup-equal w asg)
                       (identifier->field (program-id->network id)))
                (r1cs::r1cs-constraints-holdp
                 (program-id-to-fields-gadget) asg p))
           (equal (list (lookup-equal n asg) (lookup-equal w asg))
                  (program-id-to-fields id)))
  :enable (program-id-to-fields-gadget
           program-id-to-fields
           identifier-to-field))

(defruled program-id-to-fields-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            (program-id-to-fields-gadget) asg p))
  :enable program-id-to-fields-gadget)

(defconst *program-id-to-fields-sample-asg* '((n . 1) (w . 2)))

(defruled program-id-to-fields-sample-holds
  (r1cs::r1cs-constraints-holdp
   (program-id-to-fields-gadget) *program-id-to-fields-sample-asg* 5)
  :enable (program-id-to-fields-gadget r1cs::r1cs-constraints-holdp))

(define program-id-to-fields-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "program_id_to_fields() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (program-id-to-fields-circuit)
            :pred program-id-to-fields-pred
            :prime prime)

(defruled program-id-to-fields-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (program-idp id)
                (equal n (identifier->field (program-id->name id)))
                (equal w (identifier->field (program-id->network id))))
           (and (program-id-to-fields-pred prime)
                (equal (list n w) (program-id-to-fields id))))
  :enable (program-id-to-fields-pred
           program-id-to-fields
           identifier-to-field))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; HashToGroup is abstract. Address::from_group adds no constraint.

(define program-id-to-address-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No non-hash constraints. The group is
          @('hash_to_group_psd4') of the name and network fields."
  nil)

; Soundness is not claimed.  hash_to_group_psd4 is excluded, and the empty
; gadget does not determine the address.  A theorem that assumes
; (lookup-equal g asg) equals program-id-to-address and concludes the same
; equality is not an R1CS proof.

(defruled program-id-to-address-gadget-complete
  (implies (and (program-idp id)
                (symbolp g)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg g)
                (equal (lookup-equal g asg) (program-id-to-address id)))
           (r1cs::r1cs-constraints-holdp
            (program-id-to-address-gadget) asg p))
  :enable program-id-to-address-gadget)

(defconst *program-id-to-address-sample-asg* nil)

(defruled program-id-to-address-sample-holds
  (r1cs::r1cs-constraints-holdp
   (program-id-to-address-gadget) *program-id-to-address-sample-asg* 5)
  :enable (program-id-to-address-gadget r1cs::r1cs-constraints-holdp))

(define program-id-to-address-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "program_id_to_address() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (program-id-to-address-circuit)
            :pred program-id-to-address-pred
            :prime prime)

; The empty PFCS predicate does not mention the address, so it is not a
; specification of program-id-to-address.
(defruled program-id-to-address-pred-holds
  (implies (equal prime (base-prime))
           (program-id-to-address-pred prime))
  :enable program-id-to-address-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; OutputID::{public,private,future,external_record,dynamic_record,dynamic_future}
; each assert_eq a public injection with the expected field.

(define crypto-make-output-id-public-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraint of @('OutputID::public'): @('(out) (1) = (exp)')."
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-public-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-public-gadget out exp) asg p))
           (equal (crypto-make-output-id-public (lookup-equal exp asg))
                  (crypto-output-id-public (lookup-equal out asg))))
  :enable (crypto-make-output-id-public-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-public))

(defruled crypto-make-output-id-public-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-public-gadget out exp) asg p))
  :enable (crypto-make-output-id-public-gadget
           prog-assert-eq-gadget-to-equal))

(defconst *crypto-make-output-id-public-sample-asg* '((out . 4) (exp . 4)))

(defruled crypto-make-output-id-public-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-public-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-public-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-public-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_public(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-public-circuit)
            :pred crypto-make-output-id-public-pred
            :prime prime)

(defruled crypto-make-output-id-public-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out)
                (fieldp exp)
                (crypto-make-output-id-public-pred out exp prime))
           (equal (crypto-make-output-id-public exp)
                  (crypto-output-id-public out)))
  :enable (crypto-make-output-id-public-pred
           crypto-make-output-id-public))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-make-output-id-private-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-private-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-private-gadget out exp) asg p))
           (equal (crypto-make-output-id-private (lookup-equal exp asg))
                  (crypto-output-id-private (lookup-equal out asg))))
  :enable (crypto-make-output-id-private-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-private))

(defruled crypto-make-output-id-private-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-private-gadget out exp) asg p))
  :enable (crypto-make-output-id-private-gadget
           prog-assert-eq-gadget-to-equal))

(defruled crypto-make-output-id-private-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-private-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-private-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-private-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_private(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-private-circuit)
            :pred crypto-make-output-id-private-pred
            :prime prime)

(defruled crypto-make-output-id-private-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out) (fieldp exp)
                (crypto-make-output-id-private-pred out exp prime))
           (equal (crypto-make-output-id-private exp)
                  (crypto-output-id-private out)))
  :enable (crypto-make-output-id-private-pred
           crypto-make-output-id-private))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-make-output-id-future-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-future-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-future-gadget out exp) asg p))
           (equal (crypto-make-output-id-future (lookup-equal exp asg))
                  (crypto-output-id-future (lookup-equal out asg))))
  :enable (crypto-make-output-id-future-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-future))

(defruled crypto-make-output-id-future-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-future-gadget out exp) asg p))
  :enable (crypto-make-output-id-future-gadget
           prog-assert-eq-gadget-to-equal))

(defruled crypto-make-output-id-future-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-future-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-future-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-future-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_future(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-future-circuit)
            :pred crypto-make-output-id-future-pred
            :prime prime)

(defruled crypto-make-output-id-future-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out) (fieldp exp)
                (crypto-make-output-id-future-pred out exp prime))
           (equal (crypto-make-output-id-future exp)
                  (crypto-output-id-future out)))
  :enable (crypto-make-output-id-future-pred
           crypto-make-output-id-future))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-make-output-id-external-record-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-external-record-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-external-record-gadget out exp) asg p))
           (equal (crypto-make-output-id-external-record (lookup-equal exp asg))
                  (crypto-output-id-external-record (lookup-equal out asg))))
  :enable (crypto-make-output-id-external-record-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-external-record))

(defruled crypto-make-output-id-external-record-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-external-record-gadget out exp) asg p))
  :enable (crypto-make-output-id-external-record-gadget
           prog-assert-eq-gadget-to-equal))

(defruled crypto-make-output-id-external-record-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-external-record-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-external-record-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-external-record-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_external_record(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-external-record-circuit)
            :pred crypto-make-output-id-external-record-pred
            :prime prime)

(defruled crypto-make-output-id-external-record-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out) (fieldp exp)
                (crypto-make-output-id-external-record-pred out exp prime))
           (equal (crypto-make-output-id-external-record exp)
                  (crypto-output-id-external-record out)))
  :enable (crypto-make-output-id-external-record-pred
           crypto-make-output-id-external-record))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-make-output-id-dynamic-record-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-dynamic-record-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-dynamic-record-gadget out exp) asg p))
           (equal (crypto-make-output-id-dynamic-record (lookup-equal exp asg))
                  (crypto-output-id-dynamic-record (lookup-equal out asg))))
  :enable (crypto-make-output-id-dynamic-record-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-dynamic-record))

(defruled crypto-make-output-id-dynamic-record-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-dynamic-record-gadget out exp) asg p))
  :enable (crypto-make-output-id-dynamic-record-gadget
           prog-assert-eq-gadget-to-equal))

(defruled crypto-make-output-id-dynamic-record-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-dynamic-record-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-dynamic-record-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-dynamic-record-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_dynamic_record(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-dynamic-record-circuit)
            :pred crypto-make-output-id-dynamic-record-pred
            :prime prime)

(defruled crypto-make-output-id-dynamic-record-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out) (fieldp exp)
                (crypto-make-output-id-dynamic-record-pred out exp prime))
           (equal (crypto-make-output-id-dynamic-record exp)
                  (crypto-output-id-dynamic-record out)))
  :enable (crypto-make-output-id-dynamic-record-pred
           crypto-make-output-id-dynamic-record))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-make-output-id-dynamic-future-gadget ((out symbolp) (exp symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (prog-assert-eq-gadget out exp))

(defruled crypto-make-output-id-dynamic-future-gadget-sound
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-make-output-id-dynamic-future-gadget out exp) asg p))
           (equal (crypto-make-output-id-dynamic-future (lookup-equal exp asg))
                  (crypto-output-id-dynamic-future (lookup-equal out asg))))
  :enable (crypto-make-output-id-dynamic-future-gadget
           prog-assert-eq-gadget-to-equal
           crypto-make-output-id-dynamic-future))

(defruled crypto-make-output-id-dynamic-future-gadget-complete
  (implies (and (symbolp out) (symbolp exp)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg exp)
                (fieldp (lookup-equal out asg))
                (fieldp (lookup-equal exp asg))
                (equal (lookup-equal out asg) (lookup-equal exp asg)))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-dynamic-future-gadget out exp) asg p))
  :enable (crypto-make-output-id-dynamic-future-gadget
           prog-assert-eq-gadget-to-equal))

(defruled crypto-make-output-id-dynamic-future-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-dynamic-future-gadget 'out 'exp)
   *crypto-make-output-id-public-sample-asg*
   5)
  :enable (crypto-make-output-id-dynamic-future-gadget
           prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-make-output-id-dynamic-future-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_make_output_id_dynamic_future(out, exp) := {
    (out) * (1) == (exp)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-make-output-id-dynamic-future-circuit)
            :pred crypto-make-output-id-dynamic-future-pred
            :prime prime)

(defruled crypto-make-output-id-dynamic-future-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp out) (fieldp exp)
                (crypto-make-output-id-dynamic-future-pred out exp prime))
           (equal (crypto-make-output-id-dynamic-future exp)
                  (crypto-output-id-dynamic-future out)))
  :enable (crypto-make-output-id-dynamic-future-pred
           crypto-make-output-id-dynamic-future))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; OutputID::record.  Commitment and checksum are assert_eq.
; The sender ciphertext is accepted when it equals the expected value
; OR it is zero.  See bugs-prog.txt.

(define crypto-make-output-id-record-gadget
  ((oc symbolp) (ec symbolp)
   (ok symbolp) (ek symbolp)
   (os symbolp) (es symbolp)
   (m-eq symbolp) (r-eq symbolp)
   (m-z symbolp) (r-z symbolp)
   (or-bit symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('OutputID::record'): assert_eq on commitment and
          checksum; field inequality of the sender ciphertext with the
          expected value and with zero; OR of the equal-bit and the
          zero-bit; assert of that OR."
  (append (prog-assert-eq-gadget oc ec)
          (prog-assert-eq-gadget ok ek)
          (prog-field-neq-gadget os es m-eq r-eq p)
          (crypto-record-is-hiding-gadget os m-z r-z p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 r-eq))
                 :b (list (list 1 r-z))
                 :c (list (list 1 1)
                          (list (1- p) or-bit))))
          (prog-assert-gadget or-bit)))

(defruled crypto-make-output-id-record-gadget-complete
  :short "Completeness for snarkVM's witness, which sets the public
          ciphertext equal to the expected one."
  (implies (and (symbolp oc) (symbolp ec)
                (symbolp ok) (symbolp ek)
                (symbolp os) (symbolp es)
                (symbolp m-eq) (symbolp r-eq)
                (symbolp m-z) (symbolp r-z)
                (symbolp or-bit)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg oc)
                (r1cs::valuation-bindsp asg ec)
                (r1cs::valuation-bindsp asg ok)
                (r1cs::valuation-bindsp asg ek)
                (r1cs::valuation-bindsp asg os)
                (r1cs::valuation-bindsp asg es)
                (r1cs::valuation-bindsp asg m-eq)
                (r1cs::valuation-bindsp asg r-eq)
                (r1cs::valuation-bindsp asg m-z)
                (r1cs::valuation-bindsp asg r-z)
                (r1cs::valuation-bindsp asg or-bit)
                (fieldp (lookup-equal oc asg))
                (fieldp (lookup-equal ec asg))
                (fieldp (lookup-equal ok asg))
                (fieldp (lookup-equal ek asg))
                (fieldp (lookup-equal os asg))
                (fieldp (lookup-equal es asg))
                (equal (lookup-equal oc asg) (lookup-equal ec asg))
                (equal (lookup-equal ok asg) (lookup-equal ek asg))
                (equal (lookup-equal os asg) (lookup-equal es asg))
                (equal (lookup-equal r-eq asg)
                       (if (equal (lookup-equal os asg)
                                  (lookup-equal es asg))
                           0 1))
                (equal (lookup-equal m-eq asg)
                       (if (equal (lookup-equal os asg)
                                  (lookup-equal es asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal os asg)
                                                   (lookup-equal es asg) p)
                                      p)))
                (equal (lookup-equal r-z asg)
                       (if (equal (lookup-equal os asg) 0) 0 1))
                (equal (lookup-equal m-z asg)
                       (if (equal (lookup-equal os asg) 0)
                           1
                         (pfield::inv (lookup-equal os asg) p)))
                (equal (lookup-equal or-bit asg) 1))
           (r1cs::r1cs-constraints-holdp
            (crypto-make-output-id-record-gadget
             oc ec ok ek os es m-eq r-eq m-z r-z or-bit p)
            asg p))
  :hints (("Goal"
           :in-theory (e/d (crypto-make-output-id-record-gadget
                            prog-assert-eq-gadget-to-equal
                            prog-field-neq-gadget-to-spec
                            prog-field-neq-constraints-when-witness
                            crypto-record-is-hiding-gadget-to-spec
                            prog-assert-gadget-to-funspec
                            assert-funspec
                            enforce-funspec
                            field-is-not-equal-funspec
                            fieldp
                            bitp
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defconst *crypto-make-output-id-record-sample-asg*
  '((oc . 4) (ec . 4) (ok . 2) (ek . 2)
    (os . 3) (es . 3) (m-eq . 1) (r-eq . 0)
    (m-z . 2) (r-z . 1) (or-bit . 1)))

(defruled crypto-make-output-id-record-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-make-output-id-record-gadget
    'oc 'ec 'ok 'ek 'os 'es 'm-eq 'r-eq 'm-z 'r-z 'or-bit 5)
   *crypto-make-output-id-record-sample-asg*
   5)
  :enable (crypto-make-output-id-record-gadget
           prog-assert-eq-gadget
           prog-field-neq-gadget
           crypto-record-is-hiding-gadget
           prog-assert-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))
