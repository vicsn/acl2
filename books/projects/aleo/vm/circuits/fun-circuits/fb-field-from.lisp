; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::from and Field::from_boolean.
;
; Both are linear combinations, so the non-constant case emits no
; constraint.  The R1CS gadgets, soundness, and completeness are the
; empty gadgets in field-zero-r1cs.lisp.  This book adds the PFCS
; forms and a concrete R1CS sample for each.

(in-package "ALEOVM")

(include-book "field-zero-r1cs")
(include-book "../fun-specs/primitives-field")
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-from-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::from'): no constraints."
  (pfcs::parse-def
   "field_from(x) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-from-circuit)
            :pred fb-field-from-pred
            :prime prime)

(defruled fb-field-from-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x))
           (equal (fb-field-from-pred x prime)
                  (equal x (field-from-funspec x))))
  :enable (fb-field-from-pred field-from-funspec fieldp))

(defconst *fb-field-from-asg*
  '((x . 3)))

(defrule fb-field-from-sample
  (r1cs::r1cs-constraints-holdp
   (field-from-gadget)
   *fb-field-from-asg*
   5)
  :enable (field-from-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-from-boolean-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::from_boolean'): no constraints."
  (pfcs::parse-def
   "field_from_boolean(b) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-from-boolean-circuit)
            :pred fb-field-from-boolean-pred
            :prime prime)

(defruled fb-field-from-boolean-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b))
           (equal (fb-field-from-boolean-pred b prime)
                  (equal b (field-from-boolean-funspec b))))
  :enable (fb-field-from-boolean-pred
           field-from-boolean-funspec
           bitp))

(defconst *fb-field-from-boolean-asg*
  '((b . 1)))

(defrule fb-field-from-boolean-sample
  (r1cs::r1cs-constraints-holdp
   (field-from-boolean-gadget)
   *fb-field-from-boolean-asg*
   5)
  :enable (field-from-boolean-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
