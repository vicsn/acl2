; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS specifications of the environment constraint primitives.
; Each definition lowers to the R1CS gadget in environment-r1cs.lisp.
; Soundness and completeness are the equivalence of the lifted predicate
; with the funspec (assert_neq includes the witness multiplier).

(in-package "ALEOVM")

(include-book "environment-r1cs")
(include-book "../fun-specs/primitives-environment")
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define env-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('E::enforce'): @($(a) (b) = (c)$)."
  (pfcs::parse-def
   "env_enforce(a, b, c) := {
    (a) * (b) == (c)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (env-enforce-circuit)
            :pred env-enforce-pred
            :prime prime)

(defruled env-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a)
                (fieldp b)
                (fieldp c))
           (equal (env-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (env-enforce-pred enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define env-assert-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('E::assert'): @($(b) (1) = (1)$)."
  (pfcs::parse-def
   "env_assert(b) := {
    (b) * (1) == (1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (env-assert-circuit)
            :pred env-assert-pred
            :prime prime)

(defruled env-assert-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp b))
           (equal (env-assert-pred b prime)
                  (assert-funspec b)))
  :enable (env-assert-pred assert-funspec enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define env-assert-eq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('E::assert_eq'): @($(a) (1) = (b)$)."
  (pfcs::parse-def
   "env_assert_eq(a, b) := {
    (a) * (1) == (b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (env-assert-eq-circuit)
            :pred env-assert-eq-pred
            :prime prime)

(defruled env-assert-eq-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a)
                (fieldp b))
           (equal (env-assert-eq-pred a b prime)
                  (assert-eq-funspec a b)))
  :enable (env-assert-eq-pred assert-eq-funspec enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define env-assert-neq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('E::assert_neq'): @($(a - b) (m) = (1)$)."
  (pfcs::parse-def
   "env_assert_neq(a, b, m) := {
    (a - b) * (m) == (1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (env-assert-neq-circuit)
            :pred env-assert-neq-pred
            :prime prime)

(defruled env-assert-neq-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep a prime)
                (pfield::fep b prime)
                (pfield::fep m prime))
           (equal (env-assert-neq-pred a b m prime)
                  (equal (pfield::mul (pfield::sub a b prime) m prime) 1)))
  :enable env-assert-neq-pred)

(defruled env-assert-neq-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp a)
                (fieldp b)
                (pfield::fep m prime)
                (env-assert-neq-pred a b m prime))
           (assert-neq-funspec a b))
  :enable (env-assert-neq-pred-to-mul
           assert-neq-funspec-when-inverse-exists
           fieldp))

(defruled env-assert-neq-pred-complete
  (implies (and (equal prime (base-prime))
                (fieldp a)
                (fieldp b)
                (assert-neq-funspec a b)
                (equal m (pfield::inv (pfield::sub a b prime) prime)))
           (env-assert-neq-pred a b m prime))
  :enable (env-assert-neq-pred-to-mul
           assert-neq-funspec
           enforce-funspec
           fieldp))
