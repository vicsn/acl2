; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS and samples for Field::is_zero and Field::is_one.
;
; The R1CS gadgets and their soundness and completeness are in
; field-zero-r1cs.lisp.  snarkVM implements both as is_equal against a
; constant, which emits the two is_not_equal constraints.  Negation of
; the result bit is the linear combination 1 - r.
;
; The witness multiplier is 1 when the difference has no inverse
; (snarkVM's console::Field::one fallback) and the inverse otherwise.
; Any multiplier works in the equal case; the completeness theorems in
; field-zero-r1cs.lisp use 0, which also satisfies the constraints.

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

(define fb-field-is-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::is_zero').  @('z') is the output bit."
  (pfcs::parse-def
   "field_is_zero(x, z) := {
    (x) * (m) == (1 - z),
    (x) * (z) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-is-zero-circuit)
            :pred fb-field-is-zero-pred
            :prime prime)

(defruled fb-field-is-zero-pred-sound
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime)
                (fb-field-is-zero-pred x z prime))
           (equal (field-is-zero-funspec x) z))
  :enable (fb-field-is-zero-pred
           field-is-zero-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb-field-is-zero-pred-complete
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime)
                (equal z (field-is-zero-funspec x))
                (equal m (if (equal x 0)
                             1
                           (pfield::inv x prime))))
           (fb-field-is-zero-pred x z prime))
  :enable (field-is-zero-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance fb-field-is-zero-pred-suff (m m)))

(defruled fb-field-is-zero-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime))
           (equal (fb-field-is-zero-pred x z prime)
                  (equal z (field-is-zero-funspec x))))
  :use (fb-field-is-zero-pred-sound
        (:instance fb-field-is-zero-pred-complete
                   (m (if (equal x 0)
                          1
                        (pfield::inv x prime))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-is-one-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::is_one').  @('z') is the output bit."
  (pfcs::parse-def
   "field_is_one(x, z) := {
    (x - 1) * (m) == (1 - z),
    (x - 1) * (z) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-is-one-circuit)
            :pred fb-field-is-one-pred
            :prime prime)

(defruled fb-field-is-one-pred-sound
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime)
                (fb-field-is-one-pred x z prime))
           (equal (field-is-one-funspec x) z))
  :enable (fb-field-is-one-pred
           field-is-one-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb-field-is-one-pred-complete
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime)
                (equal z (field-is-one-funspec x))
                (equal m (if (equal x 1)
                             1
                           (pfield::inv (pfield::sub x 1 prime) prime))))
           (fb-field-is-one-pred x z prime))
  :enable (field-is-one-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance fb-field-is-one-pred-suff (m m)))

(defruled fb-field-is-one-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep z prime))
           (equal (fb-field-is-one-pred x z prime)
                  (equal z (field-is-one-funspec x))))
  :use (fb-field-is-one-pred-sound
        (:instance fb-field-is-one-pred-complete
                   (m (if (equal x 1)
                          1
                        (pfield::inv (pfield::sub x 1 prime) prime))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; p = 5, x = 0, snarkVM multiplier m = 1, neq bit r = 0, output 1 - r = 1.

(defconst *fb-field-is-zero-asg*
  '((x . 0) (m . 1) (r . 0)))

(defconst *fb-field-is-zero-prime* 5)

(defrule fb-field-is-zero-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-zero-gadget 'x 'm 'r *fb-field-is-zero-prime*)
   *fb-field-is-zero-asg*
   *fb-field-is-zero-prime*)
  :enable (field-is-zero-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

; p = 5, x = 1, m = 1, r = 0, output 1.

(defconst *fb-field-is-one-asg*
  '((x . 1) (m . 1) (r . 0)))

(defconst *fb-field-is-one-prime* 5)

(defrule fb-field-is-one-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-one-gadget 'x 'm 'r *fb-field-is-one-prime*)
   *fb-field-is-one-asg*
   *fb-field-is-one-prime*)
  :enable (field-is-one-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
