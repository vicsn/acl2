; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS and samples for Boolean::adder and Boolean::subtractor.
;
; The R1CS gadgets and their soundness and completeness are in
; boolean-adder-r1cs.lisp.  They are the variable-variable xor, and, and
; or constraints.  Negation in the subtractor is a linear combination,
; so the PFCS inlines (1 - a) and (1 - c0) instead of a boolean-not
; constraint.  The R1CS form uses a public one variable; the relation is
; the same when that variable is 1.

(in-package "ALEOVM")

(include-book "boolean-adder-r1cs")
(include-book "../fun-specs/primitives-boolean")
(include-book "../pfcs/boolean-xor")
(include-book "../pfcs/boolean-and")
(include-book "../pfcs/boolean-or")
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb-fep-when-bitp
  (implies (and (bitp x)
                (primep p)
                (< 1 p))
           (pfield::fep x p))
  :enable (bitp pfield::fep))

(defruled fb-boolean-xor-spec-is-funspec
  (implies (and (bitp x) (bitp y) (bitp z))
           (equal (boolean-xor-spec x y z prime)
                  (equal z (boolean-xor-funspec x y))))
  :enable (boolean-xor-spec boolean-xor-funspec bitp))

(defruled fb-boolean-and-spec-is-funspec
  (implies (and (bitp x) (bitp y) (bitp z))
           (equal (boolean-and-spec x y z prime)
                  (equal z (boolean-and-funspec x y))))
  :enable (boolean-and-spec boolean-and-funspec bitp))

(defruled fb-boolean-or-spec-is-funspec
  (implies (and (bitp x) (bitp y) (bitp z))
           (equal (boolean-or-spec x y z prime)
                  (equal z (boolean-or-funspec x y))))
  :enable (boolean-or-spec boolean-or-funspec bitp))

(defruled fb-and-not-left-equation
  (implies (and (primep prime)
                (< 1 prime)
                (bitp a)
                (bitp b)
                (bitp c))
           (equal (equal (pfield::mul (pfield::sub 1 a prime) b prime) c)
                  (equal c (boolean-and-funspec (boolean-not-funspec a) b))))
  :enable (boolean-and-funspec boolean-not-funspec bitp pfield::fep)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1))

(defruled fb-and-not-right-equation
  (implies (and (primep prime)
                (< 1 prime)
                (bitp a)
                (bitp b)
                (bitp c))
           (equal (equal (pfield::mul a (pfield::sub 1 b prime) prime) c)
                  (equal c (boolean-and-funspec a (boolean-not-funspec b)))))
  :enable (boolean-and-funspec boolean-not-funspec bitp pfield::fep)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-boolean-adder-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Boolean::adder')."
  (pfcs::parse-def
   "boolean_adder(a, b, carry, c0, sum, c1, c2, carry_out) := {
    boolean_xor(a, b, c0),
    boolean_xor(c0, carry, sum),
    boolean_and(a, b, c1),
    boolean_and(carry, c0, c2),
    boolean_or(c1, c2, carry_out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-boolean-adder-circuit)
            :pred fb-boolean-adder-pred
            :prime prime)

(defruled fb-boolean-adder-pred-to-funspec
  (implies (and (primep prime)
                (< 1 prime)
                (equal prime (base-prime))
                (bitp a) (bitp b) (bitp carry)
                (bitp c0) (bitp sum)
                (bitp c1) (bitp c2) (bitp carry-out))
           (equal (fb-boolean-adder-pred a b carry c0 sum c1 c2 carry-out
                                         prime)
                  (and (equal c0 (boolean-xor-funspec a b))
                       (equal sum (boolean-xor-funspec c0 carry))
                       (equal c1 (boolean-and-funspec a b))
                       (equal c2 (boolean-and-funspec carry c0))
                       (mv-let (s co)
                         (boolean-adder-funspec a b carry)
                         (and (equal sum s)
                              (equal carry-out co))))))
  :enable (fb-boolean-adder-pred
           boolean-xor-pred-to-spec
           boolean-and-pred-to-spec
           boolean-or-pred-to-spec
           fb-boolean-xor-spec-is-funspec
           fb-boolean-and-spec-is-funspec
           fb-boolean-or-spec-is-funspec
           fb-fep-when-bitp
           boolean-adder-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-boolean-subtractor-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Boolean::subtractor').
          @('(1 - a)') and @('(1 - c0)') are linear combinations."
  (pfcs::parse-def
   "boolean_subtractor(a, b, borrow, c0, difference, c1, c2, borrow_out) := {
    boolean_xor(a, b, c0),
    boolean_xor(c0, borrow, difference),
    (1 - a) * (b) == (c1),
    (borrow) * (1 - c0) == (c2),
    boolean_or(c1, c2, borrow_out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-boolean-subtractor-circuit)
            :pred fb-boolean-subtractor-pred
            :prime prime)

(defruled fb-boolean-subtractor-pred-to-funspec
  (implies (and (primep prime)
                (< 1 prime)
                (equal prime (base-prime))
                (bitp a) (bitp b) (bitp borrow)
                (bitp c0) (bitp difference)
                (bitp c1) (bitp c2) (bitp borrow-out))
           (equal (fb-boolean-subtractor-pred
                   a b borrow c0 difference c1 c2 borrow-out prime)
                  (and (equal c0 (boolean-xor-funspec a b))
                       (equal difference (boolean-xor-funspec c0 borrow))
                       (equal c1 (boolean-and-funspec
                                  (boolean-not-funspec a) b))
                       (equal c2 (boolean-and-funspec
                                  borrow (boolean-not-funspec c0)))
                       (mv-let (d bo)
                         (boolean-subtractor-funspec a b borrow)
                         (and (equal difference d)
                              (equal borrow-out bo))))))
  :enable (fb-boolean-subtractor-pred
           boolean-xor-pred-to-spec
           boolean-or-pred-to-spec
           fb-boolean-xor-spec-is-funspec
           fb-boolean-or-spec-is-funspec
           fb-and-not-left-equation
           fb-and-not-right-equation
           fb-fep-when-bitp
           boolean-subtractor-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 1 + 1 + 1 = sum 1, carry 1.  Prime 5.

(defconst *fb-boolean-adder-asg*
  '((a . 1) (b . 1) (carry . 1)
    (c0 . 0) (sum . 1) (c1 . 1) (c2 . 0) (carry-out . 1)))

(defconst *fb-boolean-adder-prime* 5)

(defrule fb-boolean-adder-sample
  (r1cs::r1cs-constraints-holdp
   (boolean-adder-gadget 'a 'b 'carry 'c0 'sum 'c1 'c2 'carry-out
                         *fb-boolean-adder-prime*)
   *fb-boolean-adder-asg*
   *fb-boolean-adder-prime*)
  :enable (boolean-adder-gadget
           boolean-xor-gadget
           boolean-and-gadget
           boolean-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

; 1 - 1 - 1 = difference 1, borrow 1.

(defconst *fb-boolean-subtractor-asg*
  '((a . 1) (b . 1) (borrow . 1)
    (c0 . 0) (difference . 1) (c1 . 0) (c2 . 1)
    (borrow-out . 1) (one . 1)))

(defconst *fb-boolean-subtractor-prime* 5)

(defrule fb-boolean-subtractor-sample
  (r1cs::r1cs-constraints-holdp
   (boolean-subtractor-gadget 'a 'b 'borrow 'c0 'difference 'c1 'c2
                              'borrow-out 'one
                              *fb-boolean-subtractor-prime*)
   *fb-boolean-subtractor-asg*
   *fb-boolean-subtractor-prime*)
  :enable (boolean-subtractor-gadget
           boolean-xor-gadget
           boolean-and-notleft-gadget
           boolean-and-notright-gadget
           boolean-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
