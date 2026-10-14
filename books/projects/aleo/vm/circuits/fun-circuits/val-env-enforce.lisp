; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; CanaryCircuit::enforce, TestnetCircuit::enforce, and
; AleoV0 / AleoCanaryV0 / AleoTestnetV0::enforce add the same
; (a) * (b) = (c) constraint as Circuit::enforce.  Constant triples are
; host-checked and add nothing.  Each delegate below is enforce-gadget.
; Soundness and completeness are enforce-gadget-to-funspec.
; The PFCS is env_enforce (the same parse, under a local name).
; The sample assignment is a = 2, b = 3, c = 6.

(in-package "ALEOVM")

(include-book "environment-r1cs")
(include-book "environment-pfcs")
(include-book "../fun-specs/curve-network")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *val-enforce-sample*
  '((a . 2) (b . 3) (c . 6)))

(defruled val-enforce-sample-holds
  (b* ((p (base-prime))
       (asg *val-enforce-sample*))
    (and (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-bindsp asg 'a)
         (r1cs::valuation-bindsp asg 'b)
         (r1cs::valuation-bindsp asg 'c)
         (r1cs::r1cs-constraints-holdp (enforce-gadget 'a 'b 'c) asg p)
         (enforce-funspec 2 3 6)))
  :enable (enforce-gadget
           enforce-gadget-to-mul
           enforce-funspec
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp
           r1cs::var-listp
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::fe-listp
           pfield::fep
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(defruled aleo-enforce-funspec-iff-enforce-funspec
  (implies (and (fieldp a) (fieldp b) (fieldp c))
           (iff (not (reserrp (aleo-enforce-funspec a b c)))
                (enforce-funspec a b c)))
  :enable (aleo-enforce-funspec enforce-funspec reserrp spec-error fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canary-circuit-enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "CanaryCircuit::enforce is Circuit::enforce."
  (enforce-gadget a b c))

(defruled canary-circuit-enforce-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (canary-circuit-enforce-gadget a b c) asg p))
           (enforce-funspec (lookup-equal a asg)
                            (lookup-equal b asg)
                            (lookup-equal c asg)))
  :enable (canary-circuit-enforce-gadget enforce-gadget-to-funspec))

(defruled canary-circuit-enforce-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (canary-circuit-enforce-gadget a b c) asg p))
  :enable (canary-circuit-enforce-gadget enforce-gadget-to-funspec))

(defconst *canary-circuit-enforce-sample* *val-enforce-sample*)

(defruled canary-circuit-enforce-sample-holds
  (r1cs::r1cs-constraints-holdp
   (canary-circuit-enforce-gadget 'a 'b 'c)
   *canary-circuit-enforce-sample*
   (base-prime))
  :enable (canary-circuit-enforce-gadget val-enforce-sample-holds))

(define canary-circuit-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "canary_circuit_enforce(a, b, c) := {
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

(pfcs::lift (canary-circuit-enforce-circuit)
            :pred canary-circuit-enforce-pred
            :prime prime)

(defruled canary-circuit-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a) (fieldp b) (fieldp c))
           (equal (canary-circuit-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (canary-circuit-enforce-pred enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define testnet-circuit-enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "TestnetCircuit::enforce is Circuit::enforce."
  (enforce-gadget a b c))

(defruled testnet-circuit-enforce-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (testnet-circuit-enforce-gadget a b c) asg p))
           (enforce-funspec (lookup-equal a asg)
                            (lookup-equal b asg)
                            (lookup-equal c asg)))
  :enable (testnet-circuit-enforce-gadget enforce-gadget-to-funspec))

(defruled testnet-circuit-enforce-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (testnet-circuit-enforce-gadget a b c) asg p))
  :enable (testnet-circuit-enforce-gadget enforce-gadget-to-funspec))

(defconst *testnet-circuit-enforce-sample* *val-enforce-sample*)

(defruled testnet-circuit-enforce-sample-holds
  (r1cs::r1cs-constraints-holdp
   (testnet-circuit-enforce-gadget 'a 'b 'c)
   *testnet-circuit-enforce-sample*
   (base-prime))
  :enable (testnet-circuit-enforce-gadget val-enforce-sample-holds))

(define testnet-circuit-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "testnet_circuit_enforce(a, b, c) := {
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

(pfcs::lift (testnet-circuit-enforce-circuit)
            :pred testnet-circuit-enforce-pred
            :prime prime)

(defruled testnet-circuit-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a) (fieldp b) (fieldp c))
           (equal (testnet-circuit-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (testnet-circuit-enforce-pred enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aleo-v0-enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "AleoV0::enforce delegates to E::enforce."
  (enforce-gadget a b c))

(defruled aleo-v0-enforce-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (aleo-v0-enforce-gadget a b c) asg p))
           (and (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg))
                (not (reserrp (aleo-enforce-funspec (lookup-equal a asg)
                                                    (lookup-equal b asg)
                                                    (lookup-equal c asg))))))
  :enable (aleo-v0-enforce-gadget
           enforce-gadget-to-funspec
           aleo-enforce-funspec-iff-enforce-funspec
           r1cs::fep-of-lookup-equal
           fieldp))

(defruled aleo-v0-enforce-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (aleo-v0-enforce-gadget a b c) asg p))
  :enable (aleo-v0-enforce-gadget enforce-gadget-to-funspec))

(defconst *aleo-v0-enforce-sample* *val-enforce-sample*)

(defruled aleo-v0-enforce-sample-holds
  (r1cs::r1cs-constraints-holdp
   (aleo-v0-enforce-gadget 'a 'b 'c)
   *aleo-v0-enforce-sample*
   (base-prime))
  :enable (aleo-v0-enforce-gadget val-enforce-sample-holds))

(define aleo-v0-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "aleo_v0_enforce(a, b, c) := {
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

(pfcs::lift (aleo-v0-enforce-circuit)
            :pred aleo-v0-enforce-pred
            :prime prime)

(defruled aleo-v0-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a) (fieldp b) (fieldp c))
           (equal (aleo-v0-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (aleo-v0-enforce-pred enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aleo-canary-v0-enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "AleoCanaryV0::enforce delegates to E::enforce."
  (enforce-gadget a b c))

(defruled aleo-canary-v0-enforce-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (aleo-canary-v0-enforce-gadget a b c) asg p))
           (enforce-funspec (lookup-equal a asg)
                            (lookup-equal b asg)
                            (lookup-equal c asg)))
  :enable (aleo-canary-v0-enforce-gadget enforce-gadget-to-funspec))

(defruled aleo-canary-v0-enforce-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (aleo-canary-v0-enforce-gadget a b c) asg p))
  :enable (aleo-canary-v0-enforce-gadget enforce-gadget-to-funspec))

(defconst *aleo-canary-v0-enforce-sample* *val-enforce-sample*)

(defruled aleo-canary-v0-enforce-sample-holds
  (r1cs::r1cs-constraints-holdp
   (aleo-canary-v0-enforce-gadget 'a 'b 'c)
   *aleo-canary-v0-enforce-sample*
   (base-prime))
  :enable (aleo-canary-v0-enforce-gadget val-enforce-sample-holds))

(define aleo-canary-v0-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "aleo_canary_v0_enforce(a, b, c) := {
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

(pfcs::lift (aleo-canary-v0-enforce-circuit)
            :pred aleo-canary-v0-enforce-pred
            :prime prime)

(defruled aleo-canary-v0-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a) (fieldp b) (fieldp c))
           (equal (aleo-canary-v0-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (aleo-canary-v0-enforce-pred enforce-funspec fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aleo-testnet-v0-enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "AleoTestnetV0::enforce delegates to E::enforce."
  (enforce-gadget a b c))

(defruled aleo-testnet-v0-enforce-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (aleo-testnet-v0-enforce-gadget a b c) asg p))
           (enforce-funspec (lookup-equal a asg)
                            (lookup-equal b asg)
                            (lookup-equal c asg)))
  :enable (aleo-testnet-v0-enforce-gadget enforce-gadget-to-funspec))

(defruled aleo-testnet-v0-enforce-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (aleo-testnet-v0-enforce-gadget a b c) asg p))
  :enable (aleo-testnet-v0-enforce-gadget enforce-gadget-to-funspec))

(defconst *aleo-testnet-v0-enforce-sample* *val-enforce-sample*)

(defruled aleo-testnet-v0-enforce-sample-holds
  (r1cs::r1cs-constraints-holdp
   (aleo-testnet-v0-enforce-gadget 'a 'b 'c)
   *aleo-testnet-v0-enforce-sample*
   (base-prime))
  :enable (aleo-testnet-v0-enforce-gadget val-enforce-sample-holds))

(define aleo-testnet-v0-enforce-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "aleo_testnet_v0_enforce(a, b, c) := {
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

(pfcs::lift (aleo-testnet-v0-enforce-circuit)
            :pred aleo-testnet-v0-enforce-pred
            :prime prime)

(defruled aleo-testnet-v0-enforce-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp a) (fieldp b) (fieldp c))
           (equal (aleo-testnet-v0-enforce-pred a b c prime)
                  (enforce-funspec a b c)))
  :enable (aleo-testnet-v0-enforce-pred enforce-funspec fieldp))
