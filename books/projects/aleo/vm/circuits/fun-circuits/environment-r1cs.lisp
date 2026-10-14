; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS specifications of snarkVM's environment constraint primitives.
;
; These are the circuits added by
;   circuit/environment/src/environment.rs  (assert, assert_eq, assert_neq)
;   circuit/environment/src/circuit.rs      (Circuit::enforce)
;   circuit/environment/src/canary_circuit.rs
;   circuit/environment/src/testnet_circuit.rs
;   circuit/network/src/{v0,canary_v0,testnet_v0}.rs  (Aleo*::enforce delegates)
;
; snarkVM adds the constraint only when at least one linear combination is
; non-constant.  A fully constant triple is checked in the host and adds
; nothing.  The gadgets below are the constraint that is added in every
; other case; the host check is the same predicate (see the funspecs).
; Constraint and density limits are not part of the gadget.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-environment")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (A) (B) = (C)

(define enforce-gadget ((a symbolp) (b symbolp) (c symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single constraint added by @('E::enforce(|| (A, B, C))')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a))
         :b (list (list 1 b))
         :c (list (list 1 c)))))

(defruled enforce-gadget-to-mul
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (c$ (lookup-equal c asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (enforce-gadget a b c) asg p)
                    (equal (pfield::mul a$ b$ p) c$))))
  :enable (enforce-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled enforce-gadget-to-funspec
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c))
           (equal (r1cs::r1cs-constraints-holdp
                   (enforce-gadget a b c) asg p)
                  (enforce-funspec (lookup-equal a asg)
                                   (lookup-equal b asg)
                                   (lookup-equal c asg))))
  :enable (enforce-gadget-to-mul enforce-funspec))

(defruled enforce-gadget-sound
  :short "R1CS-SOUND for @('enforce'): a satisfying assignment is a valid I/O."
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (r1cs::r1cs-constraints-holdp
                 (enforce-gadget a b c) asg p))
           (enforce-funspec (lookup-equal a asg)
                            (lookup-equal b asg)
                            (lookup-equal c asg)))
  :enable enforce-gadget-to-funspec)

(defruled enforce-gadget-complete
  :short "R1CS-COMPLETE for @('enforce'): a valid I/O satisfies the gadget.
          There is no witness.  If the funspec is false, no assignment of
          these variables satisfies the gadget."
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c)
                (enforce-funspec (lookup-equal a asg)
                                 (lookup-equal b asg)
                                 (lookup-equal c asg)))
           (r1cs::r1cs-constraints-holdp
            (enforce-gadget a b c) asg p))
  :enable enforce-gadget-to-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (b) (1) = (1)

(define assert-gadget ((b symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint added by @('E::assert(b)'), i.e. @($b \\cdot 1 = 1$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

(defruled assert-gadget-to-funspec
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (assert-gadget b) asg p)
                  (assert-funspec (lookup-equal b asg))))
  :enable (assert-gadget
           assert-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled assert-gadget-sound
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (r1cs::r1cs-constraints-holdp (assert-gadget b) asg p))
           (assert-funspec (lookup-equal b asg)))
  :enable assert-gadget-to-funspec)

(defruled assert-gadget-complete
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (assert-funspec (lookup-equal b asg)))
           (r1cs::r1cs-constraints-holdp (assert-gadget b) asg p))
  :enable assert-gadget-to-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (a) (1) = (b)

(define assert-eq-gadget ((a symbolp) (b symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint added by @('E::assert_eq(a, b)')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a))
         :b (list (list 1 1))
         :c (list (list 1 b)))))

(defruled assert-eq-gadget-to-funspec
  (implies (and (symbolp a)
                (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (assert-eq-gadget a b) asg p)
                  (assert-eq-funspec (lookup-equal a asg)
                                     (lookup-equal b asg))))
  :enable (assert-eq-gadget
           assert-eq-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled assert-eq-gadget-sound
  (implies (and (symbolp a)
                (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::r1cs-constraints-holdp
                 (assert-eq-gadget a b) asg p))
           (assert-eq-funspec (lookup-equal a asg)
                              (lookup-equal b asg)))
  :enable assert-eq-gadget-to-funspec)

(defruled assert-eq-gadget-complete
  (implies (and (symbolp a)
                (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (assert-eq-funspec (lookup-equal a asg)
                                   (lookup-equal b asg)))
           (r1cs::r1cs-constraints-holdp
            (assert-eq-gadget a b) asg p))
  :enable assert-eq-gadget-to-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (a - b) (m) = (1)
; m is the witness.  snarkVM sets it to (a - b)^{-1}, or 0 when a = b
; (in which case the constraint is unsatisfiable).

(define assert-neq-gadget ((a symbolp) (b symbolp) (m symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint added by @('E::assert_neq(a, b)')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a)
                  (list (1- p) b))
         :b (list (list 1 m))
         :c (list (list 1 1)))))

(defruled assert-neq-gadget-to-mul
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp m)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (m$ (lookup-equal m asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (assert-neq-gadget a b m p) asg p)
                    (equal (pfield::mul (pfield::sub a$ b$ p) m$ p) 1))))
  :enable (assert-neq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled assert-neq-funspec-when-inverse-exists
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (pfield::fep m p)
                (equal (pfield::mul (pfield::sub a b p) m p)
                       1))
           (assert-neq-funspec a b))
  :hints (("Goal"
           :in-theory (e/d (assert-neq-funspec
                            enforce-funspec
                            fieldp)
                           (pfield::sub
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-commutative))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub a b (base-prime)))
                            (p (base-prime)))
                 (:instance pfield::equal-of-0-and-sub
                            (x a)
                            (y b)
                            (p (base-prime)))))))

(defruled assert-neq-gadget-sound
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp m)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (assert-neq-gadget a b m p) asg p))
           (assert-neq-funspec (lookup-equal a asg)
                               (lookup-equal b asg)))
  :hints (("Goal"
           :use ((:instance assert-neq-funspec-when-inverse-exists
                            (a (lookup-equal a asg))
                            (b (lookup-equal b asg))
                            (m (lookup-equal m asg))
                            (p p)))
           :in-theory (e/d (assert-neq-gadget-to-mul
                            r1cs::fep-of-lookup-equal)
                           (pfield::sub
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-commutative)))))

(defruled assert-neq-gadget-complete
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp m)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (assert-neq-funspec (lookup-equal a asg)
                                    (lookup-equal b asg))
                (equal (lookup-equal m asg)
                       (pfield::inv (pfield::sub (lookup-equal a asg)
                                                 (lookup-equal b asg)
                                                 p)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (assert-neq-gadget a b m p) asg p))
  :hints (("Goal"
           :in-theory (e/d (assert-neq-gadget-to-mul
                            assert-neq-funspec
                            enforce-funspec
                            fieldp)
                           (pfield::sub
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            pfield::mul-commutative)))))
