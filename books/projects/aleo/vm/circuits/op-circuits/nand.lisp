; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Opcode-level circuit specification (OP-CIRC-SPEC) of the Aleo Instructions
; opcode `nand`, and its completeness (CIRC-COMPLETE) and soundness
; (CIRC-SOUND) with respect to the functional specification (OP-FUN-SPEC)
; boolean-nand--fun in ../samples/boolean.lisp.
;
; The `nand` instruction has the single signature (boolean, boolean) => boolean
; (synthesizer/program/src/logic/instruction/operation/mod.rs, NandOperation)
; and applies Boolean::nand to the two operands
; (circuit/types/boolean/src/nand.rs), which distinguishes these cases:
;   - first operand constant:
;       if its value is true, the result is !second,
;       otherwise the result is !first (the constant true);
;   - second operand constant (first operand not constant):
;       if its value is true, the result is !first,
;       otherwise the result is !second (the constant true);
;   - both operands variable:
;       a new private variable w is allocated,
;       the constraint (first) * (second) = (1 - w) is enforced,
;       and the result is the LC w.
; Negation (!) is as formalized by reg-lc-not in registers.lisp.
; No constraints are generated in the constant cases.

(in-package "ALEOVM")

(include-book "registers")
(include-book "projects/aleo/vm/circuits/samples/boolean" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/alists-light/lookup-eq" :dir :system))
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/number-theory/primes" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OP-CIRC-SPEC.

; Given the LCs a and b of the two operand registers,
; the name w for the variable that snarkVM may allocate,
; and the prime p,
; return the generated constraints and the LC of the destination register.

(define nand-circuit ((a r1cs::sparse-vectorp)
                      (b r1cs::sparse-vectorp)
                      (w symbolp)
                      (p primep))
  :returns (mv (constrs r1cs::r1cs-constraint-listp
                        :hyp (and (r1cs::sparse-vectorp a)
                                  (r1cs::sparse-vectorp b)
                                  (symbolp w)
                                  (posp p)))
               (out r1cs::sparse-vectorp
                    :hyp (and (r1cs::sparse-vectorp a)
                              (r1cs::sparse-vectorp b)
                              (symbolp w)
                              (posp p))))
  (cond ((reg-lc-constantp a)
         (if (equal (reg-lc-constant-value a p) 1)
             (mv nil (reg-lc-not b p))
           (mv nil (reg-lc-not a p))))
        ((reg-lc-constantp b)
         (if (equal (reg-lc-constant-value b p) 1)
             (mv nil (reg-lc-not a p))
           (mv nil (reg-lc-not b p))))
        (t (mv (list (r1cs::make-r1cs-constraint
                      :a a
                      :b b
                      :c (reg-lc-not (reg-lc-var w) p)))
               (reg-lc-var w)))))

; The C vector of the constraint in the variable case is
; snarkVM's `E::one() - w`, i.e. ((1 1) (p-1 w)).

(defruled reg-lc-not-of-reg-lc-var-explicit
  (implies (and (symbolp w)
                (primep p))
           (equal (reg-lc-not (reg-lc-var w) p)
                  (list (list 1 1) (list (1- p) w))))
  :enable (reg-lc-not reg-lc-neg-terms reg-lc-var pfield::neg)
  :use not-reg-lc-constantp-of-reg-lc-var)

; The witness assignment that snarkVM computes:
; in the variable case, w is bound to the negated conjunction of the operands
; (computed as !(a.eject_value() & b.eject_value()));
; in the constant cases no variable is allocated.

(define nand-circuit-witness ((a r1cs::sparse-vectorp)
                              (b r1cs::sparse-vectorp)
                              (w symbolp)
                              (asg (r1cs::r1cs-valuationp asg p))
                              (p primep))
  :guard (and (r1cs::good-sparse-vectorp a (strip-cars asg))
              (r1cs::good-sparse-vectorp b (strip-cars asg))
              (reg-lc-booleanp a asg p)
              (reg-lc-booleanp b asg p))
  (if (or (reg-lc-constantp a)
          (reg-lc-constantp b))
      asg
    (cons (cons w (boolean-nand--fun (reg-lc-value a asg p)
                                     (reg-lc-value b asg p)))
          asg))
  :guard-hints (("Goal" :in-theory (enable boolean-nand--pre reg-lc-booleanp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OP-FUN-SPEC is total on booleans.

; boolean-nand--fun returns a boolean for all boolean inputs,
; so there are no error inputs,
; and the error clause of CIRC-COMPLETE is vacuous.

(defruled boolean-nand--fun-total
  (implies (boolean-nand--pre x y)
           (bitp (boolean-nand--fun x y)))
  :enable (boolean-nand--fun))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CIRC-COMPLETE.

; For every prime p,
; every assignment asg under which the operand LCs are boolean-valued,
; and every variable w not bound by asg and not occurring in the operand LCs,
; the witness assignment extends asg, is a valuation,
; preserves the operand values,
; satisfies the generated constraints,
; and gives the output LC the value of the functional specification.

(defruled nand-circuit-complete
  (implies (and (primep p)
                (r1cs::sparse-vectorp a)
                (r1cs::sparse-vectorp b)
                (symbolp w)
                (r1cs::r1cs-valuationp asg p)
                (not (r1cs::valuation-bindsp asg w))
                (not (member-equal w (reg-lc-vars a)))
                (not (member-equal w (reg-lc-vars b)))
                (reg-lc-booleanp a asg p)
                (reg-lc-booleanp b asg p))
           (b* ((x (reg-lc-value a asg p))
                (y (reg-lc-value b asg p))
                ((mv constrs out) (nand-circuit a b w p))
                (asg2 (nand-circuit-witness a b w asg p)))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (valuation-extendsp asg2 asg)
                  (equal (reg-lc-value a asg2 p) x)
                  (equal (reg-lc-value b asg2 p) y)
                  (r1cs::r1cs-constraints-holdp constrs asg2 p)
                  (equal (reg-lc-value out asg2 p)
                         (boolean-nand--fun x y)))))
  :enable (nand-circuit
           nand-circuit-witness
           reg-lc-booleanp
           boolean-nand--fun
           bitp)
  :use ((:instance reg-lc-value-when-reg-lc-constantp (lc a))
        (:instance reg-lc-value-when-reg-lc-constantp (lc b))))

; The same, phrased for every valid I/O pair of the functional specification:
; if z is the result of the functional specification on the operand values,
; there exists an assignment extending asg
; that satisfies the constraints and gives the output LC the value z.

(defun-sk nand-circuit-satisfiable-with-output (a b w asg z p)
  (exists asg2
          (and (r1cs::r1cs-valuationp asg2 p)
               (valuation-extendsp asg2 asg)
               (equal (reg-lc-value a asg2 p) (reg-lc-value a asg p))
               (equal (reg-lc-value b asg2 p) (reg-lc-value b asg p))
               (r1cs::r1cs-constraints-holdp (mv-nth 0 (nand-circuit a b w p))
                                             asg2
                                             p)
               (equal (reg-lc-value (mv-nth 1 (nand-circuit a b w p)) asg2 p)
                      z))))

(defruled nand-circuit-complete-io
  (implies (and (primep p)
                (r1cs::sparse-vectorp a)
                (r1cs::sparse-vectorp b)
                (symbolp w)
                (r1cs::r1cs-valuationp asg p)
                (not (r1cs::valuation-bindsp asg w))
                (not (member-equal w (reg-lc-vars a)))
                (not (member-equal w (reg-lc-vars b)))
                (reg-lc-booleanp a asg p)
                (reg-lc-booleanp b asg p)
                (equal z (boolean-nand--fun (reg-lc-value a asg p)
                                            (reg-lc-value b asg p))))
           (nand-circuit-satisfiable-with-output a b w asg z p))
  :use (nand-circuit-complete
        (:instance nand-circuit-satisfiable-with-output-suff
                   (asg2 (nand-circuit-witness a b w asg p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CIRC-SOUND.

; For every prime p and every assignment asg
; under which the operand LCs are boolean-valued
; and the generated constraints hold,
; the output LC has the value of the functional specification.

(defrulel equal-of-add-of-1-and-1
  (implies (and (integerp p)
                (< 1 p))
           (equal (equal (pfield::add 1 x p) 1)
                  (equal (mod (ifix x) p) 0)))
  :enable (pfield::add acl2::mod-sum-cases))

(defruled nand-circuit-sound
  (implies (and (primep p)
                (r1cs::sparse-vectorp a)
                (r1cs::sparse-vectorp b)
                (symbolp w)
                (reg-lc-booleanp a asg p)
                (reg-lc-booleanp b asg p))
           (b* ((x (reg-lc-value a asg p))
                (y (reg-lc-value b asg p))
                ((mv constrs out) (nand-circuit a b w p)))
             (implies (r1cs::r1cs-constraints-holdp constrs asg p)
                      (equal (reg-lc-value out asg p)
                             (boolean-nand--fun x y)))))
  :enable (nand-circuit
           reg-lc-booleanp
           boolean-nand--fun
           bitp)
  :use ((:instance reg-lc-value-when-reg-lc-constantp (lc a))
        (:instance reg-lc-value-when-reg-lc-constantp (lc b))))

; The output register is boolean-valued under every satisfying assignment.

(defruled nand-circuit-output-booleanp
  (implies (and (primep p)
                (r1cs::sparse-vectorp a)
                (r1cs::sparse-vectorp b)
                (symbolp w)
                (reg-lc-booleanp a asg p)
                (reg-lc-booleanp b asg p)
                (r1cs::r1cs-constraints-holdp (mv-nth 0 (nand-circuit a b w p))
                                              asg
                                              p))
           (reg-lc-booleanp (mv-nth 1 (nand-circuit a b w p)) asg p))
  :use nand-circuit-sound
  :enable (reg-lc-booleanp boolean-nand--fun))
