; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A model of Aleo Instructions registers as linear combinations (LCs)
; of R1CS variables, for use in opcode-level circuit specifications.
;
; In snarkVM a circuit value (e.g. a Boolean) wraps a LinearCombination,
; which consists of a constant field element plus a list of
; (variable, coefficient) terms
; (see circuit/environment/src/helpers/linear_combination.rs
; and circuit/types/boolean/src/lib.rs).
; A register therefore holds an LC, not necessarily a single variable:
; e.g. `not` produces `1 - L` without allocating a variable,
; and a literal operand is a constant LC.
;
; We represent a register LC as a sparse vector of the Kestrel R1CS library
; (kestrel/crypto/r1cs/sparse/r1cs.lisp),
; i.e. a list of (coefficient pseudo-variable) pairs,
; where the pseudo-variable 1 stands for the constant 1.
; A snarkVM LC with constant c and terms (v1,c1) ... (vn,cn)
; is represented as ((c 1) (c1 v1) ... (cn vn)),
; omitting the (c 1) pair when c is 0.
; snarkVM's public variable with index 0, whose value is always 1
; and which snarkVM merges with the constant when generating the R1CS,
; is also represented by the pseudo-variable 1.
; Sparse vectors are not required to be normalized
; (no sorting, merging of duplicates, or removal of zero coefficients);
; normalization does not affect the value of an LC.

(in-package "ALEOVM")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/alists-light/lookup-eq" :dir :system))
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/number-theory/primes" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values of register LCs.

; The value of a register LC under an assignment of the R1CS variables.

(define reg-lc-value ((lc r1cs::sparse-vectorp)
                      (asg (r1cs::r1cs-valuationp asg p))
                      (p primep))
  :guard (r1cs::good-sparse-vectorp lc (strip-cars asg))
  :returns (val (pfield::fep val p)
                :hyp (posp p)
                :hints (("Goal" :in-theory (enable r1cs::fep-of-dot-product))))
  (r1cs::dot-product lc asg p))

; A register LC is boolean-valued under an assignment
; when its value is 0 or 1.
; snarkVM maintains this invariant for every Boolean
; (see LinearCombination::is_boolean_type).

(define reg-lc-booleanp ((lc r1cs::sparse-vectorp)
                         (asg (r1cs::r1cs-valuationp asg p))
                         (p primep))
  :guard (r1cs::good-sparse-vectorp lc (strip-cars asg))
  :returns (yes/no booleanp)
  (bitp (reg-lc-value lc asg p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variables of register LCs, and constant vs. variable registers.

; The R1CS variables that occur in a register LC.

(define reg-lc-vars ((lc r1cs::sparse-vectorp))
  :returns (vars symbol-listp
                 :hyp (r1cs::sparse-vectorp lc)
                 :hints (("Goal" :in-theory (enable r1cs::sparse-vectorp))))
  (b* (((when (endp lc)) nil)
       (pvar (second (first lc))))
    (if (equal pvar 1)
        (reg-lc-vars (rest lc))
      (cons pvar (reg-lc-vars (rest lc)))))
  :guard-hints (("Goal" :in-theory (enable r1cs::sparse-vectorp))))

; A register LC is constant when it has no variable terms.
; This corresponds to LinearCombination::is_constant in snarkVM,
; which holds when the list of terms is empty.

(define reg-lc-constantp ((lc r1cs::sparse-vectorp))
  :returns (yes/no booleanp)
  (endp (reg-lc-vars lc)))

; The value of a constant register LC, i.e. the sum of its coefficients.

(define reg-lc-constant-value ((lc r1cs::sparse-vectorp) (p primep))
  :returns (val (pfield::fep val p) :hyp (posp p))
  (if (endp lc)
      0
    (pfield::add (mod (first (first lc)) p)
                 (reg-lc-constant-value (rest lc) p)
                 p))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable r1cs::sparse-vectorp))))

; The value of a constant register LC does not depend on the assignment.

(defruled reg-lc-value-when-reg-lc-constantp
  (implies (and (r1cs::sparse-vectorp lc)
                (reg-lc-constantp lc)
                (posp p))
           (equal (reg-lc-value lc asg p)
                  (reg-lc-constant-value lc p)))
  :induct (len lc)
  :enable (reg-lc-value
           reg-lc-constantp
           reg-lc-vars
           reg-lc-constant-value
           r1cs::dot-product
           r1cs::sparse-vectorp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constructors of register LCs.

; A constant register LC with value k.
; This corresponds to Boolean::constant and Field::constant in snarkVM.

(define reg-lc-const ((k natp))
  :returns (lc r1cs::sparse-vectorp :hyp (natp k))
  (if (equal k 0)
      nil
    (list (list k 1))))

(defrule reg-lc-constantp-of-reg-lc-const
  (reg-lc-constantp (reg-lc-const k))
  :enable (reg-lc-constantp reg-lc-vars reg-lc-const))

(defrule reg-lc-value-of-reg-lc-const
  (implies (and (pfield::fep k p)
                (posp p))
           (equal (reg-lc-value (reg-lc-const k) asg p)
                  k))
  :enable (reg-lc-value reg-lc-const r1cs::dot-product))

; A register LC consisting of a single variable w with coefficient 1.
; This is the LC that snarkVM produces from a newly allocated variable,
; via From<Variable> for LinearCombination.

(define reg-lc-var ((w symbolp))
  :returns (lc r1cs::sparse-vectorp :hyp (symbolp w))
  (list (list 1 w)))

(defrule reg-lc-vars-of-reg-lc-var
  (implies (symbolp w)
           (equal (reg-lc-vars (reg-lc-var w))
                  (list w)))
  :enable (reg-lc-vars reg-lc-var))

(defrule not-reg-lc-constantp-of-reg-lc-var
  (implies (symbolp w)
           (not (reg-lc-constantp (reg-lc-var w))))
  :enable reg-lc-constantp)

(defrule reg-lc-value-of-reg-lc-var
  (implies (and (symbolp w)
                (posp p))
           (equal (reg-lc-value (reg-lc-var w) asg p)
                  (mod (ifix (lookup-equal w asg)) p)))
  :enable (reg-lc-value reg-lc-var r1cs::dot-product pfield::add pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Negation of register LCs.

; Negate all the coefficients of an LC, i.e. form -L.

(define reg-lc-neg-terms ((lc r1cs::sparse-vectorp) (p primep))
  :returns (new-lc r1cs::sparse-vectorp
                   :hyp (r1cs::sparse-vectorp lc)
                   :hints (("Goal" :in-theory (enable r1cs::sparse-vectorp))))
  (if (endp lc)
      nil
    (cons (list (pfield::neg (mod (first (first lc)) p) p)
                (second (first lc)))
          (reg-lc-neg-terms (rest lc) p)))
  :guard-hints (("Goal" :in-theory (enable r1cs::sparse-vectorp))))

(defrule reg-lc-value-of-reg-lc-neg-terms
  (implies (and (r1cs::sparse-vectorp lc)
                (posp p))
           (equal (reg-lc-value (reg-lc-neg-terms lc p) asg p)
                  (pfield::neg (reg-lc-value lc asg p) p)))
  :induct (len lc)
  :enable (reg-lc-value
           reg-lc-neg-terms
           r1cs::dot-product
           r1cs::sparse-vectorp))

; The `1 - L` LC that snarkVM forms for `!L` (circuit/types/boolean/src/not.rs):
;   - if L is constant, `E::one() - L`, i.e. the constant LC 1 - L;
;   - otherwise `Variable::Public(0) - L`,
;     i.e. the term 1 (the public variable with index 0) followed by -L.

(define reg-lc-not ((lc r1cs::sparse-vectorp) (p primep))
  :returns (new-lc r1cs::sparse-vectorp :hyp (and (r1cs::sparse-vectorp lc)
                                                  (posp p)))
  (if (reg-lc-constantp lc)
      (reg-lc-const (pfield::sub 1 (reg-lc-constant-value lc p) p))
    (cons (list 1 1) (reg-lc-neg-terms lc p))))

(defrule reg-lc-constantp-of-reg-lc-not
  (equal (reg-lc-constantp (reg-lc-not lc p))
         (reg-lc-constantp lc))
  :enable (reg-lc-not reg-lc-constantp reg-lc-vars reg-lc-const)
  :prep-lemmas
  ((defrule reg-lc-vars-of-reg-lc-neg-terms
     (equal (reg-lc-vars (reg-lc-neg-terms lc p))
            (reg-lc-vars lc))
     :induct (len lc)
     :enable (reg-lc-vars reg-lc-neg-terms))))

(defrule reg-lc-value-of-reg-lc-not
  (implies (and (r1cs::sparse-vectorp lc)
                (posp p))
           (equal (reg-lc-value (reg-lc-not lc p) asg p)
                  (pfield::sub 1 (reg-lc-value lc asg p) p)))
  :enable (reg-lc-not
           reg-lc-value-when-reg-lc-constantp)
  :prep-lemmas
  ((defrule reg-lc-value-of-cons-1-1
     (implies (posp p)
              (equal (reg-lc-value (cons (list 1 1) lc) asg p)
                     (pfield::add 1 (reg-lc-value lc asg p) p)))
     :enable (reg-lc-value r1cs::dot-product pfield::add pfield::mul))))

; `!L` is boolean-valued when L is.

(defrule reg-lc-booleanp-of-reg-lc-not
  (implies (and (r1cs::sparse-vectorp lc)
                (primep p)
                (reg-lc-booleanp lc asg p))
           (reg-lc-booleanp (reg-lc-not lc p) asg p))
  :enable (reg-lc-booleanp bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constraints over register LCs.

; An R1CS constraint (A) * (B) = (C) holds when
; the product of the values of the LCs A and B equals the value of the LC C.

(defrule r1cs-constraint-holdsp-of-r1cs-constraint
  (equal (r1cs::r1cs-constraint-holdsp (r1cs::r1cs-constraint a b c) asg p)
         (equal (pfield::mul (reg-lc-value a asg p) (reg-lc-value b asg p) p)
                (reg-lc-value c asg p)))
  :enable (r1cs::r1cs-constraint-holdsp reg-lc-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extending assignments.

; An assignment NEW extends an assignment OLD
; when every variable bound by OLD is bound by NEW to the same value.

(defun-sk valuation-extendsp (new old)
  (forall var
          (implies (r1cs::valuation-bindsp old var)
                   (and (r1cs::valuation-bindsp new var)
                        (equal (lookup-equal var new)
                               (lookup-equal var old))))))

(in-theory (disable valuation-extendsp valuation-extendsp-necc))

(defrule valuation-extendsp-reflexive
  (valuation-extendsp asg asg)
  :enable valuation-extendsp)

(defrule valuation-extendsp-of-cons-fresh
  (implies (not (r1cs::valuation-bindsp asg w))
           (valuation-extendsp (cons (cons w v) asg) asg))
  :enable (valuation-extendsp r1cs::valuation-bindsp))

; Adding a binding for a variable not in an LC does not change its value.

(defrule reg-lc-value-of-cons-when-not-member-reg-lc-vars
  (implies (not (member-equal w (reg-lc-vars lc)))
           (equal (reg-lc-value lc (cons (cons w v) asg) p)
                  (reg-lc-value lc asg p)))
  :induct (len lc)
  :enable (reg-lc-value reg-lc-vars r1cs::dot-product))

; Adding a binding for a fresh variable to a valuation yields a valuation.

(defrule r1cs-valuationp-of-cons-fresh
  (implies (and (r1cs::r1cs-valuationp asg p)
                (symbolp w)
                (not (r1cs::valuation-bindsp asg w))
                (pfield::fep v p))
           (r1cs::r1cs-valuationp (cons (cons w v) asg) p))
  :enable (r1cs::r1cs-valuationp r1cs::valuation-bindsp))
