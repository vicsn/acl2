; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Linear-combination builders for circuits whose constraint operands are
; snarkVM linear combinations rather than single variables (Elligator2,
; Pedersen).  A linear combination is a sparse vector; addition is append
; and multiplication by a constant scales the coefficients, as in snarkVM's
; LinearCombination, so neither emits a constraint.  hped-c is one
; R1CS constraint a * b = c.  The dot-product rules below turn a
; constraint into a field equation over the operand values.

(in-package "ALEOVM")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/alists-light/lookup-eq" :dir :system))

(define hped-lc-v (v)
  :short "The variable @('v') as a linear combination."
  (list (list 1 v)))

(define hped-lc-1 ()
  :short "The constant 1."
  (list (list 1 1)))

(define hped-lc-add (a b)
  :verify-guards nil
  (append a b))

(define hped-lc-scale ((k integerp) a)
  :verify-guards nil
  (if (atom a)
      nil
    (cons (list (* (ifix k) (ifix (first (car a)))) (second (car a)))
          (hped-lc-scale k (cdr a)))))

(define hped-lc-neg (a)
  :verify-guards nil
  (hped-lc-scale -1 a))

(define hped-lc-sub (a b)
  :verify-guards nil
  (hped-lc-add a (hped-lc-neg b)))

(define hped-c (a b c)
  :verify-guards nil
  :short "The R1CS constraint @($a \\cdot b = c$)."
  (r1cs::r1cs-constraint a b c))

(defmacro hped-dot (v)
  `(r1cs::dot-product ,v asg p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule hped-sparse-vectorp-of-lc-v
  (implies (symbolp v)
           (r1cs::sparse-vectorp (hped-lc-v v)))
  :enable (hped-lc-v r1cs::sparse-vectorp))

(defrule hped-sparse-vectorp-of-lc-1
  (r1cs::sparse-vectorp (hped-lc-1))
  :enable (hped-lc-1 r1cs::sparse-vectorp))

(defrule hped-sparse-vectorp-of-lc-add
  (implies (and (r1cs::sparse-vectorp a) (r1cs::sparse-vectorp b))
           (r1cs::sparse-vectorp (hped-lc-add a b)))
  :enable hped-lc-add)

(defrule hped-sparse-vectorp-of-lc-scale
  (implies (r1cs::sparse-vectorp a)
           (r1cs::sparse-vectorp (hped-lc-scale k a)))
  :induct (len a)
  :enable (hped-lc-scale r1cs::sparse-vectorp))

(defrule hped-sparse-vectorp-of-lc-neg
  (implies (r1cs::sparse-vectorp a)
           (r1cs::sparse-vectorp (hped-lc-neg a)))
  :enable hped-lc-neg)

(defrule hped-sparse-vectorp-of-lc-sub
  (implies (and (r1cs::sparse-vectorp a) (r1cs::sparse-vectorp b))
           (r1cs::sparse-vectorp (hped-lc-sub a b)))
  :enable hped-lc-sub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule hped-dot-of-lc-v
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp v)
                (r1cs::valuation-bindsp asg v))
           (equal (hped-dot (hped-lc-v v))
                  (lookup-equal v asg)))
  :enable (hped-lc-v r1cs::dot-product r1cs::fep-of-lookup-equal))

(defrule hped-dot-of-lc-1
  (implies (primep p)
           (equal (hped-dot (hped-lc-1)) 1))
  :enable (hped-lc-1 r1cs::dot-product))

(defrule hped-dot-of-lc-add
  (implies (primep p)
           (equal (hped-dot (hped-lc-add a b))
                  (pfield::add (hped-dot a) (hped-dot b) p)))
  :enable hped-lc-add)

(defruledl hped-mod-of-times-is-mul
  (implies (and (integerp k) (integerp c) (posp p))
           (equal (mod (* k c) p)
                  (pfield::mul k c p)))
  :enable (pfield::mul acl2::pos-fix))

(defruled hped-dot-of-lc-scale-mod
  (implies (and (primep p) (integerp k))
           (equal (hped-dot (hped-lc-scale k a))
                  (pfield::mul (mod k p) (hped-dot a) p)))
  :induct (len a)
  :enable (hped-lc-scale r1cs::dot-product hped-mod-of-times-is-mul))

(defrule hped-dot-of-lc-scale
  (implies (and (primep p) (pfield::fep k p))
           (equal (hped-dot (hped-lc-scale k a))
                  (pfield::mul k (hped-dot a) p)))
  :use hped-dot-of-lc-scale-mod
  :enable pfield::fep)

(defrule hped-dot-of-lc-neg
  (implies (primep p)
           (equal (hped-dot (hped-lc-neg a))
                  (pfield::neg (hped-dot a) p)))
  :enable hped-lc-neg
  :use (:instance hped-dot-of-lc-scale-mod (k -1)))

(defrule hped-dot-of-lc-sub
  (implies (primep p)
           (equal (hped-dot (hped-lc-sub a b))
                  (pfield::sub (hped-dot a) (hped-dot b) p)))
  :enable (hped-lc-sub pfield::sub))

(defrule hped-holdsp-of-c
  (equal (r1cs::r1cs-constraint-holdsp (hped-c a b c) asg p)
         (equal (pfield::mul (hped-dot a)
                             (hped-dot b)
                             p)
                (hped-dot c)))
  :enable (hped-c r1cs::r1cs-constraint-holdsp r1cs::r1cs-constraint
           r1cs::r1cs-constraint->a r1cs::r1cs-constraint->b r1cs::r1cs-constraint->c))
