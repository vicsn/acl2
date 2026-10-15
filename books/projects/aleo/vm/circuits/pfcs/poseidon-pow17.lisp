; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; S-box of hash.psd2 and hash.psd4.
; snarkVM raises a field element to alpha = 17 by four squarings and one
; multiplication: x^2, x^4, x^8, x^16, x^17.  Every non-constant S-box in the
; Poseidon samples is five R1CS constraints of this shape.

(in-package "ALEOVM")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ poseidon-pow17
  :parents (circuits-pfcs)
  :short "Formalization and verification of the Poseidon S-box @($x^{17}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Aleo opcodes @('hash.psd2') and @('hash.psd4') use Poseidon
     with @($\\alpha = 17$).  snarkVM compiles each S-box to five
     rank-1 constraints")
   (xdoc::@[]
    "\\begin{align*}
     x \\cdot x &= a && (x^2) \\\\
     a \\cdot a &= b && (x^4) \\\\
     b \\cdot b &= c && (x^8) \\\\
     c \\cdot c &= d && (x^{16}) \\\\
     d \\cdot x &= y && (x^{17})
     \\end{align*}")
   (xdoc::p
    "The intermediates are parameters, so the lifted predicate is quantifier-free.
     @(see hash-psd) calls this relation once per non-constant S-box
     and leaves the intermediates free in the hash relation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pow17-spec ((x (pfield::fep x prime))
                    (a (pfield::fep a prime))
                    (b (pfield::fep b prime))
                    (c (pfield::fep c prime))
                    (d (pfield::fep d prime))
                    (y (pfield::fep y prime))
                    (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the S-box: the intermediates are the successive squares."
  (and (equal a (pfield::pow x 2 prime))
       (equal b (pfield::pow x 4 prime))
       (equal c (pfield::pow x 8 prime))
       (equal d (pfield::pow x 16 prime))
       (equal y (pfield::pow x 17 prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pow17-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The five multiplications that compute @($x^{17}$)."
  (pfcs::parse-def
   "pow17(x, a, b, c, d, y) := {
    (x) * (x) == (a),
    (a) * (a) == (b),
    (b) * (b) == (c),
    (c) * (c) == (d),
    (d) * (x) == (y)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pow17-lifting
  :short "Lifting of the circuit to a predicate."
  (pfcs::lift (pow17-circuit)
              :pred pow17-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defrule primep-implies-bounds
   (implies (primep p)
            (and (integerp p) (< 1 p) (posp p)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable primep)))))

(local
 (defthmd mul-is-pow-2
   (implies (and (primep p) (pfield::fep x p))
            (equal (pfield::mul x x p)
                   (pfield::pow x 2 p)))
   :hints (("Goal"
            :in-theory (e/d (pfield::pow pfield::mul-of-1-arg2)
                            (pfield::pow-of-+))
            :expand ((pfield::pow x 2 p)
                     (pfield::pow x 1 p)
                     (pfield::pow x 0 p))))))

(local
 (defthmd mul-pows-is-pow-4
   (implies (and (primep p) (pfield::fep x p))
            (equal (pfield::mul (pfield::pow x 2 p) (pfield::pow x 2 p) p)
                   (pfield::pow x 4 p)))
   :hints (("Goal"
            :use ((:instance pfield::pow-of-+ (a x) (b 2) (c 2) (p p)))
            :in-theory (disable pfield::pow)))))

(local
 (defthmd mul-pows-is-pow-8
   (implies (and (primep p) (pfield::fep x p))
            (equal (pfield::mul (pfield::pow x 4 p) (pfield::pow x 4 p) p)
                   (pfield::pow x 8 p)))
   :hints (("Goal"
            :use ((:instance pfield::pow-of-+ (a x) (b 4) (c 4) (p p)))
            :in-theory (disable pfield::pow)))))

(local
 (defthmd mul-pows-is-pow-16
   (implies (and (primep p) (pfield::fep x p))
            (equal (pfield::mul (pfield::pow x 8 p) (pfield::pow x 8 p) p)
                   (pfield::pow x 16 p)))
   :hints (("Goal"
            :use ((:instance pfield::pow-of-+ (a x) (b 8) (c 8) (p p)))
            :in-theory (disable pfield::pow)))))

(local
 (defthmd mul-pow16-x-is-pow-17
   (implies (and (primep p) (pfield::fep x p))
            (equal (pfield::mul (pfield::pow x 16 p) x p)
                   (pfield::pow x 17 p)))
   :hints (("Goal"
            :use ((:instance pfield::pow-of-+ (a x) (b 16) (c 1) (p p)))
            :in-theory (e/d (pfield::pow pfield::mul-of-1-arg2)
                            (pfield::pow-of-+))
            :expand ((pfield::pow x 1 p)
                     (pfield::pow x 0 p))))))

(local
 (defruled pow17-pred-implies-spec
   (implies (and (primep prime)
                 (pfield::fep x prime)
                 (pfield::fep a prime)
                 (pfield::fep b prime)
                 (pfield::fep c prime)
                 (pfield::fep d prime)
                 (pfield::fep y prime)
                 (pow17-pred x a b c d y prime))
            (pow17-spec x a b c d y prime))
   :enable (pow17-pred
            pow17-spec
            mul-is-pow-2
            mul-pows-is-pow-4
            mul-pows-is-pow-8
            mul-pows-is-pow-16
            mul-pow16-x-is-pow-17)))

(local
 (defruled pow17-spec-implies-pred
   (implies (and (primep prime)
                 (pfield::fep x prime)
                 (pfield::fep a prime)
                 (pfield::fep b prime)
                 (pfield::fep c prime)
                 (pfield::fep d prime)
                 (pfield::fep y prime)
                 (pow17-spec x a b c d y prime))
            (pow17-pred x a b c d y prime))
   :enable (pow17-pred
            pow17-spec
            mul-is-pow-2
            mul-pows-is-pow-4
            mul-pows-is-pow-8
            mul-pows-is-pow-16
            mul-pow16-x-is-pow-17)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pow17-correctness
  :short "Correctness of the S-box."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both directions are proved.  Soundness is the chain of squarings.
     Completeness is that the powers satisfy those squarings.
     The two agree on every field element, so the intermediates are unique."))

  (defruled pow17-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep a prime)
                  (pfield::fep b prime)
                  (pfield::fep c prime)
                  (pfield::fep d prime)
                  (pfield::fep y prime))
             (equal (pow17-pred x a b c d y prime)
                    (pow17-spec x a b c d y prime)))
    :hints (("Goal"
             :cases ((pow17-pred x a b c d y prime))
             :use (pow17-pred-implies-spec pow17-spec-implies-pred))))

  (defruled pow17-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "pow17") defs)
                         (pow17-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep a prime)
                  (pfield::fep b prime)
                  (pfield::fep c prime)
                  (pfield::fep d prime)
                  (pfield::fep y prime))
             (equal (pfcs::definition-satp
                      (pfname "pow17") defs (list x a b c d y) prime)
                    (pow17-spec x a b c d y prime)))
    :in-theory '((:e pow17-circuit)
                 (:e name-simple)
                 definition-satp-to-pow17-pred
                 pow17-pred-to-spec)))
