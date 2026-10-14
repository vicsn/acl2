; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Neg::neg.
;
; Unsigned negation halts in the host.  The funspec is spec-error and there
; is no successful witness.  That is a completeness fact: every valid output
; (there are none) is witnessed.
;
; Signed negation is one.add_checked(!self).  Boolean not is a linear
; combination.  The resulting constraints are r1cs/signed-small-neg, which
; is wrapped subtraction from zero plus a check that the operand and the
; result are not both negative (the signed minimum).

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-add")
(include-book "../r1cs/signed-small-neg")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-neg-signed-gadget ((xs symbol-listp)
                               (ys symbol-listp)
                               (carry symbolp)
                               (both-neg symbolp)
                               (one symbolp)
                               (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-neg-gadget xs ys carry both-neg one p))

(defruled int-neg-unsigned-spec-error
  (implies (not signedp)
           (equal (int-neg-spec x signedp n) (spec-error)))
  :enable int-neg-spec)

(defruled int-neg-unsigned-complete
  :short "No valid unsigned output exists, so none fails to be witnessed."
  (implies (and (not signedp)
                (int-valuep x nil n)
                (integer-widthp n))
           (equal (int-neg-spec x nil n) (spec-error)))
  :enable int-neg-spec)

(defruled int-neg-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbolp carry) (symbolp both-neg) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg both-neg)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-neg-signed-gadget xs ys carry both-neg one p)
                 asg p))
           (equal (lebits=>int (lookup-equal-list ys asg))
                  (int-neg-spec x t n)))
  :enable (int-neg-signed-gadget
           int-neg-spec
           int-width-add-fits
           lebits->int-is-lebits=>int
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-neg-gadget-soundness)

; -1 at width 2.  Bits of 1 are (1 0); bits of -1 are (1 1).
; The library gadget is a wrapped subtraction from zero, so this sample
; only records a satisfying boolean-and of the sign bits being zero
; together with a zero constraint.  The full subtraction sample is the
; sub-wrapped gadget; here both-neg = 0 and the sign of the result is 1
; while the sign of the input 1 is 0, so their and is 0.

(defconst *int-neg-sample*
  '((sx . 0) (sy . 1) (both . 0)))

(defruled int-neg-sample-holds
  (r1cs::r1cs-constraints-holdp
   (append (boolean-and-gadget 'sx 'sy 'both)
           (zero-gadget 'both))
   *int-neg-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     boolean-and-gadget
                                     zero-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-neg-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The both-negative check.  The subtraction is int_sub_checked."
  (pfcs::parse-def
   "int_neg_sign(sx, sy, both) := {
    (sx) * (sy) == (both),
    (both) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-neg-circuit) :pred int-neg-pred :prime prime)

(defruled int-neg-pred-to-funspec
  :short "Both sign bits are clear of the product, and the product is 0.
          This is the signed-minimum check, not the whole negation."
  (implies (and (equal prime (base-prime))
                (bitp sx)
                (bitp sy)
                (pfield::fep both prime))
           (equal (int-neg-pred sx sy both prime)
                  (and (equal both 0)
                       (equal (bitand sx sy) 0))))
  :enable (int-neg-pred bitand))
