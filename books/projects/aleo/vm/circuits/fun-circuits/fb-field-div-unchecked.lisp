; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::div_unchecked, both operands variable.
;
; snarkVM emits one constraint, (q) * (y) = (x).  That is
; field-div-unchecked-gadget, which is field-mul-gadget of (q, y, x).
; The PFCS predicate field-div-unchecked-pred is the same constraint.
;
; When y is not 0 the quotient is unique and equals the funspec.
; When x = y = 0 the constraint holds for every quotient.  snarkVM's
; witness is 0, which is the funspec value, but other quotients also
; satisfy the constraint.  See bugs-fb.txt.

(in-package "ALEOVM")

(include-book "../r1cs/field-div-unchecked")
(include-book "../pfcs/field-div-unchecked")
(include-book "../fun-specs/primitives-field")
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb-field-div-unchecked-gadget-sound
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (not (equal (lookup-equal y asg) 0))
                (r1cs::r1cs-constraints-holdp
                 (field-div-unchecked-gadget x y z) asg p))
           (equal (lookup-equal z asg)
                  (field-div-unchecked-funspec (lookup-equal x asg)
                                               (lookup-equal y asg)
                                               t)))
  :enable (field-div-unchecked-gadget-soundness
           field-div-unchecked-funspec
           fieldp))

(defruled fb-field-div-unchecked-gadget-complete
  :short "The snarkVM witness: @($x / y$) when @($y \\neq 0$), and 0 when
          @($x = y = 0$).  A nonzero dividend and a zero divisor is an error
          and is not claimed."
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (or (not (equal (lookup-equal y asg) 0))
                    (equal (lookup-equal x asg) 0))
                (equal (lookup-equal z asg)
                       (if (equal (lookup-equal y asg) 0)
                           0
                         (pfield::div (lookup-equal x asg)
                                      (lookup-equal y asg)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (field-div-unchecked-gadget x y z) asg p)
                (equal (lookup-equal z asg)
                       (field-div-unchecked-funspec (lookup-equal x asg)
                                                    (lookup-equal y asg)
                                                    t))))
  :enable (field-div-unchecked-gadget
           field-mul-gadget-correctness
           field-div-unchecked-funspec
           fieldp))

(defruled fb-field-div-unchecked-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (fieldp z)
                (not (equal y 0)))
           (equal (field-div-unchecked-pred x y z prime)
                  (equal z (field-div-unchecked-funspec x y t))))
  :enable (field-div-unchecked-pred-to-spec
           field-div-unchecked-spec
           field-div-unchecked-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 4 / 2 = 2 in the prime 5.

(defconst *fb-field-div-unchecked-asg*
  '((x . 4) (y . 2) (z . 2)))

(defconst *fb-field-div-unchecked-prime* 5)

(defrule fb-field-div-unchecked-sample
  (r1cs::r1cs-constraints-holdp
   (field-div-unchecked-gadget 'x 'y 'z)
   *fb-field-div-unchecked-asg*
   *fb-field-div-unchecked-prime*)
  :enable (field-div-unchecked-gadget
           field-mul-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
