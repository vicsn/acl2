; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::is_less_than in the variable/variable case is field-lt-gadget.
; field-lt-gadget-soundness is an implication from the constraints to
;   (< x y) iff the last comparison bit is 1.
; With that bit boolean, the bit equals the funspec.
;
; is_greater_than, is_greater_than_or_equal, and is_less_than_or_equal
; are already proved sound in field-compare-r1cs.lisp.  Completeness
; needs the bit-decomposition and bitwise-comparison witnesses.
; Those witnesses are not constructed here, and there is no PFCS:
; the gadget is hundreds of constraints at (base-prime).

(in-package "ALEOVM")

(include-book "field-compare-r1cs")
(include-book "../r1cs/field-lt")
(include-book "../fun-specs/primitives-field")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-is-less-than-gadget ((x symbolp)
                                      (xs symbol-listp)
                                      (xrs symbol-listp)
                                      (y symbolp)
                                      (ys symbol-listp)
                                      (yrs symbol-listp)
                                      (ds symbol-listp)
                                      (rs symbol-listp)
                                      (u symbolp)
                                      (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len xrs) (bits-lt-prime-rlen p))
              (equal (len ys) (integer-length p))
              (equal (len yrs) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-lt-gadget x xs xrs y ys yrs ds rs u p))

(defruled fb-field-is-less-than-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (bitp (car (last (lookup-equal-list rs asg))))
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-is-less-than-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p))
           (equal (car (last (lookup-equal-list rs asg)))
                  (field-is-less-than-funspec (lookup-equal x asg)
                                              (lookup-equal y asg))))
  :do-not-induct t
  :enable (fb-field-is-less-than-gadget
           field-is-less-than-funspec
           fieldp
           bitp
           pfield::fep-fix-when-fep)
  :use field-lt-gadget-soundness)
