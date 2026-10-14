; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS specifications of the field comparisons that are boolean wrappers
; around is_less_than.
;
; snarkVM circuit/types/field/src/compare.rs, variable/variable case:
;   is_greater_than(x, y)          = is_less_than(y, x)
;   is_greater_than_or_equal(x, y) = not is_less_than(x, y)
;   is_less_than_or_equal(x, y)    = not is_less_than(y, x)
;
; Boolean negation is the linear combination 1 - bit, so the last two
; gadgets are the less-than gadget (arguments swapped for <=) and the
; output value is 1 minus the less-than result bit, which is
; (car (last rs)) in field-lt-gadget.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-field")
(include-book "../r1cs/field-lt")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-is-greater-than-gadget ((x symbolp)
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
  :short "Constraints of @('Field::is_greater_than'): less-than with
          the operands swapped."
  (field-lt-gadget y ys yrs x xs xrs ds rs u p))

(defruled field-is-greater-than-gadget-sound
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
                (r1cs::r1cs-constraints-holdp
                 (field-is-greater-than-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (rs$ (lookup-equal-list rs asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (equal (equal (car (last rs$)) 1)
                             (equal (field-is-greater-than-funspec x$ y$)
                                    1)))))
  :do-not-induct t
  :enable (field-is-greater-than-gadget
           field-is-greater-than-funspec
           field-is-less-than-funspec
           fieldp
           pfield::fep-fix-when-fep)
  :use ((:instance field-lt-gadget-soundness
                   (x y) (xs ys) (xrs yrs)
                   (y x) (ys xs) (yrs xrs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-is-greater-than-or-equal-gadget ((x symbolp)
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
  :short "Constraints of @('Field::is_greater_than_or_equal').
          The result boolean is the linear combination @($1 - r$),
          where @('r') is the less-than result bit."
  (field-lt-gadget x xs xrs y ys yrs ds rs u p))

(defruled field-is-greater-than-or-equal-gadget-sound
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
                (r1cs::r1cs-constraints-holdp
                 (field-is-greater-than-or-equal-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (r$ (car (last (lookup-equal-list rs asg))))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (equal (pfield::sub 1 r$ p)
                             (field-is-greater-than-or-equal-funspec x$ y$)))))
  :do-not-induct t
  :enable (field-is-greater-than-or-equal-gadget
           field-is-greater-than-or-equal-funspec
           field-is-less-than-funspec
           boolean-not-funspec
           fieldp
           bitp
           pfield::fep-fix-when-fep)
  :use field-lt-gadget-soundness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-is-less-than-or-equal-gadget ((x symbolp)
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
  :short "Constraints of @('Field::is_less_than_or_equal'):
          less-than with the operands swapped.  The result boolean is
          @($1 - r$)."
  (field-lt-gadget y ys yrs x xs xrs ds rs u p))

(defruled field-is-less-than-or-equal-gadget-sound
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
                (r1cs::r1cs-constraints-holdp
                 (field-is-less-than-or-equal-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (r$ (car (last (lookup-equal-list rs asg))))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (equal (pfield::sub 1 r$ p)
                             (field-is-less-than-or-equal-funspec x$ y$)))))
  :do-not-induct t
  :enable (field-is-less-than-or-equal-gadget
           field-is-less-than-or-equal-funspec
           field-is-greater-than-or-equal-funspec
           field-is-less-than-funspec
           boolean-not-funspec
           fieldp
           bitp
           pfield::fep-fix-when-fep)
  :use ((:instance field-lt-gadget-soundness
                   (x y) (xs ys) (xrs yrs)
                   (y x) (ys xs) (yrs xrs))))
