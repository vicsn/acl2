; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unordered soundness of Field::square_roots_flagged_nondeterministic.
;
; snarkVM documents (circuit/types/field/src/square_root.rs) that the
; constraints do not order the two roots; that is the "nondeterministic"
; in the name.  field-square-roots-flagged-nondeterministic-funspec picks
; the lesser root first, which the constraints do not imply: swapping
; root for -root satisfies them too.  The theorem below is the honest
; reading.  Over the wires, with no hypothesis on internal wires, the
; flag equals the funspec flag and the two outputs (root, -root) are the
; funspec's two roots in one order or the other.
;
; The internal is_one and is_zero bits are forced by their own
; constraints (group-wire-sound.lisp), and the and-gate output is then a
; bit.  fb2-flagged-roots-unordered gives the square relation.  For the
; flag direction, a flag of 1 means x is nonzero and x^((p-1)/2) is not
; 1, so x is not a square by Euler's criterion.

(in-package "ALEOVM")

(include-book "fb2-field-sqrt")
(include-book "group-wire-sound")
(include-book "kestrel/crypto/ecurve/prime-field-squares-euler-criterion" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/pow" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-nonsquare-when-euler-not-one
  (implies (and (fieldp a)
                (not (equal a 0))
                (not (equal (pfield::pow a (field-modulus-minus-one-div-two)
                                         (base-prime))
                            1)))
           (not (ecurve::pfield-squarep a (base-prime))))
  :do-not-induct t
  :in-theory (e/d (fieldp pfield::fep field-modulus-minus-one-div-two)
                  (pfield::pow))
  :use ((:instance ecurve::weak-euler-criterion-contrapositive
                   (ecurve::a a) (p (base-prime)))
        (:instance pfield::pow-rewrite
                   (a a) (b (field-modulus-minus-one-div-two))
                   (p (base-prime)))))

(defruled fsa-squarep-when-root
  (implies (and (fieldp x) (fieldp r)
                (equal (pfield::mul r r (base-prime)) x))
           (ecurve::pfield-squarep x (base-prime)))
  :enable fieldp
  :use (:instance ecurve::pfield-squarep-suff (r r) (x x) (p (base-prime))))

(defruled fsa-fep-of-lesser
  (pfield::fep (field-lesser-square-root x) (base-prime))
  :in-theory (e/d (fieldp) (fieldp-of-field-lesser-square-root))
  :use fieldp-of-field-lesser-square-root)

(defmacro fsa-sqrt-hyps (&rest more)
  `(and (symbolp x)
        (equal e (field-modulus-minus-one-div-two))
        (symbol-listp ss)
        (symbol-listp pow-rs)
        (equal (len ss) (field-pow-const-slen e))
        (equal (len pow-rs) (field-pow-const-rlen e))
        (consp pow-rs)
        (symbolp one-m) (symbolp one-r) (symbolp square) (symbolp root)
        (symbolp zero-m) (symbolp zero-r) (symbolp err)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg x)
        (r1cs::valuation-binds-allp asg ss)
        (r1cs::valuation-binds-allp asg pow-rs)
        (r1cs::valuation-bindsp asg one-m)
        (r1cs::valuation-bindsp asg one-r)
        (r1cs::valuation-bindsp asg square)
        (r1cs::valuation-bindsp asg root)
        (r1cs::valuation-bindsp asg zero-m)
        (r1cs::valuation-bindsp asg zero-r)
        (r1cs::valuation-bindsp asg err)
        (r1cs::r1cs-constraints-holdp
         (fb-field-square-roots-flagged-gadget
          x e ss pow-rs one-m one-r square root zero-m zero-r err p)
         asg p)
        ,@more))

(defruled fsa-e-facts
  (and (posp (field-modulus-minus-one-div-two))
       (not (equal (field-modulus-minus-one-div-two) 1))
       (primep (base-prime)))
  :in-theory '((:e field-modulus-minus-one-div-two)
               (:e base-prime) (:e posp) (:e primep)))

(defruled fsa-sqrt-pieces
  (implies (fsa-sqrt-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (field-pow-const-gadget x e ss pow-rs p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (field-is-one-gadget (car pow-rs) one-m one-r p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (field-is-zero-gadget x zero-m zero-r p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget zero-r one-r err) asg p)))
  :do-not-induct t
  :in-theory (e/d (fb-field-square-roots-flagged-gadget
                   r1cs::r1cs-constraints-holdp-of-append)
                  ((:e base-prime)
                   (:e field-modulus-minus-one-div-two)
                   field-pow-const-gadget
                   field-is-one-gadget
                   field-is-zero-gadget
                   boolean-and-gadget)))

(defruled fsa-sqrt-internal-bits
  (implies (fsa-sqrt-hyps)
           (and (bitp (lookup-equal one-r asg))
                (bitp (lookup-equal zero-r asg))
                (bitp (lookup-equal err asg))
                (equal (lookup-equal err asg)
                       (bitand (lookup-equal zero-r asg)
                               (lookup-equal one-r asg)))))
  :do-not-induct t
  :in-theory (e/d (fsa-e-facts bitand bitp)
                  ((:e base-prime)
                   (:e field-modulus-minus-one-div-two)))
  :use (fsa-sqrt-pieces
        fsa-e-facts
        (:instance field-is-one-gadget-forces-bit
                   (x (car pow-rs)) (m one-m) (r one-r))
        (:instance field-is-zero-gadget-forces-bit
                   (x x) (m zero-m) (r zero-r))
        (:instance boolean-and-gadget-to-bitand
                   (x zero-r) (y one-r) (z err))))

(defruled fsa-sqrt-flag-one-nonsquare
  (implies (and (fsa-sqrt-hyps)
                (equal (lookup-equal err asg) 1))
           (not (ecurve::pfield-squarep (lookup-equal x asg) (base-prime))))
  :do-not-induct t
  :in-theory (e/d (fieldp bitp bitand
                   field-is-one-funspec
                   field-is-zero-funspec
                   field-is-equal-funspec
                   field-is-not-equal-funspec
                   boolean-not-funspec
                   r1cs::fep-of-lookup-equal)
                  ((:e base-prime)
                   (:e field-modulus-minus-one-div-two)
                   (:definition pfield::sub)
                   pfield::pow))
  :use (fsa-sqrt-pieces
        fsa-sqrt-internal-bits
        fsa-e-facts
        (:instance field-pow-const-soundness
                   (c e) (rs pow-rs))
        (:instance field-is-one-gadget-sound
                   (x (car pow-rs)) (m one-m) (r one-r))
        (:instance field-is-zero-gadget-sound
                   (x x) (m zero-m) (r zero-r))
        (:instance fsa-nonsquare-when-euler-not-one
                   (a (lookup-equal x asg)))))

(defruled fsa-square-roots-flagged-unordered-sound
  :short "@('square_roots_flagged_nondeterministic') over the wires: the flag
          is the funspec flag, and @('(root, -root)') is the funspec's pair of
          roots in either order.  The ordered funspec is not implied."
  (implies (fsa-sqrt-hyps)
           (b* ((x$ (lookup-equal x asg))
                (root$ (lookup-equal root asg))
                (second$ (pfield::neg root$ p))
                (flag$ (lookup-equal err asg))
                ((mv r1 r2 f)
                 (field-square-roots-flagged-nondeterministic-funspec x$)))
             (and (equal flag$ f)
                  (or (and (equal root$ r1) (equal second$ r2))
                      (and (equal root$ r2) (equal second$ r1))))))
  :do-not-induct t
  :cases ((equal (lookup-equal err asg) 1))
  :in-theory (e/d (field-square-roots-flagged-nondeterministic-funspec
                   fieldp bitp
                   r1cs::fep-of-lookup-equal)
                  ((:e base-prime)
                   (:e field-modulus-minus-one-div-two)
                   (:definition pfield::sub)))
  :use (fsa-sqrt-internal-bits
        fsa-sqrt-flag-one-nonsquare
        (:instance pfield::neg-of-neg
                   (x (field-lesser-square-root (lookup-equal x asg)))
                   (p (base-prime)))
        (:instance fsa-fep-of-lesser (x (lookup-equal x asg)))
        fsa-e-facts
        (:instance fb2-flagged-roots-unordered)
        (:instance fsa-squarep-when-root
                   (x (lookup-equal x asg))
                   (r (lookup-equal root asg)))
        (:instance fb2-field-lesser-square-root-props
                   (x (lookup-equal x asg)))
        (:instance fb2-equal-squares-implies-equal-or-neg
                   (a (lookup-equal root asg))
                   (b (field-lesser-square-root (lookup-equal x asg))))))
