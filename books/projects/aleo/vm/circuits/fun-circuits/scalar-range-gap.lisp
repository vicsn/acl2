; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness gaps for scalar circuits that trust a base-field wire.
;
; Unpatched Scalar::new (scalar-new-unpatched-accepts-non-scalar) accepts
; the scalar modulus r, which is a base field element and not a scalar.
; Operations that use that embedding without reducing modulo r then disagree
; with the scalar funspec of the residues:
;
;   is_equal / is_zero / is_one are Field::is_equal.  The wires r and 0
;   satisfy the two enforces with the not-equal bit 1, so the is_equal
;   linear combination 1 - bit is 0.  The residues are both 0.
;   The wires r+1 and 1 do the same, and the residue of r+1 is 1, so
;   is_one of that residue is 1 while the circuit returns 0.
;   crv-scalar-is-equal-gadget and crv-scalar-is-zero-gadget are this
;   field gadget (crv-equal.lisp).
;
;   ternary is Field::ternary.  Condition 1 copies the wire r, so the
;   output fails scalarp.  crv-scalar-ternary-gadget is this gadget.
;
;   is_less_than is the parity of 2*(a-b) in the base field.  2*(r-1) is
;   even, so the bit is 0, while the residues 0 and 1 compare the other way.
;   That is the arithmetic fact.  It is not yet an alist for the 253-bit
;   decomposition gadget.
;
; Scalar::add does reduce (add.rs subtracts r when the sum is not below r),
; so these are not the same gap as addition.

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled scalar-equal-modulus-disagrees-with-residue
  :short "A satisfying assignment of @('Scalar::is_equal') on the wires
          @($r$) and 0 returns false.  Both residues are 0, so
          @('scalar-is-equal-funspec') and @('scalar-is-zero-funspec')
          of those residues return true."
  (b* ((p (base-prime))
       (r (scalar-prime))
       (m (pfield::inv r p))
       (asg (list (cons 'a r)
                  (cons 'b 0)
                  (cons 'm m)
                  (cons 'neq 1))))
    (and (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-bindsp asg 'a)
         (r1cs::valuation-bindsp asg 'b)
         (r1cs::valuation-bindsp asg 'm)
         (r1cs::valuation-bindsp asg 'neq)
         (r1cs::r1cs-constraints-holdp
          (crv-field-is-not-equal-gadget 'a 'b 'm 'neq p)
          asg p)
         (not (scalarp (lookup-equal 'a asg)))
         (equal (lookup-equal 'b asg) 0)
         (equal (lookup-equal 'neq asg) 1)
         (equal (pfield::sub 1 (lookup-equal 'neq asg) p) 0)
         (equal (mod (lookup-equal 'a asg) r) 0)
         (equal (scalar-is-equal-funspec 0 0) 1)
         (equal (scalar-is-zero-funspec 0) 1)
         (equal (scalar-is-not-equal-funspec 0 0) 0)))
  :in-theory '((:e base-prime)
               (:e scalar-prime)
               (:e pfield::inv)
               (:e r1cs::r1cs-valuationp)
               (:e r1cs::valuation-bindsp)
               (:e r1cs::r1cs-constraints-holdp)
               (:e crv-field-is-not-equal-gadget)
               (:e lookup-equal)
               (:e scalarp)
               (:e pfield::sub)
               (:e mod)
               (:e scalar-is-equal-funspec)
               (:e scalar-is-zero-funspec)
               (:e scalar-is-not-equal-funspec)
               (:e cons)
               (:e not)
               (:e equal)
               (:e mod)))

(defruled scalar-one-modulus-disagrees-with-residue
  :short "A satisfying assignment of @('Scalar::is_one') on the wire
          @($r+1$) returns false.  That wire's residue is 1, so
          @('scalar-is-one-funspec') of the residue returns true."
  (b* ((p (base-prime))
       (r (scalar-prime))
       (a (+ r 1))
       (m (pfield::inv r p))
       (asg (list (cons 'a a)
                  (cons 'b 1)
                  (cons 'm m)
                  (cons 'neq 1))))
    (and (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-bindsp asg 'a)
         (r1cs::valuation-bindsp asg 'b)
         (r1cs::valuation-bindsp asg 'm)
         (r1cs::valuation-bindsp asg 'neq)
         (r1cs::r1cs-constraints-holdp
          (crv-field-is-not-equal-gadget 'a 'b 'm 'neq p)
          asg p)
         (not (scalarp (lookup-equal 'a asg)))
         (equal (lookup-equal 'neq asg) 1)
         (equal (pfield::sub 1 (lookup-equal 'neq asg) p) 0)
         (equal (mod (lookup-equal 'a asg) r) 1)
         (equal (scalar-is-one-funspec 1) 1)
         (equal (scalar-is-equal-funspec 1 1) 1)))
  :in-theory '((:e base-prime)
               (:e scalar-prime)
               (:e pfield::inv)
               (:e binary-+)
               (:e r1cs::r1cs-valuationp)
               (:e r1cs::valuation-bindsp)
               (:e r1cs::r1cs-constraints-holdp)
               (:e crv-field-is-not-equal-gadget)
               (:e lookup-equal)
               (:e scalarp)
               (:e pfield::sub)
               (:e mod)
               (:e scalar-is-one-funspec)
               (:e scalar-is-equal-funspec)
               (:e cons)
               (:e not)
               (:e equal)
               (:e mod)))

(defruled scalar-ternary-copies-non-scalar
  :short "A satisfying assignment of @('Scalar::ternary') with condition 1
          copies the wire @($r$).  The output fails @('scalarp').  The
          residue of that output is the funspec of the residues."
  (b* ((p (base-prime))
       (r (scalar-prime))
       (asg (list (cons 'c 1)
                  (cons 'a r)
                  (cons 'b 0)
                  (cons 'out r))))
    (and (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-bindsp asg 'c)
         (r1cs::valuation-bindsp asg 'a)
         (r1cs::valuation-bindsp asg 'b)
         (r1cs::valuation-bindsp asg 'out)
         (r1cs::r1cs-constraints-holdp
          (crv-field-ternary-gadget 'c 'a 'b 'out p)
          asg p)
         (equal (lookup-equal 'c asg) 1)
         (not (scalarp (lookup-equal 'out asg)))
         (equal (mod (lookup-equal 'out asg) r) 0)
         (equal (scalar-ternary-funspec 1 0 0) 0)))
  :in-theory '((:e base-prime)
               (:e scalar-prime)
               (:e r1cs::r1cs-valuationp)
               (:e r1cs::valuation-bindsp)
               (:e r1cs::r1cs-constraints-holdp)
               (:e crv-field-ternary-gadget)
               (:e lookup-equal)
               (:e scalarp)
               (:e mod)
               (:e scalar-ternary-funspec)
               (:e cons)
               (:e not)
               (:e equal)
               (:e mod)))

(defruled crv-scalar-less-than-parity-not-scalar-order
  :short "The @('is_less_than') parity test returns false for the wires
          @($r$) and 1, while the scalar residues compare the other way."
  (b* ((p (base-prime))
       (r (scalar-prime))
       (twice (pfield::mul 2 (pfield::sub r 1 p) p)))
    (and (not (scalarp r))
         (pfield::fep r p)
         (< (* 2 r) p)
         (equal twice (* 2 (- r 1)))
         (equal (mod twice 2) 0)
         (equal (scalar-is-less-than-funspec 0 1) 1)))
  :in-theory '((:e base-prime)
               (:e scalar-prime)
               (:e scalarp)
               (:e pfield::fep)
               (:e pfield::sub)
               (:e pfield::mul)
               (:e scalar-is-less-than-funspec)
               (:e mod)
               (:e <)
               (:e binary-*)
               (:e binary-+)
               (:e unary--)
               (:e not)
               (:e equal)))
