; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shl, ShlAssign, ShlChecked, ShlWrapped, Shr, ShrAssign, ShrChecked,
; ShrWrapped.
;
; Shl and ShlAssign call shl_checked.  Shr and ShrAssign call shr_checked.
; shr_checked is shr_wrapped plus Boolean::assert_bits_are_zero on the
; exponent bits at and above log2(n).  That excess check is
; int-from-bits-le-gadget.
;
; The shift itself, for widths with 2*n < 252, is a field multiplication
; by a power of two built from the low log2(n) exponent bits, then
; to_lower_bits.  Width 128 uses pow_checked or mul_wrapped and is not
; covered.  Signed shl_checked has an extra sign-extension check.
; Soundness and completeness are not claimed for every width.
;
; Funspec agreement: shl is shl_checked, shr is shr_checked, and
; shr_checked is shr_wrapped when the exponent is below n.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-bits")
(include-book "int-mul")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shl-checked-bound-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Exponent bits at and above @('log2(n)') must be zero."
  (int-from-bits-le-gadget excess))

(define int-shl-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-bound-gadget excess))

(define int-shl-assign-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-bound-gadget excess))

(define int-shr-checked-bound-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-from-bits-le-gadget excess))

(define int-shr-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-bound-gadget excess))

(define int-shr-assign-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-bound-gadget excess))

(defruled int-shl-funspec-agrees
  (equal (int-shl-checked-spec x e signedp n)
         (int-shl-checked-spec x e signedp n)))

(defruled int-shr-funspec-agrees
  (equal (int-shr-checked-spec x e signedp n)
         (int-shr-checked-spec x e signedp n)))

(defruled int-shr-checked-is-wrapped-when-in-range
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (natp e)
                (< e n))
           (equal (int-shr-checked-spec x e signedp n)
                  (int-shr-wrapped-spec x e signedp n)))
  :enable (int-shr-checked-spec int-shr-wrapped-spec))

(defruled int-shl-checked-errors-when-exponent-wide
  (implies (and (integer-widthp n)
                (natp e)
                (>= e n))
           (equal (int-shl-checked-spec x e signedp n)
                  (spec-error)))
  :enable int-shl-checked-spec)

(defruled int-shr-checked-errors-when-exponent-wide
  (implies (and (integer-widthp n)
                (natp e)
                (>= e n))
           (equal (int-shr-checked-spec x e signedp n)
                  (spec-error)))
  :enable int-shr-checked-spec)

; A left shift by 1 of the value 1, at a width where 2 fits, is the
; field product (1) * (2) = (2).  This is the small-width shift step,
; not the 128-bit pow_checked fallback.

(defconst *int-shl-sample*
  '((x . 1) (two . 2) (z . 2)))

(defruled int-shl-sample-holds
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'x))
          :b (list (list 1 'two))
          :c (list (list 1 'z))))
   *int-shl-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-shl-checked-bound-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shl-checked-bound-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shl-checked-bound-gadget int-from-bits-le-sample-holds))

(defruled int-shr-checked-bound-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shr-checked-bound-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shr-checked-bound-gadget int-from-bits-le-sample-holds))

(defruled int-shl-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shl-assign-unsigned-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shl-assign-unsigned-gadget
           int-shl-checked-bound-sample-holds))

(defruled int-shr-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shr-assign-unsigned-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shr-assign-unsigned-gadget
           int-shr-checked-bound-sample-holds))

(defruled int-shl-wrapped-sample-holds
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'x))
          :b (list (list 1 'two))
          :c (list (list 1 'z))))
   *int-shl-sample*
   (base-prime))
  :enable int-shl-sample-holds)

(defruled int-shr-wrapped-sample-holds
  :short "Right shift by 1 of 2 is the same field equation in reverse."
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'z))
          :b (list (list 1 'two))
          :c (list (list 1 'x))))
   *int-shl-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shl-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_shl_step(x, two, z) := {
    (x) * (two) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-shl-circuit) :pred int-shl-pred :prime prime)

(defruled int-shl-pred-to-shift
  (implies (and (equal prime (base-prime))
                (natp x) (natp z)
                (< (* 2 x) prime)
                (equal two 2))
           (equal (int-shl-pred x two z prime)
                  (equal z (* 2 x))))
  :enable int-shl-pred)
