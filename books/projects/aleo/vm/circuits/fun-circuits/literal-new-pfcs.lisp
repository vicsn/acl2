; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS for Literal::new.  Each relation is the constraint snarkVM emits.
; Boolean checks are the existing boolean_assert / boolean_assert_all
; relations.  Field::new and Scalar::new are empty.  The string size
; assert_eq carries the length as a constant coefficient.  Group::new is
; the 13 enforce_in_group constraints.  IdentifierLiteral::new is the
; boolean checks, the validate_byte relations, and the trailing-null
; relation.  Signature::new is two group relations; hash_to_scalar_psd4
; is the abstract equality, not a constraint emitted here.
;
; R1CS-SOUND of the identifier arm is identifier-list-sound.lisp.
; R1CS-COMPLETE stays open: the cofactor witness is not constructed, and
; a string longer than u32 is a host halt rather than an unsatisfiable
; constraint (fun-specs/README.md).

(in-package "ALEOVM")

(include-book "literal-new-r1cs")
(include-book "identifier-list-sound")
(include-book "../pfcs/boolean-assert-all")
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

; Flip (equal (mul ...) v) to the orientation used by the R1CS lemmas.
; The syntaxp stops the rule from looping when the other side is not a product.
(local
 (defthm literal-pfcs-equal-commute-mul
   (implies (syntaxp (and (consp a)
                          (eq (car a) 'pfield::mul)))
            (equal (equal a b) (equal b a)))))

(defruled literal-pfcs-mod-consts
  (implies (equal p (base-prime))
           (and (equal (mod 0 p) 0)
                (equal (mod 1 p) 1)
                (equal (mod 2 p) 2)
                (equal (mod 3021 p) 3021)))
  :hints (("Goal" :in-theory (enable (:e base-prime) (:e mod)))))

(defruled group-double-y-pfcs-shape
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p))
           (and (equal (pfield::sub (pfield::add 2 x2 p) y2 p)
                       (pfield::sub 2
                                    (pfield::add (pfield::mul (ecurve::edwards-bls12-a)
                                                              x2 p)
                                                 y2 p)
                                    p))
                (equal (pfield::add y2 x2 p)
                       (pfield::sub y2
                                    (pfield::mul (ecurve::edwards-bls12-a) x2 p)
                                    p))))
  :hints (("Goal"
           :in-theory (e/d (pfield::sub
                            group-inject-coeff-neg-one
                            primep-when-equal-base-prime)
                           ((:definition pfield::add)
                            (:definition pfield::mul)
                            (:definition pfield::neg)
                            (:executable-counterpart pfield::neg)
                            (:executable-counterpart pfield::mul)
                            (:executable-counterpart pfield::add)
                            pfield::neg-when-constant-arg1
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mul-commutative)))))

(define literal-group-square-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_square(a, c) := { (a) * (a) == (c) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-square-circuit) :pred literal-group-square-pred :prime p)

(defruled literal-group-square-pred-to-mul
  (implies (equal p (base-prime))
           (equal (literal-group-square-pred a c p)
                  (equal (pfield::mul a a p) c)))
  :enable literal-group-square-pred)

(define literal-group-prod-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_prod(a, b, c) := { (a) * (b) == (c) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-prod-circuit) :pred literal-group-prod-pred :prime p)

(defruled literal-group-prod-pred-to-mul
  (implies (equal p (base-prime))
           (equal (literal-group-prod-pred a b c p)
                  (equal (pfield::mul a b p) c)))
  :enable literal-group-prod-pred)

(define literal-group-on-curve-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_on_curve(y2, x2) := {
    (y2) * (3021 * x2 + (- 1)) == ((- 1) * x2 + (- 1))
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-on-curve-circuit)
            :pred literal-group-on-curve-pred :prime p)

(defruled literal-group-on-curve-pred-to-equation
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p))
           (equal (literal-group-on-curve-pred y2 x2 p)
                  (group-on-curve-equation y2 x2 p)))
  :hints (("Goal"
           :in-theory (e/d (literal-group-on-curve-pred
                            group-on-curve-equation
                            literal-pfcs-mod-consts
                            group-inject-coeff-neg-one)
                           ((:definition pfield::sub)
                            (:definition pfield::add)
                            (:definition pfield::mul)
                            (:definition pfield::neg)
                            (:executable-counterpart pfield::neg)
                            pfield::neg-when-constant-arg1
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mul-commutative)))))

(define literal-group-double-x-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_double_x(x3, x2, y2, xy) := {
    (x3) * ((- 1) * x2 + y2) == (2 * xy)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-double-x-circuit)
            :pred literal-group-double-x-pred :prime p)

(defruled literal-group-double-x-pred-to-equation
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (pfield::fep x3 p)
                (pfield::fep xy p))
           (equal (literal-group-double-x-pred x3 x2 y2 xy p)
                  (group-double-x-equation x3 x2 y2 xy p)))
  :hints (("Goal"
           :in-theory (e/d (literal-group-double-x-pred
                            group-double-x-equation
                            literal-pfcs-mod-consts
                            group-inject-coeff-neg-one)
                           ((:definition pfield::sub)
                            (:definition pfield::add)
                            (:definition pfield::mul)
                            (:definition pfield::neg)
                            (:executable-counterpart pfield::neg)
                            pfield::neg-when-constant-arg1
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mul-commutative)))))

(define literal-group-double-y-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_double_y(y3, x2, y2) := {
    (y3) * (2 + x2 - y2) == (y2 + x2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-double-y-circuit)
            :pred literal-group-double-y-pred :prime p)

(defruled literal-group-double-y-pred-to-equation
  (implies (and (equal p (base-prime))
                (pfield::fep x2 p)
                (pfield::fep y2 p)
                (pfield::fep y3 p))
           (equal (literal-group-double-y-pred y3 x2 y2 p)
                  (group-double-y-equation y3 x2 y2 p)))
  :hints (("Goal"
           :do-not '(fertilize generalize)
           :use ((:instance group-double-y-pfcs-shape (x2 x2) (y2 y2) (p p)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-group-double-y-pred
                         group-double-y-equation
                         literal-pfcs-mod-consts
                         group-inject-coeff-neg-one
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(define literal-group-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_group_new(x, y, qx, qy, cx2, cy2, dxy, dx2, dy2, x3, y3, exy, ex2, ey2) := {
    literal_group_square(qx, cx2),
    literal_group_square(qy, cy2),
    literal_group_on_curve(cy2, cx2),
    literal_group_prod(qx, qy, dxy),
    literal_group_square(qx, dx2),
    literal_group_square(qy, dy2),
    literal_group_double_x(x3, dx2, dy2, dxy),
    literal_group_double_y(y3, dx2, dy2),
    literal_group_prod(x3, y3, exy),
    literal_group_square(x3, ex2),
    literal_group_square(y3, ey2),
    literal_group_double_x(x, ex2, ey2, exy),
    literal_group_double_y(y, ex2, ey2)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-group-new-circuit) :pred literal-group-new-pred :prime p)

(defruled literal-group-new-pred-to-equations
  (implies (and (equal p (base-prime))
                (pfield::fep x p) (pfield::fep y p)
                (pfield::fep qx p) (pfield::fep qy p)
                (pfield::fep cx2 p) (pfield::fep cy2 p)
                (pfield::fep dxy p) (pfield::fep dx2 p) (pfield::fep dy2 p)
                (pfield::fep x3 p) (pfield::fep y3 p)
                (pfield::fep exy p) (pfield::fep ex2 p) (pfield::fep ey2 p))
           (equal (literal-group-new-pred
                   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                  (group-enforce-in-group-equations
                   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)))
  :hints (("Goal"
           :in-theory (e/d (literal-group-new-pred
                            group-enforce-in-group-equations
                            literal-group-square-pred-to-mul
                            literal-group-prod-pred-to-mul
                            literal-group-on-curve-pred-to-equation
                            literal-group-double-x-pred-to-equation
                            literal-group-double-y-pred-to-equation)
                           ((:definition group-on-curve-equation)
                            (:definition group-double-x-equation)
                            (:definition group-double-y-equation)
                            (:definition pfield::mul)
                            pfield::mul-commutative)))))

(define literal-id-or-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_or(x, y, z) := { (1 - x) * (1 - y) == (1 - z) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-or-circuit) :pred literal-id-or-pred :prime p)

(defruled literal-id-or-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-or-pred x y z p)
                  (equal (pfield::mul (pfield::sub 1 x p)
                                      (pfield::sub 1 y p)
                                      p)
                         (pfield::sub 1 z p))))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-or-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-or-gadget-to-eq
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget x y z p) asg p)
                  (equal (pfield::mul (pfield::sub 1 (lookup-equal x asg) p)
                                      (pfield::sub 1 (lookup-equal y asg) p)
                                      p)
                         (pfield::sub 1 (lookup-equal z asg) p))))
  :hints (("Goal"
           :in-theory (e/d (boolean-or-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            group-inject-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled literal-id-or-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (literal-id-or-pred (lookup-equal x asg)
                                   (lookup-equal y asg)
                                   (lookup-equal z asg)
                                   p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-or-gadget x y z p) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-id-or-pred-to-eq
                              literal-id-or-gadget-to-eq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::new is boolean_assert.  Integer::new is boolean_assert_all.

(defruled fe-listp-of-lookup-equal-list
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (pfield::fe-listp (lookup-equal-list xs asg) p))
  :hints (("Goal"
           :in-theory (enable lookup-equal-list
                              r1cs::valuation-binds-allp
                              pfield::fe-listp
                              r1cs::fep-of-lookup-equal))))

(defruled literal-boolean-pfcs-iff-r1cs
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (boolean-assert-pred (lookup-equal b asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget b p) asg p)))
  :hints (("Goal"
           :in-theory (enable boolean-assert-pred-to-spec
                              boolean-assert-spec
                              boolean-check-gadget-to-bitp
                              r1cs::fep-of-lookup-equal
                              primep-when-equal-base-prime))))

(defruled literal-bits-pfcs-iff-r1cs
  (implies (and (symbol-listp xs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (boolean-assert-all-pred (lookup-equal-list xs asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget-list xs p) asg p)))
  :hints (("Goal"
           :in-theory (enable boolean-assert-all-pred-to-spec
                              boolean-check-gadget-list-to-bit-listp
                              fe-listp-of-lookup-equal-list
                              primep-when-equal-base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::new and Scalar::new emit nothing.

(define literal-field-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def "literal_field_new() := { }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-field-new-circuit) :pred literal-field-new-pred :prime p)

(defruled literal-field-pfcs-iff-r1cs
  (equal (literal-field-new-pred p)
         (r1cs::r1cs-constraints-holdp (literal-field-new-gadget) asg p))
  :hints (("Goal" :in-theory (enable literal-field-new-pred
                                      literal-field-new-gadget))))

(define literal-scalar-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def "literal_scalar_new() := { }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-scalar-new-circuit) :pred literal-scalar-new-pred :prime p)

(defruled literal-scalar-pfcs-iff-r1cs
  (equal (literal-scalar-new-pred p)
         (r1cs::r1cs-constraints-holdp (literal-scalar-new-gadget) asg p))
  :hints (("Goal" :in-theory (enable literal-scalar-new-pred
                                      literal-scalar-new-gadget))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; String size assert_eq.  The length is a coefficient of the constant one,
; not a witness wire.

(define literal-string-size-circuit ((n natp))
  :returns (pdef pfcs::definitionp)
  (pfdef (pfname "literal_string_size" (nfix n))
         (list (pfname "size"))
         (pf= (pf* (pfconst (nfix n)) (pfconst 1))
              (pfvar (pfname "size"))))
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal"
                  :in-theory (enable literal-string-size-circuit
                                     pfcs::sr1cs-definitionp
                                     pfcs::sr1cs-constraintp
                                     pfcs::r1cs-constraintp
                                     pfcs::r1cs-polynomialp
                                     pfcs::r1cs-monomialp))))))

(defund literal-string-size-pred (n size p)
  (equal (pfield::mul (mod (nfix n) p) (mod 1 p) p) size))

(defruled literal-string-size-pred-to-len
  (implies (and (equal p (base-prime))
                (natp n)
                (< n p)
                (pfield::fep size p))
           (equal (literal-string-size-pred n size p)
                  (equal size n)))
  :hints (("Goal"
           :in-theory (e/d (literal-string-size-pred
                            literal-pfcs-mod-consts
                            primep-when-equal-base-prime)
                           (pfield::mul-commutative)))))

(defruled literal-string-size-pfcs-iff-r1cs
  (implies (and (symbolp size)
                (natp n)
                (equal p (base-prime))
                (< n p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size))
           (equal (literal-string-size-pred n (lookup-equal size asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (literal-string-size-gadget size n p) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-string-size-pred-to-len
                              literal-string-size-gadget-to-len
                              r1cs::fep-of-lookup-equal
                              primep-when-equal-base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled literal-group-new-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (qx$ (lookup-equal qx asg))
                (qy$ (lookup-equal qy asg))
                (cx2$ (lookup-equal cx2 asg))
                (cy2$ (lookup-equal cy2 asg))
                (dxy$ (lookup-equal dxy asg))
                (dx2$ (lookup-equal dx2 asg))
                (dy2$ (lookup-equal dy2 asg))
                (x3$ (lookup-equal x3 asg))
                (y3$ (lookup-equal y3 asg))
                (exy$ (lookup-equal exy asg))
                (ex2$ (lookup-equal ex2 asg))
                (ey2$ (lookup-equal ey2 asg)))
             (equal (literal-group-new-pred
                     x$ y$ qx$ qy$ cx2$ cy2$ dxy$ dx2$ dy2$
                     x3$ y3$ exy$ ex2$ ey2$ p)
                    (r1cs::r1cs-constraints-holdp
                     (group-enforce-in-group-gadget
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                     asg p))))
  :hints (("Goal"
           :in-theory (e/d (literal-group-new-pred-to-equations
                            group-enforce-in-group-gadget-to-equations
                            r1cs::fep-of-lookup-equal
                            primep-when-equal-base-prime)
                           (pfield::mul-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier validate_byte, one relation per emitted constraint shape.

(define literal-id-b7-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def "literal_id_b7(b7) := { (b7) * (1) == (0) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-b7-circuit) :pred literal-id-b7-pred :prime p)

(defruled literal-id-b7-pred-to-eq
  (implies (and (equal p (base-prime))
                (pfield::fep b7 p))
           (equal (literal-id-b7-pred b7 p)
                  (equal b7 0)))
  :hints (("Goal"
           :in-theory (e/d (literal-id-b7-pred
                            literal-pfcs-mod-consts
                            primep-when-equal-base-prime)
                           (pfield::mul-commutative)))))

(defruled literal-id-b7-pred-to-r1cs
  (implies (and (symbolp b7)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b7))
           (equal (literal-id-b7-pred (lookup-equal b7 asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-b7-zero-gadget b7) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-id-b7-pred-to-eq
                              id-b7-zero-gadget-to-zero
                              r1cs::fep-of-lookup-equal
                              primep-when-equal-base-prime))))

(define literal-id-and-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_and(x, y, z) := { (x) * (y) == (z) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-and-circuit) :pred literal-id-and-pred :prime p)

(defruled literal-id-and-pred-to-mul
  (implies (equal p (base-prime))
           (equal (literal-id-and-pred x y z p)
                  (equal (pfield::mul x y p) z)))
  :enable literal-id-and-pred)

(defruled literal-id-and-gadget-to-mul
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-and-gadget x y z) asg p)
                  (equal (pfield::mul (lookup-equal x asg)
                                      (lookup-equal y asg) p)
                         (lookup-equal z asg))))
  :hints (("Goal"
           :in-theory (e/d (boolean-and-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           (pfield::mul-commutative)))))

(defruled literal-id-and-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (literal-id-and-pred (lookup-equal x asg)
                                       (lookup-equal y asg)
                                       (lookup-equal z asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-and-gadget x y z) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-id-and-pred-to-mul
                              literal-id-and-gadget-to-mul
                              primep-when-equal-base-prime))))

(define literal-id-low5-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_low5(b0, b1, b2, b3, b4, m, r) := {
    (b0 + b1 + b2 + b3 + b4) * (m) == (r),
    (b0 + b1 + b2 + b3 + b4) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-low5-circuit) :pred literal-id-low5-pred :prime p)

(defruled literal-id-low5-pred-to-equations
  (implies (equal p (base-prime))
           (equal (literal-id-low5-pred b0 b1 b2 b3 b4 m r p)
                  (and (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p)
                                           m p)
                              r)
                       (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p)
                                           (pfield::sub 1 r p) p)
                              0))))
  :hints (("Goal"
           :in-theory (e/d (literal-id-low5-pred
                            id-low5-sum
                            literal-pfcs-mod-consts)
                           ((:definition pfield::add)
                            (:definition pfield::sub)
                            (:definition pfield::mul)
                            pfield::add-commutative
                            pfield::add-commutative-2
                            pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled literal-id-low5-pred-to-r1cs
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2)
                (symbolp b3) (symbolp b4)
                (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (equal (literal-id-low5-pred (lookup-equal b0 asg)
                                        (lookup-equal b1 asg)
                                        (lookup-equal b2 asg)
                                        (lookup-equal b3 asg)
                                        (lookup-equal b4 asg)
                                        (lookup-equal m asg)
                                        (lookup-equal r asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-low5-neq-gadget b0 b1 b2 b3 b4 m r p) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-id-low5-pred-to-equations
                              id-low5-neq-gadget-to-equations))))

(define literal-id-null-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_null(b6, b5, null) := { (1 - b6) * (1 - b5) == (null) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-null-circuit) :pred literal-id-null-pred :prime p)

(defruled literal-id-null-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-null-pred b6 b5 null p)
                  (equal null
                         (pfield::mul (pfield::sub 1 b6 p)
                                      (pfield::sub 1 b5 p) p))))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-null-pred
                         literal-pfcs-mod-consts
                         literal-pfcs-equal-commute-mul
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-null-pred-to-r1cs
  (implies (and (symbolp b6) (symbolp b5) (symbolp null)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg null))
           (equal (literal-id-null-pred (lookup-equal b6 asg)
                                        (lookup-equal b5 asg)
                                        (lookup-equal null asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-null-gadget b6 b5 null p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-null-pred-to-eq
                                      id-null-gadget-to-mul))))

(define literal-id-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def "literal_id_zero(a, b) := { (a) * (b) == (0) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-zero-circuit) :pred literal-id-zero-pred :prime p)

(defruled literal-id-zero-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-zero-pred a b p)
                  (equal (pfield::mul a b p) 0)))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-zero-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-zero-pred-to-r1cs
  (implies (and (symbolp a) (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b))
           (equal (literal-id-zero-pred (lookup-equal a asg)
                                        (lookup-equal b asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-zero-prod-gadget a b) asg p)))
  :hints (("Goal"
           :in-theory (enable literal-id-zero-pred-to-eq
                              id-zero-prod-gadget-to-mul
                              primep-when-equal-base-prime))))

(define literal-id-digit-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_digit(b5, lower, b4, idig) := {
    (b5 - lower) * (1 - b4 + idig) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-digit-circuit) :pred literal-id-digit-pred :prime p)

(defruled literal-id-digit-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-digit-pred b5 lower b4 idig p)
                  (equal (pfield::mul (pfield::sub b5 lower p)
                                      (pfield::add (pfield::sub 1 b4 p)
                                                   idig p) p)
                         0)))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-digit-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-digit-pred-to-r1cs
  (implies (and (symbolp b5) (symbolp lower) (symbolp b4) (symbolp idig)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg idig))
           (equal (literal-id-digit-pred (lookup-equal b5 asg)
                                         (lookup-equal lower asg)
                                         (lookup-equal b4 asg)
                                         (lookup-equal idig asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-digit-enforce-gadget b5 lower b4 idig p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-digit-pred-to-eq
                                      id-digit-enforce-gadget-to-mul))))

(define literal-id-xor-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_xor(x, y, z) := { (2 * x) * (y) == (y + x - z) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-xor-circuit) :pred literal-id-xor-pred :prime p)

(defruled literal-id-xor-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-xor-pred x y z p)
                  (equal (pfield::mul (pfield::mul 2 x p) y p)
                         (pfield::sub (pfield::add y x p) z p))))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-xor-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-xor-gadget-to-eq
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-xor-gadget x y z p) asg p)
                  (equal (pfield::mul (pfield::mul 2 (lookup-equal x asg) p)
                                      (lookup-equal y asg) p)
                         (pfield::sub (pfield::add (lookup-equal y asg)
                                                   (lookup-equal x asg) p)
                                      (lookup-equal z asg) p))))
  :hints (("Goal"
           :in-theory (e/d (boolean-xor-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            group-inject-coeff-neg-one
                            literal-pfcs-mod-consts)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled literal-id-xor-pred-to-r1cs
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (literal-id-xor-pred (lookup-equal x asg)
                                       (lookup-equal y asg)
                                       (lookup-equal z asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-xor-gadget x y z p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-xor-pred-to-eq
                                      literal-id-xor-gadget-to-eq))))

(define literal-id-upper-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_upper(b6, lower, r, bad) := {
    (b6 - lower) * (1 - r + bad) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-upper-circuit) :pred literal-id-upper-pred :prime p)

(defruled literal-id-upper-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-upper-pred b6 lower r bad p)
                  (equal (pfield::mul (pfield::sub b6 lower p)
                                      (pfield::add (pfield::sub 1 r p)
                                                   bad p) p)
                         0)))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-upper-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-upper-pred-to-r1cs
  (implies (and (symbolp b6) (symbolp lower) (symbolp r) (symbolp bad)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg bad))
           (equal (literal-id-upper-pred (lookup-equal b6 asg)
                                         (lookup-equal lower asg)
                                         (lookup-equal r asg)
                                         (lookup-equal bad asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-upper-lc-enforce-gadget b6 lower r bad p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-upper-pred-to-eq
                                      id-upper-lc-enforce-gadget-to-mul))))

(define literal-id-cat-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_cat(left, r, bad) := {
    (left) * (1 - r + bad) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-cat-circuit) :pred literal-id-cat-pred :prime p)

(defruled literal-id-cat-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-cat-pred left r bad p)
                  (equal (pfield::mul left
                                      (pfield::add (pfield::sub 1 r p)
                                                   bad p) p)
                         0)))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-cat-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-cat-pred-to-r1cs
  (implies (and (symbolp left) (symbolp r) (symbolp bad)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg left)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg bad))
           (equal (literal-id-cat-pred (lookup-equal left asg)
                                       (lookup-equal r asg)
                                       (lookup-equal bad asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-category-enforce-gadget left r bad p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-cat-pred-to-eq
                                      id-category-enforce-gadget-to-mul))))

(define literal-id-letter-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_letter(b6, uscore, islet) := {
    (b6) * (1 - uscore) == (islet)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-letter-circuit) :pred literal-id-letter-pred :prime p)

(defruled literal-id-letter-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-letter-pred b6 uscore islet p)
                  (equal islet
                         (pfield::mul b6 (pfield::sub 1 uscore p) p))))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-letter-pred
                         literal-pfcs-mod-consts
                         literal-pfcs-equal-commute-mul
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-letter-pred-to-r1cs
  (implies (and (symbolp b6) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet))
           (equal (literal-id-letter-pred (lookup-equal b6 asg)
                                          (lookup-equal uscore asg)
                                          (lookup-equal islet asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-letter-gadget b6 uscore islet p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-letter-pred-to-eq
                                      id-letter-gadget-to-mul))))

(define literal-id-assert-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def "literal_id_assert(b) := { (b) * (1) == (1) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-assert-circuit) :pred literal-id-assert-pred :prime p)

(defruled literal-id-assert-pred-to-eq
  (implies (and (equal p (base-prime))
                (pfield::fep b p))
           (equal (literal-id-assert-pred b p)
                  (equal b 1)))
  :hints (("Goal"
           :in-theory (e/d (literal-id-assert-pred
                            literal-pfcs-mod-consts
                            primep-when-equal-base-prime)
                           (pfield::mul-commutative)))))

(defruled literal-id-assert-pred-to-r1cs
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (literal-id-assert-pred (lookup-equal b asg) p)
                  (r1cs::r1cs-constraints-holdp (assert-gadget b) asg p)))
  :hints (("Goal"
           :in-theory (e/d (literal-id-assert-pred-to-eq
                            assert-gadget-to-funspec
                            assert-funspec
                            enforce-funspec
                            r1cs::fep-of-lookup-equal
                            primep-when-equal-base-prime)
                           (pfield::mul-commutative)))))

(define literal-id-trail1-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_trail1(prev, next) := { (prev) * (1 - next) == (0) }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-trail1-circuit) :pred literal-id-trail1-pred :prime p)

(defruled literal-id-trail1-pred-to-eq
  (implies (equal p (base-prime))
           (equal (literal-id-trail1-pred prev next p)
                  (equal (pfield::mul prev (pfield::sub 1 next p) p) 0)))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(literal-id-trail1-pred
                         literal-pfcs-mod-consts
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff))))))

(defruled literal-id-trail1-pred-to-r1cs
  (implies (and (symbolp prev) (symbolp next)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-bindsp asg next))
           (equal (literal-id-trail1-pred (lookup-equal prev asg)
                                          (lookup-equal next asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-trail-gadget prev next p) asg p)))
  :hints (("Goal" :in-theory (enable literal-id-trail1-pred-to-eq
                                      id-trail-gadget-to-mul))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-id-byte-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_byte(b0, b1, b2, b3, b4, b5, b6, b7, b4b3, b1b0, m, r, null, lower, dor, idig, xor, bu, lor, bl) := {
    literal_id_b7(b7),
    literal_id_and(b4, b3, b4b3),
    literal_id_and(b1, b0, b1b0),
    literal_id_low5(b0, b1, b2, b3, b4, m, r),
    literal_id_null(b6, b5, null),
    literal_id_and(b6, b5, lower),
    literal_id_zero(null, r),
    literal_id_or(b2, b1, dor),
    literal_id_and(b3, dor, idig),
    literal_id_digit(b5, lower, b4, idig),
    literal_id_xor(b2, b1b0, xor),
    literal_id_and(b4b3, xor, bu),
    literal_id_upper(b6, lower, r, bu),
    literal_id_or(b2, b1b0, lor),
    literal_id_and(b4b3, lor, bl),
    literal_id_cat(lower, r, bl)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-byte-circuit) :pred literal-id-byte-pred :prime p)

(defruled literal-id-byte-pred-to-r1cs
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits))
           (equal (literal-id-byte-pred
                   (lookup-equal (nth 0 bits) asg)
                   (lookup-equal (nth 1 bits) asg)
                   (lookup-equal (nth 2 bits) asg)
                   (lookup-equal (nth 3 bits) asg)
                   (lookup-equal (nth 4 bits) asg)
                   (lookup-equal (nth 5 bits) asg)
                   (lookup-equal (nth 6 bits) asg)
                   (lookup-equal (nth 7 bits) asg)
                   (lookup-equal (nth 0 wits) asg)
                   (lookup-equal (nth 1 wits) asg)
                   (lookup-equal (nth 2 wits) asg)
                   (lookup-equal (nth 3 wits) asg)
                   (lookup-equal (nth 4 wits) asg)
                   (lookup-equal (nth 5 wits) asg)
                   (lookup-equal (nth 6 wits) asg)
                   (lookup-equal (nth 7 wits) asg)
                   (lookup-equal (nth 8 wits) asg)
                   (lookup-equal (nth 9 wits) asg)
                   (lookup-equal (nth 10 wits) asg)
                   (lookup-equal (nth 11 wits) asg)
                   p)
                  (r1cs::r1cs-constraints-holdp
                   (id-byte-gadget bits wits p) asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (literal-id-byte-pred
                            id-byte-gadget
                            literal-id-b7-pred-to-r1cs
                            literal-id-and-pred-to-r1cs
                            literal-id-low5-pred-to-r1cs
                            literal-id-null-pred-to-r1cs
                            literal-id-zero-pred-to-r1cs
                            literal-id-or-pred-to-r1cs
                            literal-id-digit-pred-to-r1cs
                            literal-id-xor-pred-to-r1cs
                            literal-id-upper-pred-to-r1cs
                            literal-id-cat-pred-to-r1cs
                            member-equal-of-nth
                            symbolp-of-nth
                            r1cs::fep-of-lookup-equal
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            primep-when-equal-base-prime
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth
                            (:definition nth)
                            (:definition r1cs::valuation-binds-allp))))))

(define literal-id-first-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "literal_id_first(b4b3, b1b0, b2, b6, partial, uscore, islet) := {
    literal_id_and(b4b3, b1b0, partial),
    literal_id_and(partial, b2, uscore),
    literal_id_letter(b6, uscore, islet),
    literal_id_assert(islet)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (literal-id-first-circuit) :pred literal-id-first-pred :prime p)

(defruled literal-id-first-pred-to-r1cs
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2) (symbolp b6)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet))
           (equal (literal-id-first-pred (lookup-equal b4b3 asg)
                                         (lookup-equal b1b0 asg)
                                         (lookup-equal b2 asg)
                                         (lookup-equal b6 asg)
                                         (lookup-equal partial asg)
                                         (lookup-equal uscore asg)
                                         (lookup-equal islet asg) p)
                  (r1cs::r1cs-constraints-holdp
                   (id-first-extra-gadget b4b3 b1b0 b2 b6
                                          partial uscore islet p)
                   asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (literal-id-first-pred
                            id-first-extra-gadget
                            literal-id-and-pred-to-r1cs
                            literal-id-letter-pred-to-r1cs
                            literal-id-assert-pred-to-r1cs
                            r1cs::fep-of-lookup-equal
                            primep-when-equal-base-prime
                            r1cs::r1cs-constraints-holdp-of-append)
                           (pfield::mul-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Families over the byte list.  The ground relations above are called once
; per row; these predicates are that conjunction.

(defund literal-id-bits-pred (bitrows asg p)
  (or (atom bitrows)
      (and (boolean-assert-all-pred (lookup-equal-list (car bitrows) asg) p)
           (literal-id-bits-pred (cdr bitrows) asg p))))

(defun literal-id-bits-induct (bitrows witrows)
  (if (or (atom bitrows) (atom witrows))
      nil
    (literal-id-bits-induct (cdr bitrows) (cdr witrows))))

(defruled literal-id-bits-pred-to-r1cs
  (implies (and (id-bitrows-p bitrows)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg))
           (equal (literal-id-bits-pred bitrows asg p)
                  (r1cs::r1cs-constraints-holdp
                   (id-bit-checks bitrows p) asg p)))
  :hints (("Goal"
           :induct (literal-id-bits-induct bitrows witrows)
           :in-theory (e/d (literal-id-bits-pred
                            literal-id-bits-induct
                            id-bit-checks
                            id-bitrows-p
                            id-rows-boundp
                            literal-bits-pfcs-iff-r1cs
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth)))
          ("Subgoal *1/2" :do-not-induct t)))

(defund literal-id-byte-row-pred (bits wits asg p)
  (literal-id-byte-pred
   (lookup-equal (nth 0 bits) asg)
   (lookup-equal (nth 1 bits) asg)
   (lookup-equal (nth 2 bits) asg)
   (lookup-equal (nth 3 bits) asg)
   (lookup-equal (nth 4 bits) asg)
   (lookup-equal (nth 5 bits) asg)
   (lookup-equal (nth 6 bits) asg)
   (lookup-equal (nth 7 bits) asg)
   (lookup-equal (nth 0 wits) asg)
   (lookup-equal (nth 1 wits) asg)
   (lookup-equal (nth 2 wits) asg)
   (lookup-equal (nth 3 wits) asg)
   (lookup-equal (nth 4 wits) asg)
   (lookup-equal (nth 5 wits) asg)
   (lookup-equal (nth 6 wits) asg)
   (lookup-equal (nth 7 wits) asg)
   (lookup-equal (nth 8 wits) asg)
   (lookup-equal (nth 9 wits) asg)
   (lookup-equal (nth 10 wits) asg)
   (lookup-equal (nth 11 wits) asg)
   p))

(defund literal-id-rest-pred (bitrows witrows asg p)
  (or (atom bitrows)
      (atom witrows)
      (and (literal-id-byte-row-pred (car bitrows) (car witrows) asg p)
           (literal-id-rest-pred (cdr bitrows) (cdr witrows) asg p))))

(defun literal-id-rest-induct (bitrows witrows)
  (if (or (atom bitrows) (atom witrows))
      nil
    (literal-id-rest-induct (cdr bitrows) (cdr witrows))))

(defruled literal-id-rest-pred-to-r1cs
  (implies (and (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (equal (len bitrows) (len witrows))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg))
           (equal (literal-id-rest-pred bitrows witrows asg p)
                  (r1cs::r1cs-constraints-holdp
                   (id-rest-bytes-gadget bitrows witrows p) asg p)))
  :hints (("Goal"
           :induct (literal-id-rest-induct bitrows witrows)
           :in-theory (e/d (literal-id-rest-pred
                            literal-id-byte-row-pred
                            literal-id-rest-induct
                            id-rest-bytes-gadget
                            id-bitrows-p
                            id-witrows-p
                            id-rows-boundp
                            len
                            literal-id-byte-pred-to-r1cs
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth
                            (:definition nth)
                            (:definition id-byte-gadget))))
          ("Subgoal *1/2" :do-not-induct t)))

(defund literal-id-trail-pred (nulls asg p)
  (or (atom nulls)
      (atom (cdr nulls))
      (and (literal-id-trail1-pred (lookup-equal (car nulls) asg)
                                   (lookup-equal (cadr nulls) asg) p)
           (literal-id-trail-pred (cdr nulls) asg p))))

(defun literal-id-trail-induct (nulls)
  (if (or (atom nulls) (atom (cdr nulls)))
      nil
    (literal-id-trail-induct (cdr nulls))))

(defruled literal-id-trail-pred-to-r1cs
  (implies (and (symbol-listp nulls)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg nulls))
           (equal (literal-id-trail-pred nulls asg p)
                  (r1cs::r1cs-constraints-holdp
                   (id-trailing-gadget nulls p) asg p)))
  :hints (("Goal"
           :induct (literal-id-trail-induct nulls)
           :in-theory (e/d (literal-id-trail-pred
                            literal-id-trail-induct
                            id-trailing-gadget
                            symbol-listp
                            literal-id-trail1-pred-to-r1cs
                            member-equal-of-nth
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            (:definition r1cs::valuation-binds-allp)
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth
                            (:definition nth)
                            (:definition id-trail-gadget))))
          ("Subgoal *1/2" :do-not-induct t)))

(defund literal-id-new-pred (bitrows witrows partial uscore islet asg p)
  (and (consp bitrows)
       (consp witrows)
       (literal-id-bits-pred bitrows asg p)
       (literal-id-byte-row-pred (car bitrows) (car witrows) asg p)
       (literal-id-first-pred (lookup-equal (nth 0 (car witrows)) asg)
                              (lookup-equal (nth 1 (car witrows)) asg)
                              (lookup-equal (nth 2 (car bitrows)) asg)
                              (lookup-equal (nth 6 (car bitrows)) asg)
                              (lookup-equal partial asg)
                              (lookup-equal uscore asg)
                              (lookup-equal islet asg)
                              p)
       (literal-id-rest-pred (cdr bitrows) (cdr witrows) asg p)
       (literal-id-trail-pred (id-null-symbols witrows) asg p)))

(defruled literal-id-new-pred-to-r1cs
  :short "PFCS-SPEC of @('IdentifierLiteral::new'): the lifted relations
          hold of the wires iff @('identifier-new-gadget') does."
  (implies (and (consp bitrows)
                (consp witrows)
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (equal (len bitrows) (len witrows))
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (id-rows-boundp bitrows witrows asg))
           (equal (literal-id-new-pred bitrows witrows partial uscore islet asg p)
                  (r1cs::r1cs-constraints-holdp
                   (identifier-new-gadget bitrows witrows
                                          partial uscore islet p)
                   asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (literal-id-new-pred
                            literal-id-byte-row-pred
                            identifier-new-gadget
                            literal-id-bits-pred-to-r1cs
                            literal-id-byte-pred-to-r1cs
                            literal-id-first-pred-to-r1cs
                            literal-id-rest-pred-to-r1cs
                            literal-id-trail-pred-to-r1cs
                            id-null-symbols-boundp
                            id-bitrows-p
                            id-witrows-p
                            id-rows-boundp
                            id-bitrows-p-of-car
                            id-witrows-p-of-car
                            member-equal-of-nth
                            symbolp-of-nth
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth
                            (:definition nth)
                            (:definition id-byte-gadget)
                            (:definition id-first-extra-gadget)
                            (:definition id-bit-checks)
                            (:definition id-rest-bytes-gadget)
                            (:definition id-trailing-gadget)
                            (:definition id-null-symbols))))))
