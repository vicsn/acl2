; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ternary::ternary on Integer.
;
; In the variable-condition case snarkVM maps Boolean::ternary across the
; bits.  That is r1cs/integer-ternary, for every width and both signednesses.
; A constant condition selects a branch in the host and adds no constraint.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/integer-ternary")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-ternary-gadget ((c symbolp)
                            (xs symbol-listp)
                            (ys symbol-listp)
                            (zs symbol-listp)
                            (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Bits of @('if c then x else y')."
  (integer-ternary-gadget c xs ys zs p))

(defruled int-ternary-gadget-sound
  (implies (and (primep p)
                (symbolp c)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (bitp (lookup-equal c asg))
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-ternary-gadget c xs ys zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits
                   (int-ternary-spec (lookup-equal c asg) x y signedp n)
                   n)))
  :enable (int-ternary-gadget
           integer-ternary-gadget-correctness
           int-ternary-spec
           int->lebits))

(defruled int-ternary-gadget-complete
  (implies (and (primep p)
                (symbolp c)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (bitp (lookup-equal c asg))
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits
                        (int-ternary-spec (lookup-equal c asg) x y signedp n)
                        n)))
           (r1cs::r1cs-constraints-holdp
            (int-ternary-gadget c xs ys zs p) asg p))
  :enable (int-ternary-gadget
           integer-ternary-gadget-correctness
           int-ternary-spec
           int->lebits))

(defconst *int-ternary-sample*
  '((c . 1)
    (x0 . 1) (y0 . 0) (z0 . 1)
    (x1 . 0) (y1 . 1) (z1 . 0)))

(defruled int-ternary-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-ternary-gadget 'c '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-ternary-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-ternary-gadget
                                     integer-ternary-gadget
                                     if-gadget-variant
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "One bit of integer ternary: @('(c) (x - y) = (z - y)')."
  (pfcs::parse-def
   "int_ternary(c, x, y, z) := {
    (c) * (x - y) == (z - y)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-ternary-circuit) :pred int-ternary-pred :prime prime)

(defruled int-ternary-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp c)
                (int-valuep x nil 8)
                (int-valuep y nil 8)
                (int-valuep z nil 8)
                (< x (base-prime))
                (< y (base-prime))
                (< z (base-prime)))
           (equal (int-ternary-pred c x y z prime)
                  (equal z (int-ternary-spec c x y nil 8))))
  :enable (int-ternary-pred int-ternary-spec))
