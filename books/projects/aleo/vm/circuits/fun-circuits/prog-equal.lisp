; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS and PFCS for the program-crate equalities whose constraints are
; field inequality, boolean AND/OR, and (for a record version) inequality
; with zero.
;
; Boolean negation is the linear combination 1 - bit.

(in-package "ALEOVM")

(include-book "prog-primitives")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/values-value")
(include-book "../fun-specs/crypto-record")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled values-b-and-is-boolean-and
  (implies (and (bitp a) (bitp b))
           (equal (values-b-and a b) (boolean-and-funspec a b)))
  :hints (("Goal"
           :cases ((equal a 0) (equal b 0))
           :in-theory (enable values-b-and boolean-and-funspec bitp))))

(defruled values-b-or-is-boolean-or
  (implies (and (bitp a) (bitp b))
           (equal (values-b-or a b) (boolean-or-funspec a b)))
  :hints (("Goal"
           :cases ((equal a 0) (equal b 0))
           :in-theory (enable values-b-or boolean-or-funspec bitp))))

(defruled values-b-not-is-boolean-not
  (implies (bitp a)
           (equal (values-b-not a) (boolean-not-funspec a)))
  :hints (("Goal"
           :cases ((equal a 0))
           :in-theory (enable values-b-not boolean-not-funspec bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier::is_equal is Field::is_equal on the field elements.
; Identifier::is_not_equal is Field::is_not_equal on the same elements.

(define identifier-is-equal-gadget ((x symbolp)
                                    (y symbolp)
                                    (m symbolp)
                                    (r symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Identifier::is_equal'): field inequality,
          output bit @($1 - r$)."
  (prog-field-neq-gadget x y m r p))

(defruled identifier-is-equal-is-field-eq
  (implies (and (identifierp x) (identifierp y))
           (equal (identifier-is-equal x y)
                  (field-is-equal-funspec (identifier->field x)
                                          (identifier->field y))))
  :hints (("Goal"
           :cases ((equal (identifier->field x) (identifier->field y)))
           :in-theory (enable identifier-is-equal
                              field-is-equal-funspec
                              field-is-not-equal-funspec
                              boolean-not-funspec
                              values-bool-to-bit))))

(defruled identifier-is-equal-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (identifierp a)
                (identifierp b)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-equal-gadget x y m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (identifier-is-equal a b)))
  :enable (identifier-is-equal-gadget
           prog-field-eq-gadget-sound
           identifier-is-equal-is-field-eq
           fieldp))

(defruled identifier-is-equal-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (identifierp a)
                (identifierp b)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (equal (lookup-equal r asg)
                       (if (equal (identifier->field a)
                                  (identifier->field b))
                           0
                         1))
                (equal (lookup-equal m asg)
                       (if (equal (identifier->field a)
                                  (identifier->field b))
                           1
                         (pfield::inv (pfield::sub (identifier->field a)
                                                   (identifier->field b)
                                                   p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (identifier-is-equal-gadget x y m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (identifier-is-equal a b))))
  :enable (identifier-is-equal-gadget
           prog-field-eq-gadget-complete
           identifier-is-equal-is-field-eq
           fieldp))

(define identifier-is-not-equal-gadget ((x symbolp)
                                        (y symbolp)
                                        (m symbolp)
                                        (r symbolp)
                                        (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Identifier::is_not_equal'). The result is @('r')."
  (prog-field-neq-gadget x y m r p))

(defruled identifier-is-not-equal-funspecs-match
  (implies (and (identifierp x) (identifierp y))
           (equal (identifier-is-not-equal x y)
                  (boolean-not-funspec (identifier-is-equal x y))))
  :hints (("Goal"
           :cases ((equal (identifier->field x) (identifier->field y)))
           :in-theory (enable identifier-is-not-equal
                              identifier-is-equal
                              boolean-not-funspec
                              values-bool-to-bit))))

(defruled identifier-is-not-equal-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (identifierp a)
                (identifierp b)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-not-equal-gadget x y m r p) asg p))
           (equal (lookup-equal r asg)
                  (identifier-is-not-equal a b)))
  :enable (identifier-is-not-equal-gadget
           prog-field-neq-gadget-sound
           identifier-is-not-equal-funspecs-match
           identifier-is-equal-is-field-eq
           prog-bit-not-is-sub
           field-is-equal-funspec
           fieldp))

(defruled identifier-is-not-equal-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (identifierp a)
                (identifierp b)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (equal (lookup-equal r asg)
                       (if (equal (identifier->field a)
                                  (identifier->field b))
                           0
                         1))
                (equal (lookup-equal m asg)
                       (if (equal (identifier->field a)
                                  (identifier->field b))
                           1
                         (pfield::inv (pfield::sub (identifier->field a)
                                                   (identifier->field b)
                                                   p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (identifier-is-not-equal-gadget x y m r p) asg p)
                (equal (lookup-equal r asg)
                       (identifier-is-not-equal a b))))
  :enable (identifier-is-not-equal-gadget
           prog-field-neq-gadget-complete
           identifier-is-not-equal-funspecs-match
           identifier-is-equal-is-field-eq
           prog-bit-not-is-sub
           field-is-equal-funspec
           fieldp))

(defconst *identifier-is-equal-sample-asg*
  '((x . 3) (y . 1) (m . 3) (r . 1)))

(defruled identifier-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-is-equal-gadget 'x 'y 'm 'r 5)
   *identifier-is-equal-sample-asg*
   5)
  :enable (identifier-is-equal-gadget prog-field-neq-sample-holds))

(defruled identifier-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (identifier-is-not-equal-gadget 'x 'y 'm 'r 5)
   *identifier-is-equal-sample-asg*
   5)
  :enable (identifier-is-not-equal-gadget prog-field-neq-sample-holds))

(define identifier-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_is_equal(x, y, m, r) := {
    (x - y) * (m) == (r),
    (x - y) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-is-equal-circuit)
            :pred identifier-is-equal-pred
            :prime prime)

(defruled identifier-is-equal-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep x prime)
                (pfield::fep y prime)
                (pfield::fep m prime)
                (pfield::fep r prime))
           (equal (identifier-is-equal-pred x y m r prime)
                  (and (equal (pfield::mul (pfield::sub x y prime) m prime) r)
                       (equal (pfield::mul (pfield::sub x y prime)
                                           (pfield::sub 1 r prime)
                                           prime)
                              0))))
  :enable identifier-is-equal-pred)

(defruled identifier-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (fieldp y)
                (pfield::fep m prime)
                (bitp r)
                (identifierp a)
                (identifierp b)
                (equal x (identifier->field a))
                (equal y (identifier->field b))
                (identifier-is-equal-pred x y m r prime))
           (equal (pfield::sub 1 r prime)
                  (identifier-is-equal a b)))
  :enable (identifier-is-equal-pred-to-mul
           prog-field-neq-bit-when-constraints
           prog-bit-not-is-sub
           identifier-is-equal-is-field-eq
           field-is-equal-funspec
           fieldp))

(define identifier-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "identifier_is_not_equal(x, y, m, r) := {
    (x - y) * (m) == (r),
    (x - y) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (identifier-is-not-equal-circuit)
            :pred identifier-is-not-equal-pred
            :prime prime)

(defruled identifier-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (fieldp y)
                (pfield::fep m prime)
                (bitp r)
                (identifierp a)
                (identifierp b)
                (equal x (identifier->field a))
                (equal y (identifier->field b))
                (identifier-is-not-equal-pred x y m r prime))
           (equal r (identifier-is-not-equal a b)))
  :enable (identifier-is-not-equal-pred
           identifier-is-equal-pred-to-mul
           prog-field-neq-bit-when-constraints
           identifier-is-not-equal-funspecs-match
           identifier-is-equal-is-field-eq
           prog-bit-not-is-sub
           field-is-equal-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ProgramID::is_equal is the AND of the two identifier equalities.
; ProgramID::is_not_equal is the OR of the two identifier inequalities
; (it does not negate is_equal).

(define program-id-is-equal-gadget ((xn symbolp) (yn symbolp)
                                    (mn symbolp) (rn symbolp)
                                    (xw symbolp) (yw symbolp)
                                    (mw symbolp) (rw symbolp)
                                    (z symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('ProgramID::is_equal'): two field inequalities
          and the AND of the two equal-bits."
  (append (prog-field-neq-gadget xn yn mn rn p)
          (prog-field-neq-gadget xw yw mw rw p)
          (prog-eq-and-gadget rn rw z p)))

(defruled program-id-is-equal-components
  (implies (and (program-idp x) (program-idp y))
           (equal (program-id-is-equal x y)
                  (boolean-and-funspec
                   (identifier-is-equal (program-id->name x)
                                        (program-id->name y))
                   (identifier-is-equal (program-id->network x)
                                        (program-id->network y)))))
  :enable (program-id-is-equal values-b-and-is-boolean-and))

(defruled program-id-is-equal-gadget-sound
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg z)
                (program-idp a)
                (program-idp b)
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (bitp (lookup-equal rn asg))
                (bitp (lookup-equal rw asg))
                (r1cs::r1cs-constraints-holdp
                 (program-id-is-equal-gadget
                  xn yn mn rn xw yw mw rw z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (program-id-is-equal a b)))
  :enable (program-id-is-equal-gadget
           prog-field-neq-gadget-to-spec
           prog-eq-and-gadget-to-mul
           prog-field-neq-bit-when-constraints
           prog-eq-and-bit-when-mul
           prog-bit-not-is-sub
           program-id-is-equal-components
           identifier-is-equal-is-field-eq
           field-is-equal-funspec
           fieldp
           r1cs::fep-of-lookup-equal
           r1cs::r1cs-constraints-holdp-of-append))

(defruled program-id-is-equal-gadget-complete
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg z)
                (program-idp a)
                (program-idp b)
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (equal (lookup-equal rn asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xn asg) (lookup-equal yn asg)))
                (equal (lookup-equal rw asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xw asg) (lookup-equal yw asg)))
                (equal (lookup-equal mn asg)
                       (if (equal (lookup-equal xn asg) (lookup-equal yn asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xn asg)
                                                   (lookup-equal yn asg) p)
                                      p)))
                (equal (lookup-equal mw asg)
                       (if (equal (lookup-equal xw asg) (lookup-equal yw asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xw asg)
                                                   (lookup-equal yw asg) p)
                                      p)))
                (equal (lookup-equal z asg)
                       (boolean-and-funspec
                        (boolean-not-funspec (lookup-equal rn asg))
                        (boolean-not-funspec (lookup-equal rw asg)))))
           (r1cs::r1cs-constraints-holdp
            (program-id-is-equal-gadget xn yn mn rn xw yw mw rw z p)
            asg p))
  :enable (program-id-is-equal-gadget
           prog-field-neq-gadget-complete
           prog-eq-and-gadget-to-mul
           prog-eq-and-bit-when-mul
           field-is-not-equal-funspec
           boolean-not-funspec
           boolean-and-funspec
           fieldp
           bitp
           r1cs::r1cs-constraints-holdp-of-append))

(define program-id-is-not-equal-gadget ((xn symbolp) (yn symbolp)
                                        (mn symbolp) (rn symbolp)
                                        (xw symbolp) (yw symbolp)
                                        (mw symbolp) (rw symbolp)
                                        (z symbolp)
                                        (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('ProgramID::is_not_equal'): two field inequalities
          and the OR of the two inequality bits."
  (append (prog-field-neq-gadget xn yn mn rn p)
          (prog-field-neq-gadget xw yw mw rw p)
          (prog-bool-or-gadget rn rw z p)))

(defruled program-id-is-not-equal-components
  (implies (and (program-idp x) (program-idp y))
           (equal (program-id-is-not-equal x y)
                  (boolean-or-funspec
                   (identifier-is-not-equal (program-id->name x)
                                            (program-id->name y))
                   (identifier-is-not-equal (program-id->network x)
                                            (program-id->network y)))))
  :enable (program-id-is-not-equal values-b-or-is-boolean-or))

(defruled program-id-is-not-equal-gadget-sound
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg z)
                (program-idp a)
                (program-idp b)
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (bitp (lookup-equal rn asg))
                (bitp (lookup-equal rw asg))
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (program-id-is-not-equal-gadget
                  xn yn mn rn xw yw mw rw z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (program-id-is-not-equal a b)))
  :enable (program-id-is-not-equal-gadget
           prog-field-neq-gadget-sound
           prog-bool-or-gadget-sound
           program-id-is-not-equal-components
           identifier-is-not-equal-funspecs-match
           identifier-is-equal-is-field-eq
           prog-bit-not-is-sub
           field-is-equal-funspec
           fieldp
           r1cs::r1cs-constraints-holdp-of-append))

(defruled program-id-is-not-equal-gadget-complete
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg z)
                (program-idp a)
                (program-idp b)
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (equal (lookup-equal rn asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xn asg) (lookup-equal yn asg)))
                (equal (lookup-equal rw asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xw asg) (lookup-equal yw asg)))
                (equal (lookup-equal mn asg)
                       (if (equal (lookup-equal xn asg) (lookup-equal yn asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xn asg)
                                                   (lookup-equal yn asg) p)
                                      p)))
                (equal (lookup-equal mw asg)
                       (if (equal (lookup-equal xw asg) (lookup-equal yw asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xw asg)
                                                   (lookup-equal yw asg) p)
                                      p)))
                (equal (lookup-equal z asg)
                       (boolean-or-funspec (lookup-equal rn asg)
                                           (lookup-equal rw asg))))
           (r1cs::r1cs-constraints-holdp
            (program-id-is-not-equal-gadget xn yn mn rn xw yw mw rw z p)
            asg p))
  :enable (program-id-is-not-equal-gadget
           prog-field-neq-gadget-complete
           prog-bool-or-gadget-complete
           field-is-not-equal-funspec
           bitp
           fieldp
           r1cs::r1cs-constraints-holdp-of-append))

(defconst *program-id-is-equal-sample-asg*
  '((xn . 1) (yn . 1) (mn . 1) (rn . 0)
    (xw . 3) (yw . 1) (mw . 3) (rw . 1)
    (z . 0)))

(defruled program-id-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (program-id-is-equal-gadget 'xn 'yn 'mn 'rn 'xw 'yw 'mw 'rw 'z 5)
   *program-id-is-equal-sample-asg*
   5)
  :enable (program-id-is-equal-gadget
           prog-field-neq-gadget
           prog-eq-and-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(defconst *program-id-is-not-equal-sample-asg*
  '((xn . 1) (yn . 1) (mn . 1) (rn . 0)
    (xw . 3) (yw . 1) (mw . 3) (rw . 1)
    (z . 1)))

(defruled program-id-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (program-id-is-not-equal-gadget 'xn 'yn 'mn 'rn 'xw 'yw 'mw 'rw 'z 5)
   *program-id-is-not-equal-sample-asg*
   5)
  :enable (program-id-is-not-equal-gadget
           prog-field-neq-gadget
           prog-bool-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define program-id-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "program_id_is_equal(xn, yn, mn, rn, xw, yw, mw, rw, z) := {
    (xn - yn) * (mn) == (rn),
    (xn - yn) * (1 - rn) == (0),
    (xw - yw) * (mw) == (rw),
    (xw - yw) * (1 - rw) == (0),
    (1 - rn) * (1 - rw) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (program-id-is-equal-circuit)
            :pred program-id-is-equal-pred
            :prime prime)

(defruled program-id-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp xn) (fieldp yn) (pfield::fep mn prime) (bitp rn)
                (fieldp xw) (fieldp yw) (pfield::fep mw prime) (bitp rw)
                (program-idp a) (program-idp b)
                (equal xn (identifier->field (program-id->name a)))
                (equal yn (identifier->field (program-id->name b)))
                (equal xw (identifier->field (program-id->network a)))
                (equal yw (identifier->field (program-id->network b)))
                (program-id-is-equal-pred xn yn mn rn xw yw mw rw z prime))
           (equal z (program-id-is-equal a b)))
  :enable (program-id-is-equal-pred
           prog-field-neq-bit-when-constraints
           prog-eq-and-bit-when-mul
           prog-bit-not-is-sub
           program-id-is-equal-components
           identifier-is-equal-is-field-eq
           field-is-equal-funspec
           fieldp))

(define program-id-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "program_id_is_not_equal(xn, yn, mn, rn, xw, yw, mw, rw, z) := {
    (xn - yn) * (mn) == (rn),
    (xn - yn) * (1 - rn) == (0),
    (xw - yw) * (mw) == (rw),
    (xw - yw) * (1 - rw) == (0),
    (1 - rn) * (1 - rw) == (1 - z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (program-id-is-not-equal-circuit)
            :pred program-id-is-not-equal-pred
            :prime prime)

(defruled program-id-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp xn) (fieldp yn) (pfield::fep mn prime) (bitp rn)
                (fieldp xw) (fieldp yw) (pfield::fep mw prime) (bitp rw)
                (bitp z)
                (program-idp a) (program-idp b)
                (equal xn (identifier->field (program-id->name a)))
                (equal yn (identifier->field (program-id->name b)))
                (equal xw (identifier->field (program-id->network a)))
                (equal yw (identifier->field (program-id->network b)))
                (program-id-is-not-equal-pred
                 xn yn mn rn xw yw mw rw z prime))
           (equal z (program-id-is-not-equal a b)))
  :enable (program-id-is-not-equal-pred
           prog-field-neq-bit-when-constraints
           prog-bool-or-bit-when-mul
           program-id-is-not-equal-components
           identifier-is-not-equal-funspecs-match
           identifier-is-equal-is-field-eq
           prog-bit-not-is-sub
           field-is-equal-funspec
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DynamicFuture::is_equal ANDs four field equalities.
; DynamicFuture::is_not_equal is the negation of that result.

(define dynamic-future-is-equal-gadget
  ((xn symbolp) (yn symbolp) (mn symbolp) (rn symbolp)
   (xw symbolp) (yw symbolp) (mw symbolp) (rw symbolp)
   (xf symbolp) (yf symbolp) (mf symbolp) (rf symbolp)
   (xc symbolp) (yc symbolp) (mc symbolp) (rc symbolp)
   (z1 symbolp) (z2 symbolp) (z symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('DynamicFuture::is_equal'): four field
          inequalities and a chain of three ANDs of the equal-bits."
  (append (prog-field-neq-gadget xn yn mn rn p)
          (prog-field-neq-gadget xw yw mw rw p)
          (prog-field-neq-gadget xf yf mf rf p)
          (prog-field-neq-gadget xc yc mc rc p)
          (prog-eq-and-gadget rn rw z1 p)
          (prog-and-var-eq-gadget z1 rf z2 p)
          (prog-and-var-eq-gadget z2 rc z p)))

(defruled dynamic-future-is-equal-components
  (implies (and (dynamic-futurep x) (dynamic-futurep y)
                (fieldp (dynamic-future->program-name x))
                (fieldp (dynamic-future->program-name y))
                (fieldp (dynamic-future->program-network x))
                (fieldp (dynamic-future->program-network y))
                (fieldp (dynamic-future->function-name x))
                (fieldp (dynamic-future->function-name y))
                (fieldp (dynamic-future->checksum x))
                (fieldp (dynamic-future->checksum y)))
           (equal (dynamic-future-is-equal x y)
                  (boolean-and-funspec
                   (field-is-equal-funspec (dynamic-future->program-name x)
                                           (dynamic-future->program-name y))
                   (boolean-and-funspec
                    (field-is-equal-funspec (dynamic-future->program-network x)
                                            (dynamic-future->program-network y))
                    (boolean-and-funspec
                     (field-is-equal-funspec (dynamic-future->function-name x)
                                             (dynamic-future->function-name y))
                     (field-is-equal-funspec (dynamic-future->checksum x)
                                             (dynamic-future->checksum y)))))))
  :hints (("Goal"
           :in-theory (enable dynamic-future-is-equal
                              values-bool-to-bit
                              boolean-and-funspec
                              field-is-equal-funspec
                              field-is-not-equal-funspec
                              boolean-not-funspec
                              dynamic-future-fix
                              dynamic-future->program-name
                              dynamic-future->program-network
                              dynamic-future->function-name
                              dynamic-future->checksum
                              values-field-fix))))

(define dynamic-future-is-not-equal-gadget
  ((xn symbolp) (yn symbolp) (mn symbolp) (rn symbolp)
   (xw symbolp) (yw symbolp) (mw symbolp) (rw symbolp)
   (xf symbolp) (yf symbolp) (mf symbolp) (rf symbolp)
   (xc symbolp) (yc symbolp) (mc symbolp) (rc symbolp)
   (z1 symbolp) (z2 symbolp) (z symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as @('DynamicFuture::is_equal').
          The result bit is @($1 - z$)."
  (dynamic-future-is-equal-gadget xn yn mn rn xw yw mw rw
                                  xf yf mf rf xc yc mc rc
                                  z1 z2 z p))

(defruled dynamic-future-is-not-equal-funspecs-match
  (equal (dynamic-future-is-not-equal x y)
         (values-b-not (dynamic-future-is-equal x y)))
  :enable dynamic-future-is-not-equal)

(defconst *dynamic-future-is-equal-sample-asg*
  '((xn . 2) (yn . 2) (mn . 1) (rn . 0)
    (xw . 2) (yw . 2) (mw . 1) (rw . 0)
    (xf . 2) (yf . 2) (mf . 1) (rf . 0)
    (xc . 2) (yc . 2) (mc . 1) (rc . 0)
    (z1 . 1) (z2 . 1) (z . 1)))

(defruled dynamic-future-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (dynamic-future-is-equal-gadget
    'xn 'yn 'mn 'rn 'xw 'yw 'mw 'rw
    'xf 'yf 'mf 'rf 'xc 'yc 'mc 'rc
    'z1 'z2 'z 5)
   *dynamic-future-is-equal-sample-asg*
   5)
  :enable (dynamic-future-is-equal-gadget
           prog-field-neq-gadget
           prog-eq-and-gadget
           prog-and-var-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(defruled dynamic-future-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (dynamic-future-is-not-equal-gadget
    'xn 'yn 'mn 'rn 'xw 'yw 'mw 'rw
    'xf 'yf 'mf 'rf 'xc 'yc 'mc 'rc
    'z1 'z2 'z 5)
   *dynamic-future-is-equal-sample-asg*
   5)
  :enable (dynamic-future-is-not-equal-gadget
           dynamic-future-is-equal-sample-holds))

(defruled boolean-not-of-field-neq
  (implies (and (fieldp x)
                (fieldp y)
                (bitp r)
                (equal r (field-is-not-equal-funspec x y)))
           (equal (boolean-not-funspec r)
                  (field-is-equal-funspec x y)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (enable field-is-equal-funspec
                              field-is-not-equal-funspec
                              boolean-not-funspec
                              bitp))))

(defruled boolean-and-left-assoc-4
  :short "The circuit ANDs left to right. The funspec nests to the right."
  (implies (and (bitp a) (bitp b) (bitp c) (bitp d))
           (equal (boolean-and-funspec
                   (boolean-and-funspec
                    (boolean-and-funspec a b)
                    c)
                   d)
                  (boolean-and-funspec
                   a
                   (boolean-and-funspec
                    b
                    (boolean-and-funspec c d)))))
  :hints (("Goal"
           :cases ((equal a 0) (equal b 0) (equal c 0) (equal d 0))
           :in-theory (enable boolean-and-funspec bitp))))

(defruled dynamic-future-eq-equations-to-funspec
  :short "Four field-inequality witnesses and the left-associated AND chain
          are @('DynamicFuture::is_equal')."
  (implies (and (equal p (base-prime))
                (fieldp xn) (fieldp yn) (pfield::fep mn p) (bitp rn)
                (fieldp xw) (fieldp yw) (pfield::fep mw p) (bitp rw)
                (fieldp xf) (fieldp yf) (pfield::fep mf p) (bitp rf)
                (fieldp xc) (fieldp yc) (pfield::fep mc p) (bitp rc)
                (equal (pfield::mul (pfield::sub xn yn p) mn p) rn)
                (equal (pfield::mul (pfield::sub xn yn p)
                                    (pfield::sub 1 rn p)
                                    p)
                       0)
                (equal (pfield::mul (pfield::sub xw yw p) mw p) rw)
                (equal (pfield::mul (pfield::sub xw yw p)
                                    (pfield::sub 1 rw p)
                                    p)
                       0)
                (equal (pfield::mul (pfield::sub xf yf p) mf p) rf)
                (equal (pfield::mul (pfield::sub xf yf p)
                                    (pfield::sub 1 rf p)
                                    p)
                       0)
                (equal (pfield::mul (pfield::sub xc yc p) mc p) rc)
                (equal (pfield::mul (pfield::sub xc yc p)
                                    (pfield::sub 1 rc p)
                                    p)
                       0)
                (equal (pfield::mul (pfield::sub 1 rn p)
                                    (pfield::sub 1 rw p)
                                    p)
                       z1)
                (equal (pfield::mul z1 (pfield::sub 1 rf p) p) z2)
                (equal (pfield::mul z2 (pfield::sub 1 rc p) p) z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal xn (dynamic-future->program-name a))
                (equal yn (dynamic-future->program-name b))
                (equal xw (dynamic-future->program-network a))
                (equal yw (dynamic-future->program-network b))
                (equal xf (dynamic-future->function-name a))
                (equal yf (dynamic-future->function-name b))
                (equal xc (dynamic-future->checksum a))
                (equal yc (dynamic-future->checksum b)))
           (equal z (dynamic-future-is-equal a b)))
  :hints (("Goal"
           :in-theory (e/d (prog-field-neq-bit-when-constraints
                            prog-eq-and-mul-is-and
                            prog-and-var-eq-mul-is-and
                            boolean-not-of-field-neq
                            boolean-and-left-assoc-4
                            dynamic-future-is-equal-components
                            bitp-of-boolean-and-funspec
                            bitp-of-boolean-not-funspec
                            bitp-of-field-is-equal-funspec
                            bitp-of-field-is-not-equal-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance prog-eq-and-bit-when-mul
                            (ra rn) (rb rw) (z z1) (p p))
                 (:instance prog-and-var-eq-bit-when-mul
                            (z z1) (r rf) (w z2) (p p))
                 (:instance prog-and-var-eq-bit-when-mul
                            (z z2) (r rc) (w z) (p p))))))

(defruled dynamic-future-is-equal-gadget-sound
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp xf) (symbolp yf) (symbolp mf) (symbolp rf)
                (symbolp xc) (symbolp yc) (symbolp mc) (symbolp rc)
                (symbolp z1) (symbolp z2) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg xf)
                (r1cs::valuation-bindsp asg yf)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg xc)
                (r1cs::valuation-bindsp asg yc)
                (r1cs::valuation-bindsp asg mc)
                (r1cs::valuation-bindsp asg rc)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal (lookup-equal xn asg)
                       (dynamic-future->program-name a))
                (equal (lookup-equal yn asg)
                       (dynamic-future->program-name b))
                (equal (lookup-equal xw asg)
                       (dynamic-future->program-network a))
                (equal (lookup-equal yw asg)
                       (dynamic-future->program-network b))
                (equal (lookup-equal xf asg)
                       (dynamic-future->function-name a))
                (equal (lookup-equal yf asg)
                       (dynamic-future->function-name b))
                (equal (lookup-equal xc asg)
                       (dynamic-future->checksum a))
                (equal (lookup-equal yc asg)
                       (dynamic-future->checksum b))
                (fieldp (lookup-equal xn asg))
                (fieldp (lookup-equal yn asg))
                (fieldp (lookup-equal xw asg))
                (fieldp (lookup-equal yw asg))
                (fieldp (lookup-equal xf asg))
                (fieldp (lookup-equal yf asg))
                (fieldp (lookup-equal xc asg))
                (fieldp (lookup-equal yc asg))
                (bitp (lookup-equal rn asg))
                (bitp (lookup-equal rw asg))
                (bitp (lookup-equal rf asg))
                (bitp (lookup-equal rc asg))
                (r1cs::r1cs-constraints-holdp
                 (dynamic-future-is-equal-gadget
                  xn yn mn rn xw yw mw rw
                  xf yf mf rf xc yc mc rc
                  z1 z2 z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (dynamic-future-is-equal a b)))
  :hints (("Goal"
           :in-theory (e/d (dynamic-future-is-equal-gadget
                            prog-field-neq-gadget-to-spec
                            prog-eq-and-gadget-to-mul
                            prog-and-var-eq-gadget-to-mul
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance dynamic-future-eq-equations-to-funspec
                            (p p)
                            (xn (lookup-equal xn asg))
                            (yn (lookup-equal yn asg))
                            (mn (lookup-equal mn asg))
                            (rn (lookup-equal rn asg))
                            (xw (lookup-equal xw asg))
                            (yw (lookup-equal yw asg))
                            (mw (lookup-equal mw asg))
                            (rw (lookup-equal rw asg))
                            (xf (lookup-equal xf asg))
                            (yf (lookup-equal yf asg))
                            (mf (lookup-equal mf asg))
                            (rf (lookup-equal rf asg))
                            (xc (lookup-equal xc asg))
                            (yc (lookup-equal yc asg))
                            (mc (lookup-equal mc asg))
                            (rc (lookup-equal rc asg))
                            (z1 (lookup-equal z1 asg))
                            (z2 (lookup-equal z2 asg))
                            (z (lookup-equal z asg)))))))

(defruled dynamic-future-is-equal-gadget-complete
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp xf) (symbolp yf) (symbolp mf) (symbolp rf)
                (symbolp xc) (symbolp yc) (symbolp mc) (symbolp rc)
                (symbolp z1) (symbolp z2) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg xf)
                (r1cs::valuation-bindsp asg yf)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg xc)
                (r1cs::valuation-bindsp asg yc)
                (r1cs::valuation-bindsp asg mc)
                (r1cs::valuation-bindsp asg rc)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal (lookup-equal xn asg)
                       (dynamic-future->program-name a))
                (equal (lookup-equal yn asg)
                       (dynamic-future->program-name b))
                (equal (lookup-equal xw asg)
                       (dynamic-future->program-network a))
                (equal (lookup-equal yw asg)
                       (dynamic-future->program-network b))
                (equal (lookup-equal xf asg)
                       (dynamic-future->function-name a))
                (equal (lookup-equal yf asg)
                       (dynamic-future->function-name b))
                (equal (lookup-equal xc asg)
                       (dynamic-future->checksum a))
                (equal (lookup-equal yc asg)
                       (dynamic-future->checksum b))
                (fieldp (lookup-equal xn asg))
                (fieldp (lookup-equal yn asg))
                (fieldp (lookup-equal xw asg))
                (fieldp (lookup-equal yw asg))
                (fieldp (lookup-equal xf asg))
                (fieldp (lookup-equal yf asg))
                (fieldp (lookup-equal xc asg))
                (fieldp (lookup-equal yc asg))
                (equal (lookup-equal rn asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xn asg) (lookup-equal yn asg)))
                (equal (lookup-equal rw asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xw asg) (lookup-equal yw asg)))
                (equal (lookup-equal rf asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xf asg) (lookup-equal yf asg)))
                (equal (lookup-equal rc asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xc asg) (lookup-equal yc asg)))
                (equal (lookup-equal mn asg)
                       (if (equal (lookup-equal xn asg)
                                  (lookup-equal yn asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xn asg)
                                                   (lookup-equal yn asg) p)
                                      p)))
                (equal (lookup-equal mw asg)
                       (if (equal (lookup-equal xw asg)
                                  (lookup-equal yw asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xw asg)
                                                   (lookup-equal yw asg) p)
                                      p)))
                (equal (lookup-equal mf asg)
                       (if (equal (lookup-equal xf asg)
                                  (lookup-equal yf asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xf asg)
                                                   (lookup-equal yf asg) p)
                                      p)))
                (equal (lookup-equal mc asg)
                       (if (equal (lookup-equal xc asg)
                                  (lookup-equal yc asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xc asg)
                                                   (lookup-equal yc asg) p)
                                      p)))
                (equal (lookup-equal z1 asg)
                       (boolean-and-funspec
                        (boolean-not-funspec (lookup-equal rn asg))
                        (boolean-not-funspec (lookup-equal rw asg))))
                (equal (lookup-equal z2 asg)
                       (boolean-and-funspec
                        (lookup-equal z1 asg)
                        (boolean-not-funspec (lookup-equal rf asg))))
                (equal (lookup-equal z asg)
                       (boolean-and-funspec
                        (lookup-equal z2 asg)
                        (boolean-not-funspec (lookup-equal rc asg)))))
           (and (r1cs::r1cs-constraints-holdp
                 (dynamic-future-is-equal-gadget
                  xn yn mn rn xw yw mw rw
                  xf yf mf rf xc yc mc rc
                  z1 z2 z p)
                 asg p)
                (equal (lookup-equal z asg)
                       (dynamic-future-is-equal a b))))
  :hints (("Goal"
           :use ((:instance prog-field-neq-constraints-when-witness
                            (x (lookup-equal xn asg))
                            (y (lookup-equal yn asg))
                            (m (lookup-equal mn asg))
                            (r (lookup-equal rn asg))
                            (p p))
                 (:instance prog-field-neq-constraints-when-witness
                            (x (lookup-equal xw asg))
                            (y (lookup-equal yw asg))
                            (m (lookup-equal mw asg))
                            (r (lookup-equal rw asg))
                            (p p))
                 (:instance prog-field-neq-constraints-when-witness
                            (x (lookup-equal xf asg))
                            (y (lookup-equal yf asg))
                            (m (lookup-equal mf asg))
                            (r (lookup-equal rf asg))
                            (p p))
                 (:instance prog-field-neq-constraints-when-witness
                            (x (lookup-equal xc asg))
                            (y (lookup-equal yc asg))
                            (m (lookup-equal mc asg))
                            (r (lookup-equal rc asg))
                            (p p)))
           :in-theory (e/d (dynamic-future-is-equal-gadget
                            prog-field-neq-gadget-to-spec
                            prog-eq-and-gadget-to-mul
                            prog-eq-and-mul-is-and
                            prog-and-var-eq-gadget-to-mul
                            prog-and-var-eq-mul-is-and
                            dynamic-future-eq-equations-to-funspec
                            bitp-of-field-is-not-equal-funspec
                            bitp-of-boolean-and-funspec
                            bitp-of-boolean-not-funspec
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2
                            prog-field-neq-constraints-when-witness)))))

(defruled dynamic-future-is-not-equal-gadget-sound
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp xf) (symbolp yf) (symbolp mf) (symbolp rf)
                (symbolp xc) (symbolp yc) (symbolp mc) (symbolp rc)
                (symbolp z1) (symbolp z2) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg xf)
                (r1cs::valuation-bindsp asg yf)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg xc)
                (r1cs::valuation-bindsp asg yc)
                (r1cs::valuation-bindsp asg mc)
                (r1cs::valuation-bindsp asg rc)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal (lookup-equal xn asg)
                       (dynamic-future->program-name a))
                (equal (lookup-equal yn asg)
                       (dynamic-future->program-name b))
                (equal (lookup-equal xw asg)
                       (dynamic-future->program-network a))
                (equal (lookup-equal yw asg)
                       (dynamic-future->program-network b))
                (equal (lookup-equal xf asg)
                       (dynamic-future->function-name a))
                (equal (lookup-equal yf asg)
                       (dynamic-future->function-name b))
                (equal (lookup-equal xc asg)
                       (dynamic-future->checksum a))
                (equal (lookup-equal yc asg)
                       (dynamic-future->checksum b))
                (fieldp (lookup-equal xn asg))
                (fieldp (lookup-equal yn asg))
                (fieldp (lookup-equal xw asg))
                (fieldp (lookup-equal yw asg))
                (fieldp (lookup-equal xf asg))
                (fieldp (lookup-equal yf asg))
                (fieldp (lookup-equal xc asg))
                (fieldp (lookup-equal yc asg))
                (bitp (lookup-equal rn asg))
                (bitp (lookup-equal rw asg))
                (bitp (lookup-equal rf asg))
                (bitp (lookup-equal rc asg))
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (dynamic-future-is-not-equal-gadget
                  xn yn mn rn xw yw mw rw
                  xf yf mf rf xc yc mc rc
                  z1 z2 z p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal z asg) p)
                  (dynamic-future-is-not-equal a b)))
  :enable (dynamic-future-is-not-equal-gadget
           dynamic-future-is-equal-gadget-sound
           dynamic-future-is-not-equal-funspecs-match
           values-b-not-is-boolean-not
           prog-bit-not-is-sub
           bitp-of-dynamic-future-is-equal))

(defruled dynamic-future-is-not-equal-gadget-complete
  (implies (and (symbolp xn) (symbolp yn) (symbolp mn) (symbolp rn)
                (symbolp xw) (symbolp yw) (symbolp mw) (symbolp rw)
                (symbolp xf) (symbolp yf) (symbolp mf) (symbolp rf)
                (symbolp xc) (symbolp yc) (symbolp mc) (symbolp rc)
                (symbolp z1) (symbolp z2) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xn)
                (r1cs::valuation-bindsp asg yn)
                (r1cs::valuation-bindsp asg mn)
                (r1cs::valuation-bindsp asg rn)
                (r1cs::valuation-bindsp asg xw)
                (r1cs::valuation-bindsp asg yw)
                (r1cs::valuation-bindsp asg mw)
                (r1cs::valuation-bindsp asg rw)
                (r1cs::valuation-bindsp asg xf)
                (r1cs::valuation-bindsp asg yf)
                (r1cs::valuation-bindsp asg mf)
                (r1cs::valuation-bindsp asg rf)
                (r1cs::valuation-bindsp asg xc)
                (r1cs::valuation-bindsp asg yc)
                (r1cs::valuation-bindsp asg mc)
                (r1cs::valuation-bindsp asg rc)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg z2)
                (r1cs::valuation-bindsp asg z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal (lookup-equal xn asg)
                       (dynamic-future->program-name a))
                (equal (lookup-equal yn asg)
                       (dynamic-future->program-name b))
                (equal (lookup-equal xw asg)
                       (dynamic-future->program-network a))
                (equal (lookup-equal yw asg)
                       (dynamic-future->program-network b))
                (equal (lookup-equal xf asg)
                       (dynamic-future->function-name a))
                (equal (lookup-equal yf asg)
                       (dynamic-future->function-name b))
                (equal (lookup-equal xc asg)
                       (dynamic-future->checksum a))
                (equal (lookup-equal yc asg)
                       (dynamic-future->checksum b))
                (fieldp (lookup-equal xn asg))
                (fieldp (lookup-equal yn asg))
                (fieldp (lookup-equal xw asg))
                (fieldp (lookup-equal yw asg))
                (fieldp (lookup-equal xf asg))
                (fieldp (lookup-equal yf asg))
                (fieldp (lookup-equal xc asg))
                (fieldp (lookup-equal yc asg))
                (equal (lookup-equal rn asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xn asg) (lookup-equal yn asg)))
                (equal (lookup-equal rw asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xw asg) (lookup-equal yw asg)))
                (equal (lookup-equal rf asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xf asg) (lookup-equal yf asg)))
                (equal (lookup-equal rc asg)
                       (field-is-not-equal-funspec
                        (lookup-equal xc asg) (lookup-equal yc asg)))
                (equal (lookup-equal mn asg)
                       (if (equal (lookup-equal xn asg)
                                  (lookup-equal yn asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xn asg)
                                                   (lookup-equal yn asg) p)
                                      p)))
                (equal (lookup-equal mw asg)
                       (if (equal (lookup-equal xw asg)
                                  (lookup-equal yw asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xw asg)
                                                   (lookup-equal yw asg) p)
                                      p)))
                (equal (lookup-equal mf asg)
                       (if (equal (lookup-equal xf asg)
                                  (lookup-equal yf asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xf asg)
                                                   (lookup-equal yf asg) p)
                                      p)))
                (equal (lookup-equal mc asg)
                       (if (equal (lookup-equal xc asg)
                                  (lookup-equal yc asg))
                           1
                         (pfield::inv (pfield::sub (lookup-equal xc asg)
                                                   (lookup-equal yc asg) p)
                                      p)))
                (equal (lookup-equal z1 asg)
                       (boolean-and-funspec
                        (boolean-not-funspec (lookup-equal rn asg))
                        (boolean-not-funspec (lookup-equal rw asg))))
                (equal (lookup-equal z2 asg)
                       (boolean-and-funspec
                        (lookup-equal z1 asg)
                        (boolean-not-funspec (lookup-equal rf asg))))
                (equal (lookup-equal z asg)
                       (boolean-and-funspec
                        (lookup-equal z2 asg)
                        (boolean-not-funspec (lookup-equal rc asg)))))
           (and (r1cs::r1cs-constraints-holdp
                 (dynamic-future-is-not-equal-gadget
                  xn yn mn rn xw yw mw rw
                  xf yf mf rf xc yc mc rc
                  z1 z2 z p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal z asg) p)
                       (dynamic-future-is-not-equal a b))))
  :hints (("Goal"
           :use ((:instance dynamic-future-is-equal-gadget-complete
                            (xn xn) (yn yn) (mn mn) (rn rn)
                            (xw xw) (yw yw) (mw mw) (rw rw)
                            (xf xf) (yf yf) (mf mf) (rf rf)
                            (xc xc) (yc yc) (mc mc) (rc rc)
                            (z1 z1) (z2 z2) (z z) (p p)
                            (asg asg) (a a) (b b)))
           :in-theory (e/d (dynamic-future-is-not-equal-gadget
                            dynamic-future-is-not-equal-funspecs-match
                            values-b-not-is-boolean-not
                            prog-bit-not-is-sub
                            bitp-of-dynamic-future-is-equal)
                           (dynamic-future-is-equal-gadget-complete)))))

(define dynamic-future-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "dynamic_future_is_equal(xn, yn, mn, rn, xw, yw, mw, rw, xf, yf, mf, rf, xc, yc, mc, rc, z1, z2, z) := {
    (xn - yn) * (mn) == (rn),
    (xn - yn) * (1 - rn) == (0),
    (xw - yw) * (mw) == (rw),
    (xw - yw) * (1 - rw) == (0),
    (xf - yf) * (mf) == (rf),
    (xf - yf) * (1 - rf) == (0),
    (xc - yc) * (mc) == (rc),
    (xc - yc) * (1 - rc) == (0),
    (1 - rn) * (1 - rw) == (z1),
    (z1) * (1 - rf) == (z2),
    (z2) * (1 - rc) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (dynamic-future-is-equal-circuit)
            :pred dynamic-future-is-equal-pred
            :prime prime)

(defruled dynamic-future-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp xn) (fieldp yn) (pfield::fep mn prime) (bitp rn)
                (fieldp xw) (fieldp yw) (pfield::fep mw prime) (bitp rw)
                (fieldp xf) (fieldp yf) (pfield::fep mf prime) (bitp rf)
                (fieldp xc) (fieldp yc) (pfield::fep mc prime) (bitp rc)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal xn (dynamic-future->program-name a))
                (equal yn (dynamic-future->program-name b))
                (equal xw (dynamic-future->program-network a))
                (equal yw (dynamic-future->program-network b))
                (equal xf (dynamic-future->function-name a))
                (equal yf (dynamic-future->function-name b))
                (equal xc (dynamic-future->checksum a))
                (equal yc (dynamic-future->checksum b))
                (dynamic-future-is-equal-pred
                 xn yn mn rn xw yw mw rw
                 xf yf mf rf xc yc mc rc
                 z1 z2 z prime))
           (equal z (dynamic-future-is-equal a b)))
  :enable (dynamic-future-is-equal-pred
           dynamic-future-eq-equations-to-funspec))

(define dynamic-future-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "dynamic_future_is_not_equal(xn, yn, mn, rn, xw, yw, mw, rw, xf, yf, mf, rf, xc, yc, mc, rc, z1, z2, z) := {
    (xn - yn) * (mn) == (rn),
    (xn - yn) * (1 - rn) == (0),
    (xw - yw) * (mw) == (rw),
    (xw - yw) * (1 - rw) == (0),
    (xf - yf) * (mf) == (rf),
    (xf - yf) * (1 - rf) == (0),
    (xc - yc) * (mc) == (rc),
    (xc - yc) * (1 - rc) == (0),
    (1 - rn) * (1 - rw) == (z1),
    (z1) * (1 - rf) == (z2),
    (z2) * (1 - rc) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (dynamic-future-is-not-equal-circuit)
            :pred dynamic-future-is-not-equal-pred
            :prime prime)

(defruled dynamic-future-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp xn) (fieldp yn) (pfield::fep mn prime) (bitp rn)
                (fieldp xw) (fieldp yw) (pfield::fep mw prime) (bitp rw)
                (fieldp xf) (fieldp yf) (pfield::fep mf prime) (bitp rf)
                (fieldp xc) (fieldp yc) (pfield::fep mc prime) (bitp rc)
                (bitp z)
                (dynamic-futurep a)
                (dynamic-futurep b)
                (equal xn (dynamic-future->program-name a))
                (equal yn (dynamic-future->program-name b))
                (equal xw (dynamic-future->program-network a))
                (equal yw (dynamic-future->program-network b))
                (equal xf (dynamic-future->function-name a))
                (equal yf (dynamic-future->function-name b))
                (equal xc (dynamic-future->checksum a))
                (equal yc (dynamic-future->checksum b))
                (dynamic-future-is-not-equal-pred
                 xn yn mn rn xw yw mw rw
                 xf yf mf rf xc yc mc rc
                 z1 z2 z prime))
           (equal (pfield::sub 1 z prime)
                  (dynamic-future-is-not-equal a b)))
  :enable (dynamic-future-is-not-equal-pred
           dynamic-future-eq-equations-to-funspec
           dynamic-future-is-not-equal-funspecs-match
           values-b-not-is-boolean-not
           prog-bit-not-is-sub
           bitp-of-dynamic-future-is-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record::is_hiding is the negation of U8::is_zero, and a non-constant
; integer compared with constant zero emits the two field-inequality
; constraints on the integer's field value.

(define crypto-record-is-hiding-gadget ((v symbolp)
                                        (m symbolp)
                                        (r symbolp)
                                        (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Record::is_hiding'): @('(v) (m) = (r)') and
          @('(v) (1 - r) = (0)'). The result is @('r')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 v))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 v))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c nil)))

(defruled crypto-record-is-hiding-gadget-to-spec
  (implies (and (symbolp v) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((v$ (lookup-equal v asg))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crypto-record-is-hiding-gadget v m r p) asg p)
                    (and (equal (pfield::mul v$ m$ p) r$)
                         (equal (pfield::mul v$ (pfield::sub 1 r$ p) p)
                                0)))))
  :enable (crypto-record-is-hiding-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled crypto-record-is-hiding-is-nonzero
  (implies (and (acl2::ubyte8p version)
                (equal v (acl2::ubyte8-fix version)))
           (equal (crypto-record-is-hiding version)
                  (field-is-not-equal-funspec v 0)))
  :enable (crypto-record-is-hiding
           field-is-not-equal-funspec
           acl2::ubyte8-fix
           acl2::ubyte8p))

(defruled crypto-record-is-hiding-gadget-sound
  (implies (and (symbolp v) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (acl2::ubyte8p version)
                (equal (lookup-equal v asg) (acl2::ubyte8-fix version))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crypto-record-is-hiding-gadget v m r p) asg p))
           (equal (lookup-equal r asg)
                  (crypto-record-is-hiding version)))
  :enable (crypto-record-is-hiding-gadget-to-spec
           crypto-record-is-hiding-is-nonzero
           prog-field-neq-bit-when-constraints
           fieldp
           r1cs::fep-of-lookup-equal))

(defruled crypto-record-is-hiding-gadget-complete
  (implies (and (symbolp v) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (acl2::ubyte8p version)
                (equal (lookup-equal v asg) (acl2::ubyte8-fix version))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal v asg) 0) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal v asg) 0)
                           1
                         (pfield::inv (lookup-equal v asg) p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crypto-record-is-hiding-gadget v m r p) asg p)
                (equal (lookup-equal r asg)
                       (crypto-record-is-hiding version))))
  :enable (crypto-record-is-hiding-gadget-to-spec
           crypto-record-is-hiding-is-nonzero
           prog-field-neq-constraints-when-witness
           fieldp))

(defconst *crypto-record-is-hiding-sample-asg*
  '((v . 3) (m . 2) (r . 1)))

(defruled crypto-record-is-hiding-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crypto-record-is-hiding-gadget 'v 'm 'r 5)
   *crypto-record-is-hiding-sample-asg*
   5)
  :enable (crypto-record-is-hiding-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define crypto-record-is-hiding-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crypto_record_is_hiding(v, m, r) := {
    (v) * (m) == (r),
    (v) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crypto-record-is-hiding-circuit)
            :pred crypto-record-is-hiding-pred
            :prime prime)

(defruled crypto-record-is-hiding-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp v)
                (pfield::fep m prime)
                (bitp r)
                (acl2::ubyte8p version)
                (equal v (acl2::ubyte8-fix version))
                (crypto-record-is-hiding-pred v m r prime))
           (equal r (crypto-record-is-hiding version)))
  :enable (crypto-record-is-hiding-pred
           prog-field-neq-bit-when-constraints
           crypto-record-is-hiding-is-nonzero
           fieldp))
