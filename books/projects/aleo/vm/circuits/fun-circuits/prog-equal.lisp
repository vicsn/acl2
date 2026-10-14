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
