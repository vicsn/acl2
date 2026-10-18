; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::cast (snarkVM circuit/program/src/data/literal/cast/field.rs) as a
; dispatch on the destination type.  The destination is fixed when the
; circuit is synthesized, so the constraints are those of one arm:
;   Address, Group   Group::from_x_coordinate (Address::from_field wraps it)
;   Boolean          is_zero, is_one, OR, assert
;   Field            none (clone)
;   Integer          Integer::from_field = Field::to_lower_bits_le(BITS)
;   Scalar           Scalar::from_field
;   IdentifierLiteral  IdentifierLiteral::from_field
;   Signature, String  no Cast impl; field-cast fails, no constraint.
; progx-field-cast-out is the literal the output wires denote.

(in-package "ALEOVM")

(include-book "progx-field-cast-arms")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-field-cast-scalar-arm
  (implies (and (equal p (base-prime))
                (symbolp x) (symbol-listp xs) (symbol-listp frs)
                (symbolp u) (symbol-listp srs)
                (equal (len xs) 253) (equal (len frs) 252)
                (equal (len srs) 250)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg frs)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-binds-allp asg srs)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-gadget x xs frs u srs p) asg p))
           (equal (field-cast (lookup-equal x asg) (literal-type-scalar))
                  (literal-scalar
                   (lebits=>nat (take 251 (lookup-equal-list xs asg))))))
  :hints (("Goal"
           :use (scalar-from-field-gadget-sound)
           :in-theory (e/d (field-cast values-literal-type-integerp
                            values-scalar-from-field
                            values-field-fix-when-fieldp
                            scalarp pfield::fep primep-of-base-prime)
                           (scalar-from-field-gadget
                            scalar-from-field-funspec
                            sfb-value)))))

(defruled progx-field-cast-identifier-arm
  (implies (fsa-idlit-hyps
            (fsa-field-hyps)
            (r1cs::r1cs-constraints-holdp
             (fsa-idlit-from-field-gadget x rs u bitrows excess witrows
                                          partial uscore islet p)
             asg p))
           (equal (field-cast (lookup-equal x asg) (literal-type-identifier))
                  (literal-identifier
                   (make-identifier-literal
                    :bytes (id-decode-rows bitrows asg)))))
  :hints (("Goal"
           :use fsa-idlit-from-field-gadget-sound
           :in-theory (e/d (field-cast values-literal-type-integerp
                            values-field-fix-when-fieldp
                            fieldp r1cs::fep-of-lookup-equal)
                           (identifier-literal-from-field
                            fsa-idlit-from-field-gadget)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule progx-literal-type-when-address
  (implies (and (literal-typep to) (literal-type-case to :address))
           (equal to (literal-type-address)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-address))

(defrule progx-literal-type-when-group
  (implies (and (literal-typep to) (literal-type-case to :group))
           (equal to (literal-type-group)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-group))

(defrule progx-literal-type-when-boolean
  (implies (and (literal-typep to) (literal-type-case to :boolean))
           (equal to (literal-type-boolean)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-boolean))

(defrule progx-literal-type-when-field
  (implies (and (literal-typep to) (literal-type-case to :field))
           (equal to (literal-type-field)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-field))

(defrule progx-literal-type-when-scalar
  (implies (and (literal-typep to) (literal-type-case to :scalar))
           (equal to (literal-type-scalar)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-scalar))

(defrule progx-literal-type-when-identifier
  (implies (and (literal-typep to) (literal-type-case to :identifier))
           (equal to (literal-type-identifier)))
  :rule-classes nil
  :enable (literal-typep literal-type-kind literal-type-identifier))

(defmacro progx-field-cast-call ()
  '(progx-field-cast-gadget to x
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit
    ixs
    sxs frs u srs
    rs bitrows excess witrows partial uscore islet
    p))

(define progx-field-cast-gadget ((to literal-typep) x
                                 y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                 m-z r-z m-o r-o or-bit
                                 ixs
                                 sxs frs u srs
                                 rs bitrows excess witrows partial uscore islet
                                 (p primep))
  :verify-guards nil
  (cond ((values-literal-type-integerp to) (int-from-field-gadget x ixs p))
        (t (literal-type-case
            to
            :address (grp-from-x-coordinate-gadget
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
            :group (grp-from-x-coordinate-gadget
                    x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
            :boolean (field-cast-to-boolean-gadget x m-z r-z m-o r-o or-bit p)
            :scalar (scalar-from-field-gadget x sxs frs u srs p)
            :identifier (fsa-idlit-from-field-gadget
                         x rs u bitrows excess witrows partial uscore islet p)
            :otherwise nil))))

(define progx-field-cast-out ((to literal-typep) x y r-o ixs sxs bitrows asg)
  :verify-guards nil
  :short "The literal the output wires denote."
  (b* ((xv (lookup-equal x asg))
       (pt (ecurve::point-finite xv (lookup-equal y asg))))
    (cond ((values-literal-type-integerp to)
           (values-integer-literal
            to (lebits->int (lookup-equal-list ixs asg)
                            (values-literal-type-signedp to))))
          (t (literal-type-case
              to
              :address (literal-address pt)
              :group (literal-group pt)
              :boolean (literal-boolean
                        (pfield::sub 1 (lookup-equal r-o asg) (base-prime)))
              :field (literal-field xv)
              :scalar (literal-scalar
                       (lebits=>nat (take 251 (lookup-equal-list sxs asg))))
              :identifier (literal-identifier
                           (make-identifier-literal
                            :bytes (id-decode-rows bitrows asg)))
              :otherwise (spec-error))))))

(defmacro progx-field-cast-hyps (&rest more)
  `(and (literal-typep to)
        (equal p (base-prime))
        (symbolp x)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg x)
        (implies (or (literal-type-case to :group)
                     (literal-type-case to :address))
                 (grp-from-xy-wire-hyps))
        (implies (literal-type-case to :boolean)
                 (and (symbolp m-z) (symbolp r-z)
                      (symbolp m-o) (symbolp r-o) (symbolp or-bit)
                      (r1cs::valuation-bindsp asg m-z)
                      (r1cs::valuation-bindsp asg r-z)
                      (r1cs::valuation-bindsp asg m-o)
                      (r1cs::valuation-bindsp asg r-o)
                      (r1cs::valuation-bindsp asg or-bit)))
        (implies (values-literal-type-integerp to)
                 (and (symbol-listp ixs)
                      (equal (len ixs) (values-literal-type-width to))
                      (r1cs::valuation-binds-allp asg ixs)))
        (implies (literal-type-case to :scalar)
                 (and (symbol-listp sxs) (symbol-listp frs)
                      (symbolp u) (symbol-listp srs)
                      (equal (len sxs) 253) (equal (len frs) 252)
                      (equal (len srs) 250)
                      (r1cs::valuation-binds-allp asg sxs)
                      (r1cs::valuation-binds-allp asg frs)
                      (r1cs::valuation-bindsp asg u)
                      (r1cs::valuation-binds-allp asg srs)
                      (equal (lookup-equal u asg) 1)))
        (implies (literal-type-case to :identifier)
                 (fsa-idlit-hyps (fsa-field-hyps)))
        ,@more))

(defruled progx-field-cast-sound
  :short "R1CS-SOUND of Field::cast: for every destination type, the
          constraints imply that the literal of the output wires is the
          funspec of the input wire.  No type hypothesis on the input."
  (implies (progx-field-cast-hyps
            (r1cs::r1cs-constraints-holdp
             (progx-field-cast-call)
             asg p))
           (equal (progx-field-cast-out to x y r-o ixs sxs bitrows asg)
                  (field-cast (lookup-equal x asg) to)))
  :cases ((values-literal-type-integerp to)
          (literal-type-case to :address)
          (literal-type-case to :group)
          (literal-type-case to :boolean)
          (literal-type-case to :field)
          (literal-type-case to :scalar)
          (literal-type-case to :identifier))
  :hints (("Subgoal 7"
           :use (:instance progx-field-cast-integer-arm (f x) (xs ixs))
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        (:e values-literal-type-integerp)))
          ("Subgoal 6"
           :use (progx-field-cast-group-arm progx-literal-type-when-address)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp literal-type-kind
                        (:e literal-type-address) (:e member-eq)))
          ("Subgoal 5"
           :use (progx-field-cast-group-arm progx-literal-type-when-group)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp literal-type-kind
                        (:e literal-type-group) (:e member-eq)))
          ("Subgoal 4"
           :use (progx-field-cast-boolean-arm progx-literal-type-when-boolean)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp
                        (:e literal-type-boolean) (:e member-eq)))
          ("Subgoal 3"
           :use ((:instance progx-field-cast-field-arm (x (lookup-equal x asg))) progx-literal-type-when-field)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp
                        fieldp r1cs::fep-of-lookup-equal
                        (:e literal-type-field) (:e member-eq)))
          ("Subgoal 2"
           :use ((:instance progx-field-cast-scalar-arm (xs sxs)) progx-literal-type-when-scalar)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp
                        (:e literal-type-scalar) (:e member-eq)))
          ("Subgoal 1"
           :use (progx-field-cast-identifier-arm progx-literal-type-when-identifier)
           :in-theory '(progx-field-cast-gadget progx-field-cast-out
                        values-literal-type-integerp
                        (:e literal-type-identifier) (:e member-eq)))
          ("Subgoal 8"
           :in-theory (e/d (progx-field-cast-out field-cast
                            values-literal-type-integerp)
                           (progx-field-cast-gadget)))))

(defruled progx-field-cast-gadget-when-address
  :short "R1CS-COMPLETE of Field::cast reduces to the address arm's complete theorem."
  (equal (progx-field-cast-gadget (literal-type-address) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         (grp-from-x-coordinate-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))
  :enable (progx-field-cast-gadget values-literal-type-integerp))

(defruled progx-field-cast-gadget-when-group
  :short "R1CS-COMPLETE of Field::cast reduces to the group arm's complete theorem."
  (equal (progx-field-cast-gadget (literal-type-group) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         (grp-from-x-coordinate-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))
  :enable (progx-field-cast-gadget values-literal-type-integerp))

(defruled progx-field-cast-gadget-when-boolean
  :short "R1CS-COMPLETE of Field::cast reduces to the boolean arm's complete theorem."
  (equal (progx-field-cast-gadget (literal-type-boolean) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         (field-cast-to-boolean-gadget x m-z r-z m-o r-o or-bit p))
  :enable (progx-field-cast-gadget values-literal-type-integerp))

(defruled progx-field-cast-gadget-when-scalar
  :short "R1CS-COMPLETE of Field::cast reduces to the scalar arm's complete theorem."
  (equal (progx-field-cast-gadget (literal-type-scalar) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         (scalar-from-field-gadget x sxs frs u srs p))
  :enable (progx-field-cast-gadget values-literal-type-integerp))

(defruled progx-field-cast-gadget-when-identifier
  :short "R1CS-COMPLETE of Field::cast reduces to the identifier arm's complete theorem."
  (equal (progx-field-cast-gadget (literal-type-identifier) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         (fsa-idlit-from-field-gadget x rs u bitrows excess witrows partial uscore islet p))
  :enable (progx-field-cast-gadget values-literal-type-integerp))

(defruled progx-field-cast-gadget-when-integer
  (implies (values-literal-type-integerp to)
           (equal (progx-field-cast-call) (int-from-field-gadget x ixs p)))
  :enable progx-field-cast-gadget)

(defruled progx-field-cast-gadget-when-field
  (equal (progx-field-cast-gadget (literal-type-field) x
          y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
          m-z r-z m-o r-o or-bit ixs sxs frs u srs
          rs bitrows excess witrows partial uscore islet p)
         nil)
  :enable (progx-field-cast-gadget values-literal-type-integerp))
