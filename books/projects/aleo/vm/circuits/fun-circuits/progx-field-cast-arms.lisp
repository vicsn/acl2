; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Per-destination soundness of Field::cast (snarkVM
; circuit/program/src/data/literal/cast/field.rs), each stated against
; field-cast:
;   Address  Address::from_field = Group::from_x_coordinate
;   Boolean  is_zero, is_one, OR, assert
;   Field    clone
;   Group    Group::from_x_coordinate
;   Integer  Integer::from_field = Field::to_lower_bits_le(BITS)
;   Scalar   Scalar::from_field
;   IdentifierLiteral  IdentifierLiteral::from_field
; The arm theorems carry no type hypothesis beyond the wire valuation.

(in-package "ALEOVM")

(include-book "fsa-address-from")
(include-book "fsa-idlit-from-bits")
(include-book "int-field")
(include-book "scalar-from-bits-r1cs")
(include-book "prog-catalog")
(include-book "acct-equal-sound")
(include-book "../fun-specs/values-cast")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bridges from the arm funspecs to the helpers field-cast uses.

(defruled progx-y-of-groupp-is-fieldp
  (implies (groupp p)
           (fieldp (ecurve::point-finite->y p)))
  :enable groupp)

(defruled progx-values-group-from-x-when-groupp
  (implies (and (fieldp x) (fieldp y)
                (groupp (ecurve::point-finite x y)))
           (equal (values-group-from-x x)
                  (ecurve::point-finite x y)))
  :use ((:instance values-x-in-subgroupp-suff)
        (:instance grp-groupp-same-abscissa
                   (y1 y)
                   (y2 (values-x-in-subgroupp-witness x)))
        (:instance progx-y-of-groupp-is-fieldp
                   (p (ecurve::point-finite
                       x (values-x-in-subgroupp-witness x)))))
  :in-theory '(values-group-from-x values-x-in-subgroupp
               fieldp pfield::fep-fw-to-natp
               acl2::natp-compound-recognizer
               ecurve::point-finite->y-of-point-finite nfix))

(defruled progx-not-reserrp-of-point-finite
  (not (reserrp (ecurve::point-finite a b)))
  :enable (reserrp ecurve::point-finite))

(defruled progx-field-cast-group-arm
  :short "Field::cast to Group and to Address over the
          Group::from_x_coordinate wires."
  (implies (and (grp-from-xy-wire-hyps
                 (r1cs::r1cs-constraints-holdp
                  (grp-from-x-coordinate-gadget
                   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                  asg p)))
           (and (equal (field-cast (lookup-equal x asg) (literal-type-group))
                       (literal-group
                        (ecurve::point-finite (lookup-equal x asg)
                                              (lookup-equal y asg))))
                (equal (field-cast (lookup-equal x asg) (literal-type-address))
                       (literal-address
                        (ecurve::point-finite (lookup-equal x asg)
                                              (lookup-equal y asg))))))
  :hints (("Goal"
           :use (grp-from-x-coordinate-gadget-sound
                 (:instance progx-not-reserrp-of-point-finite
                            (a (lookup-equal x asg)) (b (lookup-equal y asg)))
                 (:instance return-type-of-group-from-x-coordinate-funspec
                            (x (lookup-equal x asg)))
                 (:instance progx-values-group-from-x-when-groupp
                            (x (lookup-equal x asg))
                            (y (lookup-equal y asg))))
           :in-theory (e/d (field-cast values-literal-type-integerp
                            values-field-fix-when-fieldp
                            fieldp r1cs::fep-of-lookup-equal)
                           (values-group-from-x
                            group-from-x-coordinate-funspec
                            grp-from-x-coordinate-gadget
                            groupp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer.

(defruled progx-values-int-from-field-is-spec
  (implies (and (fieldp f)
                (integer-widthp n)
                (not (equal (int-from-field-spec f signedp n) (spec-error))))
           (equal (values-int-from-field f signedp n)
                  (int-from-field-spec f signedp n)))
  :hints (("Goal"
           :in-theory (enable values-int-from-field int-from-field-spec
                              int-wrap values-int-of-unsigned
                              values-field-fix-when-fieldp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              fieldp pfield::fep))))

(defruled progx-field-cast-integer-arm
  (implies (and (equal p (base-prime))
                (symbolp f)
                (symbol-listp xs)
                (values-literal-type-integerp to)
                (equal (len xs) (values-literal-type-width to))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::r1cs-constraints-holdp
                 (int-from-field-gadget f xs p) asg p))
           (equal (field-cast (lookup-equal f asg) to)
                  (values-integer-literal
                   to
                   (lebits->int (lookup-equal-list xs asg)
                                (values-literal-type-signedp to)))))
  :hints (("Goal"
           :use ((:instance int-from-field-gadget-sound
                            (n (len xs))
                            (signedp (values-literal-type-signedp to)))
                 (:instance progx-values-int-from-field-is-spec
                            (f (lookup-equal f asg))
                            (n (len xs))
                            (signedp (values-literal-type-signedp to))))
           :in-theory (e/d (field-cast values-field-fix-when-fieldp
                            fieldp r1cs::fep-of-lookup-equal
                            integer-widthp values-literal-type-width)
                           (int-from-field-gadget
                            values-int-from-field
                            int-from-field-spec
                            lebits->int)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boolean.

(defruled progx-field-cast-boolean-bits
  (implies (and (symbolp x) (symbolp m-z) (symbolp r-z)
                (symbolp m-o) (symbolp r-o) (symbolp or-bit)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m-z)
                (r1cs::valuation-bindsp asg r-z)
                (r1cs::valuation-bindsp asg m-o)
                (r1cs::valuation-bindsp asg r-o)
                (r1cs::valuation-bindsp asg or-bit)
                (r1cs::r1cs-constraints-holdp
                 (field-cast-to-boolean-gadget x m-z r-z m-o r-o or-bit p)
                 asg p))
           (and (bitp (lookup-equal r-z asg))
                (bitp (lookup-equal r-o asg))
                (bitp (lookup-equal or-bit asg))))
  :hints (("Goal"
           :use ((:instance field-is-zero-gadget-to-spec (m m-z) (r r-z))
                 (:instance field-is-one-gadget-to-spec (m m-o) (r r-o))
                 (:instance prog-assert-gadget-to-funspec (b or-bit))
                 (:instance acct-neq-values-bitp
                            (d (lookup-equal x asg))
                            (m (lookup-equal m-z asg))
                            (r (lookup-equal r-z asg)))
                 (:instance acct-neq-values-bitp
                            (d (pfield::sub (lookup-equal x asg) 1 p))
                            (m (lookup-equal m-o asg))
                            (r (lookup-equal r-o asg))))
           :in-theory (e/d (field-cast-to-boolean-gadget
                            r1cs::r1cs-constraints-holdp-of-append
                            assert-funspec enforce-funspec
                            primep-of-base-prime)
                           (field-is-zero-gadget field-is-one-gadget
                            prog-demorgan-or-gadget prog-assert-gadget
                            (:e base-prime))))))

(defruled progx-field-cast-boolean-arm
  (implies (and (symbolp x) (symbolp m-z) (symbolp r-z)
                (symbolp m-o) (symbolp r-o) (symbolp or-bit)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m-z)
                (r1cs::valuation-bindsp asg r-z)
                (r1cs::valuation-bindsp asg m-o)
                (r1cs::valuation-bindsp asg r-o)
                (r1cs::valuation-bindsp asg or-bit)
                (r1cs::r1cs-constraints-holdp
                 (field-cast-to-boolean-gadget x m-z r-z m-o r-o or-bit p)
                 asg p))
           (equal (field-cast (lookup-equal x asg) (literal-type-boolean))
                  (literal-boolean
                   (pfield::sub 1 (lookup-equal r-o asg) p))))
  :hints (("Goal"
           :use (field-cast-to-boolean-gadget-sound
                 progx-field-cast-boolean-bits)
           :in-theory '(fieldp r1cs::fep-of-lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Field.

(defruled progx-field-cast-field-arm
  (implies (fieldp x)
           (equal (field-cast x (literal-type-field))
                  (literal-field x)))
  :enable (field-cast values-literal-type-integerp
           values-field-fix-when-fieldp))
