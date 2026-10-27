; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::cast (snarkVM circuit/program/src/data/literal/cast/scalar.rs).
; A circuit Scalar is a Field variable s (plus cached bits), and to_field is
; that field, so:
;   Address, Group, IdentifierLiteral  Field::cast on s
;   Boolean   is_one, is_zero (Field::is_equal on s), OR, assert: the
;             Field::cast Boolean arm on s
;   Field, Scalar  no constraint
;   Integer   to_bits_le (Scalar::write_bits_le, its first call on s), then
;             Integer::from_bits_le, which asserts the bits above the width
;             are zero
;   Signature, String  no Cast impl; scalar-cast fails, no constraint.

(in-package "ALEOVM")

(include-book "progx-idlit-cast")
(include-book "scalar-write-bits-r1cs")
(include-book "int-bits")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-fieldp-when-scalarp
  (implies (scalarp s) (fieldp s))
  :enable (scalarp fieldp pfield::fep)
  :disable ((:e scalar-prime) (:e base-prime))
  :prep-lemmas
  ((defrule scalar-below-base
     (< (scalar-prime) (base-prime))
     :enable (scalar-prime base-prime))))

(defruled progx-int-wrap-is-of-unsigned
  (implies (and (natp s) (posp n) (< s (expt 2 n)))
           (equal (int-wrap s signedp n)
                  (values-int-of-unsigned s signedp n)))
  :enable (int-wrap values-int-of-unsigned acl2::pos-fix))

(define progx-scalar-cast-gadget ((to literal-typep) s
                                  y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                  m-z r-z m-o r-o or-bit
                                  ixs
                                  sxs frs u srs
                                  rs bitrows excess witrows partial uscore islet
                                  sbits sbrs
                                  (p primep))
  :verify-guards nil
  (cond ((values-literal-type-integerp to)
         (append (scalar-write-bits-le-gadget s sbits sbrs p)
                 (int-from-bits-le-gadget
                  (nthcdr (values-literal-type-width to) sbits))))
        ((or (literal-type-case to :field)
             (literal-type-case to :scalar)
             (literal-type-case to :signature)
             (literal-type-case to :string))
         nil)
        (t (progx-field-cast-gadget to s
            y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
            m-z r-z m-o r-o or-bit ixs sxs frs u srs
            rs bitrows excess witrows partial uscore islet p))))

(defmacro progx-scalar-cast-call ()
  '(progx-scalar-cast-gadget to s
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit ixs sxs frs u srs
    rs bitrows excess witrows partial uscore islet sbits sbrs p))

(define progx-scalar-cast-out ((to literal-typep) s y r-o ixs sxs bitrows
                               sbits asg)
  :verify-guards nil
  :short "The literal the output wires denote.  For an integer destination it
          is the Integer::from_bits_le reading of the scalar bit wires."
  (cond ((values-literal-type-integerp to)
         (values-integer-literal
          to (int-wrap (lebits=>nat (lookup-equal-list sbits asg))
                       (values-literal-type-signedp to)
                       (values-literal-type-width to))))
        ((literal-type-case to :field) (literal-field (lookup-equal s asg)))
        ((literal-type-case to :scalar) (literal-scalar (lookup-equal s asg)))
        (t (progx-field-cast-out to s y r-o ixs sxs bitrows asg))))

(defmacro progx-scalar-cast-hyps (&rest more)
  `(and (literal-typep to)
        (equal p (base-prime))
        (symbolp s)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg s)
        (scalarp (lookup-equal s asg))
        (implies (values-literal-type-integerp to)
                 (and (symbol-listp sbits) (symbol-listp sbrs)
                      (equal (len sbits) 251) (equal (len sbrs) 250)
                      (r1cs::valuation-binds-allp asg sbits)
                      (r1cs::valuation-binds-allp asg sbrs)))
        (implies (not (or (values-literal-type-integerp to)
                          (literal-type-case to :field)
                          (literal-type-case to :scalar)))
                 (progx-field-cast-hypsp to s
                  y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                  m-z r-z m-o r-o or-bit ixs sxs frs u srs
                  rs bitrows excess witrows partial uscore islet p asg))
        ,@more))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer arm.

(defruled progx-len-nthcdr-of-251
  (implies (and (equal (len xs) 251) (natp n) (<= n 251))
           (equal (len (nthcdr n xs)) (- 251 n))))

(defruled progx-base-prime-above-251
  (< 251 (base-prime))
  :enable base-prime)

(defruled progx-width-at-most-128
  (and (<= (values-literal-type-width to) 128)
       (posp (values-literal-type-width to)))
  :enable values-literal-type-width)

(defruled progx-scalar-cast-integer-sound
  (implies (and (values-literal-type-integerp to)
                (progx-scalar-cast-hyps)
                (r1cs::r1cs-constraints-holdp
                 (append (scalar-write-bits-le-gadget s sbits sbrs p)
                         (int-from-bits-le-gadget
                          (nthcdr (values-literal-type-width to) sbits)))
                 asg p))
           (equal (values-integer-literal
                   to (int-wrap (lebits=>nat (lookup-equal-list sbits asg))
                                (values-literal-type-signedp to)
                                (values-literal-type-width to)))
                  (scalar-cast (lookup-equal s asg) to)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance scalar-write-bits-le-gadget-sound
                            (xs sbits) (rs sbrs) (acc nil))
                 (:instance int-from-bits-le-gadget-sound
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to))
                            (bits (lookup-equal-list sbits asg))
                            (excess (nthcdr (values-literal-type-width to)
                                            sbits)))
                 (:instance progx-len-nthcdr-of-251
                            (xs sbits) (n (values-literal-type-width to)))
                 progx-width-at-most-128
                 progx-base-prime-above-251
                 progx-integer-widthp-of-width
                 (:instance int-from-bits-le-not-error-implies-below
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to))
                            (bits (lookup-equal-list sbits asg)))
                 (:instance progx-int-wrap-is-of-unsigned
                            (s (lookup-equal s asg))
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to))))
           :in-theory (e/d (scalar-cast values-scalar-fix-when-scalarp
                            r1cs::r1cs-constraints-holdp-of-append
                            primep-of-base-prime
                            lookup-equal-list-of-nthcdr
                            scalarp)
                           (scalar-write-bits-le-gadget
                            int-from-bits-le-gadget
                            int-wrap values-int-of-unsigned
                            integer-widthp
                            values-literal-type-width
                            (:e base-prime) (:e scalar-prime) (:e expt))))))

(defruled progx-scalar-cast-integer-complete
  (implies (and (values-literal-type-integerp to)
                (progx-scalar-cast-hyps)
                (not (reserrp (scalar-cast (lookup-equal s asg) to)))
                (equal (lookup-equal-list sbits asg)
                       (scalar-bits-le (lookup-equal s asg)))
                (equal (lookup-equal-list sbrs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list sbits asg)
                        (scalar-modulus-minus-one-bits))))
           (r1cs::r1cs-constraints-holdp
            (append (scalar-write-bits-le-gadget s sbits sbrs p)
                    (int-from-bits-le-gadget
                     (nthcdr (values-literal-type-width to) sbits)))
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance scalar-write-bits-le-gadget-complete
                            (xs sbits) (rs sbrs) (acc nil))
                 (:instance scalar-write-bits-le-gadget-sound
                            (xs sbits) (rs sbrs) (acc nil))
                 (:instance int-from-bits-le-gadget-complete
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to))
                            (bits (lookup-equal-list sbits asg))
                            (excess (nthcdr (values-literal-type-width to)
                                            sbits)))
                 (:instance progx-len-nthcdr-of-251
                            (xs sbits) (n (values-literal-type-width to)))
                 progx-width-at-most-128
                 progx-base-prime-above-251
                 progx-integer-widthp-of-width)
           :in-theory (e/d (scalar-cast values-scalar-fix-when-scalarp
                            r1cs::r1cs-constraints-holdp-of-append
                            primep-of-base-prime
                            lookup-equal-list-of-nthcdr
                            int-from-bits-le-spec
                            not-spec-error-when-integerp
                            scalarp)
                           (scalar-write-bits-le-gadget
                            int-from-bits-le-gadget
                            int-wrap values-int-of-unsigned
                            integer-widthp
                            values-literal-type-width
                            (:e base-prime) (:e scalar-prime) (:e expt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Field-routed destinations.

(defruled progx-scalar-cast-is-field-cast
  (implies (and (scalarp s)
                (not (values-literal-type-integerp to))
                (not (literal-type-case to :field))
                (not (literal-type-case to :scalar)))
           (equal (scalar-cast s to) (field-cast s to)))
  :use progx-fieldp-when-scalarp
  :enable (scalar-cast field-cast values-scalar-fix-when-scalarp
           values-field-fix-when-fieldp))

(defruled progx-scalar-cast-gadget-when-field-routed
  (implies (and (not (values-literal-type-integerp to))
                (not (literal-type-case to :field))
                (not (literal-type-case to :scalar))
                (not (literal-type-case to :signature))
                (not (literal-type-case to :string)))
           (equal (progx-scalar-cast-call)
                  (progx-field-cast-gadget to s
                   y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                   m-z r-z m-o r-o or-bit ixs sxs frs u srs
                   rs bitrows excess witrows partial uscore islet p)))
  :enable progx-scalar-cast-gadget)

(defruled progx-scalar-cast-signature-string
  (implies (or (literal-type-case to :signature)
               (literal-type-case to :string))
           (and (equal (progx-scalar-cast-call) nil)
                (equal (scalar-cast s to) (spec-error))))
  :enable (progx-scalar-cast-gadget scalar-cast values-literal-type-integerp))

(defruled progx-scalar-cast-out-field-routed
  (implies (and (not (values-literal-type-integerp to))
                (not (literal-type-case to :field))
                (not (literal-type-case to :scalar)))
           (equal (progx-scalar-cast-out to s y r-o ixs sxs bitrows sbits asg)
                  (progx-field-cast-out to s y r-o ixs sxs bitrows asg)))
  :enable progx-scalar-cast-out)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-scalar-cast-sound
  :short "R1CS-SOUND of Scalar::cast: for every destination type, the
          constraints imply that the literal of the output wires is the
          funspec of the input scalar."
  (implies (progx-scalar-cast-hyps
            (r1cs::r1cs-constraints-holdp (progx-scalar-cast-call) asg p))
           (equal (progx-scalar-cast-out to s y r-o ixs sxs bitrows sbits asg)
                  (scalar-cast (lookup-equal s asg) to)))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (literal-type-case to :field)
          (literal-type-case to :scalar)
          (or (literal-type-case to :signature)
              (literal-type-case to :string)))
  :hints (("Subgoal 5"
           :use (progx-scalar-cast-out-field-routed
                 (:instance progx-scalar-cast-is-field-cast
                            (s (lookup-equal s asg)))
                 progx-scalar-cast-gadget-when-field-routed
                 (:instance progx-field-cast-sound-hypsp (x s)))
           :in-theory nil)
          ("Subgoal 4"
           :use progx-scalar-cast-integer-sound
           :in-theory '(progx-scalar-cast-gadget progx-scalar-cast-out))
          ("Subgoal 3"
           :in-theory '(progx-scalar-cast-out scalar-cast
                        values-literal-type-integerp
                        values-scalar-fix-when-scalarp
                        (:e member-eq)))
          ("Subgoal 2"
           :in-theory '(progx-scalar-cast-out scalar-cast
                        values-literal-type-integerp
                        values-scalar-fix-when-scalarp
                        (:e member-eq)))
          ("Subgoal 1"
           :in-theory '(progx-scalar-cast-out progx-field-cast-out
                        values-literal-type-integerp scalar-cast
                        (:e member-eq)))))

(define progx-scalar-cast-witsp ((to literal-typep) s
                                 y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                 m-z r-z m-o r-o or-bit
                                 ixs
                                 sxs frs u srs
                                 rs bitrows excess witrows partial uscore islet
                                 sbits sbrs
                                 (p primep) asg)
  :verify-guards nil
  :short "Canonical witnesses: the scalar bits and their fold witness for an
          integer destination, otherwise those of the Field::cast arm on s."
  (if (values-literal-type-integerp to)
      (and (equal (lookup-equal-list sbits asg)
                  (scalar-bits-le (lookup-equal s asg)))
           (equal (lookup-equal-list sbrs asg)
                  (crv-bits-lte-const-witness
                   (lookup-equal-list sbits asg)
                   (scalar-modulus-minus-one-bits))))
    (progx-field-cast-witsp to s
     y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
     m-z r-z m-o r-o or-bit ixs sxs frs u srs
     rs bitrows excess witrows partial uscore islet p asg)))

(defruled progx-scalar-cast-complete
  :short "R1CS-COMPLETE of Scalar::cast: for every destination type on which
          scalar-cast does not fail, the canonical witnesses satisfy the
          dispatch gadget."
  (implies (progx-scalar-cast-hyps
            (not (reserrp (scalar-cast (lookup-equal s asg) to)))
            (progx-scalar-cast-witsp to s
             y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
             m-z r-z m-o r-o or-bit ixs sxs frs u srs
             rs bitrows excess witrows partial uscore islet sbits sbrs p asg))
           (r1cs::r1cs-constraints-holdp (progx-scalar-cast-call) asg p))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (literal-type-case to :field)
          (literal-type-case to :scalar)
          (or (literal-type-case to :signature)
              (literal-type-case to :string)))
  :hints (("Subgoal 5"
           :use ((:instance progx-scalar-cast-is-field-cast
                            (s (lookup-equal s asg)))
                 progx-scalar-cast-gadget-when-field-routed
                 (:instance progx-field-cast-complete-hypsp (x s)))
           :in-theory '(progx-scalar-cast-witsp))
          ("Subgoal 4"
           :use progx-scalar-cast-integer-complete
           :in-theory '(progx-scalar-cast-gadget progx-scalar-cast-witsp))
          ("Subgoal 3"
           :in-theory '(progx-scalar-cast-gadget values-literal-type-integerp
                        r1cs::r1cs-constraints-holdp (:e member-eq)))
          ("Subgoal 2"
           :in-theory '(progx-scalar-cast-gadget values-literal-type-integerp
                        r1cs::r1cs-constraints-holdp (:e member-eq)))
          ("Subgoal 1"
           :in-theory '(progx-scalar-cast-gadget values-literal-type-integerp
                        r1cs::r1cs-constraints-holdp (:e member-eq)))))
