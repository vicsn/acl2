; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Integer::cast (snarkVM circuit/program/src/data/literal/cast/integer.rs)
; from the integer type `from` (width n0, signedness s0) on the input bit
; wires xs:
;   Address, Group, IdentifierLiteral  to_field, then Field::cast
;   Boolean   is_zero, is_one (to_field().is_equal), OR, assert: the
;             Field::cast Boolean arm on to_field
;   Field     to_field, no constraint
;   Scalar    Scalar::from_bits_le of n0 <= 128 bits, no constraint
;   Integer   the sign/width arm of progx-int-cast-int.lisp
;   Signature, String  no Cast impl; integer-cast fails, no constraint.
; to_field is the linear combination sum 2^i xs[i]; the Field::cast wire x
; stands for it and the theorems take its value to be that combination's
; value, as in grp-from-bits.lisp.

(in-package "ALEOVM")

(include-book "progx-int-cast-int")
(include-book "progx-scalar-cast")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-int-cast-gadget ((from literal-typep) (to literal-typep) xs x
                               y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                               m-z r-z m-o r-o or-bit
                               ixs
                               sxs frs u srs
                               rs bitrows excess witrows partial uscore islet
                               (p primep))
  :verify-guards nil
  (cond ((values-literal-type-integerp to)
         (progx-icast-int-gadget xs
                                 (values-literal-type-signedp from)
                                 (values-literal-type-signedp to)
                                 (values-literal-type-width to)
                                 p))
        ((or (literal-type-case to :field)
             (literal-type-case to :scalar)
             (literal-type-case to :signature)
             (literal-type-case to :string))
         nil)
        (t (progx-field-cast-call))))

(defmacro progx-int-cast-call ()
  '(progx-int-cast-gadget from to xs x
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit ixs sxs frs u srs
    rs bitrows excess witrows partial uscore islet p))

(define progx-int-cast-out ((from literal-typep) (to literal-typep) xs x
                            y r-o ixs sxs bitrows asg)
  :verify-guards nil
  :short "The literal the output wires denote.  For an integer destination it
          is the Integer::from_bits_le reading of the bits the arm passes
          to it (progx-icast-obits of the input bit values)."
  (cond ((values-literal-type-integerp to)
         (values-integer-literal
          to (int-wrap (lebits=>nat
                        (progx-icast-obits (lookup-equal-list xs asg)
                                           (values-literal-type-signedp from)
                                           (values-literal-type-signedp to)
                                           (values-literal-type-width to)))
                       (values-literal-type-signedp to)
                       (values-literal-type-width to))))
        ((literal-type-case to :field) (literal-field (lookup-equal x asg)))
        ((literal-type-case to :scalar) (literal-scalar (lookup-equal x asg)))
        (t (progx-field-cast-out to x y r-o ixs sxs bitrows asg))))

(defmacro progx-int-cast-field-routedp ()
  '(not (or (values-literal-type-integerp to)
            (literal-type-case to :field)
            (literal-type-case to :scalar)
            (literal-type-case to :signature)
            (literal-type-case to :string))))

(defmacro progx-int-cast-hyps (&rest more)
  `(and (literal-typep to)
        (literal-typep from)
        (values-literal-type-integerp from)
        (equal p (base-prime))
        (symbol-listp xs)
        (equal (len xs) (values-literal-type-width from))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (bit-listp (lookup-equal-list xs asg))
        (equal (lookup-equal x asg)
               (lebits=>nat (lookup-equal-list xs asg)))
        (implies (progx-int-cast-field-routedp)
                 (progx-field-cast-hypsp-call))
        ,@more))

(defmacro progx-int-cast-spec ()
  '(integer-cast (lebits->int (lookup-equal-list xs asg)
                              (values-literal-type-signedp from))
                 (values-literal-type-width from)
                 to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Value bridges.

(defruled progx-int-to-field-of-lebits->int
  (implies (and (bit-listp bs) (consp bs))
           (equal (values-int-to-field (lebits->int bs s0) (len bs))
                  (lebits=>nat bs)))
  :use (progx-lebits->int-cases progx-lebits-bound)
  :enable values-int-to-field)

(defruled progx-lebits->int-zero-one
  (implies (and (bit-listp bs) (<= 2 (len bs)))
           (and (equal (or (equal (lebits->int bs s0) 0)
                           (equal (lebits->int bs s0) 1))
                       (or (equal (lebits=>nat bs) 0)
                           (equal (lebits=>nat bs) 1)))
                (implies (or (equal (lebits=>nat bs) 0)
                             (equal (lebits=>nat bs) 1))
                         (equal (lebits->int bs s0) (lebits=>nat bs)))))
  :do-not-induct t
  :use (progx-lebits->int-cases
        progx-msb-0-iff-small
        progx-msb-0-or-1
        progx-lebits-bound
        (:instance progx-expt-2-mono (a 1) (b (1- (len bs))))))

(defruled progx-int-cast-is-field-cast
  (implies (and (bit-listp bs) (<= 2 (len bs)) (<= (len bs) 128)
                (not (values-literal-type-integerp to))
                (not (literal-type-case to :field))
                (not (literal-type-case to :scalar))
                (not (literal-type-case to :signature))
                (not (literal-type-case to :string)))
           (equal (integer-cast (lebits->int bs s0) (len bs) to)
                  (field-cast (lebits=>nat bs) to)))
  :do-not-induct t
  :use (progx-int-to-field-of-lebits->int progx-lebits->int-zero-one
        (:instance values-fieldp-of-int-to-field
                   (x (lebits->int bs s0)) (n (len bs))))
  :enable (integer-cast field-cast values-field-fix-when-fieldp)
  :disable (lebits->int values-int-to-field))

(defruled progx-int-cast-signature-string
  (implies (or (literal-type-case to :signature)
               (literal-type-case to :string))
           (equal (integer-cast x n to) (spec-error)))
  :enable (integer-cast values-literal-type-integerp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer arm.

(defruled progx-int-cast-integer-arm
  (implies (and (values-literal-type-integerp to)
                (progx-int-cast-hyps))
           (and (equal (r1cs::r1cs-constraints-holdp
                        (progx-icast-int-gadget
                         xs (values-literal-type-signedp from)
                         (values-literal-type-signedp to)
                         (values-literal-type-width to) p)
                        asg p)
                       (not (reserrp (progx-int-cast-spec))))
                (implies (not (reserrp (progx-int-cast-spec)))
                         (equal (progx-int-cast-out from to xs x
                                                    y r-o ixs sxs bitrows asg)
                                (progx-int-cast-spec)))))
  :do-not-induct t
  :use ((:instance progx-icast-int-gadget-iff
                   (s0 (values-literal-type-signedp from))
                   (s1 (values-literal-type-signedp to))
                   (n1 (values-literal-type-width to)))
        (:instance progx-icast-value
                   (bs (lookup-equal-list xs asg))
                   (s0 (values-literal-type-signedp from))
                   (s1 (values-literal-type-signedp to))
                   (n1 (values-literal-type-width to)))
        (:instance progx-width-at-most-128 (to from))
        (:instance progx-width-at-most-128 (to to)))
  :in-theory (e/d (progx-int-cast-out integer-cast)
                  (progx-icast-int-gadget progx-icast-predp progx-icast-obits
                   int-valuep int-wrap lebits->int values-int-to-field
                   values-integer-literal values-literal-type-width
                   values-literal-type-signedp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-width-at-least-8
  (<= 8 (values-literal-type-width to))
  :enable values-literal-type-width)

(defruled progx-int-cast-field-routed
  (implies (and (progx-int-cast-field-routedp)
                (progx-int-cast-hyps))
           (and (equal (progx-int-cast-call) (progx-field-cast-call))
                (equal (progx-int-cast-out from to xs x
                                           y r-o ixs sxs bitrows asg)
                       (progx-field-cast-out to x y r-o ixs sxs bitrows asg))
                (equal (progx-int-cast-spec)
                       (field-cast (lookup-equal x asg) to))))
  :do-not-induct t
  :use ((:instance progx-int-cast-is-field-cast
                   (bs (lookup-equal-list xs asg))
                   (s0 (values-literal-type-signedp from)))
        (:instance progx-width-at-most-128 (to from))
        (:instance progx-width-at-least-8 (to from)))
  :in-theory '(progx-int-cast-gadget progx-int-cast-out
               len-of-lookup-equal-list))

(defruled progx-int-cast-field-scalar
  (implies (and (or (literal-type-case to :field)
                    (literal-type-case to :scalar))
                (progx-int-cast-hyps))
           (and (equal (progx-int-cast-call) nil)
                (equal (progx-int-cast-out from to xs x
                                           y r-o ixs sxs bitrows asg)
                       (progx-int-cast-spec))))
  :do-not-induct t
  :use ((:instance progx-int-to-field-of-lebits->int
                   (bs (lookup-equal-list xs asg))
                   (s0 (values-literal-type-signedp from)))
        (:instance progx-width-at-most-128 (to from)))
  :in-theory (e/d (progx-int-cast-gadget progx-int-cast-out integer-cast
                   values-literal-type-integerp)
                  (lebits->int values-int-to-field values-literal-type-width)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-int-cast-sound
  :short "R1CS-SOUND of Integer::cast: for every destination type, the
          constraints imply that the literal of the output wires is the
          funspec of the input integer."
  (implies (progx-int-cast-hyps
            (r1cs::r1cs-constraints-holdp (progx-int-cast-call) asg p))
           (equal (progx-int-cast-out from to xs x y r-o ixs sxs bitrows asg)
                  (progx-int-cast-spec)))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (or (literal-type-case to :field)
              (literal-type-case to :scalar))
          (or (literal-type-case to :signature)
              (literal-type-case to :string)))
  :hints (("Subgoal 4"
           :use (progx-int-cast-field-routed
                 (:instance progx-field-cast-sound-hypsp))
           :in-theory nil)
          ("Subgoal 3"
           :use progx-int-cast-integer-arm
           :in-theory '(progx-int-cast-gadget))
          ("Subgoal 2"
           :use progx-int-cast-field-scalar
           :in-theory nil)
          ("Subgoal 1"
           :use (:instance progx-int-cast-signature-string
                           (x (lebits->int (lookup-equal-list xs asg)
                                           (values-literal-type-signedp from)))
                           (n (values-literal-type-width from)))
           :in-theory '(progx-int-cast-out progx-field-cast-out
                        values-literal-type-integerp
                        (:e member-eq)))))

(define progx-int-cast-witsp ((to literal-typep) x
                              y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                              m-z r-z m-o r-o or-bit
                              ixs
                              sxs frs u srs
                              rs bitrows excess witrows partial uscore islet
                              (p primep) asg)
  :verify-guards nil
  :short "Canonical witnesses: none for the Integer, Field, Scalar, Signature
          and String destinations, otherwise those of the Field::cast arm on
          the to_field wire."
  (if (progx-int-cast-field-routedp)
      (progx-field-cast-wits-call)
    t))

(defruled progx-int-cast-complete
  :short "R1CS-COMPLETE of Integer::cast: for every destination type on
          which integer-cast does not fail, the canonical witnesses satisfy
          the dispatch gadget."
  (implies (progx-int-cast-hyps
            (not (reserrp (progx-int-cast-spec)))
            (progx-int-cast-witsp to x
             y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
             m-z r-z m-o r-o or-bit ixs sxs frs u srs
             rs bitrows excess witrows partial uscore islet p asg))
           (r1cs::r1cs-constraints-holdp (progx-int-cast-call) asg p))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (or (literal-type-case to :field)
              (literal-type-case to :scalar))
          (or (literal-type-case to :signature)
              (literal-type-case to :string)))
  :hints (("Subgoal 4"
           :use (progx-int-cast-field-routed
                 (:instance progx-field-cast-complete-hypsp))
           :in-theory '(progx-int-cast-witsp))
          ("Subgoal 3"
           :use progx-int-cast-integer-arm
           :in-theory '(progx-int-cast-gadget))
          ("Subgoal 2"
           :use progx-int-cast-field-scalar
           :in-theory '(r1cs::r1cs-constraints-holdp))
          ("Subgoal 1"
           :in-theory '(progx-int-cast-gadget values-literal-type-integerp
                        r1cs::r1cs-constraints-holdp (:e member-eq)))))
