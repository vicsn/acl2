; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::cast (snarkVM
; circuit/program/src/data/literal/cast/identifier.rs):
;   Field              to_field (a linear combination of the byte bits)
;   IdentifierLiteral  clone
;   otherwise          to_field, then Field::cast
; The input is the identifier literal whose bytes the bit rows inrows carry.
; The output of to_field is a linear combination; the Field::cast wire x
; stands for it and the theorems take its value to be that combination's
; value, as in grp-from-bits.lisp.

(in-package "ALEOVM")

(include-book "progx-field-cast-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-id-decode-rows-when-matchp
  (implies (and (acl2::ubyte8-listp bytes)
                (id-bits-matchp bytes rows asg))
           (equal (id-decode-rows rows asg) bytes))
  :induct (id-bits-matchp bytes rows asg)
  :enable (id-bits-matchp id-decode-rows values-nat-to-lebits
           acl2::lebits=>nat-of-nat=>lebits acl2::ubyte8p))

(defruled progx-identifier-literal-of-own-bytes
  (implies (identifier-literalp id)
           (equal (make-identifier-literal :bytes (identifier-literal->bytes id))
                  id))
  :enable identifier-literal-fix-when-identifier-literalp)

(defruled progx-ubyte8-listp-of-bytes
  (acl2::ubyte8-listp (identifier-literal->bytes id)))

(define progx-field-cast-hypsp ((to literal-typep) x
                                y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                m-z r-z m-o r-o or-bit
                                ixs
                                sxs frs u srs
                                rs bitrows excess witrows partial uscore islet
                                (p primep) asg)
  :verify-guards nil
  :ignore-ok t
  :irrelevant-formals-ok t
  :short "The wire hypotheses of progx-field-cast-sound, as a predicate."
  (progx-field-cast-hyps))

(defmacro progx-field-cast-hypsp-call ()
  '(progx-field-cast-hypsp to x
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit ixs sxs frs u srs
    rs bitrows excess witrows partial uscore islet p asg))

(defruled progx-field-cast-sound-hypsp
  (implies (and (progx-field-cast-hypsp-call)
                (r1cs::r1cs-constraints-holdp (progx-field-cast-call) asg p))
           (equal (progx-field-cast-out to x y r-o ixs sxs bitrows asg)
                  (field-cast (lookup-equal x asg) to)))
  :use progx-field-cast-sound
  :in-theory '(progx-field-cast-hypsp))

(defruled progx-field-cast-complete-hypsp
  (implies (and (progx-field-cast-hypsp-call)
                (not (reserrp (field-cast (lookup-equal x asg) to)))
                (progx-field-cast-wits-call))
           (r1cs::r1cs-constraints-holdp (progx-field-cast-call) asg p))
  :use progx-field-cast-complete
  :in-theory '(progx-field-cast-hypsp))

(defruled progx-field-cast-when-signature-or-string
  (implies (or (equal (literal-type-kind to) :signature)
               (equal (literal-type-kind to) :string))
           (equal (field-cast x to) (spec-error)))
  :enable (field-cast values-literal-type-integerp))

(define progx-idlit-cast-gadget ((to literal-typep) x
                                 y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                 m-z r-z m-o r-o or-bit
                                 ixs
                                 sxs frs u srs
                                 rs bitrows excess witrows partial uscore islet
                                 (p primep))
  :verify-guards nil
  :short "No constraint for the Field and IdentifierLiteral destinations;
          otherwise the Field::cast dispatch on the to_field wire."
  (if (or (literal-type-case to :field)
          (literal-type-case to :identifier))
      nil
    (progx-field-cast-call)))

(defmacro progx-idlit-cast-call ()
  '(progx-idlit-cast-gadget to x
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit ixs sxs frs u srs
    rs bitrows excess witrows partial uscore islet p))

(define progx-idlit-cast-out ((to literal-typep) x y r-o ixs sxs bitrows
                              inrows asg)
  :verify-guards nil
  :short "The literal the output wires denote."
  (cond ((literal-type-case to :field) (literal-field (lookup-equal x asg)))
        ((literal-type-case to :identifier)
         (literal-identifier
          (make-identifier-literal :bytes (id-decode-rows inrows asg))))
        (t (progx-field-cast-out to x y r-o ixs sxs bitrows asg))))

(defmacro progx-idlit-cast-hyps (&rest more)
  `(and (literal-typep to)
        (equal p (base-prime))
        (identifier-literalp id)
        (id-bits-matchp (identifier-literal->bytes id) inrows asg)
        (r1cs::r1cs-valuationp asg p)
        (equal (lookup-equal x asg)
               (values-lebits-to-field
                (lookup-equal-list (fsa-id-flatten inrows) asg)))
        (implies (not (or (literal-type-case to :field)
                          (literal-type-case to :identifier)))
                 (progx-field-cast-hypsp-call))
        ,@more))

(defruled progx-idlit-x-is-to-field
  (implies (progx-idlit-cast-hyps)
           (equal (lookup-equal x asg) (identifier-literal-to-field id)))
  :use (:instance fsa-identifier-to-field-wire-sound (x id) (bitrows inrows))
  :in-theory '((:e identifier-to-field-gadget)
               r1cs::r1cs-constraints-holdp))

(defruled progx-idlit-cast-sound
  :short "R1CS-SOUND of IdentifierLiteral::cast: for every destination type,
          the constraints imply that the literal of the output wires is the
          funspec of the input identifier literal."
  (implies (progx-idlit-cast-hyps
            (r1cs::r1cs-constraints-holdp (progx-idlit-cast-call) asg p))
           (equal (progx-idlit-cast-out to x y r-o ixs sxs bitrows inrows asg)
                  (identifier-literal-cast id to)))
  :do-not-induct t
  :cases ((literal-type-case to :field)
          (literal-type-case to :identifier))
  :hints (("Subgoal 2"
           :use progx-idlit-x-is-to-field
           :in-theory '(progx-idlit-cast-out identifier-literal-cast
                        (:e literal-type-kind$inline)))
          ("Subgoal 1"
           :use ((:instance progx-id-decode-rows-when-matchp
                            (bytes (identifier-literal->bytes id))
                            (rows inrows))
                 progx-identifier-literal-of-own-bytes)
           :in-theory '(progx-idlit-cast-out identifier-literal-cast
                        progx-ubyte8-listp-of-bytes
                        (:e literal-type-kind$inline)))
          ("Subgoal 3"
           :use (progx-idlit-x-is-to-field progx-field-cast-sound-hypsp)
           :in-theory '(progx-idlit-cast-out identifier-literal-cast
                        progx-idlit-cast-gadget
                        progx-field-cast-when-signature-or-string))))

(defruled progx-idlit-cast-complete
  :short "R1CS-COMPLETE of IdentifierLiteral::cast: for every destination type
          on which identifier-literal-cast does not fail, the canonical
          witnesses of the Field::cast arm satisfy the constraints."
  (implies (progx-idlit-cast-hyps
            (not (reserrp (identifier-literal-cast id to)))
            (progx-field-cast-wits-call))
           (r1cs::r1cs-constraints-holdp (progx-idlit-cast-call) asg p))
  :do-not-induct t
  :cases ((literal-type-case to :field)
          (literal-type-case to :identifier))
  :hints (("Subgoal 3"
           :use (progx-idlit-x-is-to-field progx-field-cast-complete-hypsp)
           :in-theory '(identifier-literal-cast progx-idlit-cast-gadget
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 2"
           :in-theory '(progx-idlit-cast-gadget r1cs::r1cs-constraints-holdp))
          ("Subgoal 1"
           :in-theory '(progx-idlit-cast-gadget r1cs::r1cs-constraints-holdp))))
