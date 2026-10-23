; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::cast (snarkVM circuit/program/src/data/literal/cast/boolean.rs).
; Every destination except IdentifierLiteral is cast_lossy
; (progx-boolean-cast-lossy.lisp: no constraint).  The IdentifierLiteral
; arm is `let field: Field = self.cast(); field.cast()`, i.e.
; Field::from_boolean (the boolean's own variable, no constraint) followed by
; IdentifierLiteral::from_field on that wire (fsa-idlit-from-field-gadget).
; For a bit that arm can never succeed: the constraints imply that
; identifier-literal-from-field returns a literal, and the funspec of the
; cast is that literal; on 0 or 1 the funspec fails, so the soundness theorem
; holds and the completeness theorem has no instance for that arm.

(in-package "ALEOVM")

(include-book "progx-boolean-cast-lossy")
(include-book "fsa-idlit-from-bits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-boolean-cast-gadget ((to literal-typep)
                                   (x symbolp)
                                   (rs symbol-listp)
                                   (u symbolp)
                                   (bitrows true-listp)
                                   (excess symbol-listp)
                                   (witrows true-listp)
                                   (partial symbolp) (uscore symbolp)
                                   (islet symbolp)
                                   (p primep))
  :verify-guards nil
  (if (literal-type-case to :identifier)
      (fsa-idlit-from-field-gadget x rs u bitrows excess witrows
                                   partial uscore islet p)
    (progx-boolean-cast-lossy-gadget)))

(define progx-boolean-cast-out ((b bitp) (to literal-typep) bitrows asg)
  :verify-guards nil
  :short "The literal the output wires and linear combinations denote."
  (if (literal-type-case to :identifier)
      (literal-identifier
       (make-identifier-literal :bytes (id-decode-rows bitrows asg)))
    (progx-boolean-cast-lossy-lc-literal b to)))

(defruled progx-boolean-cast-sound
  (implies (and (fsa-idlit-hyps
                 (fsa-field-hyps)
                 (bitp (lookup-equal x asg))
                 (r1cs::r1cs-constraints-holdp
                  (progx-boolean-cast-gadget to x rs u bitrows excess witrows
                                             partial uscore islet p)
                  asg p)))
           (equal (progx-boolean-cast-out (lookup-equal x asg) to bitrows asg)
                  (boolean-cast (lookup-equal x asg) to)))
  :cases ((literal-type-case to :identifier))
  :hints (("Subgoal 2"
           :in-theory (e/d (progx-boolean-cast-out boolean-cast)
                           (progx-boolean-cast-lossy-lc-literal
                            boolean-cast-lossy))
           :use (:instance progx-boolean-cast-lossy-lc-is-funspec
                           (b (lookup-equal x asg))))
          ("Subgoal 1"
           :in-theory (e/d (progx-boolean-cast-gadget
                            progx-boolean-cast-out
                            boolean-cast field-cast bitp)
                           (fsa-idlit-from-field-gadget
                            identifier-literal-from-field))
           :use fsa-idlit-from-field-gadget-sound)))

(defruled progx-boolean-cast-identifier-fails-const
  (implies (bitp b)
           (reserrp (boolean-cast b (literal-type-identifier))))
  :hints (("Goal" :cases ((equal b 0))
           :in-theory (enable bitp))))

(defruled progx-boolean-cast-identifier-fails
  (implies (and (bitp b) (literal-type-case to :identifier))
           (reserrp (boolean-cast b to)))
  :hints (("Goal"
           :use progx-boolean-cast-identifier-fails-const
           :in-theory (e/d (boolean-cast field-cast
                            values-literal-type-integerp)
                           (identifier-literal-from-field)))))

(defruled progx-boolean-cast-complete
  :short "For every destination where the funspec succeeds (all but
          IdentifierLiteral) the gadget is empty, so any assignment
          satisfies it and the output is the funspec."
  (implies (and (bitp b)
                (not (reserrp (boolean-cast b to))))
           (and (r1cs::r1cs-constraints-holdp
                 (progx-boolean-cast-gadget to x rs u bitrows excess witrows
                                            partial uscore islet p)
                 asg p)
                (equal (progx-boolean-cast-out b to bitrows asg)
                       (boolean-cast b to))))
  :hints (("Goal"
           :cases ((literal-type-case to :identifier))
           :in-theory (e/d (progx-boolean-cast-gadget
                            progx-boolean-cast-out
                            progx-boolean-cast-lossy-gadget
                            progx-boolean-cast-lossy-lc-is-funspec
                            boolean-cast)
                           (progx-boolean-cast-lossy-lc-literal
                            boolean-cast-lossy))
           :use (:instance progx-boolean-cast-identifier-fails))))
