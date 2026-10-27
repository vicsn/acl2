; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier and ProgramID is_equal / is_not_equal soundness with no
; hypothesis beyond the constraints.  The theorems in prog-equal.lisp assume
; identifierp / program-idp inputs and bit-valued internal wires.  The
; Field::is_not_equal constraints force the result wires to be bits, and the
; Boolean AND / OR outputs of bits are bits.  The identifierp hypothesis is not
; needed: identifier->field fixes its argument, and every field value is the
; field of an identifier (progx-every-field-is-an-identifier-field), so the
; wire hypotheses restrict nothing beyond the valuation.

(in-package "ALEOVM")

(include-book "prog-equal")
(include-book "acct-equal-sound")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-every-field-is-an-identifier-field
  (implies (fieldp f)
           (and (identifierp (identifier f 0))
                (equal (identifier->field (identifier f 0)) f)))
  :enable (identifierp identifier->field))

(defruled progx-neq-r-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (prog-field-neq-gadget x y m r p) asg p)
                (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (bitp (lookup-equal r asg)))
  :hints (("Goal"
           :use (prog-field-neq-gadget-to-spec
                 (:instance acct-neq-values-bitp
                            (d (pfield::sub (lookup-equal x asg)
                                            (lookup-equal y asg) p))
                            (m (lookup-equal m asg))
                            (r (lookup-equal r asg)))))))

(defruled progx-or-values-bitp
  (implies (and (primep p)
                (bitp x) (bitp y)
                (pfield::fep z p)
                (equal (pfield::mul (pfield::sub 1 x p)
                                    (pfield::sub 1 y p)
                                    p)
                       (pfield::sub 1 z p)))
           (bitp z))
  :hints (("Goal"
           :cases ((equal (pfield::sub 1 z p) 0))
           :in-theory (e/d (bitp) ((:definition pfield::sub)))
           :use ((:instance pfield::equal-of-0-and-sub (x 1) (y z))))))

(defruled progx-or-z-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (prog-bool-or-gadget x y z p) asg p)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (bitp (lookup-equal z asg)))
  :hints (("Goal"
           :use (prog-bool-or-gadget-to-mul
                 (:instance progx-or-values-bitp
                            (x (lookup-equal x asg))
                            (y (lookup-equal y asg))
                            (z (lookup-equal z asg)))))))

(defruled progx-field-of-identifier-fix
  (equal (identifier->field (identifier-fix a)) (identifier->field a)))

(defruled progx-name-of-program-id-fix
  (equal (program-id->name (program-id-fix a)) (program-id->name a)))

(defruled progx-network-of-program-id-fix
  (equal (program-id->network (program-id-fix a)) (program-id->network a)))

(defruled progx-identifier-is-equal-of-fix
  (equal (identifier-is-equal (identifier-fix a) (identifier-fix b))
         (identifier-is-equal a b))
  :enable identifier-is-equal)

(defruled progx-identifier-is-not-equal-of-fix
  (equal (identifier-is-not-equal (identifier-fix a) (identifier-fix b))
         (identifier-is-not-equal a b))
  :enable identifier-is-not-equal)

(defruled progx-program-id-is-equal-of-fix
  (equal (program-id-is-equal (program-id-fix a) (program-id-fix b))
         (program-id-is-equal a b))
  :enable program-id-is-equal)

(defruled progx-program-id-is-not-equal-of-fix
  (equal (program-id-is-not-equal (program-id-fix a) (program-id-fix b))
         (program-id-is-not-equal a b))
  :enable program-id-is-not-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-identifier-is-equal-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-equal-gadget x y m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (identifier-is-equal a b)))
  :hints (("Goal"
           :use ((:instance identifier-is-equal-gadget-sound
                            (a (identifier-fix a)) (b (identifier-fix b)))
                 progx-identifier-is-equal-of-fix
                 (:instance progx-neq-r-bitp))
           :in-theory '(identifier-is-equal-gadget
                        identifierp-of-identifier-fix
                        progx-field-of-identifier-fix
                        primep-of-base-prime))))

(defruled progx-identifier-is-not-equal-sound
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal x asg) (identifier->field a))
                (equal (lookup-equal y asg) (identifier->field b))
                (r1cs::r1cs-constraints-holdp
                 (identifier-is-not-equal-gadget x y m r p) asg p))
           (equal (lookup-equal r asg)
                  (identifier-is-not-equal a b)))
  :hints (("Goal"
           :use ((:instance identifier-is-not-equal-gadget-sound
                            (a (identifier-fix a)) (b (identifier-fix b)))
                 progx-identifier-is-not-equal-of-fix
                 (:instance progx-neq-r-bitp))
           :in-theory '(identifier-is-not-equal-gadget
                        identifierp-of-identifier-fix
                        progx-field-of-identifier-fix
                        primep-of-base-prime))))

(defruled progx-program-id-is-equal-sound
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
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (r1cs::r1cs-constraints-holdp
                 (program-id-is-equal-gadget
                  xn yn mn rn xw yw mw rw z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (program-id-is-equal a b)))
  :hints (("Goal"
           :use ((:instance program-id-is-equal-gadget-sound
                            (a (program-id-fix a)) (b (program-id-fix b)))
                 progx-program-id-is-equal-of-fix
                 (:instance progx-neq-r-bitp
                            (x xn) (y yn) (m mn) (r rn))
                 (:instance progx-neq-r-bitp
                            (x xw) (y yw) (m mw) (r rw)))
           :in-theory '(program-id-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        program-idp-of-program-id-fix
                        progx-name-of-program-id-fix
                        progx-network-of-program-id-fix
                        primep-of-base-prime))))

(defruled progx-program-id-is-not-equal-sound
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
                (equal (lookup-equal xn asg)
                       (identifier->field (program-id->name a)))
                (equal (lookup-equal yn asg)
                       (identifier->field (program-id->name b)))
                (equal (lookup-equal xw asg)
                       (identifier->field (program-id->network a)))
                (equal (lookup-equal yw asg)
                       (identifier->field (program-id->network b)))
                (r1cs::r1cs-constraints-holdp
                 (program-id-is-not-equal-gadget
                  xn yn mn rn xw yw mw rw z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (program-id-is-not-equal a b)))
  :hints (("Goal"
           :use ((:instance program-id-is-not-equal-gadget-sound
                            (a (program-id-fix a)) (b (program-id-fix b)))
                 progx-program-id-is-not-equal-of-fix
                 (:instance progx-neq-r-bitp
                            (x xn) (y yn) (m mn) (r rn))
                 (:instance progx-neq-r-bitp
                            (x xw) (y yw) (m mw) (r rw))
                 (:instance progx-or-z-bitp (x rn) (y rw)))
           :in-theory '(program-id-is-not-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        program-idp-of-program-id-fix
                        progx-name-of-program-id-fix
                        progx-network-of-program-id-fix
                        primep-of-base-prime))))
