; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::cast_lossy (snarkVM circuit/program/src/data/literal/cast_lossy/
; boolean.rs).  On a non-constant boolean b every arm is a ternary between
; constants, which allocates no variable and emits no constraint:
;   Field::ternary(b, c1, c0) = b * c1 + (1 - b) * c0      (field, scalar,
;                                                          group/address x, y)
;   Boolean::ternary(b, 1, 0) = b,  Boolean::ternary(b, 0, 0) = 0
;                                                          (integer bits)
;   Field::from_boolean(b) = b,  Boolean -> Boolean is b itself.
; progx-boolean-cast-lossy-lc-literal is the literal those linear
; combinations denote; the theorems show it is boolean-cast-lossy.
; Signature, string and identifier have no CastLossy impl for Boolean.

(in-package "ALEOVM")

(include-book "progx-group-generator")
(include-book "../fun-specs/values-cast")
(include-book "../r1cs/boolean-and")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-lebits-value ((bits bit-listp))
  :returns (n natp)
  (if (endp bits)
      0
    (+ (bfix (car bits)) (* 2 (progx-lebits-value (cdr bits))))))

(define progx-field-ternary-const ((b bitp) (c1 fieldp) (c0 fieldp))
  :returns (v natp)
  :short "Field::ternary of a variable condition between two constants."
  (pfield::add (pfield::mul b c1 (base-prime))
               (pfield::mul (pfield::sub 1 b (base-prime)) c0 (base-prime))
               (base-prime)))

(define progx-boolean-cast-lossy-lc-literal ((b bitp) (to literal-typep))
  :returns (r literal-resultp)
  (b* ((b (bfix b))
       (gx (progx-field-ternary-const b *progx-generator-x* 0))
       (gy (progx-field-ternary-const b *progx-generator-y* 1)))
    (cond
     ((values-literal-type-integerp to)
      (b* ((n (values-literal-type-width to))
           (bits (cons b (repeat (1- n) 0))))
        (values-integer-literal
         to
         (values-int-of-unsigned (progx-lebits-value bits)
                                 (values-literal-type-signedp to)
                                 n))))
     (t
      (literal-type-case
       to
       :address (literal-address (values-to-group (ecurve::point-finite gx gy)))
       :boolean (literal-boolean b)
       :field (literal-field b)
       :group (literal-group (values-to-group (ecurve::point-finite gx gy)))
       :scalar (literal-scalar (progx-field-ternary-const b 1 0))
       :otherwise (spec-error)))))
  :guard-hints (("Goal" :in-theory (enable bitp values-fieldp-when-bounded
                                           values-scalarp-when-bounded
                                           progx-field-ternary-const)))
  :prepwork ((local (in-theory (enable bitp)))))

(define progx-boolean-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled progx-lebits-value-of-zeros
  (equal (progx-lebits-value (repeat k 0)) 0)
  :induct (repeat k 0)
  :enable (progx-lebits-value repeat))

(defruled progx-values-to-group-of-generator-point
  (equal (values-to-group
          (ecurve::point-finite *progx-generator-x* *progx-generator-y*))
         (values-group-generator))
  :use (progx-groupp-of-generator-point
        progx-values-group-generator-is-point)
  :in-theory '(values-to-group))

(defruled progx-values-to-group-of-zero-point
  (equal (values-to-group (ecurve::point-finite 0 1))
         (values-group-zero))
  :use (:instance groupp-of-values-group-zero)
  :in-theory '(values-to-group values-group-zero
               (:e ecurve::twisted-edwards-zero) (:e ecurve::point-finite)))

(defruled progx-boolean-cast-lossy-lc-is-funspec
  (implies (bitp b)
           (equal (progx-boolean-cast-lossy-lc-literal b to)
                  (boolean-cast-lossy b to)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (e/d (progx-boolean-cast-lossy-lc-literal
                              boolean-cast-lossy
                              progx-field-ternary-const
                              progx-lebits-value
                              progx-lebits-value-of-zeros
                              progx-values-to-group-of-generator-point
                              progx-values-to-group-of-zero-point
                              values-int-of-unsigned
                              values-literal-type-width
                              values-literal-type-signedp
                              bitp)
                           (values-to-group values-group-generator
                            values-group-zero
                            (:e values-to-group)
                            (:e ecurve::point-finite))))))

(defruled progx-boolean-cast-lossy-sound
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (progx-boolean-cast-lossy-gadget) asg p))
           (equal (progx-boolean-cast-lossy-lc-literal (lookup-equal b asg) to)
                  (boolean-cast-lossy (lookup-equal b asg) to)))
  :hints (("Goal" :use (:instance progx-boolean-cast-lossy-lc-is-funspec
                                  (b (lookup-equal b asg))))))

(defruled progx-boolean-cast-lossy-complete
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg)))
           (and (r1cs::r1cs-constraints-holdp
                 (progx-boolean-cast-lossy-gadget) asg p)
                (equal (progx-boolean-cast-lossy-lc-literal
                        (lookup-equal b asg) to)
                       (boolean-cast-lossy (lookup-equal b asg) to))))
  :hints (("Goal" :use (:instance progx-boolean-cast-lossy-lc-is-funspec
                                  (b (lookup-equal b asg)))
           :in-theory (enable progx-boolean-cast-lossy-gadget))))
