; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed DivChecked::div_checked and RemChecked::rem_checked (also Div::div,
; DivAssign::div_assign, Rem::rem, RemAssign::rem_assign), variable
; operands, widths 8, 16, 32, 64:
;
;   overflows = x.is_equal(MIN) & y.is_equal(-1)
;   E::assert(!overflows)
;   then the div_wrapped / rem_wrapped circuit.
;
; Each is_equal is !is_not_equal (free NOT), so the AND of the two
; negated not-equal bits is (1 - e1) * (1 - e2) = ov, i.e.
; boolean-nor-gadget, and E::assert(!ov) is (1 - ov) * 1 = 1.
; The constant operands MIN and -1 are passed as bit wires holding their
; bits, as int-is-zero-gadget and int-is-one-gadget do in int-equal.

(in-package "ALEOVM")

(include-book "int-divshift-signed-div")
(include-book "int-equal")
(include-book "../r1cs/boolean-nor")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Assert !ov.

(define int-divshift-assert-not-gadget ((ov symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1) (list (1- p) ov))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

(defruled int-divshift-assert-not-gadget-correct
  (implies (and (primep p)
                (symbolp ov)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg ov))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-assert-not-gadget ov p) asg p)
                  (equal (lookup-equal ov asg) 0)))
  :enable (int-divshift-assert-not-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers.

(defruledl int-divshift-sdc-integerp
  (implies (int-valuep x signedp n) (integerp x))
  :enable int-valuep)

(defruledl int-divshift-sdc-posp
  (implies (integer-widthp n) (posp n))
  :enable integer-widthp)

(defruledl int-divshift-sdc-constants-valuep
  (implies (posp n)
           (and (int-valuep (int-min t n) t n)
                (int-valuep -1 t n)))
  :enable (int-valuep int-min int-max))

(defruledl int-divshift-sdc-int->lebits-when-mod-equal
  (implies (equal (mod (ifix x) (expt 2 n)) (mod (ifix c) (expt 2 n)))
           (equal (int->lebits x n) (int->lebits c n)))
  :enable int->lebits)

(defrulel int-divshift-sdc-nat-injective
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep c t n)
                (equal (lebits=>nat (int->lebits x n))
                       (lebits=>nat (int->lebits c n))))
           (equal x c))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits->int-of-int->lebits (signedp t))
        (:instance lebits->int-of-int->lebits (x c) (signedp t))
        (:instance lebits=>nat-of-int->lebits)
        (:instance lebits=>nat-of-int->lebits (x c))
        (:instance int-divshift-sdc-int->lebits-when-mod-equal)
        (:instance int-divshift-sdc-integerp (signedp t))
        (:instance int-divshift-sdc-integerp (x c) (signedp t)))
  :disable (lebits->int-of-int->lebits lebits=>nat-of-int->lebits))

(defruled int-divshift-sdc-neq-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp cs)
                (symbolp e) (symbolp w) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len cs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg cs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep c t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list cs asg) (int->lebits c n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-equal-gadget xs cs e w one p) asg p))
           (equal (lookup-equal e asg) (if (equal x c) 0 1)))
  :do-not-induct t
  :use ((:instance unsigned-small-neq-gadget-soundness
                   (ys cs) (z e))
        (:instance int-divshift-sdc-nat-injective)
        (:instance int-width-lt-prime-bits)
        (:instance int-divshift-sdc-posp))
  :enable (int-is-equal-gadget
           int-is-not-equal-gadget
           bit-listp-of-int->lebits-explicit)
  :disable ((:e primep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Spec bridges: without the MIN / -1 case the checked specs agree with the
; wrapped ones.

(defruled int-divshift-div-checked-is-wrapped
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1))))
           (and (integerp (int-div-checked-spec x y t n))
                (equal (int->lebits (int-div-wrapped-spec x y t n) n)
                       (int->lebits (int-div-checked-spec x y t n) n))))
  :do-not-induct t
  :use (:instance int-divshift-truncate-fits (k (expt 2 (1- n))))
  :enable (int-div-checked-spec int-div-wrapped-spec
           int->lebits-of-int-wrap
           int-valuep int-min int-max)
  :disable truncate)

(defruled int-divshift-rem-checked-is-wrapped
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1))))
           (and (integerp (int-rem-checked-spec x y t n))
                (equal (int-rem-checked-spec x y t n)
                       (int-rem-wrapped-spec x y t n))))
  :do-not-induct t
  :use ((:instance int-divshift-truncate-fits (k (expt 2 (1- n))))
        (:instance int-divshift-integerp-of-rem)
        (:instance int-divshift-sdc-integerp (signedp t))
        (:instance int-divshift-sdc-integerp (x y) (signedp t)))
  :enable (int-rem-checked-spec int-rem-wrapped-spec
           int-valuep int-min int-max)
  :disable (truncate rem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Overflow check alone.

(defund int-divshift-overflow-check-gadget (xs ys mins negones e1 w1 e2 w2 ov
                                               one p)
  (declare (xargs :verify-guards nil))
  (append (int-is-equal-gadget xs mins e1 w1 one p)
          (int-is-equal-gadget ys negones e2 w2 one p)
          (boolean-nor-gadget e1 e2 ov p)
          (int-divshift-assert-not-gadget ov p)))

(defmacro int-divshift-ovf-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (symbol-listp xs) (symbol-listp ys)
        (symbol-listp mins) (symbol-listp negones)
        (symbolp e1) (symbolp w1) (symbolp e2) (symbolp w2)
        (symbolp ov) (symbolp one)
        (equal n (len xs))
        (integer-widthp n)
        (equal (len ys) n)
        (equal (len mins) n)
        (equal (len negones) n)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg mins)
        (r1cs::valuation-binds-allp asg negones)
        (r1cs::valuation-bindsp asg e1)
        (r1cs::valuation-bindsp asg w1)
        (r1cs::valuation-bindsp asg e2)
        (r1cs::valuation-bindsp asg w2)
        (r1cs::valuation-bindsp asg ov)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (int-valuep x t n)
        (int-valuep y t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ys asg) (int->lebits y n))
        (equal (lookup-equal-list mins asg) (int->lebits (int-min t n) n))
        (equal (lookup-equal-list negones asg) (int->lebits -1 n))))

(defruled int-divshift-overflow-check-sound
  (implies (and (int-divshift-ovf-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-overflow-check-gadget
                  xs ys mins negones e1 w1 e2 w2 ov one p)
                 asg p))
           (not (and (equal x (int-min t n)) (equal y -1))))
  :do-not-induct t
  :use ((:instance int-divshift-sdc-neq-sound
                   (cs mins) (e e1) (w w1) (c (int-min t n)))
        (:instance int-divshift-sdc-neq-sound
                   (xs ys) (x y) (cs negones) (e e2) (w w2) (c -1))
        (:instance int-divshift-sdc-posp)
        (:instance int-divshift-sdc-constants-valuep)
        (:instance boolean-nor-gadget-to-bitnor (x e1) (y e2) (z ov))
        (:instance int-divshift-assert-not-gadget-correct))
  :enable (int-divshift-overflow-check-gadget bitnor)
  :disable ((:e primep) int-is-equal-gadget boolean-nor-gadget
            int-divshift-assert-not-gadget))

(defruled int-divshift-overflow-check-complete
  (implies (and (int-divshift-ovf-hyps)
                (not (and (equal x (int-min t n)) (equal y -1)))
                (equal (lookup-equal e1 asg)
                       (int-is-not-equal-spec x (int-min t n) t n))
                (equal (lookup-equal w1 asg)
                       (if (equal x (int-min t n))
                           0
                         (pfield::inv
                          (pfield::sub (int-spec-unsigned x n)
                                       (int-spec-unsigned (int-min t n) n)
                                       p)
                          p)))
                (equal (lookup-equal e2 asg)
                       (int-is-not-equal-spec y -1 t n))
                (equal (lookup-equal w2 asg)
                       (if (equal y -1)
                           0
                         (pfield::inv
                          (pfield::sub (int-spec-unsigned y n)
                                       (int-spec-unsigned -1 n)
                                       p)
                          p)))
                (equal (lookup-equal ov asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-overflow-check-gadget
             xs ys mins negones e1 w1 e2 w2 ov one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-is-equal-gadget-complete
                   (ys mins) (z e1) (w w1) (y (int-min t n)) (signedp t))
        (:instance int-is-equal-gadget-complete
                   (xs ys) (x y) (ys negones) (z e2) (w w2) (y -1)
                   (signedp t))
        (:instance int-divshift-sdc-posp)
        (:instance int-divshift-sdc-constants-valuep)
        (:instance boolean-nor-gadget-to-bitnor (x e1) (y e2) (z ov))
        (:instance int-divshift-assert-not-gadget-correct))
  :enable (int-divshift-overflow-check-gadget
           bitnor
           int-is-not-equal-spec
           int-spec-bool)
  :disable ((:e primep) int-is-equal-gadget boolean-nor-gadget
            int-divshift-assert-not-gadget
            int-is-equal-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; div_checked and rem_checked.

(defund int-divshift-signed-div-checked-gadget
  (xs ys mins negones e1 w1 e2 w2 ov
      axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-divshift-overflow-check-gadget
           xs ys mins negones e1 w1 e2 w2 ov one p)
          (int-divshift-signed-div-wrapped-gadget
           xs ys axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)))

(defund int-divshift-signed-rem-checked-gadget
  (xs ys mins negones e1 w1 e2 w2 ov
      axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-divshift-overflow-check-gadget
           xs ys mins negones e1 w1 e2 w2 ov one p)
          (int-divshift-signed-rem-wrapped-gadget
           xs ys axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)))

(defruled int-divshift-signed-div-checked-gadget-sound
  :short "Signed div_checked (and div, div_assign), widths 8-64: given
          Integer::new operands, the constraints rule out a zero divisor
          and MIN / -1, and force the output bits to the spec."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd-common-hyps)
                (symbolp s) (symbol-listp nqs)
                (equal (len nqs) n)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg nqs)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-signed-div-checked-gadget
                  xs ys mins negones e1 w1 e2 w2 ov
                  axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
                 asg p))
           (and (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1)))
                (integerp (int-div-checked-spec x y t n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-checked-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-sound)
                 (:instance int-divshift-signed-div-wrapped-gadget-sound)
                 (:instance int-divshift-sdc-posp)
                 (:instance int-divshift-div-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-div-checked-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruled int-divshift-signed-rem-checked-gadget-sound
  :short "Signed rem_checked (and rem, rem_assign), widths 8-64: given
          Integer::new operands, the constraints rule out a zero divisor
          and MIN / -1, and force the output bits to the spec."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd-common-hyps)
                (symbol-listp nrs)
                (equal (len nrs) n)
                (r1cs::valuation-binds-allp asg nrs)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-signed-rem-checked-gadget
                  xs ys mins negones e1 w1 e2 w2 ov
                  axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
                 asg p))
           (and (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1)))
                (integerp (int-rem-checked-spec x y t n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-checked-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-sound)
                 (:instance int-divshift-signed-rem-wrapped-gadget-sound)
                 (:instance int-divshift-sdc-posp)
                 (:instance int-divshift-rem-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-checked-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defmacro int-divshift-ovf-witness-hyps ()
  '(and (not (and (equal x (int-min t n)) (equal y -1)))
        (equal (lookup-equal e1 asg)
               (int-is-not-equal-spec x (int-min t n) t n))
        (equal (lookup-equal w1 asg)
               (if (equal x (int-min t n))
                   0
                 (pfield::inv
                  (pfield::sub (int-spec-unsigned x n)
                               (int-spec-unsigned (int-min t n) n)
                               p)
                  p)))
        (equal (lookup-equal e2 asg)
               (int-is-not-equal-spec y -1 t n))
        (equal (lookup-equal w2 asg)
               (if (equal y -1)
                   0
                 (pfield::inv
                  (pfield::sub (int-spec-unsigned y n)
                               (int-spec-unsigned -1 n)
                               p)
                  p)))
        (equal (lookup-equal ov asg) 0)))

(defruled int-divshift-signed-div-checked-gadget-complete
  :short "Signed div_checked, widths 8-64: the snarkVM witnesses satisfy
          the constraints whenever the spec is not an error."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd-common-hyps)
                (symbolp s) (symbol-listp nqs)
                (equal (len nqs) n)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg nqs)
                (int-divshift-ovf-witness-hyps)
                (int-divshift-sd-witness-hyps)
                (equal (lookup-equal s asg)
                       (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (equal (lookup-equal-list nqs asg)
                       (int->lebits (- (truncate (abs x) (abs y))) n))
                (equal (lookup-equal nc asg)
                       (if (< 0 (truncate (abs x) (abs y))) 0 1))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-checked-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-div-checked-gadget
             xs ys mins negones e1 w1 e2 w2 ov
             axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-complete)
                 (:instance int-divshift-signed-div-wrapped-gadget-complete)
                 (:instance int-divshift-sdc-posp)
                 (:instance int-divshift-div-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-div-checked-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruled int-divshift-signed-rem-checked-gadget-complete
  :short "Signed rem_checked, widths 8-64: the snarkVM witnesses satisfy
          the constraints whenever the spec is not an error."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd-common-hyps)
                (symbol-listp nrs)
                (equal (len nrs) n)
                (r1cs::valuation-binds-allp asg nrs)
                (int-divshift-ovf-witness-hyps)
                (int-divshift-sd-witness-hyps)
                (equal (lookup-equal-list nrs asg)
                       (int->lebits (- (rem (abs x) (abs y))) n))
                (equal (lookup-equal nc asg)
                       (if (< 0 (rem (abs x) (abs y))) 0 1))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-checked-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-rem-checked-gadget
             xs ys mins negones e1 w1 e2 w2 ov
             axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-complete)
                 (:instance int-divshift-signed-rem-wrapped-gadget-complete)
                 (:instance int-divshift-sdc-posp)
                 (:instance int-divshift-rem-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-checked-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))
