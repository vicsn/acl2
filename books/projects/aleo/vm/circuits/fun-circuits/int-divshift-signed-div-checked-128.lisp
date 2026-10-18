; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed div_checked and rem_checked at width 128 (also div, div_assign,
; rem, rem_assign): the overflow check of int-divshift-signed-div-checked
; followed by the 128-bit wrapped circuits of int-divshift-signed-div-128.

(in-package "ALEOVM")

(include-book "int-divshift-signed-div-128")
(include-book "int-divshift-signed-div-checked")

(defruledl int-divshift-sdc128-posp
  (implies (integer-widthp n) (posp n))
  :enable integer-widthp)

(defund int-divshift-signed-div-checked-128-gadget
  (xs ys mins negones e1 w1 e2 w2 ov
      axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d s nqs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-divshift-overflow-check-gadget
           xs ys mins negones e1 w1 e2 w2 ov one p)
          (int-divshift-signed-div-wrapped-128-gadget
           xs ys axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d s nqs nc zs one p)))

(defund int-divshift-signed-rem-checked-128-gadget
  (xs ys mins negones e1 w1 e2 w2 ov
      axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d nrs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-divshift-overflow-check-gadget
           xs ys mins negones e1 w1 e2 w2 ov one p)
          (int-divshift-signed-rem-wrapped-128-gadget
           xs ys axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d nrs nc zs one p)))

(defruled int-divshift-signed-div-checked-128-gadget-sound
  :short "Signed div_checked (and div, div_assign), widths 8-64: given
          Integer::new operands, the constraints rule out a zero divisor
          and MIN / -1, and force the output bits to the spec."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd128-common-hyps)
                (symbolp s) (symbol-listp nqs)
                (equal (len nqs) n)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg nqs)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-signed-div-checked-128-gadget
                  xs ys mins negones e1 w1 e2 w2 ov
                  axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d s nqs nc zs one p)
                 asg p))
           (and (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1)))
                (integerp (int-div-checked-spec x y t n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-checked-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-sound)
                 (:instance int-divshift-signed-div-wrapped-128-gadget-sound)
                 (:instance int-divshift-sdc128-posp)
                 (:instance int-divshift-div-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-div-checked-128-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruled int-divshift-signed-rem-checked-128-gadget-sound
  :short "Signed rem_checked (and rem, rem_assign), widths 8-64: given
          Integer::new operands, the constraints rule out a zero divisor
          and MIN / -1, and force the output bits to the spec."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd128-common-hyps)
                (symbol-listp nrs)
                (equal (len nrs) n)
                (r1cs::valuation-binds-allp asg nrs)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-signed-rem-checked-128-gadget
                  xs ys mins negones e1 w1 e2 w2 ov
                  axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d nrs nc zs one p)
                 asg p))
           (and (not (equal y 0))
                (not (and (equal x (int-min t n)) (equal y -1)))
                (integerp (int-rem-checked-spec x y t n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-checked-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-sound)
                 (:instance int-divshift-signed-rem-wrapped-128-gadget-sound)
                 (:instance int-divshift-sdc128-posp)
                 (:instance int-divshift-rem-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-checked-128-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defmacro int-divshift-ovf128-witness-hyps ()
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

(defruled int-divshift-signed-div-checked-128-gadget-complete
  :short "Signed div_checked, widths 8-64: the snarkVM witnesses satisfy
          the constraints whenever the spec is not an error."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd128-common-hyps)
                (symbolp s) (symbol-listp nqs)
                (equal (len nqs) n)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg nqs)
                (int-divshift-ovf128-witness-hyps)
                (int-divshift-sd128-witness-hyps)
                (equal (lookup-equal s asg)
                       (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (equal (lookup-equal-list nqs asg)
                       (int->lebits (- (truncate (abs x) (abs y))) n))
                (equal (lookup-equal nc asg)
                       (if (< 0 (truncate (abs x) (abs y))) 0 1))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-checked-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-div-checked-128-gadget
             xs ys mins negones e1 w1 e2 w2 ov
             axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d s nqs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-complete)
                 (:instance int-divshift-signed-div-wrapped-128-gadget-complete)
                 (:instance int-divshift-sdc128-posp)
                 (:instance int-divshift-div-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-div-checked-128-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruled int-divshift-signed-rem-checked-128-gadget-complete
  :short "Signed rem_checked, widths 8-64: the snarkVM witnesses satisfy
          the constraints whenever the spec is not an error."
  (implies (and (int-divshift-ovf-hyps)
                (int-divshift-sd128-common-hyps)
                (symbol-listp nrs)
                (equal (len nrs) n)
                (r1cs::valuation-binds-allp asg nrs)
                (int-divshift-ovf128-witness-hyps)
                (int-divshift-sd128-witness-hyps)
                (equal (lookup-equal-list nrs asg)
                       (int->lebits (- (rem (abs x) (abs y))) n))
                (equal (lookup-equal nc asg)
                       (if (< 0 (rem (abs x) (abs y))) 0 1))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-checked-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-rem-checked-128-gadget
             xs ys mins negones e1 w1 e2 w2 ov
             axs mxs cx ays mys cy qs rs ll hl lh hh ms mcl mch ls l ds d nrs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-overflow-check-complete)
                 (:instance int-divshift-signed-rem-wrapped-128-gadget-complete)
                 (:instance int-divshift-sdc128-posp)
                 (:instance int-divshift-rem-checked-is-wrapped))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-checked-128-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))
