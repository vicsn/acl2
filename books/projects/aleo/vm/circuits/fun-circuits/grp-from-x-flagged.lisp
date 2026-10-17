; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::from_x_coordinate_flagged (circuit/types/group/src/helpers/
; from_x_coordinate.rs).  The circuit squares x, witnesses yy with
; yy (d x^2 - 1) = a x^2 - 1, takes the unordered flagged square roots of
; yy, runs is_in_group on (x, root) and (x, -root), and selects the
; ordinate and flag with ternaries, an and and an or.
;
; Soundness does not need the order of the roots: on a square, both
; candidates are on the curve, so is_in_group decides membership, and any
; subgroup point with abscissa x has ordinate +-root.  On a non-square the
; ordinate is 0 and the flag 1 whatever the is_in_group bits are, which are
; bits by their is_zero constraints.  The funspec halts when is_in_group's
; formulas hit a zero denominator on the off-curve (x, 0); soundness assumes
; it does not.

(in-package "ALEOVM")

(include-book "grp-is-in-group")
(include-book "fsa-field-sqrt-flagged")
(include-book "crv-curve")

(defmacro grp-fl-num (xx)
  `(pfield::sub (pfield::mul (ecurve::edwards-bls12-a) ,xx (base-prime)) 1 (base-prime)))
(defmacro grp-fl-den (xx)
  `(pfield::sub (pfield::mul (ecurve::edwards-bls12-d) ,xx (base-prime)) 1 (base-prime)))

(defruled grp-fl-a-d-facts
  (and (pfield::fep (ecurve::edwards-bls12-a) (base-prime))
       (pfield::fep (ecurve::edwards-bls12-d) (base-prime))
       (not (equal (ecurve::edwards-bls12-a) (ecurve::edwards-bls12-d)))
       (primep (base-prime))
       (< 2 (base-prime)))
  :in-theory '((:e <) (:e ecurve::edwards-bls12-a) (:e ecurve::edwards-bls12-d)
               (:e base-prime) (:e pfield::fep) (:e primep)))

(defrule grp-fl-cancel
  (implies (and (primep p) (pfield::fep x p) (pfield::fep y p) (pfield::fep tt p)
                (not (equal tt 0))
                (equal (pfield::mul x tt p) (pfield::mul y tt p)))
           (equal x y))
  :rule-classes nil
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-den-nonzero-gen
  (implies (and (primep p) (< 2 p) (pfield::fep a p) (pfield::fep d p) (pfield::fep tt p)
                (not (equal a d))
                (equal (pfield::sub (pfield::mul d tt p) 1 p) 0))
           (not (equal (pfield::sub (pfield::mul a tt p) 1 p) 0)))
  :use ((:instance grp-fl-cancel (x a) (y d)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

(defruled grp-fl-den-nonzero
  :short "@($y^2 (d x^2 - 1) = a x^2 - 1$) forces @($d x^2 - 1 \\neq 0$),
          since @($a \\neq d$)."
  (implies (and (fieldp xx) (fieldp yy)
                (equal (pfield::mul yy (grp-fl-den xx) (base-prime))
                       (grp-fl-num xx)))
           (not (equal (grp-fl-den xx) 0)))
  :use (grp-fl-a-d-facts
        (:instance grp-fl-den-nonzero-gen
                   (p (base-prime)) (a (ecurve::edwards-bls12-a))
                   (d (ecurve::edwards-bls12-d)) (tt xx)))
  :in-theory '(fieldp pfield::mul-of-0-arg2 (:e pfield::fep))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-num-is-neg
  (implies (fieldp xx)
           (equal (grp-fl-num xx)
                  (pfield::sub (pfield::neg xx (base-prime)) 1 (base-prime))))
  :use (:instance crv-edwards-a-is-minus-one (p (base-prime)))
  :in-theory (enable fieldp)
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-coords
  (implies (and (fieldp x) (fieldp y))
           (curve-coordinatesp (ecurve::point-finite x y)))
  :enable (curve-coordinatesp fieldp))

(defruled grp-fl-on-curve-iff
  :short "With @($y^2 (d x^2 - 1) = a x^2 - 1$) and a nonzero denominator,
          @($(x, y)$) is on the curve iff @($y^2$) is @('yy')."
  (implies (and (fieldp x) (fieldp y) (fieldp yy)
                (equal (pfield::mul yy (grp-fl-den (pfield::mul x x (base-prime)))
                                    (base-prime))
                       (grp-fl-num (pfield::mul x x (base-prime)))))
           (equal (ecurve::edwards-bls12-pointp (ecurve::point-finite x y))
                  (equal (pfield::mul y y (base-prime)) yy)))
  :do-not-induct t
  :use (grp-fl-a-d-facts
        (:instance grp-fl-coords)
        (:instance crv-curve-coordinates-on-curve-iff-snarkvm
                   (p (base-prime)) (pt (ecurve::point-finite x y)))
        (:instance grp-fl-num-is-neg (xx (pfield::mul x x (base-prime))))
        (:instance grp-fl-den-nonzero (xx (pfield::mul x x (base-prime))))
        (:instance grp-fl-cancel (p (base-prime))
                   (x (pfield::mul y y (base-prime))) (y yy)
                   (tt (grp-fl-den (pfield::mul x x (base-prime))))))
  :in-theory (e/d (fieldp) ((:e base-prime) ecurve::edwards-bls12-pointp
                            pfield::mul pfield::sub pfield::neg
                            ecurve::edwards-bls12-d ecurve::edwards-bls12-a))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-is-zero-gadget-out-bit
  (implies (and (symbolp x) (symbolp y)
                (symbolp mx) (symbolp rx) (symbolp my) (symbolp ry) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x) (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg mx) (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg my) (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg out)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-zero-gadget x y mx rx my ry out p) asg p))
           (bitp (lookup-equal out asg)))
  :do-not-induct t
  :use ((:instance field-is-zero-gadget-forces-bit (m mx) (r rx))
        (:instance field-is-one-gadget-forces-bit (x y) (m my) (r ry))
        (:instance crv-and-not-gadget-to-mul (rx rx) (ry ry))
        primep-of-base-prime)
  :in-theory (e/d (crv-group-is-zero-gadget r1cs::r1cs-constraints-holdp-of-append bitp)
                  (field-is-zero-gadget field-is-one-gadget crv-and-not-gadget
                   (:e base-prime)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-is-in-group-gadget-out-bit
  (implies (and (grp-csteps-boundp steps asg)
                (grp-bound-all bx by mx rx my ry out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (grp-is-in-group-gadget bx by steps mx rx my ry out p) asg p))
           (bitp (lookup-equal out asg)))
  :do-not-induct t
  :use ((:instance grp-cmul-steps-out-bound
                   (cbits (cdr (grp-r-bits))) (ax bx) (ay by))
        (:instance grp-is-zero-gadget-out-bit
                   (x (first (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
                   (y (second (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))))
  :in-theory '(grp-is-in-group-gadget r1cs::r1cs-constraints-holdp-of-append))

(define grp-fl-yy-gadget ((yy symbolp) (xx symbolp) (p primep))
  :short "@('E::enforce(yy, d * xx - 1, a * xx - 1)'), with @('a') and
          @('d') constant coefficients."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 yy))
         :b (list (list (ecurve::edwards-bls12-d) xx) (list (1- p) 1))
         :c (list (list (ecurve::edwards-bls12-a) xx) (list (1- p) 1)))))

(define grp-fl-ternary-zero2-gadget ((c symbolp) (a symbolp) (r symbolp))
  :short "@('Field::ternary(c, a, 0)'): @($(a - 0) \\cdot c = r - 0$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a))
         :b (list (list 1 c))
         :c (list (list 1 r)))))

(define grp-fl-ternary-zero1-gadget ((c symbolp) (b symbolp) (r symbolp) (p primep))
  :short "@('Field::ternary(c, 0, b)'): @($(0 - b) \\cdot c = r - b$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) b))
         :b (list (list 1 c))
         :c (list (list 1 r) (list (1- p) b)))))

(define grp-fl-or-gadget ((u symbolp) (v symbolp) (w symbolp) (p primep))
  :short "@('Boolean::bitor'): @($(1 - u)(1 - v) = 1 - w$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1) (list (1- p) u))
         :b (list (list 1 1) (list (1- p) v))
         :c (list (list 1 1) (list (1- p) w)))))

(defmacro grp-fl-holds (gadget) `(r1cs::r1cs-constraints-holdp ,gadget asg p))

(defruled grp-fl-yy-gadget-to-eq
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (grp-bound-all yy xx)
                (grp-fl-holds (grp-fl-yy-gadget yy xx p)))
           (equal (pfield::mul (lookup-equal yy asg) (grp-fl-den (lookup-equal xx asg)) p)
                  (grp-fl-num (lookup-equal xx asg))))
  :do-not-induct t
  :use grp-fl-a-d-facts
  :in-theory (e/d (grp-fl-yy-gadget r1cs::r1cs-constraint-holdsp r1cs::dot-product
                   pfield::sub)
                  ((:e base-prime) ecurve::edwards-bls12-d ecurve::edwards-bls12-a))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-ternary-zero2-to-eq
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (grp-bound-all c a r)
                (bitp (lookup-equal c asg))
                (grp-fl-holds (grp-fl-ternary-zero2-gadget c a r)))
           (equal (lookup-equal r asg)
                  (if (equal (lookup-equal c asg) 1) (lookup-equal a asg) 0)))
  :do-not-induct t
  :in-theory (e/d (grp-fl-ternary-zero2-gadget r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product bitp)
                  ((:e base-prime)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-ternary-zero1-to-eq
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (grp-bound-all c b r)
                (bitp (lookup-equal c asg))
                (grp-fl-holds (grp-fl-ternary-zero1-gadget c b r p)))
           (equal (lookup-equal r asg)
                  (if (equal (lookup-equal c asg) 1) 0 (lookup-equal b asg))))
  :do-not-induct t
  :use primep-of-base-prime
  :in-theory (e/d (grp-fl-ternary-zero1-gadget r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product bitp)
                  ((:e base-prime)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-or-to-eq
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (grp-bound-all u v w)
                (bitp (lookup-equal u asg))
                (bitp (lookup-equal v asg))
                (grp-fl-holds (grp-fl-or-gadget u v w p)))
           (equal (lookup-equal w asg)
                  (if (or (equal (lookup-equal u asg) 1)
                          (equal (lookup-equal v asg) 1))
                      1 0)))
  :do-not-induct t
  :use primep-of-base-prime
  :in-theory (e/d (grp-fl-or-gadget r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product bitp)
                  ((:e base-prime)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-div-gen
  (implies (and (primep p) (pfield::fep yy p) (pfield::fep num p) (pfield::fep den p)
                (not (equal den 0))
                (equal (pfield::mul yy den p) num))
           (equal (pfield::div num den p) yy))
  :use (:instance grp-fl-cancel (x (pfield::div num den p)) (y yy) (tt den))
  :enable pfield::div
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-yy-is-div
  (implies (and (fieldp xx) (fieldp yy)
                (equal (pfield::mul yy (grp-fl-den xx) (base-prime))
                       (grp-fl-num xx)))
           (equal (pfield::div (grp-fl-num xx) (grp-fl-den xx) (base-prime))
                  yy))
  :do-not-induct t
  :use (grp-fl-den-nonzero grp-fl-a-d-facts
        (:instance grp-fl-div-gen (p (base-prime))
                   (num (grp-fl-num xx)) (den (grp-fl-den xx))))
  :in-theory (e/d (fieldp) ((:e base-prime) pfield::div pfield::sub pfield::mul
                            ecurve::edwards-bls12-d ecurve::edwards-bls12-a))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defmacro grp-fl-yy-eq (xv yyv)
  `(equal (pfield::mul ,yyv (grp-fl-den (pfield::mul ,xv ,xv (base-prime))) (base-prime))
          (grp-fl-num (pfield::mul ,xv ,xv (base-prime)))))

(defruled grp-fl-groupp-ordinate-square
  (implies (and (fieldp xv) (fieldp yyv) (fieldp w)
                (grp-fl-yy-eq xv yyv)
                (groupp (ecurve::point-finite xv w)))
           (equal (pfield::mul w w (base-prime)) yyv))
  :use ((:instance grp-fl-on-curve-iff (x xv) (y w) (yy yyv))
        (:instance curve-edwards-bls12-pointp-when-groupp
                   (p (ecurve::point-finite xv w))))
  :in-theory nil)

(defruled grp-fl-in-group-square
  (implies (and (fieldp xv) (fieldp yyv)
                (grp-fl-yy-eq xv yyv)
                (curve-x-coordinate-in-group-p xv))
           (ecurve::pfield-squarep yyv (base-prime)))
  :use ((:instance grp-fl-groupp-ordinate-square
                   (w (curve-x-coordinate-in-group-witness xv)))
        (:instance fsa-squarep-when-root
                   (x yyv) (r (curve-x-coordinate-in-group-witness xv))))
  :in-theory '(curve-x-coordinate-in-group-p))

(defruled grp-fl-in-group-roots
  (implies (and (fieldp xv) (fieldp yyv) (fieldp r)
                (grp-fl-yy-eq xv yyv)
                (equal (pfield::mul r r (base-prime)) yyv)
                (curve-x-coordinate-in-group-p xv))
           (or (groupp (ecurve::point-finite xv r))
               (groupp (ecurve::point-finite xv (pfield::neg r (base-prime))))))
  :use ((:instance grp-fl-groupp-ordinate-square
                   (w (curve-x-coordinate-in-group-witness xv)))
        (:instance fb2-equal-squares-implies-equal-or-neg
                   (p (base-prime))
                   (a (curve-x-coordinate-in-group-witness xv)) (b r)))
  :in-theory '(curve-x-coordinate-in-group-p))

(defruled grp-fl-to-group-when-groupp
  (implies (and (fieldp x) (fieldp y)
                (groupp (ecurve::point-finite x y)))
           (and (curve-x-coordinate-in-group-p x)
                (equal (curve-x-coordinate-to-group x)
                       (ecurve::point-finite x y))))
  :use (grp-curve-x-coordinate-to-group-unique
        (:instance curve-x-coordinate-in-group-p-suff))
  :in-theory '(group-from-x-coordinate-funspec))

(defruled grp-fl-math
  :short "The flagged funspec in terms of the wire values the circuit
          computes: the two candidate ordinates @($\\pm r$), their
          @('is_in_group') bits and the non-square flag."
  (implies (and (fieldp xv) (fieldp yyv) (fieldp r) (bitp b1) (bitp b2)
                (grp-fl-yy-eq xv yyv)
                (equal nsq (if (ecurve::pfield-squarep yyv (base-prime)) 0 1))
                (or (equal nsq 1)
                    (and (equal (pfield::mul r r (base-prime)) yyv)
                         (equal b1 (if (groupp (ecurve::point-finite xv r)) 1 0))
                         (equal b2 (if (groupp (ecurve::point-finite
                                                xv (pfield::neg r (base-prime))))
                                       1 0))))
                (not (reserrp (group-from-x-coordinate-flagged-funspec xv))))
           (equal (group-from-x-coordinate-flagged-funspec xv)
                  (list (ecurve::point-finite
                         xv
                         (if (equal nsq 1) 0
                           (if (equal b1 1) r
                             (if (equal b2 1) (pfield::neg r (base-prime)) 0))))
                        (if (or (equal nsq 1) (and (equal b1 0) (equal b2 0))) 1 0))))
  :do-not-induct t
  :use ((:instance grp-fl-yy-is-div (xx (pfield::mul xv xv (base-prime))) (yy yyv))
        (:instance grp-fl-in-group-square)
        (:instance grp-fl-in-group-roots)
        (:instance grp-fl-to-group-when-groupp (x xv) (y r))
        (:instance grp-fl-to-group-when-groupp (x xv) (y (pfield::neg r (base-prime))))
        (:instance grp-fl-den-nonzero (xx (pfield::mul xv xv (base-prime))) (yy yyv)))
  :in-theory (e/d (group-from-x-coordinate-flagged-funspec bitp)
                  ((:e base-prime) pfield::div pfield::sub pfield::mul pfield::neg
                   ecurve::edwards-bls12-d ecurve::edwards-bls12-a
                   curve-x-coordinate-in-group-p curve-x-coordinate-to-group
                   groupp ecurve::pfield-squarep curve-raw-is-in-group))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-sqrt-decode
  (implies (fsa-sqrt-hyps)
           (and (equal (lookup-equal err asg)
                       (if (ecurve::pfield-squarep (lookup-equal x asg) p) 0 1))
                (implies (ecurve::pfield-squarep (lookup-equal x asg) p)
                         (equal (pfield::mul (lookup-equal root asg)
                                             (lookup-equal root asg) p)
                                (lookup-equal x asg)))))
  :do-not-induct t
  :use (fsa-square-roots-flagged-unordered-sound
        (:instance fb2-field-lesser-square-root-props (x (lookup-equal x asg))))
  :in-theory (e/d (field-square-roots-flagged-nondeterministic-funspec fieldp
                   r1cs::fep-of-lookup-equal)
                  ((:e base-prime) ecurve::pfield-squarep field-lesser-square-root
                   fb-field-square-roots-flagged-gadget))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-fl-iig-decode
  (implies (and (grp-iig-hyps
                 (r1cs::r1cs-constraints-holdp
                  (grp-is-in-group-gadget bx by steps mx rx my ry out p) asg p))
                (fieldp yyv)
                (grp-fl-yy-eq (lookup-equal bx asg) yyv)
                (equal (pfield::mul (lookup-equal by asg) (lookup-equal by asg) p) yyv))
           (equal (lookup-equal out asg)
                  (if (groupp (grp-pt bx by)) 1 0)))
  :use (grp-is-in-group-gadget-sound)
  :in-theory '(group-is-in-group-funspec))

(defruled grp-fl-pt-on-curve
  (implies (and (fieldp xv) (fieldp yv) (fieldp yyv)
                (grp-fl-yy-eq xv yyv)
                (equal (pfield::mul yv yv (base-prime)) yyv))
           (ecurve::edwards-bls12-pointp (ecurve::point-finite xv yv)))
  :use ((:instance grp-fl-on-curve-iff (x xv) (y yv) (yy yyv)))
  :in-theory nil)

(define grp-from-x-flagged-gadget
  ((x symbolp) (xx symbolp) (yy symbolp)
   (ss symbol-listp) (pow-rs symbol-listp) (one-m symbolp) (one-r symbolp)
   (square symbolp) (root symbolp) (zero-m symbolp) (zero-r symbolp)
   (nsq symbolp) (y2 symbolp)
   (steps1 true-listp) (mx1 symbolp) (rx1 symbolp) (my1 symbolp) (ry1 symbolp)
   (b1 symbolp)
   (steps2 true-listp) (mx2 symbolp) (rx2 symbolp) (my2 symbolp) (ry2 symbolp)
   (b2 symbolp)
   (t2 symbolp) (t1 symbolp) (y symbolp) (nb symbolp) (flag symbolp)
   (p primep))
  :verify-guards nil
  :short "Constraints of @('Group::from_x_coordinate_flagged').
          @('xx = x * x'); the witness @('yy') with
          @('yy * (d xx - 1) = a xx - 1'); the flagged square roots of
          @('yy') (@('root'), the linear combination @('-root') and the
          non-square bit @('nsq')); @('is_in_group') on @('(x, root)') and
          @('(x, y2)'); @('t2 = ternary(b2, y2, 0)'),
          @('t1 = ternary(b1, root, t2)'), @('y = ternary(nsq, 0, t1)');
          @('nb = !b1 & !b2'); @('flag = nsq | nb').  The wire @('y2')
          stands for the linear combination @('-root')."
  (append (crv-field-square-gadget x xx)
          (grp-fl-yy-gadget yy xx p)
          (fb-field-square-roots-flagged-gadget
           yy (field-modulus-minus-one-div-two) ss pow-rs
           one-m one-r square root zero-m zero-r nsq p)
          (grp-is-in-group-gadget x root steps1 mx1 rx1 my1 ry1 b1 p)
          (grp-is-in-group-gadget x y2 steps2 mx2 rx2 my2 ry2 b2 p)
          (grp-fl-ternary-zero2-gadget b2 y2 t2)
          (crv-field-ternary-gadget b1 root t2 t1 p)
          (grp-fl-ternary-zero1-gadget nsq t1 y p)
          (crv-and-not-gadget b1 b2 nb p)
          (grp-fl-or-gadget nsq nb flag p)))

(defmacro grp-fl-hyps (&rest more)
  `(and (grp-bound-all x xx yy one-m one-r square root zero-m zero-r nsq y2
                       mx1 rx1 my1 ry1 b1 mx2 rx2 my2 ry2 b2 t2 t1 y nb flag)
        (symbol-listp ss) (symbol-listp pow-rs)
        (equal (len ss) (field-pow-const-slen (field-modulus-minus-one-div-two)))
        (equal (len pow-rs) (field-pow-const-rlen (field-modulus-minus-one-div-two)))
        (consp pow-rs)
        (r1cs::valuation-binds-allp asg ss)
        (r1cs::valuation-binds-allp asg pow-rs)
        (grp-csteps-boundp steps1 asg)
        (grp-csteps-boundp steps2 asg)
        (equal (len steps1) (len (cdr (grp-r-bits))))
        (equal (len steps2) (len (cdr (grp-r-bits))))
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal (lookup-equal y2 asg) (pfield::neg (lookup-equal root asg) p))
        ,@more))

(defruled grp-fl-neg-square
  (implies (fieldp r)
           (equal (pfield::mul (pfield::neg r (base-prime)) (pfield::neg r (base-prime))
                               (base-prime))
                  (pfield::mul r r (base-prime))))
  :enable fieldp
  :disable ((:e base-prime))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defmacro grp-fl-gadget-call ()
  '(grp-from-x-flagged-gadget x xx yy ss pow-rs one-m one-r square root
                              zero-m zero-r nsq y2
                              steps1 mx1 rx1 my1 ry1 b1
                              steps2 mx2 rx2 my2 ry2 b2
                              t2 t1 y nb flag p))

(defruled grp-fl-pieces
  (implies (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p)
           (and (grp-fl-holds (crv-field-square-gadget x xx))
                (grp-fl-holds (grp-fl-yy-gadget yy xx p))
                (grp-fl-holds (fb-field-square-roots-flagged-gadget
                               yy (field-modulus-minus-one-div-two) ss pow-rs
                               one-m one-r square root zero-m zero-r nsq p))
                (grp-fl-holds (grp-is-in-group-gadget x root steps1 mx1 rx1 my1 ry1 b1 p))
                (grp-fl-holds (grp-is-in-group-gadget x y2 steps2 mx2 rx2 my2 ry2 b2 p))
                (grp-fl-holds (grp-fl-ternary-zero2-gadget b2 y2 t2))
                (grp-fl-holds (crv-field-ternary-gadget b1 root t2 t1 p))
                (grp-fl-holds (grp-fl-ternary-zero1-gadget nsq t1 y p))
                (grp-fl-holds (crv-and-not-gadget b1 b2 nb p))
                (grp-fl-holds (grp-fl-or-gadget nsq nb flag p))))
  :in-theory '(grp-from-x-flagged-gadget r1cs::r1cs-constraints-holdp-of-append))

(defruled grp-fl-front
  (implies (grp-fl-hyps (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p))
           (b* ((xv (lookup-equal x asg)) (yyv (lookup-equal yy asg))
                (r (lookup-equal root asg)))
             (and (grp-fl-yy-eq xv yyv)
                  (equal (lookup-equal nsq asg)
                         (if (ecurve::pfield-squarep yyv (base-prime)) 0 1))
                  (implies (ecurve::pfield-squarep yyv (base-prime))
                           (equal (pfield::mul r r (base-prime)) yyv)))))
  :do-not-induct t
  :use (grp-fl-pieces
        (:instance crv-field-square-gadget-to-mul (z xx))
        (:instance grp-fl-yy-gadget-to-eq)
        (:instance grp-fl-sqrt-decode (x yy) (e (field-modulus-minus-one-div-two))
                   (err nsq))
        primep-of-base-prime)
  :in-theory '((:e field-modulus-minus-one-div-two)))

(defruled grp-fl-bits
  (implies (grp-fl-hyps (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p))
           (and (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal b2 asg))))
  :do-not-induct t
  :use (grp-fl-pieces
        (:instance grp-is-in-group-gadget-out-bit (bx x) (by root) (steps steps1)
                   (mx mx1) (rx rx1) (my my1) (ry ry1) (out b1))
        (:instance grp-is-in-group-gadget-out-bit (bx x) (by y2) (steps steps2)
                   (mx mx2) (rx rx2) (my my2) (ry ry2) (out b2)))
  :in-theory nil)

(defruled grp-fl-square-bits
  (implies (and (grp-fl-hyps (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p))
                (ecurve::pfield-squarep (lookup-equal yy asg) (base-prime)))
           (b* ((xv (lookup-equal x asg)) (r (lookup-equal root asg)))
             (and (equal (lookup-equal b1 asg)
                         (if (groupp (ecurve::point-finite xv r)) 1 0))
                  (equal (lookup-equal b2 asg)
                         (if (groupp (ecurve::point-finite
                                      xv (pfield::neg r (base-prime))))
                             1 0)))))
  :do-not-induct t
  :use (grp-fl-pieces grp-fl-front
        (:instance grp-fl-pt-on-curve (xv (lookup-equal x asg))
                   (yv (lookup-equal root asg)) (yyv (lookup-equal yy asg)))
        (:instance grp-fl-pt-on-curve (xv (lookup-equal x asg))
                   (yv (lookup-equal y2 asg)) (yyv (lookup-equal yy asg)))
        (:instance grp-fl-neg-square (r (lookup-equal root asg)))
        (:instance grp-fl-iig-decode (bx x) (by root) (steps steps1)
                   (mx mx1) (rx rx1) (my my1) (ry ry1) (out b1)
                   (yyv (lookup-equal yy asg)))
        (:instance grp-fl-iig-decode (bx x) (by y2) (steps steps2)
                   (mx mx2) (rx rx2) (my my2) (ry ry2) (out b2)
                   (yyv (lookup-equal yy asg))))
  :in-theory '(fieldp r1cs::fep-of-lookup-equal))

(defruled grp-fl-select
  (implies (grp-fl-hyps (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p))
           (b* ((b1v (lookup-equal b1 asg)) (b2v (lookup-equal b2 asg))
                (nsqv (lookup-equal nsq asg)) (r (lookup-equal root asg)))
             (and (equal (lookup-equal y asg)
                         (if (equal nsqv 1) 0
                           (if (equal b1v 1) r
                             (if (equal b2v 1) (pfield::neg r (base-prime)) 0))))
                  (equal (lookup-equal flag asg)
                         (if (or (equal nsqv 1) (and (equal b1v 0) (equal b2v 0)))
                             1 0)))))
  :do-not-induct t
  :cases ((and (equal (lookup-equal b1 asg) 0) (equal (lookup-equal b2 asg) 0))
          (and (equal (lookup-equal b1 asg) 0) (equal (lookup-equal b2 asg) 1))
          (and (equal (lookup-equal b1 asg) 1) (equal (lookup-equal b2 asg) 0))
          (and (equal (lookup-equal b1 asg) 1) (equal (lookup-equal b2 asg) 1)))
  :use (grp-fl-pieces grp-fl-bits grp-fl-front
        (:instance grp-fl-ternary-zero2-to-eq (c b2) (a y2) (r t2))
        (:instance crv-field-ternary-gadget-sound (c b1) (a root) (b t2) (r t1))
        (:instance grp-fl-ternary-zero1-to-eq (c nsq) (b t1) (r y))
        (:instance crv-and-not-gadget-to-mul (rx b1) (ry b2) (out nb))
        (:instance grp-fl-or-to-eq (u nsq) (v nb) (w flag))
        primep-of-base-prime)
  :in-theory '(field-ternary-funspec bitp (:e pfield::sub) (:e pfield::mul)
               (:e bitp) eql (:e base-prime)))

(defruled grp-from-x-flagged-gadget-sound
  :short "R1CS-SOUND of @('Group::from_x_coordinate_flagged'), given that
          the funspec does not halt (on a non-square, @('is_in_group')
          evaluates the formulas on @($(x, 0)$), which halts on a zero
          denominator): the output point and flag are the funspec's."
  (implies (grp-fl-hyps
            (not (reserrp (group-from-x-coordinate-flagged-funspec
                           (lookup-equal x asg))))
            (r1cs::r1cs-constraints-holdp (grp-fl-gadget-call) asg p))
           (equal (group-from-x-coordinate-flagged-funspec (lookup-equal x asg))
                  (list (ecurve::point-finite (lookup-equal x asg) (lookup-equal y asg))
                        (lookup-equal flag asg))))
  :do-not-induct t
  :cases ((ecurve::pfield-squarep (lookup-equal yy asg) (base-prime)))
  :use (grp-fl-front grp-fl-bits grp-fl-square-bits grp-fl-select
        (:instance grp-fl-math (xv (lookup-equal x asg)) (yyv (lookup-equal yy asg))
                   (r (lookup-equal root asg))
                   (b1 (lookup-equal b1 asg)) (b2 (lookup-equal b2 asg))
                   (nsq (lookup-equal nsq asg))))
  :in-theory '(fieldp r1cs::fep-of-lookup-equal))
