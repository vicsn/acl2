; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::mul / mul_assign (circuit/types/group/src/mul.rs): output starts at
; the zero point; for each big-endian scalar bit, output = output.double()
; then output = ternary(bit, base + output, output).  The add gadget is
; called with the doubled point as `this` and the base as `that`.  With
; variable bits, the first iteration is only a ternary against the constant
; zero point (grp-mul-first-gadget); the rest are double/add/ternary steps
; (grp-mul-steps-gadget).  By induction the output is edwards-bls12-mul of
; the bit value.  The constant-bit variant (grp-cmul-*) is used by
; is_in_group: leading zeros emit nothing, the first one makes output = base,
; and each further bit emits a double and an add, with a constant ternary.

(in-package "ALEOVM")

(include-book "grp-from-x-coordinate")
(include-book "crv-add-complete")
(include-book "crv-sub-double")
(include-book "group-wire-sound")
(include-book "compute-key-from-private-key")

(define grp-mul-step-val (bit base acc)
  :verify-guards nil
  (b* ((dbl (ecurve::edwards-bls12-add acc acc))
       (sum (ecurve::edwards-bls12-add dbl base)))
    (if (equal bit 1) sum dbl)))

(defruled grp-mul-step-val-pointp
  (implies (and (ecurve::edwards-bls12-pointp base) (ecurve::edwards-bls12-pointp acc))
           (ecurve::edwards-bls12-pointp (grp-mul-step-val bit base acc)))
  :enable grp-mul-step-val)

(define grp-mul-fold ((bits bit-listp) base acc)
  :verify-guards nil
  (if (endp bits)
      acc
    (grp-mul-fold (cdr bits) base (grp-mul-step-val (car bits) base acc))))

(define grp-mul-fold-val ((bits bit-listp) (k natp))
  :verify-guards nil
  (if (endp bits)
      k
    (grp-mul-fold-val (cdr bits) (+ k k (if (equal (car bits) 1) 1 0)))))

(defruled grp-edwards-mul-add
  (implies (and (ecurve::edwards-bls12-pointp b) (natp i) (natp j))
           (equal (ecurve::edwards-bls12-add (ecurve::edwards-bls12-mul i b)
                                             (ecurve::edwards-bls12-mul j b))
                  (ecurve::edwards-bls12-mul (+ i j) b)))
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-mul ecurve::edwards-bls12-pointp)
  :use (:instance ecurve::twisted-edwards-mul-of-scalar-addition
                  (ecurve::scalar1 i) (ecurve::scalar2 j) (ecurve::point b)
                  (ecurve::curve (ecurve::edwards-bls12-curve))))

(defruled grp-edwards-mul-1
  (implies (ecurve::edwards-bls12-pointp b)
           (equal (ecurve::edwards-bls12-mul 1 b) b))
  :enable (ecurve::edwards-bls12-mul ecurve::edwards-bls12-pointp))

(defruled grp-mul-fold-is-mul
  (implies (and (ecurve::edwards-bls12-pointp b) (bit-listp bits) (natp k))
           (equal (grp-mul-fold bits b (ecurve::edwards-bls12-mul k b))
                  (ecurve::edwards-bls12-mul (grp-mul-fold-val bits k) b)))
  :induct (grp-mul-fold-val bits k)
  :enable (grp-mul-fold grp-mul-fold-val)
  :hints (("Subgoal *1/2"
           :use ((:instance grp-edwards-mul-add (i k) (j k))
                 (:instance grp-edwards-mul-add (i (+ k k)) (j 1))
                 grp-edwards-mul-1)
           :expand ((grp-mul-fold bits b (ecurve::edwards-bls12-mul k b)))
           :in-theory (e/d (grp-mul-fold grp-mul-fold-val bitp grp-mul-step-val)
                           (ecurve::edwards-bls12-mul)))))

(defruled grp-mul-fold-val-is-bebits
  (implies (and (bit-listp bits) (natp k))
           (equal (grp-mul-fold-val bits k)
                  (+ (* k (expt 2 (len bits))) (acl2::bebits=>nat bits))))
  :induct (grp-mul-fold-val bits k)
  :enable (grp-mul-fold-val acl2::bebits=>nat acl2::bendian=>nat-of-cons
           bitp)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))


(define grp-syms-boundp ((syms) (asg))
  :verify-guards nil
  (if (atom syms)
      t
    (and (symbolp (car syms))
         (r1cs::valuation-bindsp asg (car syms))
         (grp-syms-boundp (cdr syms) asg))))

(defruled grp-syms-boundp-nth
  (implies (and (grp-syms-boundp syms asg) (< (nfix i) (len syms)))
           (and (symbolp (nth i syms))
                (r1cs::valuation-bindsp asg (nth i syms))))
  :induct (nth i syms)
  :enable (grp-syms-boundp nth))

(defmacro grp-pt (x y)
  `(ecurve::point-finite (lookup-equal ,x asg) (lookup-equal ,y asg)))

(defruled grp-point-coords
  (implies (and (fieldp x) (fieldp y))
           (and (equal (ecurve::point-finite->x (ecurve::point-finite x y)) x)
                (equal (ecurve::point-finite->y (ecurve::point-finite x y)) y)))
  :enable (fieldp pfield::fep))

(defmacro grp-step-body (bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
  `(append (crv-group-double-gadget ,ax ,ay ,dxy ,dx2 ,dy2 ,dx ,dy p)
           (crv-group-add-gadget ,dx ,dy ,bx ,by ,u ,v0 ,v1 ,v01 ,sx ,sy p)
           (crv-group-ternary-gadget ,bit ,sx ,sy ,dx ,dy ,ox ,oy p)))

(defmacro grp-bound-all (&rest syms)
  (if (endp syms) t
    `(and (symbolp ,(car syms)) (r1cs::valuation-bindsp asg ,(car syms))
          (grp-bound-all ,@(cdr syms)))))

(defruled grp-mul-step-body-sound
  (implies (and (grp-bound-all bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (bitp (lookup-equal bit asg))
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-step-body bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
                 asg p))
           (b* ((a (grp-pt ax ay))
                (b (grp-pt bx by))
                (dbl (ecurve::edwards-bls12-add a a))
                (sum (ecurve::edwards-bls12-add dbl b)))
             (and (equal (grp-pt dx dy) dbl)
                  (equal (grp-pt sx sy) sum)
                  (equal (grp-pt ox oy)
                         (if (equal (lookup-equal bit asg) 1) sum dbl)))))
  :do-not-induct t
  :use ((:instance grp-point-coords (x (lookup-equal ax asg)) (y (lookup-equal ay asg)))
        (:instance grp-point-coords (x (lookup-equal bx asg)) (y (lookup-equal by asg)))
        (:instance grp-point-coords (x (lookup-equal dx asg)) (y (lookup-equal dy asg)))
        (:instance grp-point-coords (x (lookup-equal sx asg)) (y (lookup-equal sy asg)))
        (:instance crv-group-double-gadget-sound
                   (x ax) (y ay) (xy dxy) (x2 dx2) (y2 dy2)
                   (x3 dx) (y3 dy) (pt (grp-pt ax ay)))
        (:instance crv-group-add-gadget-sound
                   (x1 dx) (y1 dy) (x2 bx) (y2 by)
                   (x3 sx) (y3 sy)
                   (p1 (grp-pt dx dy)) (p2 (grp-pt bx by)))
        (:instance crv-group-ternary-gadget-sound
                   (c bit) (x1 sx) (y1 sy) (x2 dx) (y2 dy)
                   (rx ox) (ry oy)
                   (p1 (grp-pt sx sy))
                   (p2 (grp-pt dx dy)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (grp-pt ax ay)) (ecurve::point2 (grp-pt ax ay)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (grp-pt dx dy)) (ecurve::point2 (grp-pt bx by))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               group-double-funspec group-add-funspec group-ternary-funspec
               fieldp r1cs::fep-of-lookup-equal primep-of-base-prime))

(define grp-mul-step-gadget ((bit symbolp) (bx symbolp) (by symbolp)
                             (ax symbolp) (ay symbolp)
                             (w true-listp) (p primep))
  :verify-guards nil
  (grp-step-body bit bx by ax ay (nth 0 w) (nth 1 w) (nth 2 w) (nth 3 w) (nth 4 w)
                 (nth 5 w) (nth 6 w) (nth 7 w) (nth 8 w) (nth 9 w) (nth 10 w)
                 (nth 11 w) (nth 12 w)))

(defruled grp-mul-step-gadget-sound
  (implies (and (symbolp bit) (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal (len w) 13)
                (grp-syms-boundp w asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (bitp (lookup-equal bit asg))
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-step-gadget bit bx by ax ay w p) asg p))
           (equal (grp-pt (nth 11 w) (nth 12 w))
                  (grp-mul-step-val (lookup-equal bit asg) (grp-pt bx by) (grp-pt ax ay))))
  :do-not-induct t
  :use ((:instance grp-mul-step-body-sound
                   (dxy (nth 0 w)) (dx2 (nth 1 w)) (dy2 (nth 2 w)) (dx (nth 3 w))
                   (dy (nth 4 w)) (u (nth 5 w)) (v0 (nth 6 w)) (v1 (nth 7 w))
                   (v01 (nth 8 w)) (sx (nth 9 w)) (sy (nth 10 w)) (ox (nth 11 w))
                   (oy (nth 12 w)))
        (:instance grp-syms-boundp-nth (syms w) (i 0))
        (:instance grp-syms-boundp-nth (syms w) (i 1))
        (:instance grp-syms-boundp-nth (syms w) (i 2))
        (:instance grp-syms-boundp-nth (syms w) (i 3))
        (:instance grp-syms-boundp-nth (syms w) (i 4))
        (:instance grp-syms-boundp-nth (syms w) (i 5))
        (:instance grp-syms-boundp-nth (syms w) (i 6))
        (:instance grp-syms-boundp-nth (syms w) (i 7))
        (:instance grp-syms-boundp-nth (syms w) (i 8))
        (:instance grp-syms-boundp-nth (syms w) (i 9))
        (:instance grp-syms-boundp-nth (syms w) (i 10))
        (:instance grp-syms-boundp-nth (syms w) (i 11))
        (:instance grp-syms-boundp-nth (syms w) (i 12)))
  :in-theory '(grp-mul-step-gadget grp-mul-step-val (:e <) (:e nfix)))

(define grp-mul-steps-gadget ((bits symbol-listp) (steps true-listp)
                              (bx symbolp) (by symbolp)
                              (ax symbolp) (ay symbolp) (p primep))
  :verify-guards nil
  (if (or (atom bits) (atom steps))
      nil
    (b* ((w (car steps)))
      (append (grp-mul-step-gadget (car bits) bx by ax ay w p)
              (grp-mul-steps-gadget (cdr bits) (cdr steps) bx by
                                    (nth 11 w) (nth 12 w) p)))))

(define grp-mul-steps-out ((bits symbol-listp) (steps true-listp)
                           (ax symbolp) (ay symbolp))
  :verify-guards nil
  (if (or (atom bits) (atom steps))
      (list ax ay)
    (grp-mul-steps-out (cdr bits) (cdr steps)
                       (nth 11 (car steps)) (nth 12 (car steps)))))

(define grp-steps-boundp (steps asg)
  :verify-guards nil
  (if (atom steps)
      t
    (and (equal (len (car steps)) 13)
         (grp-syms-boundp (car steps) asg)
         (grp-steps-boundp (cdr steps) asg))))

(define grp-bits-ok (bits asg)
  :verify-guards nil
  (if (atom bits)
      t
    (and (symbolp (car bits))
         (r1cs::valuation-bindsp asg (car bits))
         (bitp (lookup-equal (car bits) asg))
         (grp-bits-ok (cdr bits) asg))))

(define grp-bit-vals (bits asg)
  :verify-guards nil
  (if (atom bits)
      nil
    (cons (lookup-equal (car bits) asg) (grp-bit-vals (cdr bits) asg))))

(defun grp-steps-ind (bits steps ax ay)
  (if (or (atom bits) (atom steps))
      (list ax ay)
    (grp-steps-ind (cdr bits) (cdr steps) (nth 11 (car steps)) (nth 12 (car steps)))))

(defruled grp-mul-steps-gadget-sound
  (implies (and (grp-bits-ok bits asg)
                (grp-steps-boundp steps asg)
                (equal (len steps) (len bits))
                (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-steps-gadget bits steps bx by ax ay p) asg p))
           (b* ((out (grp-mul-steps-out bits steps ax ay)))
             (equal (grp-pt (first out) (second out))
                    (grp-mul-fold (grp-bit-vals bits asg) (grp-pt bx by) (grp-pt ax ay)))))
  :induct (grp-steps-ind bits steps ax ay)
  :hints (("Subgoal *1/2"
           :use ((:instance grp-mul-step-gadget-sound (bit (car bits)) (w (car steps)))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 11))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 12))
                 (:instance grp-mul-step-val-pointp
                            (bit (lookup-equal (car bits) asg))
                            (base (grp-pt bx by)) (acc (grp-pt ax ay))))
           :expand ((:free (p) (grp-mul-steps-gadget bits steps bx by ax ay p))
                    (grp-mul-steps-out bits steps ax ay)
                    (grp-bit-vals bits asg)
                    (grp-bits-ok bits asg)
                    (grp-steps-boundp steps asg)
                    (len bits) (len steps)
                    (:free (b a) (grp-mul-fold (cons (lookup-equal (car bits) asg)
                                                     (grp-bit-vals (cdr bits) asg))
                                               b a)))
           :in-theory '(r1cs::r1cs-constraints-holdp-of-append
                        car-cons cdr-cons (:e <) (:e nfix) endp atom
                        acl2::fix (:e acl2::fix) (:t len)))
          ("Subgoal *1/1"
           :expand ((grp-mul-steps-out bits steps ax ay)
                    (grp-bit-vals bits asg)
                    (grp-mul-fold nil (grp-pt bx by) (grp-pt ax ay))
                    (len bits) (len steps))
           :in-theory (enable grp-mul-fold))))

(define grp-mul-first-gadget ((bit symbolp) (bx symbolp) (by symbolp)
                              (ox symbolp) (oy symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "First iteration with a variable bit: @('double(0)') and
          @('base + 0') fold to the zero constant and @('base'), so only
          @('Group::ternary(bit, base, 0)') is emitted, with constant
          second operands 0 (abscissa) and 1 (ordinate)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 bit))
         :b (list (list 1 bx))
         :c (list (list 1 ox)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 bit))
         :b (list (list 1 by) (list (- p 1) 1))
         :c (list (list 1 oy) (list (- p 1) 1)))))

(defruled grp-mul-first-gadget-sound
  (implies (and (symbolp bit) (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg bx)
                (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ox)
                (r1cs::valuation-bindsp asg oy)
                (bitp (lookup-equal bit asg))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-first-gadget bit bx by ox oy p) asg p))
           (equal (grp-pt ox oy)
                  (if (equal (lookup-equal bit asg) 1)
                      (grp-pt bx by)
                    (ecurve::twisted-edwards-zero))))
  :do-not-induct t
  :enable (grp-mul-first-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           bitp
           ecurve::twisted-edwards-zero
           r1cs::fep-of-lookup-equal
           primep-of-base-prime)
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system) (include-book "kestrel/prime-fields/equal-of-add-cancel-bind-free" :dir :system)))

(define grp-mul-gadget ((bits symbol-listp) (ox symbolp) (oy symbolp)
                        (steps true-listp)
                        (bx symbolp) (by symbolp) (p primep))
  :verify-guards nil
  :short "@('Group::mul_assign') on variable bits: the first iteration
          (ternary against the constant zero point, output wires @('ox'),
          @('oy')), then one double/add/ternary step per remaining bit."
  (append (grp-mul-first-gadget (car bits) bx by ox oy p)
          (grp-mul-steps-gadget (cdr bits) steps bx by ox oy p)))

(define grp-mul-out ((bits symbol-listp) (ox symbolp) (oy symbolp)
                     (steps true-listp))
  :verify-guards nil
  (grp-mul-steps-out (cdr bits) steps ox oy))

(defruled grp-bit-listp-of-bit-vals
  (implies (grp-bits-ok bits asg)
           (bit-listp (grp-bit-vals bits asg)))
  :induct (len bits)
  :enable (grp-bits-ok grp-bit-vals))

(defrule grp-len-of-bit-vals
  (equal (len (grp-bit-vals bits asg)) (len bits))
  :induct (len bits)
  :enable grp-bit-vals)

(defruled grp-zero-is-mul-0
  (equal (ecurve::edwards-bls12-mul 0 b) (ecurve::twisted-edwards-zero))
  :enable ecurve::edwards-bls12-mul)

(defruled grp-twisted-zero-pointp
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero)))

(defruled grp-mul-gadget-sound
  (implies (and (consp bits)
                (grp-bits-ok bits asg)
                (grp-steps-boundp steps asg)
                (equal (len steps) (len (cdr bits)))
                (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-gadget bits ox oy steps bx by p) asg p))
           (b* ((out (grp-mul-out bits ox oy steps)))
             (equal (grp-pt (first out) (second out))
                    (ecurve::edwards-bls12-mul
                     (acl2::bebits=>nat (grp-bit-vals bits asg))
                     (grp-pt bx by)))))
  :do-not-induct t
  :use ((:instance grp-mul-first-gadget-sound (bit (car bits)))
        (:instance grp-mul-steps-gadget-sound
                   (bits (cdr bits)) (ax ox) (ay oy))
        (:instance grp-mul-fold-is-mul
                   (bits (grp-bit-vals (cdr bits) asg))
                   (b (grp-pt bx by))
                   (k (lookup-equal (car bits) asg)))
        (:instance grp-mul-fold-val-is-bebits
                   (bits (grp-bit-vals (cdr bits) asg))
                   (k (lookup-equal (car bits) asg)))
        (:instance grp-bit-listp-of-bit-vals (bits (cdr bits)))
        (:instance acl2::bendian=>nat-of-cons
                   (acl2::base 2)
                   (acl2::hidigit (lookup-equal (car bits) asg))
                   (acl2::lodigits (grp-bit-vals (cdr bits) asg)))
        (:instance grp-zero-is-mul-0 (b (grp-pt bx by)))
        (:instance grp-edwards-mul-1 (b (grp-pt bx by)))
        grp-twisted-zero-pointp)
  :expand ((grp-bits-ok bits asg) (grp-bit-vals bits asg))
  :in-theory (e/d (grp-mul-gadget grp-mul-out bitp acl2::bebits=>nat
                   r1cs::r1cs-constraints-holdp-of-append
                   grp-len-of-bit-vals)
                  (grp-mul-fold-is-mul grp-mul-fold-val-is-bebits
                   ecurve::edwards-bls12-mul)))
(defmacro grp-lk (w) `(lookup-equal ,w asg))

(defmacro grp-step-canon (bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
  `(b* ((q (base-prime))
        (a (grp-pt ,ax ,ay))
        (b (grp-pt ,bx ,by))
        (dbl (ecurve::edwards-bls12-add a a))
        (sum (ecurve::edwards-bls12-add dbl b)))
     (and (equal (grp-lk ,dxy) (pfield::mul (grp-lk ,ax) (grp-lk ,ay) q))
          (equal (grp-lk ,dx2) (pfield::mul (grp-lk ,ax) (grp-lk ,ax) q))
          (equal (grp-lk ,dy2) (pfield::mul (grp-lk ,ay) (grp-lk ,ay) q))
          (equal (grp-lk ,dx) (ecurve::point-finite->x dbl))
          (equal (grp-lk ,dy) (ecurve::point-finite->y dbl))
          (equal (grp-lk ,u) (pfield::mul (pfield::add (grp-lk ,dx) (grp-lk ,dy) q)
                                      (pfield::add (grp-lk ,bx) (grp-lk ,by) q) q))
          (equal (grp-lk ,v0) (pfield::mul (grp-lk ,dx) (grp-lk ,by) q))
          (equal (grp-lk ,v1) (pfield::mul (grp-lk ,bx) (grp-lk ,dy) q))
          (equal (grp-lk ,v01) (pfield::mul (grp-lk ,v0) (grp-lk ,v1) q))
          (equal (grp-lk ,sx) (ecurve::point-finite->x sum))
          (equal (grp-lk ,sy) (ecurve::point-finite->y sum))
          (equal (grp-lk ,ox) (field-ternary-funspec (grp-lk ,bit) (grp-lk ,sx) (grp-lk ,dx)))
          (equal (grp-lk ,oy) (field-ternary-funspec (grp-lk ,bit) (grp-lk ,sy) (grp-lk ,dy))))))

(defruled grp-mul-step-body-complete
  (implies (and (grp-bound-all bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (bitp (lookup-equal bit asg))
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-step-canon bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy))
           (and (r1cs::r1cs-constraints-holdp
                 (grp-step-body bit bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy ox oy)
                 asg p)
                (equal (grp-pt ox oy)
                       (grp-mul-step-val (lookup-equal bit asg) (grp-pt bx by) (grp-pt ax ay)))))
  :do-not-induct t
  :use ((:instance grp-point-coords (x (lookup-equal ax asg)) (y (lookup-equal ay asg)))
        (:instance grp-point-coords (x (lookup-equal bx asg)) (y (lookup-equal by asg)))
        (:instance crv-fep-of-edwards-bls12-coords (p (base-prime))
                   (pt (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))))
        (:instance crv-fep-of-edwards-bls12-coords (p (base-prime))
                   (pt (ecurve::edwards-bls12-add
                        (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))
                        (grp-pt bx by))))
        (:instance crv-group-double-gadget-complete
                   (x ax) (y ay) (xy dxy) (x2 dx2) (y2 dy2)
                   (x3 dx) (y3 dy) (pt (grp-pt ax ay)))
        (:instance crv-group-add-gadget-complete
                   (x1 dx) (y1 dy) (x2 bx) (y2 by)
                   (x3 sx) (y3 sy)
                   (p1 (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay)))
                   (p2 (grp-pt bx by)))
        (:instance crv-group-ternary-gadget-complete
                   (c bit) (x1 sx) (y1 sy) (x2 dx) (y2 dy)
                   (rx ox) (ry oy)
                   (p1 (ecurve::edwards-bls12-add
                        (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))
                        (grp-pt bx by)))
                   (p2 (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (grp-pt ax ay)) (ecurve::point2 (grp-pt ax ay)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay)))
                   (ecurve::point2 (grp-pt bx by))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               group-double-funspec group-add-funspec group-ternary-funspec
               grp-mul-step-val
               fieldp r1cs::fep-of-lookup-equal primep-of-base-prime))

(define grp-step-canonp (bit bx by ax ay w asg)
  :verify-guards nil
  :short "The canonical witnesses of one step: the snarkVM products,
          the doubling and sum coordinates, and the selected point."
  (grp-step-canon bit bx by ax ay (nth 0 w) (nth 1 w) (nth 2 w) (nth 3 w) (nth 4 w)
                  (nth 5 w) (nth 6 w) (nth 7 w) (nth 8 w) (nth 9 w) (nth 10 w)
                  (nth 11 w) (nth 12 w)))

(defruled grp-mul-step-gadget-complete
  (implies (and (symbolp bit) (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal (len w) 13)
                (grp-syms-boundp w asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (bitp (lookup-equal bit asg))
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-step-canonp bit bx by ax ay w asg))
           (and (r1cs::r1cs-constraints-holdp
                 (grp-mul-step-gadget bit bx by ax ay w p) asg p)
                (equal (grp-pt (nth 11 w) (nth 12 w))
                       (grp-mul-step-val (lookup-equal bit asg) (grp-pt bx by) (grp-pt ax ay)))))
  :do-not-induct t
  :use ((:instance grp-mul-step-body-complete
                   (dxy (nth 0 w)) (dx2 (nth 1 w)) (dy2 (nth 2 w)) (dx (nth 3 w))
                   (dy (nth 4 w)) (u (nth 5 w)) (v0 (nth 6 w)) (v1 (nth 7 w))
                   (v01 (nth 8 w)) (sx (nth 9 w)) (sy (nth 10 w)) (ox (nth 11 w))
                   (oy (nth 12 w)))
        (:instance grp-syms-boundp-nth (syms w) (i 0))
        (:instance grp-syms-boundp-nth (syms w) (i 1))
        (:instance grp-syms-boundp-nth (syms w) (i 2))
        (:instance grp-syms-boundp-nth (syms w) (i 3))
        (:instance grp-syms-boundp-nth (syms w) (i 4))
        (:instance grp-syms-boundp-nth (syms w) (i 5))
        (:instance grp-syms-boundp-nth (syms w) (i 6))
        (:instance grp-syms-boundp-nth (syms w) (i 7))
        (:instance grp-syms-boundp-nth (syms w) (i 8))
        (:instance grp-syms-boundp-nth (syms w) (i 9))
        (:instance grp-syms-boundp-nth (syms w) (i 10))
        (:instance grp-syms-boundp-nth (syms w) (i 11))
        (:instance grp-syms-boundp-nth (syms w) (i 12)))
  :in-theory '(grp-mul-step-gadget grp-step-canonp (:e <) (:e nfix)))

(define grp-steps-canonp (bits steps bx by ax ay asg)
  :verify-guards nil
  (if (or (atom bits) (atom steps))
      t
    (and (grp-step-canonp (car bits) bx by ax ay (car steps) asg)
         (grp-steps-canonp (cdr bits) (cdr steps) bx by
                           (nth 11 (car steps)) (nth 12 (car steps)) asg))))

(defruled grp-mul-steps-gadget-complete
  (implies (and (grp-bits-ok bits asg)
                (grp-steps-boundp steps asg)
                (equal (len steps) (len bits))
                (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-steps-canonp bits steps bx by ax ay asg))
           (r1cs::r1cs-constraints-holdp
            (grp-mul-steps-gadget bits steps bx by ax ay p) asg p))
  :induct (grp-steps-ind bits steps ax ay)
  :hints (("Subgoal *1/2"
           :use ((:instance grp-mul-step-gadget-complete (bit (car bits)) (w (car steps)))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 11))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 12))
                 (:instance grp-mul-step-val-pointp
                            (bit (lookup-equal (car bits) asg))
                            (base (grp-pt bx by)) (acc (grp-pt ax ay))))
           :expand ((:free (p) (grp-mul-steps-gadget bits steps bx by ax ay p))
                    (grp-steps-canonp bits steps bx by ax ay asg)
                    (grp-bits-ok bits asg)
                    (grp-steps-boundp steps asg)
                    (len bits) (len steps))
           :in-theory '(r1cs::r1cs-constraints-holdp-of-append
                        car-cons cdr-cons (:e <) (:e nfix) endp atom
                        acl2::fix (:e acl2::fix) (:t len)))
          ("Subgoal *1/1"
           :expand ((:free (p) (grp-mul-steps-gadget bits steps bx by ax ay p)))
           :in-theory (enable r1cs::r1cs-constraints-holdp))))

(defruled grp-mul-first-gadget-complete
  (implies (and (symbolp bit) (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg bx)
                (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ox)
                (r1cs::valuation-bindsp asg oy)
                (bitp (lookup-equal bit asg))
                (equal (lookup-equal ox asg)
                       (if (equal (lookup-equal bit asg) 1) (lookup-equal bx asg) 0))
                (equal (lookup-equal oy asg)
                       (if (equal (lookup-equal bit asg) 1) (lookup-equal by asg) 1)))
           (r1cs::r1cs-constraints-holdp
            (grp-mul-first-gadget bit bx by ox oy p) asg p))
  :do-not-induct t
  :enable (grp-mul-first-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           bitp
           r1cs::fep-of-lookup-equal
           primep-of-base-prime)
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled grp-mul-gadget-complete
  :short "R1CS-COMPLETE of variable-bit @('Group::mul_assign'): the
          canonical first-iteration selection and canonical step witnesses
          satisfy the constraints."
  (implies (and (consp bits)
                (grp-bits-ok bits asg)
                (grp-steps-boundp steps asg)
                (equal (len steps) (len (cdr bits)))
                (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (equal (lookup-equal ox asg)
                       (if (equal (lookup-equal (car bits) asg) 1) (lookup-equal bx asg) 0))
                (equal (lookup-equal oy asg)
                       (if (equal (lookup-equal (car bits) asg) 1) (lookup-equal by asg) 1))
                (grp-steps-canonp (cdr bits) steps bx by ox oy asg))
           (r1cs::r1cs-constraints-holdp
            (grp-mul-gadget bits ox oy steps bx by p) asg p))
  :do-not-induct t
  :use ((:instance grp-mul-first-gadget-complete (bit (car bits)))
        (:instance grp-mul-first-gadget-sound (bit (car bits)))
        (:instance grp-mul-steps-gadget-complete
                   (bits (cdr bits)) (ax ox) (ay oy))
        grp-twisted-zero-pointp)
  :expand ((grp-bits-ok bits asg))
  :in-theory '(grp-mul-gadget r1cs::r1cs-constraints-holdp-of-append))

(defruled grp-mul-gadget-sound-funspec
  :short "R1CS-SOUND of @('Group::mul') / @('Group::mul_assign') for a
          variable scalar: if the bit wires are @('Scalar::to_bits_be') of
          @('s') (the reverse of @(tsee scalar-bits-le)), the output is
          @(tsee group-mul-funspec)."
  (implies (and (consp bits)
                (grp-bits-ok bits asg)
                (grp-steps-boundp steps asg)
                (equal (len steps) (len (cdr bits)))
                (symbolp bx) (symbolp by) (symbolp ox) (symbolp oy)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (scalarp s)
                (equal (grp-bit-vals bits asg) (rev (scalar-bits-le s)))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-gadget bits ox oy steps bx by p) asg p))
           (b* ((out (grp-mul-out bits ox oy steps)))
             (and (equal (grp-pt (first out) (second out))
                         (group-mul-funspec (grp-pt bx by) s))
                  (equal (grp-pt (first out) (second out))
                         (group-mul-assign-funspec (grp-pt bx by) s)))))
  :do-not-induct t
  :use (grp-mul-gadget-sound
        lebits=>nat-of-scalar-bits-le
        (:instance acl2::bendian=>nat-of-rev
                   (acl2::base 2) (acl2::digits (scalar-bits-le s))))
  :in-theory '(group-mul-funspec group-mul-assign-funspec
               acl2::bebits=>nat acl2::lebits=>nat lnfix nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constant bits (used by is_in_group): after the leading zeros and the
;; first 1, each bit emits a double and an add; the constant ternary selects
;; the sum or the double without constraints.

(defmacro grp-cstep-body (bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
  `(append (crv-group-double-gadget ,ax ,ay ,dxy ,dx2 ,dy2 ,dx ,dy p)
           (crv-group-add-gadget ,dx ,dy ,bx ,by ,u ,v0 ,v1 ,v01 ,sx ,sy p)))

(defruled grp-cmul-step-body-sound
  (implies (and (grp-bound-all bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-cstep-body bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
                 asg p))
           (b* ((a (grp-pt ax ay))
                (b (grp-pt bx by))
                (dbl (ecurve::edwards-bls12-add a a))
                (sum (ecurve::edwards-bls12-add dbl b)))
             (and (equal (grp-pt dx dy) dbl)
                  (equal (grp-pt sx sy) sum))))
  :do-not-induct t
  :use ((:instance grp-point-coords (x (lookup-equal ax asg)) (y (lookup-equal ay asg)))
        (:instance grp-point-coords (x (lookup-equal bx asg)) (y (lookup-equal by asg)))
        (:instance grp-point-coords (x (lookup-equal dx asg)) (y (lookup-equal dy asg)))
        (:instance crv-group-double-gadget-sound
                   (x ax) (y ay) (xy dxy) (x2 dx2) (y2 dy2)
                   (x3 dx) (y3 dy) (pt (grp-pt ax ay)))
        (:instance crv-group-add-gadget-sound
                   (x1 dx) (y1 dy) (x2 bx) (y2 by)
                   (x3 sx) (y3 sy)
                   (p1 (grp-pt dx dy)) (p2 (grp-pt bx by)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (grp-pt ax ay)) (ecurve::point2 (grp-pt ax ay))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               group-double-funspec group-add-funspec
               fieldp r1cs::fep-of-lookup-equal primep-of-base-prime))

(defmacro grp-cstep-canon (bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
  `(b* ((q (base-prime))
        (a (grp-pt ,ax ,ay))
        (b (grp-pt ,bx ,by))
        (dbl (ecurve::edwards-bls12-add a a))
        (sum (ecurve::edwards-bls12-add dbl b)))
     (and (equal (grp-lk ,dxy) (pfield::mul (grp-lk ,ax) (grp-lk ,ay) q))
          (equal (grp-lk ,dx2) (pfield::mul (grp-lk ,ax) (grp-lk ,ax) q))
          (equal (grp-lk ,dy2) (pfield::mul (grp-lk ,ay) (grp-lk ,ay) q))
          (equal (grp-lk ,dx) (ecurve::point-finite->x dbl))
          (equal (grp-lk ,dy) (ecurve::point-finite->y dbl))
          (equal (grp-lk ,u) (pfield::mul (pfield::add (grp-lk ,dx) (grp-lk ,dy) q)
                                          (pfield::add (grp-lk ,bx) (grp-lk ,by) q) q))
          (equal (grp-lk ,v0) (pfield::mul (grp-lk ,dx) (grp-lk ,by) q))
          (equal (grp-lk ,v1) (pfield::mul (grp-lk ,bx) (grp-lk ,dy) q))
          (equal (grp-lk ,v01) (pfield::mul (grp-lk ,v0) (grp-lk ,v1) q))
          (equal (grp-lk ,sx) (ecurve::point-finite->x sum))
          (equal (grp-lk ,sy) (ecurve::point-finite->y sum)))))

(defruled grp-cmul-step-body-complete
  (implies (and (grp-bound-all bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-cstep-canon bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy))
           (and (r1cs::r1cs-constraints-holdp
                 (grp-cstep-body bx by ax ay dxy dx2 dy2 dx dy u v0 v1 v01 sx sy)
                 asg p)
                (equal (grp-pt dx dy)
                       (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay)))
                (equal (grp-pt sx sy)
                       (ecurve::edwards-bls12-add
                        (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))
                        (grp-pt bx by)))))
  :do-not-induct t
  :use ((:instance grp-point-coords (x (lookup-equal ax asg)) (y (lookup-equal ay asg)))
        (:instance grp-point-coords (x (lookup-equal bx asg)) (y (lookup-equal by asg)))
        (:instance crv-fep-of-edwards-bls12-coords (p (base-prime))
                   (pt (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))))
        (:instance crv-fep-of-edwards-bls12-coords (p (base-prime))
                   (pt (ecurve::edwards-bls12-add
                        (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay))
                        (grp-pt bx by))))
        (:instance crv-group-double-gadget-complete
                   (x ax) (y ay) (xy dxy) (x2 dx2) (y2 dy2)
                   (x3 dx) (y3 dy) (pt (grp-pt ax ay)))
        (:instance crv-group-double-gadget-sound
                   (x ax) (y ay) (xy dxy) (x2 dx2) (y2 dy2)
                   (x3 dx) (y3 dy) (pt (grp-pt ax ay)))
        (:instance crv-group-add-gadget-complete
                   (x1 dx) (y1 dy) (x2 bx) (y2 by)
                   (x3 sx) (y3 sy)
                   (p1 (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay)))
                   (p2 (grp-pt bx by)))
        (:instance crv-group-add-gadget-sound
                   (x1 dx) (y1 dy) (x2 bx) (y2 by)
                   (x3 sx) (y3 sy)
                   (p1 (grp-pt dx dy)) (p2 (grp-pt bx by)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (grp-pt ax ay)) (ecurve::point2 (grp-pt ax ay)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (ecurve::edwards-bls12-add (grp-pt ax ay) (grp-pt ax ay)))
                   (ecurve::point2 (grp-pt bx by))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               group-double-funspec group-add-funspec
               fieldp r1cs::fep-of-lookup-equal primep-of-base-prime))

(define grp-cmul-step-gadget ((bx symbolp) (by symbolp) (ax symbolp) (ay symbolp)
                              (w true-listp) (p primep))
  :verify-guards nil
  (grp-cstep-body bx by ax ay (nth 0 w) (nth 1 w) (nth 2 w) (nth 3 w) (nth 4 w)
                  (nth 5 w) (nth 6 w) (nth 7 w) (nth 8 w) (nth 9 w) (nth 10 w)))

(define grp-cnext-x (bit w)
  :verify-guards nil
  (if (equal bit 1) (nth 9 w) (nth 3 w)))

(define grp-cnext-y (bit w)
  :verify-guards nil
  (if (equal bit 1) (nth 10 w) (nth 4 w)))

(defruled grp-cmul-step-gadget-sound
  (implies (and (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal (len w) 11)
                (grp-syms-boundp w asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-cmul-step-gadget bx by ax ay w p) asg p))
           (and (symbolp (grp-cnext-x bit w))
                (symbolp (grp-cnext-y bit w))
                (r1cs::valuation-bindsp asg (grp-cnext-x bit w))
                (r1cs::valuation-bindsp asg (grp-cnext-y bit w))
                (equal (grp-pt (grp-cnext-x bit w) (grp-cnext-y bit w))
                       (grp-mul-step-val bit (grp-pt bx by) (grp-pt ax ay)))))
  :do-not-induct t
  :use ((:instance grp-cmul-step-body-sound
                   (dxy (nth 0 w)) (dx2 (nth 1 w)) (dy2 (nth 2 w)) (dx (nth 3 w))
                   (dy (nth 4 w)) (u (nth 5 w)) (v0 (nth 6 w)) (v1 (nth 7 w))
                   (v01 (nth 8 w)) (sx (nth 9 w)) (sy (nth 10 w)))
        (:instance grp-syms-boundp-nth (syms w) (i 0))
        (:instance grp-syms-boundp-nth (syms w) (i 1))
        (:instance grp-syms-boundp-nth (syms w) (i 2))
        (:instance grp-syms-boundp-nth (syms w) (i 3))
        (:instance grp-syms-boundp-nth (syms w) (i 4))
        (:instance grp-syms-boundp-nth (syms w) (i 5))
        (:instance grp-syms-boundp-nth (syms w) (i 6))
        (:instance grp-syms-boundp-nth (syms w) (i 7))
        (:instance grp-syms-boundp-nth (syms w) (i 8))
        (:instance grp-syms-boundp-nth (syms w) (i 9))
        (:instance grp-syms-boundp-nth (syms w) (i 10)))
  :in-theory '(grp-cmul-step-gadget grp-mul-step-val grp-cnext-x grp-cnext-y
               (:e <) (:e nfix)))

(define grp-cmul-steps-gadget ((cbits bit-listp) (steps true-listp)
                               (bx symbolp) (by symbolp)
                               (ax symbolp) (ay symbolp) (p primep))
  :verify-guards nil
  :short "The variable iterations of @('Group::mul_assign') for constant
          bits, after the first 1 bit: a double and an add per bit,
          the constant ternary picking the sum or the double."
  (if (or (atom cbits) (atom steps))
      nil
    (b* ((w (car steps)))
      (append (grp-cmul-step-gadget bx by ax ay w p)
              (grp-cmul-steps-gadget (cdr cbits) (cdr steps) bx by
                                     (grp-cnext-x (car cbits) w)
                                     (grp-cnext-y (car cbits) w) p)))))

(define grp-cmul-steps-out ((cbits bit-listp) (steps true-listp)
                            (ax symbolp) (ay symbolp))
  :verify-guards nil
  (if (or (atom cbits) (atom steps))
      (list ax ay)
    (grp-cmul-steps-out (cdr cbits) (cdr steps)
                        (grp-cnext-x (car cbits) (car steps))
                        (grp-cnext-y (car cbits) (car steps)))))

(defun grp-csteps-ind (cbits steps ax ay)
  (if (or (atom cbits) (atom steps))
      (list ax ay)
    (grp-csteps-ind (cdr cbits) (cdr steps)
                    (grp-cnext-x (car cbits) (car steps))
                    (grp-cnext-y (car cbits) (car steps)))))

(define grp-csteps-boundp (steps asg)
  :verify-guards nil
  (if (atom steps)
      t
    (and (equal (len (car steps)) 11)
         (grp-syms-boundp (car steps) asg)
         (grp-csteps-boundp (cdr steps) asg))))

(defruled grp-cmul-steps-gadget-sound
  (implies (and (grp-csteps-boundp steps asg)
                (equal (len steps) (len cbits))
                (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (r1cs::r1cs-constraints-holdp
                 (grp-cmul-steps-gadget cbits steps bx by ax ay p) asg p))
           (b* ((out (grp-cmul-steps-out cbits steps ax ay)))
             (equal (grp-pt (first out) (second out))
                    (grp-mul-fold cbits (grp-pt bx by) (grp-pt ax ay)))))
  :induct (grp-csteps-ind cbits steps ax ay)
  :hints (("Subgoal *1/2"
           :use ((:instance grp-cmul-step-gadget-sound (bit (car cbits)) (w (car steps)))
                 (:instance grp-mul-step-val-pointp
                            (bit (car cbits))
                            (base (grp-pt bx by)) (acc (grp-pt ax ay))))
           :expand ((:free (p) (grp-cmul-steps-gadget cbits steps bx by ax ay p))
                    (grp-cmul-steps-out cbits steps ax ay)
                    (grp-csteps-boundp steps asg)
                    (len cbits) (len steps)
                    (:free (b a) (grp-mul-fold cbits b a)))
           :in-theory '(r1cs::r1cs-constraints-holdp-of-append
                        car-cons cdr-cons (:e <) (:e nfix) endp atom
                        acl2::fix (:e acl2::fix) (:t len)))
          ("Subgoal *1/1"
           :expand ((grp-cmul-steps-out cbits steps ax ay)
                    (len cbits) (len steps))
           :in-theory (enable grp-mul-fold))))

(define grp-cstep-canonp (bx by ax ay w asg)
  :verify-guards nil
  (grp-cstep-canon bx by ax ay (nth 0 w) (nth 1 w) (nth 2 w) (nth 3 w) (nth 4 w)
                   (nth 5 w) (nth 6 w) (nth 7 w) (nth 8 w) (nth 9 w) (nth 10 w)))

(defruled grp-cmul-step-gadget-complete
  (implies (and (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal (len w) 11)
                (grp-syms-boundp w asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-cstep-canonp bx by ax ay w asg))
           (r1cs::r1cs-constraints-holdp
            (grp-cmul-step-gadget bx by ax ay w p) asg p))
  :do-not-induct t
  :use ((:instance grp-cmul-step-body-complete
                   (dxy (nth 0 w)) (dx2 (nth 1 w)) (dy2 (nth 2 w)) (dx (nth 3 w))
                   (dy (nth 4 w)) (u (nth 5 w)) (v0 (nth 6 w)) (v1 (nth 7 w))
                   (v01 (nth 8 w)) (sx (nth 9 w)) (sy (nth 10 w)))
        (:instance grp-syms-boundp-nth (syms w) (i 0))
        (:instance grp-syms-boundp-nth (syms w) (i 1))
        (:instance grp-syms-boundp-nth (syms w) (i 2))
        (:instance grp-syms-boundp-nth (syms w) (i 3))
        (:instance grp-syms-boundp-nth (syms w) (i 4))
        (:instance grp-syms-boundp-nth (syms w) (i 5))
        (:instance grp-syms-boundp-nth (syms w) (i 6))
        (:instance grp-syms-boundp-nth (syms w) (i 7))
        (:instance grp-syms-boundp-nth (syms w) (i 8))
        (:instance grp-syms-boundp-nth (syms w) (i 9))
        (:instance grp-syms-boundp-nth (syms w) (i 10)))
  :in-theory '(grp-cmul-step-gadget grp-cstep-canonp (:e <) (:e nfix)))

(define grp-csteps-canonp (cbits steps bx by ax ay asg)
  :verify-guards nil
  (if (or (atom cbits) (atom steps))
      t
    (and (grp-cstep-canonp bx by ax ay (car steps) asg)
         (grp-csteps-canonp (cdr cbits) (cdr steps) bx by
                            (grp-cnext-x (car cbits) (car steps))
                            (grp-cnext-y (car cbits) (car steps)) asg))))

(defruled grp-cmul-steps-gadget-complete
  (implies (and (grp-csteps-boundp steps asg)
                (equal (len steps) (len cbits))
                (symbolp bx) (symbolp by) (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg bx) (r1cs::valuation-bindsp asg by)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp (grp-pt bx by))
                (ecurve::edwards-bls12-pointp (grp-pt ax ay))
                (grp-csteps-canonp cbits steps bx by ax ay asg))
           (r1cs::r1cs-constraints-holdp
            (grp-cmul-steps-gadget cbits steps bx by ax ay p) asg p))
  :induct (grp-csteps-ind cbits steps ax ay)
  :hints (("Subgoal *1/2"
           :use ((:instance grp-cmul-step-gadget-complete (w (car steps)))
                 (:instance grp-cmul-step-gadget-sound (bit (car cbits)) (w (car steps)))
                 (:instance grp-mul-step-val-pointp
                            (bit (car cbits))
                            (base (grp-pt bx by)) (acc (grp-pt ax ay))))
           :expand ((:free (p) (grp-cmul-steps-gadget cbits steps bx by ax ay p))
                    (grp-csteps-canonp cbits steps bx by ax ay asg)
                    (grp-csteps-boundp steps asg)
                    (len cbits) (len steps))
           :in-theory '(r1cs::r1cs-constraints-holdp-of-append
                        car-cons cdr-cons (:e <) (:e nfix) endp atom
                        acl2::fix (:e acl2::fix) (:t len)))
          ("Subgoal *1/1"
           :expand ((:free (p) (grp-cmul-steps-gadget cbits steps bx by ax ay p)))
           :in-theory (enable r1cs::r1cs-constraints-holdp))))
