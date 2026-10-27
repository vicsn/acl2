; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::is_in_group (circuit/types/group/src/lib.rs) multiplies the point by
; the constant big-endian bits of the subgroup order r and calls is_zero on
; the product.  The constraints are the constant-bit mul steps of grp-mul.lisp
; over the bits of r after the leading one, then crv-group-is-zero-gadget.

(in-package "ALEOVM")

(include-book "grp-mul")

(define grp-r-bits ()
  :short "The big-endian bits of the subgroup order @($r$), without the
          leading zeros (constant false bits emit no constraints)."
  (acl2::nat=>bebits (integer-length (scalar-prime)) (scalar-prime)))

(defruled grp-r-bits-facts
  (and (equal (car (grp-r-bits)) 1)
       (bit-listp (cdr (grp-r-bits)))
       (equal (grp-mul-fold-val (cdr (grp-r-bits)) 1) (scalar-prime)))
  :in-theory '((:e grp-r-bits) (:e car) (:e cdr) (:e bit-listp)
               (:e grp-mul-fold-val) (:e scalar-prime) (:e equal)))

(defruled grp-r-kills-iff-groupp
  (implies (ecurve::edwards-bls12-pointp b)
           (iff (equal (ecurve::edwards-bls12-mul (scalar-prime) b)
                       (ecurve::twisted-edwards-zero))
                (groupp b)))
  :use ((:instance ecurve::grp-r-point-killed (ecurve::pt b))
        (:instance ecurve::twisted-edwards-point-orderp-when-prime-kills
                   (ecurve::point b)
                   (ecurve::r (ecurve::edwards-bls12-r))
                   (ecurve::curve (ecurve::edwards-bls12-curve))))
  :in-theory '(groupp scalar-prime ecurve::edwards-bls12-mul
               ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-pointp
               ecurve::primep-of-edwards-bls12-r
               ecurve::twisted-edwards-curve-completep-of-edwards-bls12-curve))

(define grp-is-in-group-gadget ((bx symbolp) (by symbolp) (steps true-listp)
                                (mx symbolp) (rx symbolp) (my symbolp) (ry symbolp)
                                (out symbolp) (p primep))
  :verify-guards nil
  :short "@('Group::is_in_group'): @('Group::mul_assign') by the constant
          bits of @($r$), then @('Group::is_zero') of the product."
  (b* ((prod (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
    (append (grp-cmul-steps-gadget (cdr (grp-r-bits)) steps bx by bx by p)
            (crv-group-is-zero-gadget (first prod) (second prod)
                                      mx rx my ry out p))))

(defmacro grp-iig-hyps (&rest more)
  `(and (grp-csteps-boundp steps asg)
        (equal (len steps) (len (cdr (grp-r-bits))))
        (grp-bound-all bx by mx rx my ry out)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (ecurve::edwards-bls12-pointp (grp-pt bx by))
        ,@more))

(defruled grp-cmul-steps-out-bound
  (implies (and (grp-csteps-boundp steps asg)
                (symbolp ax) (symbolp ay)
                (r1cs::valuation-bindsp asg ax) (r1cs::valuation-bindsp asg ay))
           (b* ((out (grp-cmul-steps-out cbits steps ax ay)))
             (and (symbolp (first out)) (symbolp (second out))
                  (r1cs::valuation-bindsp asg (first out))
                  (r1cs::valuation-bindsp asg (second out)))))
  :induct (grp-csteps-ind cbits steps ax ay)
  :hints (("Subgoal *1/2"
           :expand ((grp-cmul-steps-out cbits steps ax ay)
                    (grp-csteps-boundp steps asg))
           :use ((:instance grp-syms-boundp-nth (syms (car steps)) (i 3))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 4))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 9))
                 (:instance grp-syms-boundp-nth (syms (car steps)) (i 10)))
           :in-theory (enable grp-cnext-x grp-cnext-y))
          ("Subgoal *1/1"
           :expand ((grp-cmul-steps-out cbits steps ax ay)))))

(defruled grp-is-in-group-product
  (implies (grp-iig-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-cmul-steps-gadget (cdr (grp-r-bits)) steps bx by bx by p) asg p))
           (b* ((prod (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
             (equal (grp-pt (first prod) (second prod))
                    (ecurve::edwards-bls12-mul (scalar-prime) (grp-pt bx by)))))
  :do-not-induct t
  :use ((:instance grp-cmul-steps-gadget-sound
                   (cbits (cdr (grp-r-bits))) (ax bx) (ay by))
        (:instance grp-mul-fold-is-mul
                   (bits (cdr (grp-r-bits))) (b (grp-pt bx by)) (k 1))
        (:instance grp-edwards-mul-1 (b (grp-pt bx by)))
        grp-r-bits-facts)
  :in-theory '((:e natp)))

(defruled grp-is-in-group-gadget-sound
  :short "R1CS-SOUND of @('Group::is_in_group') on a curve point (the
          precondition snarkVM documents): the output bit is
          @(tsee group-is-in-group-funspec)."
  (implies (grp-iig-hyps
            (r1cs::r1cs-constraints-holdp
             (grp-is-in-group-gadget bx by steps mx rx my ry out p) asg p))
           (equal (lookup-equal out asg)
                  (group-is-in-group-funspec (grp-pt bx by))))
  :do-not-induct t
  :use (grp-is-in-group-product
        (:instance grp-cmul-steps-out-bound
                   (cbits (cdr (grp-r-bits))) (ax bx) (ay by))
        (:instance crv-group-is-zero-wire-sound
                   (x (first (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
                   (y (second (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
                   (p0 (ecurve::edwards-bls12-mul (scalar-prime) (grp-pt bx by))))
        (:instance grp-point-coords
                   (x (lookup-equal (first (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)) asg))
                   (y (lookup-equal (second (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)) asg)))
        (:instance grp-r-kills-iff-groupp (b (grp-pt bx by)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (scalar-prime)) (ecurve::point (grp-pt bx by))))
  :in-theory '(grp-is-in-group-gadget r1cs::r1cs-constraints-holdp-of-append
               group-is-in-group-funspec group-is-zero-funspec
               fieldp r1cs::fep-of-lookup-equal))

(defruled grp-is-in-group-gadget-complete
  :short "R1CS-COMPLETE of @('Group::is_in_group') on a curve point: the
          canonical double/add witnesses and the canonical @('is_zero')
          witnesses of the product satisfy the constraints."
  (implies (grp-iig-hyps
            (grp-csteps-canonp (cdr (grp-r-bits)) steps bx by bx by asg)
            (b* ((prod (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by))
                 (x (lookup-equal (first prod) asg))
                 (y (lookup-equal (second prod) asg)))
              (and (equal (lookup-equal rx asg) (if (equal x 0) 0 1))
                   (equal (lookup-equal mx asg)
                          (if (equal x 0) 0 (pfield::inv x p)))
                   (equal (lookup-equal ry asg) (if (equal y 1) 0 1))
                   (equal (lookup-equal my asg)
                          (if (equal y 1) 0 (pfield::inv (pfield::sub y 1 p) p)))
                   (equal (lookup-equal out asg)
                          (group-is-in-group-funspec (grp-pt bx by))))))
           (r1cs::r1cs-constraints-holdp
            (grp-is-in-group-gadget bx by steps mx rx my ry out p) asg p))
  :do-not-induct t
  :use ((:instance grp-cmul-steps-gadget-complete
                   (cbits (cdr (grp-r-bits))) (ax bx) (ay by))
        grp-is-in-group-product
        (:instance grp-cmul-steps-out-bound
                   (cbits (cdr (grp-r-bits))) (ax bx) (ay by))
        (:instance crv-group-is-zero-gadget-complete
                   (x (first (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
                   (y (second (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)))
                   (p0 (ecurve::edwards-bls12-mul (scalar-prime) (grp-pt bx by))))
        (:instance grp-point-coords
                   (x (lookup-equal (first (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)) asg))
                   (y (lookup-equal (second (grp-cmul-steps-out (cdr (grp-r-bits)) steps bx by)) asg)))
        (:instance grp-r-kills-iff-groupp (b (grp-pt bx by)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (scalar-prime)) (ecurve::point (grp-pt bx by))))
  :in-theory '(grp-is-in-group-gadget r1cs::r1cs-constraints-holdp-of-append
               group-is-in-group-funspec group-is-zero-funspec
               fieldp r1cs::fep-of-lookup-equal))
