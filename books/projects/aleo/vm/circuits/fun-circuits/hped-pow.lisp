; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::pow with a constant exponent on a linear-combination base
; (circuit/types/field/src/pow.rs).  The output starts at the constant 1.
; Leading zero bits square a constant; the first 1 bit multiplies the
; constant 1 by the base, which is the base linear combination itself.
; Each later bit squares the accumulator (one constraint) and, for a 1 bit,
; multiplies by the base (one more constraint).  hped-pow-gadget emits the
; constraints for the bits after the leading 1, starting from the base.

(in-package "ALEOVM")

(include-book "hped-lc")
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(define hped-pow-gadget (g (cs bit-listp) (pw true-listp) acc)
  :verify-guards nil
  :short "@('pw') holds one wire pair @('(s r)') per bit:
          @('s') the square and @('r') the product (used for 1 bits)."
  (if (endp cs)
      nil
    (b* ((s (first (car pw)))
         (r (second (car pw)))
         (sq (hped-c acc acc (hped-lc-v s))))
      (if (equal (car cs) 1)
          (list* sq
                 (hped-c (hped-lc-v s) g (hped-lc-v r))
                 (hped-pow-gadget g (cdr cs) (cdr pw) (hped-lc-v r)))
        (cons sq (hped-pow-gadget g (cdr cs) (cdr pw) (hped-lc-v s)))))))

(define hped-pow-out ((cs bit-listp) (pw true-listp) acc)
  :verify-guards nil
  :short "The linear combination of the result."
  (if (endp cs)
      acc
    (hped-pow-out (cdr cs) (cdr pw)
                  (if (equal (car cs) 1)
                      (hped-lc-v (second (car pw)))
                    (hped-lc-v (first (car pw)))))))

(define hped-pow-exp ((cs bit-listp) (k natp))
  :verify-guards nil
  (if (endp cs)
      k
    (hped-pow-exp (cdr cs) (+ k k (if (equal (car cs) 1) 1 0)))))

(define hped-pw-boundp (cs pw asg)
  :verify-guards nil
  (if (endp cs)
      t
    (and (consp pw)
         (symbolp (first (car pw)))
         (symbolp (second (car pw)))
         (r1cs::valuation-bindsp asg (first (car pw)))
         (r1cs::valuation-bindsp asg (second (car pw)))
         (hped-pw-boundp (cdr cs) (cdr pw) asg))))

(defruledl hped-pow-step
  (implies (and (primep p) (natp k) (pfield::fep x p))
           (and (equal (pfield::mul (pfield::pow x k p) (pfield::pow x k p) p)
                       (pfield::pow x (+ k k) p))
                (equal (pfield::mul (pfield::pow x (+ k k) p) x p)
                       (pfield::pow x (+ 1 k k) p))))
  :use ((:instance pfield::pow-of-+ (pfield::p p) (a x) (b k) (c k))
        (:instance pfield::pow-of-+ (pfield::p p) (a x) (b (+ k k)) (c 1)))
  :disable pfield::pow-of-+
  :enable pfield::pow-of-1-arg2)

(defun hped-pow-ind (cs pw acc k)
  (declare (xargs :verify-guards nil))
  (if (endp cs)
      (list pw acc k)
    (hped-pow-ind (cdr cs) (cdr pw)
                  (if (equal (car cs) 1)
                      (hped-lc-v (second (car pw)))
                    (hped-lc-v (first (car pw))))
                  (+ k k (if (equal (car cs) 1) 1 0)))))

(defruled hped-pow-gadget-sound
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (bit-listp cs)
                (hped-pw-boundp cs pw asg)
                (natp k)
                (equal (hped-dot acc) (pfield::pow (hped-dot g) k p))
                (r1cs::r1cs-constraints-holdp (hped-pow-gadget g cs pw acc) asg p))
           (equal (hped-dot (hped-pow-out cs pw acc))
                  (pfield::pow (hped-dot g) (hped-pow-exp cs k) p)))
  :induct (hped-pow-ind cs pw acc k)
  :enable (hped-pow-gadget hped-pow-out hped-pow-exp hped-pw-boundp)
  :hints (("Subgoal *1/2" :use ((:instance hped-pow-step (x (hped-dot g)))))))

(defun hped-pw-canonp (g cs pw acc asg p)
  (declare (xargs :verify-guards nil))
  (if (endp cs)
      t
    (b* ((s (first (car pw)))
         (r (second (car pw)))
         (sv (pfield::mul (hped-dot acc) (hped-dot acc) p)))
      (and (equal (lookup-equal s asg) sv)
           (if (equal (car cs) 1)
               (and (equal (lookup-equal r asg) (pfield::mul sv (hped-dot g) p))
                    (hped-pw-canonp g (cdr cs) (cdr pw) (hped-lc-v r) asg p))
             (hped-pw-canonp g (cdr cs) (cdr pw) (hped-lc-v s) asg p))))))

(defruled hped-pow-gadget-complete
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (hped-pw-boundp cs pw asg)
                (hped-pw-canonp g cs pw acc asg p))
           (r1cs::r1cs-constraints-holdp (hped-pow-gadget g cs pw acc) asg p))
  :induct (hped-pow-gadget g cs pw acc)
  :enable (hped-pow-gadget hped-pw-boundp))
