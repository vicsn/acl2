;; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The concrete Literal wire representation of ptx-elit.lisp extended with
; the Group arm (prefix ptx-g-) and then the Address arm (prefix ptx-a-),
; for all four leaf interfaces.
;
; A Group (Address) leaf wire is (:group gw xs rs) ((:address gw xs rs)):
; gw the 14 wires of enforce_in_group (x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3
; exy ex2 ey2), xs the 253 bit wires of the x-coordinate and rs its
; range-check wires.  The point is (x, y); the leaf is typed when the
; point is groupp and the assignment covers gw, xs and rs.
;
;   Literal::new          literal-group-new-gadget on gw (enforce_in_group);
;                         soundness is literal-group-new-sound-unconditional
;                         / literal-address-new-sound-unconditional
;                         (group-unconditional.lisp, which discharges the
;                         cofactor hypothesis by
;                         edwards-bls12-cofactor-clears-holds); the witness
;                         is group-enforce-in-group-witness-lookupsp;
;   write_bits_le / _be   crv-group-write-bits-le-gadget x xs rs ptx-one
;                         (crv-address-write-bits-le-gadget); the output is
;                         xs, reversed for be;
;   is_equal / _not_equal crv-group-is-not-equal-gadget (crv-address-...)
;                         on the coordinates with fresh wires mx rx my ry
;                         out; out is is_equal and the is_not_equal output
;                         is 1 - out.  The bitp hypotheses on rx, ry, out
;                         are discharged by crv-group-is-equal-wire-sound
;                         (group-wire-sound.lisp), through
;                         lit-literal-is-equal-group-sound.

(in-package "ALEOVM")

(include-book "ptx-elit")
(include-book "group-unconditional")
(include-book "group-wire-sound")
(include-book "literal-new-group-complete")
(include-book "crv-bits")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-g-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

(defruled ptx-g-bindsp-of-nth
  (implies (and (r1cs::valuation-binds-allp asg l)
                (natp i)
                (< i (len l)))
           (r1cs::valuation-bindsp asg (nth i l)))
  :induct (nth i l)
  :enable nth)

(defruled ptx-g-symbolp-of-nth
  (implies (symbol-listp l) (symbolp (nth i l)))
  :induct (nth i l)
  :enable nth)

(defruled ptx-g-base-field-size-in-bits
  (equal (base-field-size-in-bits) 253)
  :enable ((:e base-field-size-in-bits)))

(defruled ptx-g-binds-allp-of-append
  (equal (r1cs::valuation-binds-allp asg (append a b))
         (and (r1cs::valuation-binds-allp asg a)
              (r1cs::valuation-binds-allp asg b)))
  :induct (len a)
  :enable r1cs::valuation-binds-allp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The group arm (prefix ptx-g-, over ptx-e-).

(defun ptx-g-shapep (w)
  (and (eq (car w) :group)
       (symbol-listp (second w))
       (equal (len (second w)) 14)
       (symbol-listp (third w))
       (equal (len (third w)) 253)
       (symbol-listp (fourth w))
       (equal (len (fourth w)) (bits-lt-prime-rlen (base-prime)))))

(defun ptx-g-vars (w)
  (append (second w) (third w) (fourth w)))

(defun ptx-g-pt (w asg)
  (ecurve::point-finite (lookup-equal (nth 0 (second w)) asg)
                        (lookup-equal (nth 1 (second w)) asg)))

(defun ptx-g-new-gadget-of (gw)
  (literal-group-new-gadget (nth 0 gw) (nth 1 gw) (nth 2 gw) (nth 3 gw)
                            (nth 4 gw) (nth 5 gw) (nth 6 gw) (nth 7 gw)
                            (nth 8 gw) (nth 9 gw) (nth 10 gw) (nth 11 gw)
                            (nth 12 gw) (nth 13 gw) (base-prime)))

(defun ptx-g-new-witness-of (gw pt asg)
  (group-enforce-in-group-witness-lookupsp
   (nth 0 gw) (nth 1 gw) (nth 2 gw) (nth 3 gw)
   (nth 4 gw) (nth 5 gw) (nth 6 gw) (nth 7 gw)
   (nth 8 gw) (nth 9 gw) (nth 10 gw) (nth 11 gw)
   (nth 12 gw) (nth 13 gw) pt asg (base-prime)))

(defun ptx-g-bits-witnessp (w asg)
  (and (equal (lookup-equal-list (third w) asg)
              (group-write-bits-le-funspec (ptx-g-pt w asg)))
       (equal (lookup-equal-list (fourth w) asg)
              (crv-bits-lte-const-witness
               (lookup-equal-list (third w) asg)
               (nat=>lebits* (1- (base-prime)))))))

(defun ptx-g-names-okp (names)
  (and (symbol-listp names) (<= 5 (len names))))

(defun ptx-g-eq-okp (wa wb names)
  (and (ptx-g-shapep wa) (ptx-g-shapep wb) (ptx-g-names-okp names)))

;; The leaf.

(defun ptx-g-leaf-val (w asg)
  (if (eq (car w) :group)
      (literal-group (ptx-g-pt w asg))
    (ptx-e-leaf-val w asg)))

(defun ptx-g-leaf-typed (w asg)
  (if (eq (car w) :group)
      (and (ptx-g-shapep w)
           (groupp (ptx-g-pt w asg))
           (r1cs::valuation-binds-allp asg (ptx-g-vars w)))
    (ptx-e-leaf-typed w asg)))

(defun ptx-g-leaf-variant (w)
  (if (eq (car w) :group) 3 (ptx-e-leaf-variant w)))

(defun ptx-g-leaf-size (w)
  (if (eq (car w) :group) 253 (ptx-e-leaf-size w)))

(defun ptx-g-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :group)) (ptx-e-leaf-bits-gadget w bigp))
        ((ptx-g-shapep w)
         (crv-group-write-bits-le-gadget (nth 0 (second w)) (third w) (fourth w)
                                      'ptx-one (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-g-leaf-bits-out (w bigp)
  (if (eq (car w) :group)
      (if bigp (rev (third w)) (third w))
    (ptx-e-leaf-bits-out w bigp)))

(defun ptx-g-leaf-bits-witnessp (w bigp asg p)
  (if (eq (car w) :group)
      (ptx-g-bits-witnessp w asg)
    (ptx-e-leaf-bits-witnessp w bigp asg p)))

(defun ptx-g-leaf-new-gadget (w)
  (cond ((not (eq (car w) :group)) (ptx-e-leaf-new-gadget w))
        ((ptx-g-shapep w) (ptx-g-new-gadget-of (second w)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-g-leaf-new-vars (w)
  (cond ((not (eq (car w) :group)) (ptx-e-leaf-new-vars w))
        ((ptx-g-shapep w) (ptx-g-vars w))
        (t nil)))

(defun ptx-g-leaf-new-witnessp (w x asg p)
  (if (eq (car w) :group)
      (and (r1cs::r1cs-valuationp asg p)
           (r1cs::valuation-binds-allp asg (ptx-g-leaf-new-vars w))
           (ptx-g-leaf-typed w asg)
           (equal (ptx-g-leaf-val w asg) x)
           (ptx-g-new-witness-of (second w) (ptx-g-pt w asg) asg))
    (ptx-e-leaf-new-witnessp w x asg p)))

(defun ptx-g-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :group)) (ptx-e-leaf-eq-gadget wa wb neq names))
        ((ptx-g-eq-okp wa wb names)
         (crv-group-is-not-equal-gadget
          (nth 0 (second wa)) (nth 1 (second wa))
          (nth 0 (second wb)) (nth 1 (second wb))
          (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names) (nth 4 names)
          (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-g-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :group)) (ptx-e-leaf-eq-out wa wb neq names))
        ((ptx-g-eq-okp wa wb names) (ptx-c-zout (nth 4 names) (not neq)))
        (t 0)))

(defun ptx-g-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :group)) (ptx-e-leaf-eq-nvars wa wb neq))
        (t 5)))

(defun ptx-g-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :group))
         (ptx-e-leaf-eq-witnessp wa wb neq names asg p))
        (t (b* ((x1 (lookup-equal (nth 0 (second wa)) asg))
                (y1 (lookup-equal (nth 1 (second wa)) asg))
                (x2 (lookup-equal (nth 0 (second wb)) asg))
                (y2 (lookup-equal (nth 1 (second wb)) asg)))
             (and (ptx-g-names-okp names)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal (nth 1 names) asg)
                         (if (equal x1 x2) 0 1))
                  (equal (lookup-equal (nth 0 names) asg)
                         (if (equal x1 x2)
                             0
                           (pfield::inv (pfield::sub x1 x2 (base-prime))
                                        (base-prime))))
                  (equal (lookup-equal (nth 3 names) asg)
                         (if (equal y1 y2) 0 1))
                  (equal (lookup-equal (nth 2 names) asg)
                         (if (equal y1 y2)
                             0
                           (pfield::inv (pfield::sub y1 y2 (base-prime))
                                        (base-prime))))
                  (equal (lookup-equal (nth 4 names) asg)
                         (group-is-equal-funspec (ptx-g-pt wa asg)
                                                 (ptx-g-pt wb asg))))))))

;; Lemmas.

(defruled ptx-g-leaf-when-not-group
  (implies (not (eq (car w) :group))
           (and (equal (ptx-g-leaf-typed w asg) (ptx-e-leaf-typed w asg))
                (equal (ptx-g-leaf-val w asg) (ptx-e-leaf-val w asg))
                (equal (ptx-g-leaf-new-gadget w) (ptx-e-leaf-new-gadget w))
                (equal (ptx-g-leaf-new-vars w) (ptx-e-leaf-new-vars w))
                (equal (ptx-g-leaf-new-witnessp w x asg p)
                       (ptx-e-leaf-new-witnessp w x asg p))
                (equal (ptx-g-leaf-bits-gadget w bigp)
                       (ptx-e-leaf-bits-gadget w bigp))
                (equal (ptx-g-leaf-bits-out w bigp)
                       (ptx-e-leaf-bits-out w bigp))
                (equal (ptx-g-leaf-bits-witnessp w bigp asg p)
                       (ptx-e-leaf-bits-witnessp w bigp asg p)))))

(defruled ptx-g-literal-facts
  (and (literalp (literal-group x))
       (equal (literal-variant (literal-group x)) 3)
       (equal (literal-size-in-bits (literal-group x)) 253)
       (equal (literal-kind (literal-group x)) :group)
       (equal (literal-new (literal-group x)) (literal-group x)))
  :enable (literal-variant literal-size-in-bits literal-new))

(defruled ptx-g-typed-facts
  (implies (and (eq (car w) :group)
                (ptx-g-leaf-typed w asg))
           (and (symbolp (nth 0 (second w)))
                (symbolp (nth 1 (second w)))
                (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w)))
                (r1cs::valuation-binds-allp asg (third w))
                (r1cs::valuation-binds-allp asg (fourth w))
                (ecurve::edwards-bls12-pointp (ptx-g-pt w asg))
                (groupp (ptx-g-pt w asg))))
  :enable (ptx-g-binds-allp-of-append)
  :use ((:instance ptx-g-bindsp-of-nth (l (second w)) (i 0))
        (:instance ptx-g-bindsp-of-nth (l (second w)) (i 1))
        (:instance ptx-g-symbolp-of-nth (l (second w)) (i 0))
        (:instance ptx-g-symbolp-of-nth (l (second w)) (i 1)))
  :disable ptx-g-pt)

(defruled ptx-g-pt-coords
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w))))
           (and (equal (ecurve::point-finite->x (ptx-g-pt w asg))
                       (lookup-equal (nth 0 (second w)) asg))
                (equal (ecurve::point-finite->y (ptx-g-pt w asg))
                       (lookup-equal (nth 1 (second w)) asg))))
  :use ((:instance r1cs::fep-of-lookup-equal (var (nth 0 (second w)))
         (prime (base-prime)) (valuation asg))
        (:instance r1cs::fep-of-lookup-equal (var (nth 1 (second w)))
         (prime (base-prime)) (valuation asg)))
  :enable pfield::fep
  :disable nth)

(defruled ptx-g-leaf-constraints
  (and (literalp (ptx-g-leaf-val w asg))
       (implies (ptx-g-leaf-typed w asg)
                (equal (literal-variant (ptx-g-leaf-val w asg))
                       (ptx-g-leaf-variant w)))
       (implies (ptx-g-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-g-leaf-val w asg))
                       (ptx-g-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-g-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use (ptx-e-leaf-constraints ptx-g-leaf-when-not-group)
  :enable ptx-g-literal-facts
  :disable (ptx-e-leaf-val ptx-e-leaf-typed equal-of-literal-boolean
                             ptx-g-pt))

(defruled ptx-g-leaf-bits-sound-group
  (implies (and (eq (car w) :group)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-g-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-g-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-g-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-g-leaf-val w asg))
                    (literal-to-bits-le (ptx-g-leaf-val w asg)))))
  :do-not-induct t
  :use (ptx-g-typed-facts ptx-g-pt-coords
        (:instance lit-literal-write-bits-le-group-sound
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (p0 (ptx-g-pt w asg)))
        (:instance lit-literal-write-bits-be-group-sound
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (p0 (ptx-g-pt w asg))))
  :enable (ptx-d-integer-length-of-base-prime ptx-d-oddp-of-base-prime
           ptx-g-base-field-size-in-bits crv-group-write-bits-be-gadget
           crv-address-write-bits-be-gadget crv-address-write-bits-le-gadget
           ptx-c-bindsp-when-lookup)
  :disable (ptx-g-pt ptx-g-vars))

(defruled ptx-g-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-g-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-g-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-g-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-g-leaf-val w asg))
                    (literal-to-bits-le (ptx-g-leaf-val w asg)))))
  :use (ptx-g-leaf-bits-sound-group ptx-e-leaf-bits-sound
        ptx-g-leaf-when-not-group)
  :disable (ptx-g-shapep ptx-e-leaf-val ptx-e-leaf-typed
                           ptx-g-leaf-typed ptx-g-leaf-val ptx-g-pt))

(defruled ptx-g-leaf-bits-complete-group
  (implies (and (eq (car w) :group)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-g-leaf-typed w asg)
                (ptx-g-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-g-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-g-typed-facts ptx-g-pt-coords
        (:instance crv-group-write-bits-le-gadget-complete
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (pt (ptx-g-pt w asg))))
  :enable (ptx-d-integer-length-of-base-prime ptx-d-oddp-of-base-prime
           ptx-c-bindsp-when-lookup)
  :disable (ptx-g-pt ptx-g-vars))

(defruled ptx-g-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-g-leaf-typed w asg)
                (ptx-g-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-g-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-g-leaf-bits-complete-group ptx-e-leaf-bits-complete
        ptx-g-leaf-when-not-group)
  :disable (ptx-g-shapep ptx-e-leaf-val ptx-e-leaf-typed
                           ptx-g-leaf-typed ptx-g-leaf-val ptx-g-pt
                           ptx-g-bits-witnessp ptx-e-leaf-bits-gadget
                           ptx-e-leaf-bits-witnessp))

(defrule ptx-g-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-g-leaf-new-vars w))
  :enable ptx-e-leaf-new-vars)

(defruled ptx-g-literal-new-of-leaf-val
  (equal (literal-new (ptx-g-leaf-val w asg))
         (ptx-g-leaf-val w asg))
  :use ptx-e-literal-new-of-leaf-val
  :enable ptx-g-literal-facts
  :disable (ptx-e-leaf-val ptx-g-pt))

(defruled ptx-g-nth-bindsp-of-vars
  (implies (and (ptx-g-shapep w)
                (r1cs::valuation-binds-allp asg (ptx-g-vars w)))
           (and (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w)))
                (r1cs::valuation-bindsp asg (nth 2 (second w)))
                (r1cs::valuation-bindsp asg (nth 3 (second w)))
                (r1cs::valuation-bindsp asg (nth 4 (second w)))
                (r1cs::valuation-bindsp asg (nth 5 (second w)))
                (r1cs::valuation-bindsp asg (nth 6 (second w)))
                (r1cs::valuation-bindsp asg (nth 7 (second w)))
                (r1cs::valuation-bindsp asg (nth 8 (second w)))
                (r1cs::valuation-bindsp asg (nth 9 (second w)))
                (r1cs::valuation-bindsp asg (nth 10 (second w)))
                (r1cs::valuation-bindsp asg (nth 11 (second w)))
                (r1cs::valuation-bindsp asg (nth 12 (second w)))
                (r1cs::valuation-bindsp asg (nth 13 (second w)))
                (symbolp (nth 0 (second w))) (symbolp (nth 1 (second w)))
                (symbolp (nth 2 (second w))) (symbolp (nth 3 (second w)))
                (symbolp (nth 4 (second w))) (symbolp (nth 5 (second w)))
                (symbolp (nth 6 (second w))) (symbolp (nth 7 (second w)))
                (symbolp (nth 8 (second w))) (symbolp (nth 9 (second w)))
                (symbolp (nth 10 (second w))) (symbolp (nth 11 (second w)))
                (symbolp (nth 12 (second w))) (symbolp (nth 13 (second w)))))
  :enable (ptx-g-binds-allp-of-append ptx-g-bindsp-of-nth ptx-g-symbolp-of-nth)
  :disable nth)

(defruled ptx-g-leaf-new-sound-group
  (implies (and (eq (car w) :group)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-g-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-g-leaf-new-gadget w) asg p))
           (ptx-g-leaf-typed w asg))
  :do-not-induct t
  :use (ptx-g-nth-bindsp-of-vars
        (:instance literal-group-new-sound-unconditional
         (xcoord (nth 0 (second w))) (ycoord (nth 1 (second w)))
         (qx (nth 2 (second w))) (qy (nth 3 (second w)))
         (cx2 (nth 4 (second w))) (cy2 (nth 5 (second w)))
         (dxy (nth 6 (second w))) (dx2 (nth 7 (second w)))
         (dy2 (nth 8 (second w))) (x3 (nth 9 (second w)))
         (y3 (nth 10 (second w))) (exy (nth 11 (second w)))
         (ex2 (nth 12 (second w))) (ey2 (nth 13 (second w)))))
  :disable (ptx-g-vars nth))

(defruled ptx-g-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-g-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-g-leaf-new-gadget w) asg p))
           (and (ptx-g-leaf-typed w asg)
                (equal (literal-new (ptx-g-leaf-val w asg))
                       (ptx-g-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-e-leaf-new-sound ptx-g-leaf-when-not-group
        ptx-g-leaf-new-sound-group)
  :enable ptx-g-literal-new-of-leaf-val
  :disable (ptx-e-leaf-typed ptx-e-leaf-val ptx-e-leaf-new-gadget
                               ptx-e-leaf-new-vars ptx-g-leaf-typed
                               ptx-g-leaf-val ptx-g-leaf-new-gadget
                               ptx-g-leaf-new-vars))

(defruled ptx-g-leaf-new-complete-group
  (implies (and (eq (car w) :group)
                (equal p (base-prime))
                (ptx-g-leaf-new-witnessp w x asg p))
           (r1cs::r1cs-constraints-holdp (ptx-g-leaf-new-gadget w) asg p))
  :do-not-induct t
  :use (ptx-g-nth-bindsp-of-vars
        (:instance literal-group-new-complete
         (x (literal-group (ptx-g-pt w asg)))
         (xcoord (nth 0 (second w))) (ycoord (nth 1 (second w)))
         (qx (nth 2 (second w))) (qy (nth 3 (second w)))
         (cx2 (nth 4 (second w))) (cy2 (nth 5 (second w)))
         (dxy (nth 6 (second w))) (dx2 (nth 7 (second w)))
         (dy2 (nth 8 (second w))) (x3 (nth 9 (second w)))
         (y3 (nth 10 (second w))) (exy (nth 11 (second w)))
         (ex2 (nth 12 (second w))) (ey2 (nth 13 (second w)))))
  :enable ptx-g-literal-facts
  :disable (ptx-g-vars nth ptx-g-pt group-enforce-in-group-witness-lookupsp))

(defruled ptx-g-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-g-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-g-leaf-new-gadget w) asg p)
                (equal (ptx-g-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use ((:instance ptx-e-leaf-new-complete)
        ptx-g-leaf-new-complete-group
        ptx-g-leaf-when-not-group)
  :enable (ptx-g-literal-new-of-leaf-val)
  :disable (ptx-e-leaf-val ptx-e-leaf-typed ptx-e-leaf-new-gadget
                             ptx-e-leaf-new-vars ptx-e-leaf-new-witnessp
                             ptx-g-leaf-val ptx-g-leaf-typed
                             ptx-g-leaf-new-gadget ptx-g-new-witness-of))

(defruled ptx-g-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-g-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-g-leaf-new-gadget w)
                                              asg p)))
  :use ((:instance ptx-e-leaf-new-error)
        (:instance ptx-g-leaf-constraints)
        ptx-g-leaf-when-not-group)
  :enable ptx-g-literal-new-of-leaf-val
  :disable (ptx-g-leaf-val ptx-g-leaf-typed ptx-e-leaf-new-gadget
                             ptx-e-leaf-new-witnessp ptx-g-new-witness-of
                             ptx-e-leaf-val))

(defrule ptx-g-natp-of-leaf-eq-nvars
  (natp (ptx-g-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defrule ptx-g-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-g-leaf-eq-out wa wb neq names))
                             (ptx-g-leaf-eq-out wa wb neq names)))
  :use (ptx-e-sparse-vectorp-of-leaf-eq-out
        (:instance ptx-d-sparse-vectorp-of-zout (z (nth 4 names)) (neq (not neq))))
  :enable ptx-g-symbolp-of-nth
  :disable (ptx-c-zout ptx-e-sparse-vectorp-of-leaf-eq-out ptx-e-leaf-eq-out))

(defruled ptx-g-kind-of-leaf-val
  (implies (ptx-g-leaf-typed w asg)
           (equal (literal-kind (ptx-g-leaf-val w asg)) (car w)))
  :use ptx-e-kind-of-leaf-val
  :enable ptx-g-literal-facts
  :disable (ptx-e-leaf-val ptx-e-leaf-typed ptx-g-pt))

(defruled ptx-g-eq-core
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbol-listp names)
                (<= 5 (len names))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-binds-allp asg names)
                (groupp p1)
                (groupp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-is-not-equal-gadget
                  x1 y1 x2 y2
                  (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names)
                  (nth 4 names) p)
                 asg p))
           (equal (ptx-bval (ptx-c-zout (nth 4 names) (not neq)) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (literal-group p1)
                                                   (literal-group p2)))
                     (values-literal-equalp (literal-group p1)
                                            (literal-group p2))))))
  :do-not-induct t
  :use ((:instance ptx-g-bindsp-of-nth (l names) (i 0))
        (:instance ptx-g-bindsp-of-nth (l names) (i 1))
        (:instance ptx-g-bindsp-of-nth (l names) (i 2))
        (:instance ptx-g-bindsp-of-nth (l names) (i 3))
        (:instance ptx-g-bindsp-of-nth (l names) (i 4))
        (:instance ptx-g-symbolp-of-nth (l names) (i 0))
        (:instance ptx-g-symbolp-of-nth (l names) (i 1))
        (:instance ptx-g-symbolp-of-nth (l names) (i 2))
        (:instance ptx-g-symbolp-of-nth (l names) (i 3))
        (:instance ptx-g-symbolp-of-nth (l names) (i 4))
        (:instance lit-literal-is-equal-group-sound
         (mx (nth 0 names)) (rx (nth 1 names)) (my (nth 2 names))
         (ry (nth 3 names)) (out (nth 4 names)))
        (:instance ptx-c-bval-of-zout (z (nth 4 names)) (neq (not neq))))
  :enable (literal-is-equal values-bool-to-bit crv-group-is-not-equal-gadget)
  :disable (ptx-c-zout lit-literal-is-equal-group-sound nth))

(defruled ptx-g-leaf-eq-sound-group
  (implies (and (equal (car wa) :group)
                (equal (car wb) :group)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-g-leaf-typed wa asg)
                (ptx-g-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-g-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-g-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-g-leaf-val wa asg)
                                                   (ptx-g-leaf-val wb asg)))
                     (values-literal-equalp (ptx-g-leaf-val wa asg)
                                            (ptx-g-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-g-typed-facts (w wa))
        (:instance ptx-g-typed-facts (w wb))
        (:instance ptx-g-pt-coords (w wa))
        (:instance ptx-g-pt-coords (w wb))
        (:instance ptx-g-eq-core
         (x1 (nth 0 (second wa))) (y1 (nth 1 (second wa)))
         (x2 (nth 0 (second wb))) (y2 (nth 1 (second wb)))
         (p1 (ptx-g-pt wa asg)) (p2 (ptx-g-pt wb asg))))
  :enable ptx-c-false-constraint-fails-base
  :disable (ptx-c-zout ptx-g-pt nth ptx-g-vars ptx-g-shapep
                       ptx-g-typed-facts ptx-g-pt-coords ptx-g-eq-core
                       crv-group-is-not-equal-gadget))

(defruled ptx-g-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (and (equal (ptx-g-leaf-eq-out wa wb neq names) (if neq 1 0))
                (equal (ptx-g-leaf-eq-gadget wa wb neq names)
                       (lit-literal-equal-mismatch-gadget)))))

(defruled ptx-g-leaf-eq-when-not-group
  (implies (not (equal (car wa) :group))
           (and (equal (ptx-g-leaf-eq-gadget wa wb neq names)
                       (ptx-e-leaf-eq-gadget wa wb neq names))
                (equal (ptx-g-leaf-eq-out wa wb neq names)
                       (ptx-e-leaf-eq-out wa wb neq names))
                (equal (ptx-g-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-e-leaf-eq-witnessp wa wb neq names asg p))))
  :enable (ptx-e-leaf-eq-gadget ptx-e-leaf-eq-out ptx-e-leaf-eq-witnessp))

(defruled ptx-g-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-g-leaf-typed wa asg)
                (ptx-g-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-g-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-g-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-g-leaf-val wa asg)
                                                   (ptx-g-leaf-val wb asg)))
                     (values-literal-equalp (ptx-g-leaf-val wa asg)
                                            (ptx-g-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-g-kind-of-leaf-val (w wa))
        (:instance ptx-g-kind-of-leaf-val (w wb))
        (:instance ptx-g-leaf-constraints (w wa))
        (:instance ptx-g-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-g-leaf-val wa asg)) (y (ptx-g-leaf-val wb asg)))
        ptx-g-leaf-eq-sound-group
        (:instance ptx-e-leaf-eq-sound)
        (:instance ptx-g-leaf-when-not-group (w wa))
        (:instance ptx-g-leaf-when-not-group (w wb))
        ptx-g-leaf-eq-when-not-group)
  :enable (values-bool-to-bit ptx-g-leaf-eq-out-when-mismatch)
  :disable (ptx-g-leaf-eq-gadget ptx-g-leaf-eq-out ptx-g-leaf-typed
                                   ptx-g-leaf-val ptx-e-leaf-eq-gadget
                                   ptx-e-leaf-eq-out ptx-e-leaf-val
                                   ptx-e-leaf-typed))

(defruled ptx-g-eq-complete-core
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbol-listp names)
                (<= 5 (len names))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-binds-allp asg names)
                (groupp p1)
                (groupp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (equal (lookup-equal (nth 1 names) asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal (nth 0 names) asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal (nth 3 names) asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal (nth 2 names) asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal (nth 4 names) asg)
                       (group-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-not-equal-gadget
             x1 y1 x2 y2
             (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names)
             (nth 4 names) p)
            asg p))
  :do-not-induct t
  :use ((:instance ptx-g-bindsp-of-nth (l names) (i 0))
        (:instance ptx-g-bindsp-of-nth (l names) (i 1))
        (:instance ptx-g-bindsp-of-nth (l names) (i 2))
        (:instance ptx-g-bindsp-of-nth (l names) (i 3))
        (:instance ptx-g-bindsp-of-nth (l names) (i 4))
        (:instance ptx-g-symbolp-of-nth (l names) (i 0))
        (:instance ptx-g-symbolp-of-nth (l names) (i 1))
        (:instance ptx-g-symbolp-of-nth (l names) (i 2))
        (:instance ptx-g-symbolp-of-nth (l names) (i 3))
        (:instance ptx-g-symbolp-of-nth (l names) (i 4))
        (:instance crv-group-is-not-equal-gadget-complete
         (mx (nth 0 names)) (rx (nth 1 names)) (my (nth 2 names))
         (ry (nth 3 names)) (out (nth 4 names))))
  :in-theory (union-theories (theory 'minimal-theory)
                             '(values-edwards-bls12-pointp-when-groupp
                               (:e natp) (:e nfix))))

(defruled ptx-g-leaf-eq-complete-group
  (implies (and (equal (car wa) :group)
                (equal (car wb) :group)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-g-leaf-typed wa asg)
                (ptx-g-leaf-typed wb asg)
                (ptx-g-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-g-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance ptx-g-typed-facts (w wa))
        (:instance ptx-g-typed-facts (w wb))
        (:instance ptx-g-pt-coords (w wa))
        (:instance ptx-g-pt-coords (w wb))
        (:instance ptx-g-eq-complete-core
         (x1 (nth 0 (second wa))) (y1 (nth 1 (second wa)))
         (x2 (nth 0 (second wb))) (y2 (nth 1 (second wb)))
         (p1 (ptx-g-pt wa asg)) (p2 (ptx-g-pt wb asg))))
  :disable (ptx-g-pt nth ptx-g-vars ptx-g-shapep
                       ptx-g-typed-facts ptx-g-pt-coords
                       ptx-g-eq-complete-core crv-group-is-not-equal-gadget
                       group-is-equal-funspec))

(defruled ptx-g-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-g-leaf-typed wa asg)
                (ptx-g-leaf-typed wb asg)
                (ptx-g-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-g-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-g-leaf-eq-complete-group
        (:instance ptx-e-leaf-eq-complete)
        (:instance ptx-g-leaf-when-not-group (w wa))
        (:instance ptx-g-leaf-when-not-group (w wb))
        ptx-g-leaf-eq-when-not-group)
  :enable (lit-literal-equal-mismatch-complete ptx-g-leaf-eq-out-when-mismatch)
  :disable (lit-literal-equal-mismatch-gadget
            ptx-g-leaf-eq-gadget ptx-g-leaf-eq-witnessp ptx-g-leaf-typed
            ptx-g-leaf-val ptx-e-leaf-eq-gadget
            ptx-e-leaf-eq-witnessp ptx-e-leaf-typed
            ptx-e-leaf-val))

(in-theory (disable ptx-g-leaf-val ptx-g-leaf-typed ptx-g-leaf-variant
                    ptx-g-leaf-size ptx-g-leaf-bits-gadget ptx-g-leaf-bits-out
                    ptx-g-leaf-bits-witnessp ptx-g-leaf-new-gadget
                    ptx-g-leaf-new-vars ptx-g-leaf-new-witnessp
                    ptx-g-leaf-eq-gadget ptx-g-leaf-eq-out ptx-g-leaf-eq-nvars
                    ptx-g-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The address arm (prefix ptx-a-, over ptx-g-).

(defun ptx-a-shapep (w)
  (and (eq (car w) :address)
       (symbol-listp (second w))
       (equal (len (second w)) 14)
       (symbol-listp (third w))
       (equal (len (third w)) 253)
       (symbol-listp (fourth w))
       (equal (len (fourth w)) (bits-lt-prime-rlen (base-prime)))))

(defun ptx-a-vars (w)
  (append (second w) (third w) (fourth w)))

(defun ptx-a-pt (w asg)
  (ecurve::point-finite (lookup-equal (nth 0 (second w)) asg)
                        (lookup-equal (nth 1 (second w)) asg)))

(defun ptx-a-new-gadget-of (gw)
  (literal-group-new-gadget (nth 0 gw) (nth 1 gw) (nth 2 gw) (nth 3 gw)
                            (nth 4 gw) (nth 5 gw) (nth 6 gw) (nth 7 gw)
                            (nth 8 gw) (nth 9 gw) (nth 10 gw) (nth 11 gw)
                            (nth 12 gw) (nth 13 gw) (base-prime)))

(defun ptx-a-new-witness-of (gw pt asg)
  (group-enforce-in-group-witness-lookupsp
   (nth 0 gw) (nth 1 gw) (nth 2 gw) (nth 3 gw)
   (nth 4 gw) (nth 5 gw) (nth 6 gw) (nth 7 gw)
   (nth 8 gw) (nth 9 gw) (nth 10 gw) (nth 11 gw)
   (nth 12 gw) (nth 13 gw) pt asg (base-prime)))

(defun ptx-a-bits-witnessp (w asg)
  (and (equal (lookup-equal-list (third w) asg)
              (address-write-bits-le-funspec (ptx-a-pt w asg)))
       (equal (lookup-equal-list (fourth w) asg)
              (crv-bits-lte-const-witness
               (lookup-equal-list (third w) asg)
               (nat=>lebits* (1- (base-prime)))))))

(defun ptx-a-names-okp (names)
  (and (symbol-listp names) (<= 5 (len names))))

(defun ptx-a-eq-okp (wa wb names)
  (and (ptx-a-shapep wa) (ptx-a-shapep wb) (ptx-a-names-okp names)))

;; The leaf.

(defun ptx-a-leaf-val (w asg)
  (if (eq (car w) :address)
      (literal-address (ptx-a-pt w asg))
    (ptx-g-leaf-val w asg)))

(defun ptx-a-leaf-typed (w asg)
  (if (eq (car w) :address)
      (and (ptx-a-shapep w)
           (groupp (ptx-a-pt w asg))
           (r1cs::valuation-binds-allp asg (ptx-a-vars w)))
    (ptx-g-leaf-typed w asg)))

(defun ptx-a-leaf-variant (w)
  (if (eq (car w) :address) 0 (ptx-g-leaf-variant w)))

(defun ptx-a-leaf-size (w)
  (if (eq (car w) :address) 253 (ptx-g-leaf-size w)))

(defun ptx-a-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :address)) (ptx-g-leaf-bits-gadget w bigp))
        ((ptx-a-shapep w)
         (crv-address-write-bits-le-gadget (nth 0 (second w)) (third w) (fourth w)
                                      'ptx-one (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-a-leaf-bits-out (w bigp)
  (if (eq (car w) :address)
      (if bigp (rev (third w)) (third w))
    (ptx-g-leaf-bits-out w bigp)))

(defun ptx-a-leaf-bits-witnessp (w bigp asg p)
  (if (eq (car w) :address)
      (ptx-a-bits-witnessp w asg)
    (ptx-g-leaf-bits-witnessp w bigp asg p)))

(defun ptx-a-leaf-new-gadget (w)
  (cond ((not (eq (car w) :address)) (ptx-g-leaf-new-gadget w))
        ((ptx-a-shapep w) (ptx-a-new-gadget-of (second w)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-a-leaf-new-vars (w)
  (cond ((not (eq (car w) :address)) (ptx-g-leaf-new-vars w))
        ((ptx-a-shapep w) (ptx-a-vars w))
        (t nil)))

(defun ptx-a-leaf-new-witnessp (w x asg p)
  (if (eq (car w) :address)
      (and (r1cs::r1cs-valuationp asg p)
           (r1cs::valuation-binds-allp asg (ptx-a-leaf-new-vars w))
           (ptx-a-leaf-typed w asg)
           (equal (ptx-a-leaf-val w asg) x)
           (ptx-a-new-witness-of (second w) (ptx-a-pt w asg) asg))
    (ptx-g-leaf-new-witnessp w x asg p)))

(defun ptx-a-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :address)) (ptx-g-leaf-eq-gadget wa wb neq names))
        ((ptx-a-eq-okp wa wb names)
         (crv-address-is-not-equal-gadget
          (nth 0 (second wa)) (nth 1 (second wa))
          (nth 0 (second wb)) (nth 1 (second wb))
          (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names) (nth 4 names)
          (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-a-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :address)) (ptx-g-leaf-eq-out wa wb neq names))
        ((ptx-a-eq-okp wa wb names) (ptx-c-zout (nth 4 names) (not neq)))
        (t 0)))

(defun ptx-a-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :address)) (ptx-g-leaf-eq-nvars wa wb neq))
        (t 5)))

(defun ptx-a-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :address))
         (ptx-g-leaf-eq-witnessp wa wb neq names asg p))
        (t (b* ((x1 (lookup-equal (nth 0 (second wa)) asg))
                (y1 (lookup-equal (nth 1 (second wa)) asg))
                (x2 (lookup-equal (nth 0 (second wb)) asg))
                (y2 (lookup-equal (nth 1 (second wb)) asg)))
             (and (ptx-a-names-okp names)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal (nth 1 names) asg)
                         (if (equal x1 x2) 0 1))
                  (equal (lookup-equal (nth 0 names) asg)
                         (if (equal x1 x2)
                             0
                           (pfield::inv (pfield::sub x1 x2 (base-prime))
                                        (base-prime))))
                  (equal (lookup-equal (nth 3 names) asg)
                         (if (equal y1 y2) 0 1))
                  (equal (lookup-equal (nth 2 names) asg)
                         (if (equal y1 y2)
                             0
                           (pfield::inv (pfield::sub y1 y2 (base-prime))
                                        (base-prime))))
                  (equal (lookup-equal (nth 4 names) asg)
                         (group-is-equal-funspec (ptx-a-pt wa asg)
                                                 (ptx-a-pt wb asg))))))))

;; Lemmas.

(defruled ptx-a-leaf-when-not-address
  (implies (not (eq (car w) :address))
           (and (equal (ptx-a-leaf-typed w asg) (ptx-g-leaf-typed w asg))
                (equal (ptx-a-leaf-val w asg) (ptx-g-leaf-val w asg))
                (equal (ptx-a-leaf-new-gadget w) (ptx-g-leaf-new-gadget w))
                (equal (ptx-a-leaf-new-vars w) (ptx-g-leaf-new-vars w))
                (equal (ptx-a-leaf-new-witnessp w x asg p)
                       (ptx-g-leaf-new-witnessp w x asg p))
                (equal (ptx-a-leaf-bits-gadget w bigp)
                       (ptx-g-leaf-bits-gadget w bigp))
                (equal (ptx-a-leaf-bits-out w bigp)
                       (ptx-g-leaf-bits-out w bigp))
                (equal (ptx-a-leaf-bits-witnessp w bigp asg p)
                       (ptx-g-leaf-bits-witnessp w bigp asg p)))))

(defruled ptx-a-literal-facts
  (and (literalp (literal-address x))
       (equal (literal-variant (literal-address x)) 0)
       (equal (literal-size-in-bits (literal-address x)) 253)
       (equal (literal-kind (literal-address x)) :address)
       (equal (literal-new (literal-address x)) (literal-address x)))
  :enable (literal-variant literal-size-in-bits literal-new))

(defruled ptx-a-typed-facts
  (implies (and (eq (car w) :address)
                (ptx-a-leaf-typed w asg))
           (and (symbolp (nth 0 (second w)))
                (symbolp (nth 1 (second w)))
                (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w)))
                (r1cs::valuation-binds-allp asg (third w))
                (r1cs::valuation-binds-allp asg (fourth w))
                (ecurve::edwards-bls12-pointp (ptx-a-pt w asg))
                (groupp (ptx-a-pt w asg))))
  :enable (ptx-g-binds-allp-of-append)
  :use ((:instance ptx-g-bindsp-of-nth (l (second w)) (i 0))
        (:instance ptx-g-bindsp-of-nth (l (second w)) (i 1))
        (:instance ptx-g-symbolp-of-nth (l (second w)) (i 0))
        (:instance ptx-g-symbolp-of-nth (l (second w)) (i 1)))
  :disable ptx-a-pt)

(defruled ptx-a-pt-coords
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w))))
           (and (equal (ecurve::point-finite->x (ptx-a-pt w asg))
                       (lookup-equal (nth 0 (second w)) asg))
                (equal (ecurve::point-finite->y (ptx-a-pt w asg))
                       (lookup-equal (nth 1 (second w)) asg))))
  :use ((:instance r1cs::fep-of-lookup-equal (var (nth 0 (second w)))
         (prime (base-prime)) (valuation asg))
        (:instance r1cs::fep-of-lookup-equal (var (nth 1 (second w)))
         (prime (base-prime)) (valuation asg)))
  :enable pfield::fep
  :disable nth)

(defruled ptx-a-leaf-constraints
  (and (literalp (ptx-a-leaf-val w asg))
       (implies (ptx-a-leaf-typed w asg)
                (equal (literal-variant (ptx-a-leaf-val w asg))
                       (ptx-a-leaf-variant w)))
       (implies (ptx-a-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-a-leaf-val w asg))
                       (ptx-a-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-a-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use (ptx-g-leaf-constraints ptx-a-leaf-when-not-address)
  :enable ptx-a-literal-facts
  :disable (ptx-g-leaf-val ptx-g-leaf-typed equal-of-literal-boolean
                             ptx-a-pt))

(defruled ptx-a-leaf-bits-sound-address
  (implies (and (eq (car w) :address)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-a-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-a-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-a-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-a-leaf-val w asg))
                    (literal-to-bits-le (ptx-a-leaf-val w asg)))))
  :do-not-induct t
  :use (ptx-a-typed-facts ptx-a-pt-coords
        (:instance lit-literal-write-bits-le-address-sound
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (p0 (ptx-a-pt w asg)))
        (:instance lit-literal-write-bits-be-address-sound
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (p0 (ptx-a-pt w asg))))
  :enable (ptx-d-integer-length-of-base-prime ptx-d-oddp-of-base-prime
           ptx-g-base-field-size-in-bits crv-group-write-bits-be-gadget
           crv-address-write-bits-be-gadget crv-address-write-bits-le-gadget
           ptx-c-bindsp-when-lookup)
  :disable (ptx-a-pt ptx-a-vars))

(defruled ptx-a-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-a-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-a-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-a-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-a-leaf-val w asg))
                    (literal-to-bits-le (ptx-a-leaf-val w asg)))))
  :use (ptx-a-leaf-bits-sound-address ptx-g-leaf-bits-sound
        ptx-a-leaf-when-not-address)
  :disable (ptx-a-shapep ptx-g-leaf-val ptx-g-leaf-typed
                           ptx-a-leaf-typed ptx-a-leaf-val ptx-a-pt))

(defruled ptx-a-leaf-bits-complete-address
  (implies (and (eq (car w) :address)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-a-leaf-typed w asg)
                (ptx-a-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-a-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-a-typed-facts ptx-a-pt-coords
        (:instance crv-address-write-bits-le-gadget-complete
         (x (nth 0 (second w))) (xs (third w)) (rs (fourth w)) (u 'ptx-one)
         (pt (ptx-a-pt w asg))))
  :enable (ptx-d-integer-length-of-base-prime ptx-d-oddp-of-base-prime
           ptx-c-bindsp-when-lookup)
  :disable (ptx-a-pt ptx-a-vars))

(defruled ptx-a-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-a-leaf-typed w asg)
                (ptx-a-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-a-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-a-leaf-bits-complete-address ptx-g-leaf-bits-complete
        ptx-a-leaf-when-not-address)
  :disable (ptx-a-shapep ptx-g-leaf-val ptx-g-leaf-typed
                           ptx-a-leaf-typed ptx-a-leaf-val ptx-a-pt
                           ptx-a-bits-witnessp ptx-g-leaf-bits-gadget
                           ptx-g-leaf-bits-witnessp))

(defrule ptx-a-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-a-leaf-new-vars w))
  :enable ptx-g-leaf-new-vars)

(defruled ptx-a-literal-new-of-leaf-val
  (equal (literal-new (ptx-a-leaf-val w asg))
         (ptx-a-leaf-val w asg))
  :use ptx-g-literal-new-of-leaf-val
  :enable ptx-a-literal-facts
  :disable (ptx-g-leaf-val ptx-a-pt))

(defruled ptx-a-nth-bindsp-of-vars
  (implies (and (ptx-a-shapep w)
                (r1cs::valuation-binds-allp asg (ptx-a-vars w)))
           (and (r1cs::valuation-bindsp asg (nth 0 (second w)))
                (r1cs::valuation-bindsp asg (nth 1 (second w)))
                (r1cs::valuation-bindsp asg (nth 2 (second w)))
                (r1cs::valuation-bindsp asg (nth 3 (second w)))
                (r1cs::valuation-bindsp asg (nth 4 (second w)))
                (r1cs::valuation-bindsp asg (nth 5 (second w)))
                (r1cs::valuation-bindsp asg (nth 6 (second w)))
                (r1cs::valuation-bindsp asg (nth 7 (second w)))
                (r1cs::valuation-bindsp asg (nth 8 (second w)))
                (r1cs::valuation-bindsp asg (nth 9 (second w)))
                (r1cs::valuation-bindsp asg (nth 10 (second w)))
                (r1cs::valuation-bindsp asg (nth 11 (second w)))
                (r1cs::valuation-bindsp asg (nth 12 (second w)))
                (r1cs::valuation-bindsp asg (nth 13 (second w)))
                (symbolp (nth 0 (second w))) (symbolp (nth 1 (second w)))
                (symbolp (nth 2 (second w))) (symbolp (nth 3 (second w)))
                (symbolp (nth 4 (second w))) (symbolp (nth 5 (second w)))
                (symbolp (nth 6 (second w))) (symbolp (nth 7 (second w)))
                (symbolp (nth 8 (second w))) (symbolp (nth 9 (second w)))
                (symbolp (nth 10 (second w))) (symbolp (nth 11 (second w)))
                (symbolp (nth 12 (second w))) (symbolp (nth 13 (second w)))))
  :enable (ptx-g-binds-allp-of-append ptx-g-bindsp-of-nth ptx-g-symbolp-of-nth)
  :disable nth)

(defruled ptx-a-leaf-new-sound-address
  (implies (and (eq (car w) :address)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-a-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-a-leaf-new-gadget w) asg p))
           (ptx-a-leaf-typed w asg))
  :do-not-induct t
  :use (ptx-a-nth-bindsp-of-vars
        (:instance literal-address-new-sound-unconditional
         (xcoord (nth 0 (second w))) (ycoord (nth 1 (second w)))
         (qx (nth 2 (second w))) (qy (nth 3 (second w)))
         (cx2 (nth 4 (second w))) (cy2 (nth 5 (second w)))
         (dxy (nth 6 (second w))) (dx2 (nth 7 (second w)))
         (dy2 (nth 8 (second w))) (x3 (nth 9 (second w)))
         (y3 (nth 10 (second w))) (exy (nth 11 (second w)))
         (ex2 (nth 12 (second w))) (ey2 (nth 13 (second w)))))
  :disable (ptx-a-vars nth))

(defruled ptx-a-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-a-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-a-leaf-new-gadget w) asg p))
           (and (ptx-a-leaf-typed w asg)
                (equal (literal-new (ptx-a-leaf-val w asg))
                       (ptx-a-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-g-leaf-new-sound ptx-a-leaf-when-not-address
        ptx-a-leaf-new-sound-address)
  :enable ptx-a-literal-new-of-leaf-val
  :disable (ptx-g-leaf-typed ptx-g-leaf-val ptx-g-leaf-new-gadget
                               ptx-g-leaf-new-vars ptx-a-leaf-typed
                               ptx-a-leaf-val ptx-a-leaf-new-gadget
                               ptx-a-leaf-new-vars))

(defruled ptx-a-leaf-new-complete-address
  (implies (and (eq (car w) :address)
                (equal p (base-prime))
                (ptx-a-leaf-new-witnessp w x asg p))
           (r1cs::r1cs-constraints-holdp (ptx-a-leaf-new-gadget w) asg p))
  :do-not-induct t
  :use (ptx-a-nth-bindsp-of-vars
        (:instance literal-address-new-complete
         (x (literal-address (ptx-a-pt w asg)))
         (xcoord (nth 0 (second w))) (ycoord (nth 1 (second w)))
         (qx (nth 2 (second w))) (qy (nth 3 (second w)))
         (cx2 (nth 4 (second w))) (cy2 (nth 5 (second w)))
         (dxy (nth 6 (second w))) (dx2 (nth 7 (second w)))
         (dy2 (nth 8 (second w))) (x3 (nth 9 (second w)))
         (y3 (nth 10 (second w))) (exy (nth 11 (second w)))
         (ex2 (nth 12 (second w))) (ey2 (nth 13 (second w)))))
  :enable ptx-a-literal-facts
  :disable (ptx-a-vars nth ptx-a-pt group-enforce-in-group-witness-lookupsp))

(defruled ptx-a-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-a-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-a-leaf-new-gadget w) asg p)
                (equal (ptx-a-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use ((:instance ptx-g-leaf-new-complete)
        ptx-a-leaf-new-complete-address
        ptx-a-leaf-when-not-address)
  :enable (ptx-a-literal-new-of-leaf-val)
  :disable (ptx-g-leaf-val ptx-g-leaf-typed ptx-g-leaf-new-gadget
                             ptx-g-leaf-new-vars ptx-g-leaf-new-witnessp
                             ptx-a-leaf-val ptx-a-leaf-typed
                             ptx-a-leaf-new-gadget ptx-a-new-witness-of))

(defruled ptx-a-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-a-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-a-leaf-new-gadget w)
                                              asg p)))
  :use ((:instance ptx-g-leaf-new-error)
        (:instance ptx-a-leaf-constraints)
        ptx-a-leaf-when-not-address)
  :enable ptx-a-literal-new-of-leaf-val
  :disable (ptx-a-leaf-val ptx-a-leaf-typed ptx-g-leaf-new-gadget
                             ptx-g-leaf-new-witnessp ptx-a-new-witness-of
                             ptx-g-leaf-val))

(defrule ptx-a-natp-of-leaf-eq-nvars
  (natp (ptx-a-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defrule ptx-a-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-a-leaf-eq-out wa wb neq names))
                             (ptx-a-leaf-eq-out wa wb neq names)))
  :use (ptx-g-sparse-vectorp-of-leaf-eq-out
        (:instance ptx-d-sparse-vectorp-of-zout (z (nth 4 names)) (neq (not neq))))
  :enable ptx-g-symbolp-of-nth
  :disable (ptx-c-zout ptx-g-sparse-vectorp-of-leaf-eq-out ptx-g-leaf-eq-out))

(defruled ptx-a-kind-of-leaf-val
  (implies (ptx-a-leaf-typed w asg)
           (equal (literal-kind (ptx-a-leaf-val w asg)) (car w)))
  :use ptx-g-kind-of-leaf-val
  :enable ptx-a-literal-facts
  :disable (ptx-g-leaf-val ptx-g-leaf-typed ptx-a-pt))

(defruled ptx-a-eq-core
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbol-listp names)
                (<= 5 (len names))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-binds-allp asg names)
                (groupp p1)
                (groupp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-is-not-equal-gadget
                  x1 y1 x2 y2
                  (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names)
                  (nth 4 names) p)
                 asg p))
           (equal (ptx-bval (ptx-c-zout (nth 4 names) (not neq)) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (literal-address p1)
                                                   (literal-address p2)))
                     (values-literal-equalp (literal-address p1)
                                            (literal-address p2))))))
  :do-not-induct t
  :use ((:instance ptx-g-bindsp-of-nth (l names) (i 0))
        (:instance ptx-g-bindsp-of-nth (l names) (i 1))
        (:instance ptx-g-bindsp-of-nth (l names) (i 2))
        (:instance ptx-g-bindsp-of-nth (l names) (i 3))
        (:instance ptx-g-bindsp-of-nth (l names) (i 4))
        (:instance ptx-g-symbolp-of-nth (l names) (i 0))
        (:instance ptx-g-symbolp-of-nth (l names) (i 1))
        (:instance ptx-g-symbolp-of-nth (l names) (i 2))
        (:instance ptx-g-symbolp-of-nth (l names) (i 3))
        (:instance ptx-g-symbolp-of-nth (l names) (i 4))
        (:instance lit-literal-is-equal-address-sound
         (mx (nth 0 names)) (rx (nth 1 names)) (my (nth 2 names))
         (ry (nth 3 names)) (out (nth 4 names)))
        (:instance ptx-c-bval-of-zout (z (nth 4 names)) (neq (not neq))))
  :enable (literal-is-equal values-bool-to-bit crv-address-is-not-equal-gadget)
  :disable (ptx-c-zout lit-literal-is-equal-address-sound nth))

(defruled ptx-a-leaf-eq-sound-address
  (implies (and (equal (car wa) :address)
                (equal (car wb) :address)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-a-leaf-typed wa asg)
                (ptx-a-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-a-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-a-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-a-leaf-val wa asg)
                                                   (ptx-a-leaf-val wb asg)))
                     (values-literal-equalp (ptx-a-leaf-val wa asg)
                                            (ptx-a-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-a-typed-facts (w wa))
        (:instance ptx-a-typed-facts (w wb))
        (:instance ptx-a-pt-coords (w wa))
        (:instance ptx-a-pt-coords (w wb))
        (:instance ptx-a-eq-core
         (x1 (nth 0 (second wa))) (y1 (nth 1 (second wa)))
         (x2 (nth 0 (second wb))) (y2 (nth 1 (second wb)))
         (p1 (ptx-a-pt wa asg)) (p2 (ptx-a-pt wb asg))))
  :enable ptx-c-false-constraint-fails-base
  :disable (ptx-c-zout ptx-a-pt nth ptx-a-vars ptx-a-shapep
                       ptx-a-typed-facts ptx-a-pt-coords ptx-a-eq-core
                       crv-address-is-not-equal-gadget))

(defruled ptx-a-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (and (equal (ptx-a-leaf-eq-out wa wb neq names) (if neq 1 0))
                (equal (ptx-a-leaf-eq-gadget wa wb neq names)
                       (lit-literal-equal-mismatch-gadget)))))

(defruled ptx-a-leaf-eq-when-not-address
  (implies (not (equal (car wa) :address))
           (and (equal (ptx-a-leaf-eq-gadget wa wb neq names)
                       (ptx-g-leaf-eq-gadget wa wb neq names))
                (equal (ptx-a-leaf-eq-out wa wb neq names)
                       (ptx-g-leaf-eq-out wa wb neq names))
                (equal (ptx-a-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-g-leaf-eq-witnessp wa wb neq names asg p))))
  :enable (ptx-g-leaf-eq-gadget ptx-g-leaf-eq-out ptx-g-leaf-eq-witnessp))

(defruled ptx-a-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-a-leaf-typed wa asg)
                (ptx-a-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-a-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-a-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-a-leaf-val wa asg)
                                                   (ptx-a-leaf-val wb asg)))
                     (values-literal-equalp (ptx-a-leaf-val wa asg)
                                            (ptx-a-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-a-kind-of-leaf-val (w wa))
        (:instance ptx-a-kind-of-leaf-val (w wb))
        (:instance ptx-a-leaf-constraints (w wa))
        (:instance ptx-a-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-a-leaf-val wa asg)) (y (ptx-a-leaf-val wb asg)))
        ptx-a-leaf-eq-sound-address
        (:instance ptx-g-leaf-eq-sound)
        (:instance ptx-a-leaf-when-not-address (w wa))
        (:instance ptx-a-leaf-when-not-address (w wb))
        ptx-a-leaf-eq-when-not-address)
  :enable (values-bool-to-bit ptx-a-leaf-eq-out-when-mismatch)
  :disable (ptx-a-leaf-eq-gadget ptx-a-leaf-eq-out ptx-a-leaf-typed
                                   ptx-a-leaf-val ptx-g-leaf-eq-gadget
                                   ptx-g-leaf-eq-out ptx-g-leaf-val
                                   ptx-g-leaf-typed))

(defruled ptx-a-eq-complete-core
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbol-listp names)
                (<= 5 (len names))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-binds-allp asg names)
                (groupp p1)
                (groupp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (equal (lookup-equal (nth 1 names) asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0 1))
                (equal (lookup-equal (nth 0 names) asg)
                       (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                                   (lookup-equal x2 asg) p)
                                      p)))
                (equal (lookup-equal (nth 3 names) asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0 1))
                (equal (lookup-equal (nth 2 names) asg)
                       (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                                   (lookup-equal y2 asg) p)
                                      p)))
                (equal (lookup-equal (nth 4 names) asg)
                       (group-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-address-is-not-equal-gadget
             x1 y1 x2 y2
             (nth 0 names) (nth 1 names) (nth 2 names) (nth 3 names)
             (nth 4 names) p)
            asg p))
  :do-not-induct t
  :use ((:instance ptx-g-bindsp-of-nth (l names) (i 0))
        (:instance ptx-g-bindsp-of-nth (l names) (i 1))
        (:instance ptx-g-bindsp-of-nth (l names) (i 2))
        (:instance ptx-g-bindsp-of-nth (l names) (i 3))
        (:instance ptx-g-bindsp-of-nth (l names) (i 4))
        (:instance ptx-g-symbolp-of-nth (l names) (i 0))
        (:instance ptx-g-symbolp-of-nth (l names) (i 1))
        (:instance ptx-g-symbolp-of-nth (l names) (i 2))
        (:instance ptx-g-symbolp-of-nth (l names) (i 3))
        (:instance ptx-g-symbolp-of-nth (l names) (i 4))
        (:instance crv-address-is-not-equal-gadget-complete
         (mx (nth 0 names)) (rx (nth 1 names)) (my (nth 2 names))
         (ry (nth 3 names)) (out (nth 4 names))))
  :in-theory (union-theories (theory 'minimal-theory)
                             '(values-edwards-bls12-pointp-when-groupp
                               (:e natp) (:e nfix))))

(defruled ptx-a-leaf-eq-complete-address
  (implies (and (equal (car wa) :address)
                (equal (car wb) :address)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-a-leaf-typed wa asg)
                (ptx-a-leaf-typed wb asg)
                (ptx-a-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-a-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance ptx-a-typed-facts (w wa))
        (:instance ptx-a-typed-facts (w wb))
        (:instance ptx-a-pt-coords (w wa))
        (:instance ptx-a-pt-coords (w wb))
        (:instance ptx-a-eq-complete-core
         (x1 (nth 0 (second wa))) (y1 (nth 1 (second wa)))
         (x2 (nth 0 (second wb))) (y2 (nth 1 (second wb)))
         (p1 (ptx-a-pt wa asg)) (p2 (ptx-a-pt wb asg))))
  :disable (ptx-a-pt nth ptx-a-vars ptx-a-shapep
                       ptx-a-typed-facts ptx-a-pt-coords
                       ptx-a-eq-complete-core crv-address-is-not-equal-gadget
                       group-is-equal-funspec))

(defruled ptx-a-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-a-leaf-typed wa asg)
                (ptx-a-leaf-typed wb asg)
                (ptx-a-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-a-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-a-leaf-eq-complete-address
        (:instance ptx-g-leaf-eq-complete)
        (:instance ptx-a-leaf-when-not-address (w wa))
        (:instance ptx-a-leaf-when-not-address (w wb))
        ptx-a-leaf-eq-when-not-address)
  :enable (lit-literal-equal-mismatch-complete ptx-a-leaf-eq-out-when-mismatch)
  :disable (lit-literal-equal-mismatch-gadget
            ptx-a-leaf-eq-gadget ptx-a-leaf-eq-witnessp ptx-a-leaf-typed
            ptx-a-leaf-val ptx-g-leaf-eq-gadget
            ptx-g-leaf-eq-witnessp ptx-g-leaf-typed
            ptx-g-leaf-val))

(in-theory (disable ptx-a-leaf-val ptx-a-leaf-typed ptx-a-leaf-variant
                    ptx-a-leaf-size ptx-a-leaf-bits-gadget ptx-a-leaf-bits-out
                    ptx-a-leaf-bits-witnessp ptx-a-leaf-new-gadget
                    ptx-a-leaf-new-vars ptx-a-leaf-new-witnessp
                    ptx-a-leaf-eq-gadget ptx-a-leaf-eq-out ptx-a-leaf-eq-nvars
                    ptx-a-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Plaintext / Entry theorems instantiated with the leaf covering
;; Boolean, Integer, Field, Scalar, Group and Address.

(ptx-gen-copy "PTX-A-")
(ptx-gen-instances "PTX-A-")
