; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value::is_equal / is_not_equal (snarkVM circuit/program/src/data/value/equal.rs):
; different variants give a constant; the same variant uses the arm's
; is_equal / is_not_equal.
(in-package "ALEOVM")

(include-book "rec-value")
(include-book "rec-future-eq")
(set-verify-guards-eagerness 0)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Value::is_equal (neq nil) / is_not_equal (neq t): (cons constraints
; output-term).  Different variants give the constant false (true); the
; same variant uses the arm's is_equal / is_not_equal.  ew lists the fresh
; wires of the pair:
;   plaintext:      the names of ptx-eq;
;   record:         (oe ne vm vr za zb zc names) of rec-record-eq;
;   future:         the names of rec-feq;
;   dynamic record: (omx orx omy ory oout rm rr z1 nmx nrx nmy nry nout z2
;                    vm vr z3) of DynamicRecord::is_equal (output z3, and
;                    1 - z3 for is_not_equal);
;   dynamic future: the 11 names of rec-dfeq.

(define rec-dreq-gadget (a b ew)
  (b* ((oga (rec-drw-og a)) (ogb (rec-drw-og b))
       (nga (rec-drw-ng a)) (ngb (rec-drw-ng b)))
    (rec-dynamic-record-is-equal-gadget
     (nth 0 oga) (nth 1 oga) (nth 0 ogb) (nth 1 ogb)
     (nth 0 ew) (nth 1 ew) (nth 2 ew) (nth 3 ew) (nth 4 ew)
     (rec-drw-rt a) (rec-drw-rt b) (nth 5 ew) (nth 6 ew) (nth 7 ew)
     (nth 0 nga) (nth 1 nga) (nth 0 ngb) (nth 1 ngb)
     (nth 8 ew) (nth 9 ew) (nth 10 ew) (nth 11 ew) (nth 12 ew)
     (nth 13 ew)
     (rec-drw-vbits a) (rec-drw-vbits b) (nth 14 ew) (nth 15 ew)
     (nth 16 ew))))

(define rec-veq (va vb neq ew)
  (b* ((a (cdr va)) (b (cdr vb)))
    (cond ((not (equal (car va) (car vb))) (cons nil (if neq 1 0)))
          ((eq (car va) :plaintext) (ptx-eq a b neq ew))
          ((eq (car va) :record)
           (rec-record-eq (rec-rw-pubp a) (rec-rw-og a) (rec-rw-data a)
                          (rec-rw-ng a) (rec-rw-vbits a)
                          (rec-rw-pubp b) (rec-rw-og b) (rec-rw-data b)
                          (rec-rw-ng b) (rec-rw-vbits b)
                          (nth 0 ew) (nth 1 ew) (nth 2 ew) (nth 3 ew)
                          (nth 4 ew) (nth 5 ew) (nth 6 ew) (nth 7 ew) neq))
          ((eq (car va) :future) (rec-feq a b neq ew))
          ((eq (car va) :dynamic-record)
           (cons (rec-dreq-gadget a b ew) (rec-bit-term neq (nth 16 ew))))
          (t (rec-dfeq a b neq ew)))))

(define rec-veq-hyps (va vb neq ew asg)
  :short "The arms' R1CS-SOUND-IF of is_equal: what each operand's Inject
          establishes (typed leaves, points on the curve, boolean version
          bits) and the fresh wires symbols bound in the assignment."
  (b* ((a (cdr va)) (b (cdr vb)))
    (case (car va)
      (:plaintext (and (ptx-typed a asg) (ptx-typed b asg) (symbol-listp ew)))
      (:record
       (and (booleanp neq)
            (rec-rbinds a asg) (rec-rbinds b asg)
            (symbol-listp (nth 0 ew)) (equal (len (nth 0 ew)) 5)
            (symbol-listp (nth 1 ew)) (equal (len (nth 1 ew)) 5)
            (symbolp (nth 2 ew)) (symbolp (nth 3 ew)) (symbolp (nth 4 ew))
            (symbolp (nth 5 ew)) (symbolp (nth 6 ew))
            (symbol-listp (nth 7 ew))
            (r1cs::valuation-binds-allp asg (nth 0 ew))
            (r1cs::valuation-binds-allp asg (nth 1 ew))
            (r1cs::valuation-binds-allp asg (list (nth 2 ew) (nth 3 ew) (nth 4 ew)
                                                  (nth 5 ew) (nth 6 ew)))
            (groupp (rec-point-of (rec-rw-og a) asg))
            (groupp (rec-point-of (rec-rw-og b) asg))
            (groupp (rec-point-of (rec-rw-ng a) asg))
            (groupp (rec-point-of (rec-rw-ng b) asg))
            (bit-listp (lookup-equal-list (rec-rw-vbits a) asg))
            (bit-listp (lookup-equal-list (rec-rw-vbits b) asg))
            (rec-record-data-typed (rec-rw-data a) asg)
            (rec-record-data-typed (rec-rw-data b) asg)))
      (:future (and (rec-ftyped a asg) (rec-ftyped b asg) (symbol-listp ew)
                    (rec-feq-namesp a b neq ew asg)))
      (:dynamic-record
       (and (symbol-listp ew) (<= 17 (len ew))
            (r1cs::valuation-binds-allp asg ew)
            (rec-drbinds a asg) (rec-drbinds b asg)
            (groupp (rec-point-of (rec-drw-og a) asg))
            (groupp (rec-point-of (rec-drw-og b) asg))
            (groupp (rec-point-of (rec-drw-ng a) asg))
            (groupp (rec-point-of (rec-drw-ng b) asg))
            (bit-listp (lookup-equal-list (rec-drw-vbits a) asg))
            (bit-listp (lookup-equal-list (rec-drw-vbits b) asg))))
      (otherwise (and (rec-dftyped a asg) (rec-dftyped b asg)
                      (rec-dfnamesp ew asg))))))

(defmacro rec-veq-concl ()
  '(equal (ptx-bval (cdr (rec-veq va vb neq ew)) asg p)
          (ptx-eq-spec neq (values-value-equalp (rec-vval va asg)
                                                (rec-vval vb asg)))))

(defmacro rec-veq-sound-hyps (kind)
  `(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal (car va) ,kind)
        (equal (car vb) ,kind)
        (rec-vwp va) (rec-vwp vb)
        (rec-veq-hyps va vb neq ew asg)
        (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew)) asg p)))

(defruled rec-veq-sound-kinds
  (implies (and (consp va) (consp vb)
                (not (equal (car va) (car vb)))
                (rec-vwp va) (rec-vwp vb))
           (rec-veq-concl))
  :do-not-induct t
  :enable (rec-veq rec-vwp rec-vval values-value-equalp ptx-bval
           values-bool-to-bit))

(defruled rec-veq-sound-ptx
  (implies (rec-veq-sound-hyps :plaintext) (rec-veq-concl))
  :do-not-induct t
  :enable (rec-veq rec-veq-hyps rec-vwp rec-vval values-value-equalp
           primep-of-base-prime)
  :use (:instance ptx-eq-sound (a (cdr va)) (b (cdr vb)) (names ew)))

(defruled rec-veq-sound-future
  (implies (rec-veq-sound-hyps :future) (rec-veq-concl))
  :do-not-induct t
  :enable (rec-veq rec-veq-hyps rec-vwp rec-vval values-value-equalp)
  :use (:instance rec-feq-sound (fa (cdr va)) (fb (cdr vb)) (names ew)))

(defruled rec-veq-sound-df
  (implies (rec-veq-sound-hyps :dynamic-future) (rec-veq-concl))
  :do-not-induct t
  :enable (rec-veq rec-veq-hyps rec-vwp rec-vval values-value-equalp)
  :use (:instance rec-dfeq-sound (da (cdr va)) (db (cdr vb)) (names ew)))

(defruled rec-veq-sound-record
  (implies (rec-veq-sound-hyps :record) (rec-veq-concl))
  :do-not-induct t
  :in-theory (e/d (rec-veq rec-veq-hyps rec-vwp rec-vval values-value-equalp
                   rec-rwp rec-rbinds rec-rval rec-vb-record-equalp)
                  (rec-record-eq crypto-record-is-equal crypto-record-is-not-equal
                   values-record-equalp))
  :use (:instance rec-record-eq-sound
                  (pa (rec-rw-pubp (cdr va))) (oga (rec-rw-og (cdr va)))
                  (da (rec-rw-data (cdr va))) (nga (rec-rw-ng (cdr va)))
                  (va (rec-rw-vbits (cdr va)))
                  (pb (rec-rw-pubp (cdr vb))) (ogb (rec-rw-og (cdr vb)))
                  (db (rec-rw-data (cdr vb))) (ngb (rec-rw-ng (cdr vb)))
                  (vb (rec-rw-vbits (cdr vb)))
                  (oe (nth 0 ew)) (ne (nth 1 ew)) (vm (nth 2 ew)) (vr (nth 3 ew))
                  (za (nth 4 ew)) (zb (nth 5 ew)) (zc (nth 6 ew))
                  (names (nth 7 ew))))

(defruled rec-drval-as-make
  (equal (rec-drval w asg)
         (rec-dynamic-record-make (rec-point-of (rec-drw-og w) asg)
                                  (rec-drw-rt w)
                                  (rec-point-of (rec-drw-ng w) asg)
                                  (rec-drw-vbits w) asg))
  :enable (rec-drval rec-dynamic-record-of-wires rec-dynamic-record-make
           rec-point-of))

(defruled rec-point-of-coords
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg (nth 0 g))
                (r1cs::valuation-bindsp asg (nth 1 g)))
           (and (equal (ecurve::point-finite->x (rec-point-of g asg))
                       (lookup-equal (nth 0 g) asg))
                (equal (ecurve::point-finite->y (rec-point-of g asg))
                       (lookup-equal (nth 1 g) asg))))
  :enable (rec-point-of r1cs::fep-of-lookup-equal primep-of-base-prime)
  :use ((:instance r1cs::fep-of-lookup-equal (var (nth 0 g)) (prime (base-prime))
                   (valuation asg))
        (:instance r1cs::fep-of-lookup-equal (var (nth 1 g)) (prime (base-prime))
                   (valuation asg))))

(defrule rec-dynamic-recordp-of-make
  (dynamic-recordp (rec-dynamic-record-make o ra n vs asg))
  :enable rec-dynamic-record-make)

(defruled rec-dreq-out
  (implies (and (symbolp z)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg z)
                (equal (lookup-equal z asg) (dynamic-record-is-equal a b)))
           (equal (ptx-bval (rec-bit-term neq z) asg (base-prime))
                  (ptx-eq-spec neq (equal (dynamic-record-is-equal a b) 1))))
  :enable (crypto-bit-not values-bool-to-bit dynamic-record-is-equal)
  :use (:instance rec-bit-term-val (negp neq)))

(defruled rec-veq-sound-dr
  (implies (rec-veq-sound-hyps :dynamic-record) (rec-veq-concl))
  :do-not-induct t
  :in-theory (e/d (rec-veq rec-veq-hyps rec-vwp rec-vval values-value-equalp
                   rec-drwp rec-drbinds rec-dreq-gadget rec-drval-as-make
                   rec-point-of-coords rec-valuation-bindsp-of-nth
                   r1cs::valuation-binds-allp curve-edwards-bls12-pointp-when-groupp
                   dynamic-record-is-not-equal values-b-not)
                  (rec-dynamic-record-is-equal-gadget rec-dynamic-record-make
                   rec-point-of dynamic-record-is-equal))
  :use ((:instance rec-dynamic-record-is-equal-sound
                  (ox1 (nth 0 (rec-drw-og (cdr va)))) (oy1 (nth 1 (rec-drw-og (cdr va))))
                  (ox2 (nth 0 (rec-drw-og (cdr vb)))) (oy2 (nth 1 (rec-drw-og (cdr vb))))
                  (omx (nth 0 ew)) (orx (nth 1 ew)) (omy (nth 2 ew)) (ory (nth 3 ew))
                  (oout (nth 4 ew))
                  (ra (rec-drw-rt (cdr va))) (rb (rec-drw-rt (cdr vb)))
                  (rm (nth 5 ew)) (rr (nth 6 ew)) (z1 (nth 7 ew))
                  (nx1 (nth 0 (rec-drw-ng (cdr va)))) (ny1 (nth 1 (rec-drw-ng (cdr va))))
                  (nx2 (nth 0 (rec-drw-ng (cdr vb)))) (ny2 (nth 1 (rec-drw-ng (cdr vb))))
                  (nmx (nth 8 ew)) (nrx (nth 9 ew)) (nmy (nth 10 ew)) (nry (nth 11 ew))
                  (nout (nth 12 ew)) (z2 (nth 13 ew))
                  (vas (rec-drw-vbits (cdr va))) (vbs (rec-drw-vbits (cdr vb)))
                  (vm (nth 14 ew)) (vr (nth 15 ew)) (z3 (nth 16 ew))
                  (p1 (rec-point-of (rec-drw-og (cdr va)) asg))
                  (p2 (rec-point-of (rec-drw-og (cdr vb)) asg))
                  (q1 (rec-point-of (rec-drw-ng (cdr va)) asg))
                  (q2 (rec-point-of (rec-drw-ng (cdr vb)) asg)))
        (:instance rec-dreq-out
                   (z (nth 16 ew))
                   (a (rec-dynamic-record-make (rec-point-of (rec-drw-og (cdr va)) asg)
                                               (rec-drw-rt (cdr va))
                                               (rec-point-of (rec-drw-ng (cdr va)) asg)
                                               (rec-drw-vbits (cdr va)) asg))
                   (b (rec-dynamic-record-make (rec-point-of (rec-drw-og (cdr vb)) asg)
                                               (rec-drw-rt (cdr vb))
                                               (rec-point-of (rec-drw-ng (cdr vb)) asg)
                                               (rec-drw-vbits (cdr vb)) asg)))))

(defruled rec-veq-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-vwp va) (rec-vwp vb)
                (or (not (equal (car va) (car vb)))
                    (rec-veq-hyps va vb neq ew asg))
                (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew)) asg p))
           (rec-veq-concl))
  :do-not-induct t
  :in-theory '(rec-vwp)
  :use (rec-veq-sound-kinds rec-veq-sound-ptx rec-veq-sound-record
        rec-veq-sound-future rec-veq-sound-dr rec-veq-sound-df))

(defruled rec-value-is-equal-sound
  :short "R1CS-SOUND of Value::is_equal."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-vwp va) (rec-vwp vb)
                (or (not (equal (car va) (car vb)))
                    (rec-veq-hyps va vb nil ew asg))
                (r1cs::r1cs-constraints-holdp (car (rec-veq va vb nil ew)) asg p))
           (equal (ptx-bval (cdr (rec-veq va vb nil ew)) asg p)
                  (value-is-equal (rec-vval va asg) (rec-vval vb asg))))
  :enable value-is-equal
  :use (:instance rec-veq-sound (neq nil)))

(defruled rec-value-is-not-equal-sound
  :short "R1CS-SOUND of Value::is_not_equal."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-vwp va) (rec-vwp vb)
                (or (not (equal (car va) (car vb)))
                    (rec-veq-hyps va vb t ew asg))
                (r1cs::r1cs-constraints-holdp (car (rec-veq va vb t ew)) asg p))
           (equal (ptx-bval (cdr (rec-veq va vb t ew)) asg p)
                  (value-is-not-equal (rec-vval va asg) (rec-vval vb asg))))
  :enable value-is-not-equal
  :use (:instance rec-veq-sound (neq t)))

(defruled rec-value-eq-gadget-arms
  :short "is_equal / is_not_equal add no constraint to the arm's: different
          variants emit none; otherwise the completeness is the arm's
          (ptx-eq-complete, rec-record-eq-complete, rec-feq-complete,
          rec-dynamic-record-is-equal-complete, rec-dfeq-complete)."
  (b* ((a (cdr va)) (b (cdr vb)))
    (equal (car (rec-veq va vb neq ew))
           (cond ((not (equal (car va) (car vb))) nil)
                 ((eq (car va) :plaintext) (car (ptx-eq a b neq ew)))
                 ((eq (car va) :record)
                  (car (rec-record-eq (rec-rw-pubp a) (rec-rw-og a) (rec-rw-data a)
                                      (rec-rw-ng a) (rec-rw-vbits a)
                                      (rec-rw-pubp b) (rec-rw-og b) (rec-rw-data b)
                                      (rec-rw-ng b) (rec-rw-vbits b)
                                      (nth 0 ew) (nth 1 ew) (nth 2 ew) (nth 3 ew)
                                      (nth 4 ew) (nth 5 ew) (nth 6 ew) (nth 7 ew)
                                      neq)))
                 ((eq (car va) :future) (car (rec-feq a b neq ew)))
                 ((eq (car va) :dynamic-record) (rec-dreq-gadget a b ew))
                 (t (car (rec-dfeq a b neq ew))))))
  :enable rec-veq)

(defruled rec-value-eq-complete
  :short "R1CS-COMPLETE of Value::is_equal / is_not_equal: different variants
          always satisfy the (empty) constraints; plaintexts, futures and
          dynamic futures with snarkVM's witnesses satisfy them."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-vwp va) (rec-vwp vb))
           (and (implies (not (equal (car va) (car vb)))
                         (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew))
                                                       asg p))
                (implies (and (equal (car va) :plaintext) (equal (car vb) :plaintext)
                              (rec-veq-hyps va vb neq ew asg)
                              (ptx-eq-witnessp (cdr va) (cdr vb) neq ew asg p))
                         (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew))
                                                       asg p))
                (implies (and (equal (car va) :future) (equal (car vb) :future)
                              (rec-veq-hyps va vb neq ew asg)
                              (rec-feq-witnessp (cdr va) (cdr vb) neq ew asg))
                         (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew))
                                                       asg p))
                (implies (and (equal (car va) :dynamic-future)
                              (equal (car vb) :dynamic-future)
                              (rec-veq-hyps va vb neq ew asg)
                              (rec-dfeq-witnessp (cdr va) (cdr vb) ew asg))
                         (r1cs::r1cs-constraints-holdp (car (rec-veq va vb neq ew))
                                                       asg p))))
  :do-not-induct t
  :enable (rec-veq rec-veq-hyps rec-vwp primep-of-base-prime)
  :use ((:instance ptx-eq-complete (a (cdr va)) (b (cdr vb)) (names ew))
        (:instance rec-feq-complete (fa (cdr va)) (fb (cdr vb)) (names ew))
        (:instance rec-dfeq-complete (da (cdr va)) (db (cdr vb)) (names ew))))
