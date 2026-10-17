; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::is_equal / is_not_equal and Entry::is_equal / is_not_equal
; over a leaf interface with the hypotheses the concrete Literal::is_equal
; circuits need: the prime is the base prime, the assignment is a
; valuation covering the gadget's fresh wires (names), and the public unit
; wire ptx-one holds 1 (the convention of the integer equality gadgets,
; whose one operand is Circuit::one()).  The circuit and the proofs are
; those of ptx-equal.lisp; that book's interface stays as it is, since
; rec-record-eq.lisp builds on it.

(in-package "ALEOVM")

(include-book "ptx-entry")

(set-verify-guards-eagerness 0)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-vprimep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

(local (defrule ptx-vbinds-allp-of-cdr
         (implies (r1cs::valuation-binds-allp asg x)
                  (r1cs::valuation-binds-allp asg (cdr x)))
         :enable r1cs::valuation-binds-allp))

(local (in-theory (enable ptx-plaintext-equalp-openers
                          ptx-members-equalp-openers
                          ptx-elements-equalp-openers
                          values-bool-to-bit)))

(defconst *ptx-veq-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-vleaf-eq-gadget * * * *) => *)
   ((ptx-vleaf-eq-out * * * *) => *)
   ((ptx-vleaf-eq-nvars * * *) => *)
   ((ptx-vleaf-eq-witnessp * * * * * *) => *))

  (local (defun ptx-vleaf-eq-gadget (wa wb neq names)
           (declare (ignore wa wb neq names))
           (list *ptx-veq-false-constraint*)))
  (local (defun ptx-vleaf-eq-out (wa wb neq names)
           (declare (ignore wa wb neq names))
           0))
  (local (defun ptx-vleaf-eq-nvars (wa wb neq)
           (declare (ignore wa wb neq))
           0))
  (local (defun ptx-vleaf-eq-witnessp (wa wb neq names asg p)
           (declare (ignore wa wb neq names asg p))
           nil))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defrule ptx-vnatp-of-leaf-eq-nvars
    (natp (ptx-vleaf-eq-nvars wa wb neq))
    :rule-classes :type-prescription)

  (defrule ptx-vsparse-vectorp-of-leaf-eq-out
    (r1cs::sparse-vectorp (and (consp (ptx-vleaf-eq-out wa wb neq names))
                               (ptx-vleaf-eq-out wa wb neq names))))

  (defruled ptx-vleaf-eq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-leaf-typed wa asg)
                  (ptx-leaf-typed wb asg)
                  (r1cs::r1cs-constraints-holdp
                   (ptx-vleaf-eq-gadget wa wb neq names) asg p))
             (equal (ptx-bval (ptx-vleaf-eq-out wa wb neq names) asg p)
                    (values-bool-to-bit
                     (if neq
                         (not (values-literal-equalp (ptx-leaf-val wa asg)
                                                     (ptx-leaf-val wb asg)))
                       (values-literal-equalp (ptx-leaf-val wa asg)
                                              (ptx-leaf-val wb asg))))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-vleaf-eq-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (ptx-leaf-typed wa asg)
                  (ptx-leaf-typed wb asg)
                  (ptx-vleaf-eq-witnessp wa wb neq names asg p))
             (r1cs::r1cs-constraints-holdp
              (ptx-vleaf-eq-gadget wa wb neq names) asg p))))

(define ptx-vkind (wt)
  :enabled t
  (case (car wt) (:struct :struct) (:array :array) (otherwise :lit)))

(defines ptx-veq-count
  :flag-local nil
  :short "The number of fresh names is_equal / is_not_equal takes."

  (define ptx-veq-count (a b neq)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-vkind a) (ptx-vkind b))) 0)
          ((not (equal (ptx-vkind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-vkind a) :struct)
                   (ptx-vmeq-count (cdr a) (cdr b) neq)
                 (ptx-vleq-count (cdr a) (cdr b) neq))
             0))
          (t (ptx-vleaf-eq-nvars (cdr a) (cdr b) neq))))

  (define ptx-vmeq-count (ams bms neq)
    :measure (acl2-count ams)
    (if (or (atom ams) (atom bms))
        0
      (+ (ptx-veq-count (cdr (car ams)) (cdr (car bms)) neq)
         1
         (ptx-vmeq-count (cdr ams) (cdr bms) neq))))

  (define ptx-vleq-count (aes bes neq)
    :measure (acl2-count aes)
    (if (or (atom aes) (atom bes))
        0
      (+ (ptx-veq-count (car aes) (car bes) neq)
         1
         (ptx-vleq-count (cdr aes) (cdr bes) neq)))))

(defrule ptx-vnatp-of-eq-count
  (natp (ptx-veq-count a b neq))
  :rule-classes :type-prescription
  :expand ((ptx-veq-count a b neq)))

(defines ptx-veq
  :flag-local nil
  :short "Plaintext::is_equal (neq nil) / is_not_equal (neq t):
          (cons constraints output)."

  (define ptx-veq (a b neq names)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-vkind a) (ptx-vkind b))) (cons nil (if neq 1 0)))
          ((not (equal (ptx-vkind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-vkind a) :struct)
                   (ptx-vmeq (cdr a) (cdr b) neq (if neq 0 1) names)
                 (ptx-vleq (cdr a) (cdr b) neq (if neq 0 1) names))
             (cons nil (if neq 1 0))))
          (t (cons (ptx-vleaf-eq-gadget (cdr a) (cdr b) neq names)
                   (ptx-vleaf-eq-out (cdr a) (cdr b) neq names)))))

  (define ptx-vmeq (ams bms neq acc names)
    :measure (acl2-count ams)
    (b* (((when (or (atom ams) (atom bms))) (cons nil acc))
         (r1 (ptx-bop neq acc (ptx-name-bit (car (car ams)) (car (car bms)) neq)
                      nil))
         (sub (ptx-veq (cdr (car ams)) (cdr (car bms)) neq names))
         (k (ptx-veq-count (cdr (car ams)) (cdr (car bms)) neq))
         (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names)))
         (rest (ptx-vmeq (cdr ams) (cdr bms) neq (cdr r2) (nthcdr (1+ k) names))))
      (cons (append (car r1) (car sub) (car r2) (car rest))
            (cdr rest))))

  (define ptx-vleq (aes bes neq acc names)
    :measure (acl2-count aes)
    (b* (((when (or (atom aes) (atom bes))) (cons nil acc))
         (sub (ptx-veq (car aes) (car bes) neq names))
         (k (ptx-veq-count (car aes) (car bes) neq))
         (r (ptx-bop neq acc (cdr sub) (nth k names)))
         (rest (ptx-vleq (cdr aes) (cdr bes) neq (cdr r) (nthcdr (1+ k) names))))
      (cons (append (car sub) (car r) (car rest))
            (cdr rest)))))

(defines ptx-veq-witnessp
  :flag-local nil
  :short "Each leaf carries its Literal::is_equal witness and each
          non-folded AND / OR variable holds its value."

  (define ptx-veq-witnessp (a b neq names asg p)
    :measure (acl2-count a)
    (cond ((not (equal (ptx-vkind a) (ptx-vkind b))) t)
          ((not (equal (ptx-vkind a) :lit))
           (if (equal (len (cdr a)) (len (cdr b)))
               (if (equal (ptx-vkind a) :struct)
                   (ptx-vmeq-witnessp (cdr a) (cdr b) neq (if neq 0 1) names asg p)
                 (ptx-vleq-witnessp (cdr a) (cdr b) neq (if neq 0 1) names asg p))
             t))
          (t (and (ptx-vleaf-eq-witnessp (cdr a) (cdr b) neq names asg p) t))))

  (define ptx-vmeq-witnessp (ams bms neq acc names asg p)
    :measure (acl2-count ams)
    (b* (((when (or (atom ams) (atom bms))) t)
         (r1 (ptx-bop neq acc (ptx-name-bit (car (car ams)) (car (car bms)) neq)
                      nil))
         (sub (ptx-veq (cdr (car ams)) (cdr (car bms)) neq names))
         (k (ptx-veq-count (cdr (car ams)) (cdr (car bms)) neq))
         (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names))))
      (and (ptx-veq-witnessp (cdr (car ams)) (cdr (car bms)) neq names asg p)
           (ptx-bop-witnessp neq (cdr r1) (cdr sub) (nth k names) asg p)
           (ptx-vmeq-witnessp (cdr ams) (cdr bms) neq (cdr r2)
                             (nthcdr (1+ k) names) asg p))))

  (define ptx-vleq-witnessp (aes bes neq acc names asg p)
    :measure (acl2-count aes)
    (b* (((when (or (atom aes) (atom bes))) t)
         (sub (ptx-veq (car aes) (car bes) neq names))
         (k (ptx-veq-count (car aes) (car bes) neq))
         (r (ptx-bop neq acc (cdr sub) (nth k names))))
      (and (ptx-veq-witnessp (car aes) (car bes) neq names asg p)
           (ptx-bop-witnessp neq acc (cdr sub) (nth k names) asg p)
           (ptx-vleq-witnessp (cdr aes) (cdr bes) neq (cdr r)
                             (nthcdr (1+ k) names) asg p)))))


(defrule ptx-vblcp-of-leaf-eq-out
  (ptx-blcp (ptx-vleaf-eq-out wa wb neq names))
  :use ptx-vsparse-vectorp-of-leaf-eq-out
  :enable ptx-blcp
  :disable ptx-vsparse-vectorp-of-leaf-eq-out)




(defthm-ptx-veq-flag
  (defthm ptx-vblcp-of-eq
    (implies (symbol-listp names)
             (ptx-blcp (cdr (ptx-veq a b neq names))))
    :flag ptx-veq)
  (defthm ptx-vblcp-of-meq
    (implies (and (symbol-listp names) (ptx-blcp acc))
             (ptx-blcp (cdr (ptx-vmeq ams bms neq acc names))))
    :flag ptx-vmeq)
  (defthm ptx-vblcp-of-leq
    (implies (and (symbol-listp names) (ptx-blcp acc))
             (ptx-blcp (cdr (ptx-vleq aes bes neq acc names))))
    :flag ptx-vleq)
  :hints (("Goal"
           :in-theory (disable ptx-name-bit ptx-bop)
           :expand ((:free (neq) (ptx-veq a b neq names))
                    (:free (neq acc) (ptx-vmeq ams bms neq acc names))
                    (:free (neq acc) (ptx-vleq aes bes neq acc names))))))


(defthm-ptx-veq-flag
  (defthm ptx-veq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                                    (ptx-typed a asg)
                  (ptx-typed b asg)
                  (r1cs::r1cs-constraints-holdp (car (ptx-veq a b neq names)) asg p))
             (and (equal (ptx-bval (cdr (ptx-veq a b neq names)) asg p)
                         (ptx-eq-spec neq (values-plaintext-equalp
                                           (ptx-val a asg) (ptx-val b asg))))))
    :flag ptx-veq)
  (defthm ptx-vmeq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                                    (ptx-mtyped ams asg)
                  (ptx-mtyped bms asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car (ptx-vmeq ams bms neq acc names))
                                                asg p))
             (and (equal (ptx-bval (cdr (ptx-vmeq ams bms neq acc names)) asg p)
                         (ptx-bop-spec neq (ptx-bval acc asg p)
                                       (ptx-eq-spec neq
                                                    (values-plaintext-members-equalp
                                                     (ptx-mval ams asg)
                                                     (ptx-mval bms asg)))))))
    :flag ptx-vmeq)
  (defthm ptx-vleq-sound
    (implies (and (primep p)
                  (symbol-listp names)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                                    (ptx-ltyped aes asg)
                  (ptx-ltyped bes asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car (ptx-vleq aes bes neq acc names))
                                                asg p))
             (and (equal (ptx-bval (cdr (ptx-vleq aes bes neq acc names)) asg p)
                         (ptx-bop-spec neq (ptx-bval acc asg p)
                                       (ptx-eq-spec neq
                                                    (values-plaintext-elements-equalp
                                                     (ptx-lval aes asg)
                                                     (ptx-lval bes asg)))))))
    :flag ptx-vleq)
  :hints (("Goal"
           :in-theory (e/d (ptx-vleaf-eq-sound ptx-bop-spec bitand bitor ptx-name-bit)
                            (ptx-bop))
           :expand ((:free (neq) (ptx-veq a b neq names))
                    (:free (neq acc) (ptx-vmeq ams bms neq acc names))
                    (:free (neq acc) (ptx-vleq aes bes neq acc names))
                    (ptx-typed a asg) (ptx-typed b asg)
                    (ptx-mtyped ams asg) (ptx-mtyped bms asg)
                    (ptx-ltyped aes asg) (ptx-ltyped bes asg)
                    (ptx-val a asg) (ptx-val b asg)
                    (ptx-mval ams asg) (ptx-mval bms asg)
                    (ptx-lval aes asg) (ptx-lval bes asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defthm-ptx-veq-flag
  (defthm ptx-veq-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-typed a asg)
                  (ptx-typed b asg)
                  (ptx-veq-witnessp a b neq names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-veq a b neq names)) asg p))
    :flag ptx-veq)
  (defthm ptx-vmeq-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-mtyped ams asg)
                  (ptx-mtyped bms asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (ptx-vmeq-witnessp ams bms neq acc names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-vmeq ams bms neq acc names))
                                           asg p))
    :flag ptx-vmeq)
  (defthm ptx-vleq-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (r1cs::valuation-binds-allp asg names)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-ltyped aes asg)
                  (ptx-ltyped bes asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (ptx-vleq-witnessp aes bes neq acc names asg p))
             (r1cs::r1cs-constraints-holdp (car (ptx-vleq aes bes neq acc names))
                                           asg p))
    :flag ptx-vleq)
  :hints (("Goal"
           :in-theory (e/d (ptx-vleaf-eq-complete ptx-name-bit)
                           (ptx-bop ptx-bop-witnessp))
           :expand ((:free (neq) (ptx-veq a b neq names))
                    (:free (neq acc) (ptx-vmeq ams bms neq acc names))
                    (:free (neq acc) (ptx-vleq aes bes neq acc names))
                    (:free (neq p) (ptx-veq-witnessp a b neq names asg p))
                    (:free (neq acc p) (ptx-vmeq-witnessp ams bms neq acc names asg p))
                    (:free (neq acc p) (ptx-vleq-witnessp aes bes neq acc names asg p))
                    (ptx-typed a asg) (ptx-typed b asg)
                    (ptx-mtyped ams asg) (ptx-mtyped bms asg)
                    (ptx-ltyped aes asg) (ptx-ltyped bes asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::is_equal / is_not_equal.

(define ptx-ventry-eq (ea eb neq names)
  (if (equal (car ea) (car eb))
      (ptx-veq (cdr ea) (cdr eb) neq names)
    (cons nil (if neq 1 0))))

(define ptx-ventry-eq-witnessp (ea eb neq names asg p)
  (or (not (equal (car ea) (car eb)))
      (ptx-veq-witnessp (cdr ea) (cdr eb) neq names asg p)))

(defruled ptx-ventry-eq-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ea)
                (ptx-ewtp eb)
                (ptx-typed (cdr ea) asg)
                (ptx-typed (cdr eb) asg)
                (r1cs::r1cs-constraints-holdp (car (ptx-ventry-eq ea eb neq names))
                                              asg p))
           (equal (ptx-bval (cdr (ptx-ventry-eq ea eb neq names)) asg p)
                  (if neq
                      (entry-is-not-equal (ptx-eval ea asg) (ptx-eval eb asg))
                    (entry-is-equal (ptx-eval ea asg) (ptx-eval eb asg)))))
  :use ((:instance ptx-veq-sound (a (cdr ea)) (b (cdr eb)))
        (:instance ptx-entry-kind-of-wrap (ew ea) (pt (ptx-val (cdr ea) asg)))
        (:instance ptx-entry-kind-of-wrap (ew eb) (pt (ptx-val (cdr eb) asg)))
        primep-of-base-prime)
  :enable (ptx-ventry-eq entry-is-equal entry-is-not-equal values-entry-equalp
                         values-bool-to-bit ptx-eval ptx-entry-plaintext-of-wrap))

(defruled ptx-ventry-eq-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-typed (cdr ea) asg)
                (ptx-typed (cdr eb) asg)
                (ptx-ventry-eq-witnessp ea eb neq names asg p))
           (r1cs::r1cs-constraints-holdp (car (ptx-ventry-eq ea eb neq names))
                                         asg p))
  :use ((:instance ptx-veq-complete (a (cdr ea)) (b (cdr eb)))
        primep-of-base-prime)
  :enable (ptx-ventry-eq ptx-ventry-eq-witnessp))
