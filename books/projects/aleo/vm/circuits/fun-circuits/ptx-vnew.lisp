; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::new and Entry::new over a leaf interface with the hypotheses
; the concrete Literal::new theorems (literal-new-r1cs.lisp) need: the
; prime is the base prime, the assignment is a valuation, and it covers
; the gadget's wires (ptx-vnew-vars).  The tree and the proofs are those
; of ptx-new.lisp; that book's weaker interface stays as it is, since
; rec-record.lisp builds on it.

(in-package "ALEOVM")

(include-book "ptx-entry")

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (disable (:e base-prime))))

(defconst *ptx-vnew-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-vleaf-new-gadget *) => *)
   ((ptx-vleaf-new-vars *) => *)
   ((ptx-vleaf-new-witnessp * * * *) => *))

  (local (defun ptx-vleaf-new-gadget (w)
           (declare (ignore w))
           (list *ptx-vnew-false-constraint*)))
  (local (defun ptx-vleaf-new-vars (w)
           (declare (ignore w))
           nil))
  (local (defun ptx-vleaf-new-witnessp (w x asg p)
           (declare (ignore w x asg p))
           nil))

  (local (in-theory (disable (:e base-prime))))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defrule ptx-symbol-listp-of-vleaf-new-vars
    (symbol-listp (ptx-vleaf-new-vars w)))

  (defruled ptx-vleaf-new-sound
    (implies (and (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg (ptx-vleaf-new-vars w))
                  (r1cs::r1cs-constraints-holdp (ptx-vleaf-new-gadget w) asg p))
             (and (ptx-leaf-typed w asg)
                  (equal (literal-new (ptx-leaf-val w asg))
                         (ptx-leaf-val w asg))))
    :use primep-of-base-prime
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-vleaf-new-complete
    (implies (and (equal p (base-prime))
                  (ptx-vleaf-new-witnessp w x asg p)
                  (not (reserrp (literal-new x))))
             (and (r1cs::r1cs-constraints-holdp (ptx-vleaf-new-gadget w) asg p)
                  (equal (ptx-leaf-val w asg) (literal-new x)))))

  (defruled ptx-vleaf-new-error
    (implies (and (equal p (base-prime))
                  (ptx-vleaf-new-witnessp w x asg p)
                  (reserrp (literal-new x)))
             (not (r1cs::r1cs-constraints-holdp (ptx-vleaf-new-gadget w)
                                                asg p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ptx-vnew-gadget
  :flag-local nil
  (define ptx-vnew-gadget (wt)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-vmnew-gadget (cdr wt)))
      (:array (ptx-vlnew-gadget (cdr wt)))
      (otherwise (ptx-vleaf-new-gadget (cdr wt)))))
  (define ptx-vmnew-gadget (wms)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-vnew-gadget (cdr (car wms)))
              (ptx-vmnew-gadget (cdr wms)))))
  (define ptx-vlnew-gadget (wts)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-vnew-gadget (car wts))
              (ptx-vlnew-gadget (cdr wts))))))

(defines ptx-vnew-vars
  :flag-local nil
  :short "The wires of the Literal::new gadgets, in tree order."
  (define ptx-vnew-vars (wt)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-vmnew-vars (cdr wt)))
      (:array (ptx-vlnew-vars (cdr wt)))
      (otherwise (ptx-vleaf-new-vars (cdr wt)))))
  (define ptx-vmnew-vars (wms)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-vnew-vars (cdr (car wms)))
              (ptx-vmnew-vars (cdr wms)))))
  (define ptx-vlnew-vars (wts)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-vnew-vars (car wts))
              (ptx-vlnew-vars (cdr wts))))))

(defines ptx-vnew-witnessp
  :flag-local nil
  (define ptx-vnew-witnessp (wt pt asg p)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (and (plaintext-case pt :struct)
                    (ptx-vmnew-witnessp (cdr wt) (plaintext-struct->members pt)
                                        asg p)))
      (:array (and (plaintext-case pt :array)
                   (ptx-vlnew-witnessp (cdr wt) (plaintext-array->elements pt)
                                       asg p)))
      (otherwise (and (plaintext-case pt :literal)
                      (ptx-vleaf-new-witnessp (cdr wt)
                                              (plaintext-literal->get pt)
                                              asg p)
                      t))))
  (define ptx-vmnew-witnessp (wms ms asg p)
    :measure (acl2-count wms)
    (if (atom wms)
        (atom ms)
      (and (consp ms)
           (equal (identifier-fix (car (car wms)))
                  (plaintext-member->name (car ms)))
           (ptx-vnew-witnessp (cdr (car wms))
                              (plaintext-member->value (car ms))
                              asg p)
           (ptx-vmnew-witnessp (cdr wms) (cdr ms) asg p))))
  (define ptx-vlnew-witnessp (wts es asg p)
    :measure (acl2-count wts)
    (if (atom wts)
        (atom es)
      (and (consp es)
           (ptx-vnew-witnessp (car wts) (car es) asg p)
           (ptx-vlnew-witnessp (cdr wts) (cdr es) asg p)))))

(local (in-theory (enable ptx-plaintext-new-of-literal
                          ptx-plaintext-new-of-struct
                          ptx-plaintext-new-of-array
                          ptx-elements-new-of-cons
                          ptx-elements-new-of-nil
                          ptx-members-new-of-nil
                          ptx-members-new-of-cons-nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-ptx-vnew-gadget-flag
  (defthm ptx-vnew-gadget-sound-lemma
    (implies (and (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg (ptx-vnew-vars wt))
                  (ptx-distinct (ptx-val wt asg))
                  (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p))
             (and (ptx-typed wt asg)
                  (equal (plaintext-new (ptx-val wt asg))
                         (ptx-val wt asg))))
    :flag ptx-vnew-gadget)
  (defthm ptx-vmnew-gadget-sound-lemma
    (implies (and (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg (ptx-vmnew-vars wms))
                  (no-duplicatesp-equal (ptx-member-fields (ptx-mval wms asg)))
                  (ptx-mdistinct (ptx-mval wms asg))
                  (r1cs::r1cs-constraints-holdp (ptx-vmnew-gadget wms) asg p))
             (and (ptx-mtyped wms asg)
                  (equal (values-plaintext-members-new (ptx-mval wms asg) nil)
                         (ptx-mval wms asg))))
    :flag ptx-vmnew-gadget)
  (defthm ptx-vlnew-gadget-sound-lemma
    (implies (and (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-binds-allp asg (ptx-vlnew-vars wts))
                  (ptx-ldistinct (ptx-lval wts asg))
                  (r1cs::r1cs-constraints-holdp (ptx-vlnew-gadget wts) asg p))
             (and (ptx-ltyped wts asg)
                  (equal (values-plaintext-elements-new (ptx-lval wts asg))
                         (ptx-lval wts asg))))
    :flag ptx-vlnew-gadget)
  :hints (("Goal"
           :in-theory (enable ptx-vleaf-new-sound ptx-member-fields)
           :expand ((ptx-wms-fields wms)
                    (ptx-vnew-gadget wt)
                    (ptx-vmnew-gadget wms)
                    (ptx-vlnew-gadget wts)
                    (ptx-vnew-vars wt)
                    (ptx-vmnew-vars wms)
                    (ptx-vlnew-vars wts)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)
                    (:free (x) (ptx-distinct (plaintext-literal x)))
                    (:free (x) (ptx-distinct (plaintext-struct x)))
                    (:free (x) (ptx-distinct (plaintext-array x)))
                    (:free (x y) (ptx-mdistinct (cons x y)))
                    (:free (x y) (ptx-ldistinct (cons x y)))))))

(defruled ptx-vnew-sound
  :short "R1CS-SOUND of Plaintext::new on a valuation covering the
          Literal::new wires."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-vnew-vars wt))
                (ptx-wtp wt)
                (ptx-distinct (ptx-val wt asg))
                (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p))
           (and (ptx-typed wt asg)
                (plaintextp (ptx-val wt asg))
                (equal (plaintext-new (ptx-val wt asg))
                       (ptx-val wt asg)))))

(defruled ptx-vleaf-new-val-when-holds
  (implies (and (equal p (base-prime))
                (ptx-vleaf-new-witnessp w x asg p)
                (r1cs::r1cs-constraints-holdp (ptx-vleaf-new-gadget w) asg p))
           (and (not (reserrp (literal-new x)))
                (equal (ptx-leaf-val w asg) (literal-new x))))
  :use (ptx-vleaf-new-error ptx-vleaf-new-complete))

(defruled ptx-wms-fields-when-vwitnessp
  (implies (ptx-vmnew-witnessp wms ms asg p)
           (equal (ptx-wms-fields wms)
                  (ptx-member-fields ms)))
  :induct (ind wms ms)
  :expand ((ptx-vmnew-witnessp wms ms asg p)
           (ptx-wms-fields wms)
           (ptx-member-fields ms))
  :prep-lemmas
  ((defun ind (x y)
     (if (atom x) y (ind (cdr x) (cdr y))))))

(defrule ptx-vmnew-witnessp-when-atom-ms
  (implies (and (consp wms) (atom ms))
           (not (ptx-vmnew-witnessp wms ms asg p)))
  :expand ((ptx-vmnew-witnessp wms ms asg p)))

(defrule ptx-vlnew-witnessp-when-atom-es
  (implies (and (consp wts) (atom es))
           (not (ptx-vlnew-witnessp wts es asg p)))
  :expand ((ptx-vlnew-witnessp wts es asg p)))

(defthm-ptx-vnew-witnessp-flag
  (defthm ptx-vnew-gadget-complete-lemma
    (implies (and (equal p (base-prime))
                  (plaintextp pt)
                  (ptx-distinct pt)
                  (ptx-vnew-witnessp wt pt asg p))
             (if (reserrp (plaintext-new pt))
                 (not (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p)
                    (equal (ptx-val wt asg) (plaintext-new pt)))))
    :flag ptx-vnew-witnessp)
  (defthm ptx-vmnew-gadget-complete-lemma
    (implies (and (equal p (base-prime))
                  (plaintext-member-listp ms)
                  (no-duplicatesp-equal (ptx-member-fields ms))
                  (ptx-mdistinct ms)
                  (ptx-vmnew-witnessp wms ms asg p))
             (if (reserrp (values-plaintext-members-new ms nil))
                 (not (r1cs::r1cs-constraints-holdp (ptx-vmnew-gadget wms) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-vmnew-gadget wms) asg p)
                    (equal (ptx-mval wms asg)
                           (values-plaintext-members-new ms nil)))))
    :flag ptx-vmnew-witnessp)
  (defthm ptx-vlnew-gadget-complete-lemma
    (implies (and (equal p (base-prime))
                  (plaintext-listp es)
                  (ptx-ldistinct es)
                  (ptx-vlnew-witnessp wts es asg p))
             (if (reserrp (values-plaintext-elements-new es))
                 (not (r1cs::r1cs-constraints-holdp (ptx-vlnew-gadget wts) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-vlnew-gadget wts) asg p)
                    (equal (ptx-lval wts asg)
                           (values-plaintext-elements-new es)))))
    :flag ptx-vlnew-witnessp)
  :hints (("Goal"
           :in-theory (enable ptx-vleaf-new-complete ptx-vleaf-new-error
                              ptx-vleaf-new-val-when-holds
                              ptx-wms-fields-when-vwitnessp)
           :expand ((ptx-vnew-gadget wt)
                    (ptx-vmnew-gadget wms)
                    (ptx-vlnew-gadget wts)
                    (:free (p) (ptx-vnew-witnessp wt pt asg p))
                    (:free (p) (ptx-vmnew-witnessp wms ms asg p))
                    (:free (p) (ptx-vlnew-witnessp wts es asg p))
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)
                    (ptx-distinct pt)
                    (ptx-mdistinct ms)
                    (ptx-ldistinct es)
                    (ptx-member-fields ms)
                    (plaintext-new pt)
                    (values-plaintext-elements-new es)))))

(defruled ptx-vnew-complete
  :short "R1CS-COMPLETE of Plaintext::new."
  (implies (and (equal p (base-prime))
                (ptx-wtp wt)
                (plaintextp pt)
                (ptx-distinct pt)
                (ptx-vnew-witnessp wt pt asg p))
           (if (reserrp (plaintext-new pt))
               (not (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p))
             (and (r1cs::r1cs-constraints-holdp (ptx-vnew-gadget wt) asg p)
                  (equal (ptx-val wt asg) (plaintext-new pt)))))
  :use ptx-vnew-gadget-complete-lemma)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::new.

(define ptx-ventry-new-gadget (ew)
  (ptx-vnew-gadget (cdr ew)))

(define ptx-ventry-new-vars (ew)
  (ptx-vnew-vars (cdr ew)))

(defruled ptx-ventry-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-ventry-new-vars ew))
                (ptx-ewtp ew)
                (ptx-distinct (ptx-val (cdr ew) asg))
                (r1cs::r1cs-constraints-holdp (ptx-ventry-new-gadget ew) asg p))
           (and (ptx-typed (cdr ew) asg)
                (equal (entry-new (ptx-eval ew asg))
                       (ptx-eval ew asg))))
  :use ((:instance ptx-vnew-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-new-gadget ptx-ventry-new-vars
                    ptx-entry-new-of-wrap ptx-eval))

(defruled ptx-ventry-new-complete
  (implies (and (equal p (base-prime))
                (ptx-ewtp ew)
                (plaintextp pt)
                (ptx-distinct pt)
                (ptx-vnew-witnessp (cdr ew) pt asg p))
           (if (reserrp (plaintext-new pt))
               (not (r1cs::r1cs-constraints-holdp (ptx-ventry-new-gadget ew) asg p))
             (and (r1cs::r1cs-constraints-holdp (ptx-ventry-new-gadget ew) asg p)
                  (equal (ptx-eval ew asg)
                         (entry-new (ptx-entry-wrap (car ew) pt))))))
  :use ((:instance ptx-vnew-complete (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-new-gadget ptx-entry-new-of-wrap ptx-eval))
