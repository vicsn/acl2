; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::new (Inject; snarkVM circuit/program/src/data/plaintext/mod.rs),
; by induction over the wire tree of ptx-tree.lisp.
;
; Plaintext::new runs Literal::new on each literal, injects each member
; name with Identifier::constant (no wire, no constraint), and collects the
; members into an IndexMap in the order of the console IndexMap.  The
; constraints are those of Literal::new on each leaf, in tree order.
;
; The leaf circuit is abstract (ptx-leaf-new-*), with exactly the
; properties the per-arm Literal::new theorems of literal-new-r1cs.lisp
; establish: a satisfying assignment gives a typed leaf whose literal is a
; fixed point of literal-new; the leaf witness of a literal x satisfies the
; constraints and denotes (literal-new x) when that succeeds, and no
; assignment carrying x satisfies them when it fails.
;
; Member names: a console IndexMap has distinct keys, so the input
; plaintext has distinct member names in each struct (ptx-distinct).  On
; such inputs the funspec's insertion is an append.  The output tree has
; the same constant names, so ptx-distinct of the output value is a
; synthesis-time fact; the soundness theorem takes it as a hypothesis.

(in-package "ALEOVM")

(include-book "ptx-tree")

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "std/lists/intersectp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf interface: Literal::new.

(defconst *ptx-new-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-leaf-new-gadget *) => *)
   ((ptx-leaf-new-witnessp * * * *) => *))

  (local (defun ptx-leaf-new-gadget (w)
           (declare (ignore w))
           (list *ptx-new-false-constraint*)))
  (local (defun ptx-leaf-new-witnessp (w x asg p)
           (declare (ignore w x asg p))
           nil))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defruled ptx-leaf-new-sound
    (implies (and (primep p)
                  (r1cs::r1cs-constraints-holdp (ptx-leaf-new-gadget w) asg p))
             (and (ptx-leaf-typed w asg)
                  (equal (literal-new (ptx-leaf-val w asg))
                         (ptx-leaf-val w asg))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-leaf-new-complete
    (implies (and (primep p)
                  (ptx-leaf-new-witnessp w x asg p)
                  (not (reserrp (literal-new x))))
             (and (r1cs::r1cs-constraints-holdp (ptx-leaf-new-gadget w) asg p)
                  (equal (ptx-leaf-val w asg) (literal-new x)))))

  (defruled ptx-leaf-new-error
    (implies (and (primep p)
                  (ptx-leaf-new-witnessp w x asg p)
                  (reserrp (literal-new x)))
             (not (r1cs::r1cs-constraints-holdp (ptx-leaf-new-gadget w)
                                                asg p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Distinct member names.

(define ptx-member-fields ((ms plaintext-member-listp))
  (if (endp ms)
      nil
    (cons (identifier->field (plaintext-member->name (car ms)))
          (ptx-member-fields (cdr ms))))
  ///
  (defrule ptx-member-fields-of-append
    (equal (ptx-member-fields (append xs ys))
           (append (ptx-member-fields xs) (ptx-member-fields ys))))
  (defrule ptx-member-fields-of-plaintext-member-list-fix
    (equal (ptx-member-fields (plaintext-member-list-fix ms))
           (ptx-member-fields ms))
    :enable plaintext-member-list-fix))

(defines ptx-distinct
  :flag-local nil
  :short "Each struct has member names with distinct fields
          (the console IndexMap invariant)."

  (define ptx-distinct ((pt plaintextp))
    :measure (plaintext-count pt)
    (plaintext-case
     pt
     :literal t
     :struct (and (no-duplicatesp-equal (ptx-member-fields pt.members))
                  (ptx-mdistinct pt.members))
     :array (ptx-ldistinct pt.elements)))

  (define ptx-mdistinct ((ms plaintext-member-listp))
    :measure (plaintext-member-list-count ms)
    (if (endp ms)
        t
      (and (ptx-distinct (plaintext-member->value (car ms)))
           (ptx-mdistinct (cdr ms)))))

  (define ptx-ldistinct ((es plaintext-listp))
    :measure (plaintext-list-count es)
    (if (endp es)
        t
      (and (ptx-distinct (car es))
           (ptx-ldistinct (cdr es))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The funspec on distinct names.

(defruled ptx-members-insert-when-fresh
  (implies (not (member-equal (identifier->field name)
                              (ptx-member-fields acc)))
           (equal (values-plaintext-members-insert name value acc)
                  (append (plaintext-member-list-fix acc)
                          (list (make-plaintext-member :name name
                                                       :value value)))))
  :induct (len acc)
  :expand ((values-plaintext-members-insert name value acc)
           (ptx-member-fields acc)
           (plaintext-member-list-fix acc)))

(define ptx-mnew-map ((ms plaintext-member-listp))
  :short "The members with each value injected, or the first error."
  (b* (((when (endp ms)) nil)
       (v (plaintext-new (plaintext-member->value (car ms))))
       ((when (reserrp v)) v)
       (r (ptx-mnew-map (cdr ms)))
       ((when (reserrp r)) r))
    (cons (make-plaintext-member :name (plaintext-member->name (car ms))
                                 :value v)
          r))
  ///
  (defrule ptx-member-list-p-of-mnew-map
    (implies (not (reserrp (ptx-mnew-map ms)))
             (plaintext-member-listp (ptx-mnew-map ms)))))

(local
 (defun ptx-mnew-ind (ms acc)
   (if (endp ms)
       acc
     (ptx-mnew-ind (cdr ms)
                   (values-plaintext-members-insert
                    (plaintext-member->name (car ms))
                    (plaintext-new (plaintext-member->value (car ms)))
                    acc)))))

(defruled ptx-members-new-of-acc
  (implies (and (no-duplicatesp-equal (ptx-member-fields ms))
                (not (intersectp-equal (ptx-member-fields acc)
                                       (ptx-member-fields ms))))
           (equal (values-plaintext-members-new ms acc)
                  (b* ((r (ptx-mnew-map ms)))
                    (if (reserrp r)
                        r
                      (append (plaintext-member-list-fix acc) r)))))
  :induct (ptx-mnew-ind ms acc)
  :expand ((values-plaintext-members-new ms acc)
           (ptx-mnew-map ms)
           (ptx-member-fields ms))
  :enable (ptx-members-insert-when-fresh ptx-member-fields))

(defruled ptx-members-new-of-nil-is-map
  (implies (no-duplicatesp-equal (ptx-member-fields ms))
           (equal (values-plaintext-members-new ms nil)
                  (ptx-mnew-map ms)))
  :use ((:instance ptx-members-new-of-acc (acc nil)))
  :expand ((ptx-member-fields nil)))

(defruled ptx-members-new-of-cons-nil
  (implies (and (consp ms)
                (no-duplicatesp-equal (ptx-member-fields ms)))
           (equal (values-plaintext-members-new ms nil)
                  (b* ((v (plaintext-new (plaintext-member->value (car ms))))
                       ((when (reserrp v)) v)
                       (r (values-plaintext-members-new (cdr ms) nil))
                       ((when (reserrp r)) r))
                    (cons (make-plaintext-member
                           :name (plaintext-member->name (car ms))
                           :value v)
                          r))))
  :expand ((ptx-mnew-map ms)
           (ptx-member-fields ms))
  :enable (ptx-members-new-of-nil-is-map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The circuit.

(defines ptx-new-gadget
  :flag-local nil
  :short "The constraints of Plaintext::new: Literal::new on each leaf."

  (define ptx-new-gadget (wt)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-mnew-gadget (cdr wt)))
      (:array (ptx-lnew-gadget (cdr wt)))
      (otherwise (ptx-leaf-new-gadget (cdr wt)))))

  (define ptx-mnew-gadget (wms)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-new-gadget (cdr (car wms)))
              (ptx-mnew-gadget (cdr wms)))))

  (define ptx-lnew-gadget (wts)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-new-gadget (car wts))
              (ptx-lnew-gadget (cdr wts))))))

(defines ptx-new-witnessp
  :flag-local nil
  :short "The output tree has the shape and member names of the console
          plaintext, and each leaf carries the Literal::new witness of the
          corresponding console literal."

  (define ptx-new-witnessp (wt pt asg p)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (and (plaintext-case pt :struct)
                    (ptx-mnew-witnessp (cdr wt) (plaintext-struct->members pt)
                                       asg p)))
      (:array (and (plaintext-case pt :array)
                   (ptx-lnew-witnessp (cdr wt) (plaintext-array->elements pt)
                                      asg p)))
      (otherwise (and (plaintext-case pt :literal)
                      (ptx-leaf-new-witnessp (cdr wt)
                                             (plaintext-literal->get pt)
                                             asg p)
                      t))))

  (define ptx-mnew-witnessp (wms ms asg p)
    :measure (acl2-count wms)
    (if (atom wms)
        (atom ms)
      (and (consp ms)
           (equal (identifier-fix (car (car wms)))
                  (plaintext-member->name (car ms)))
           (ptx-new-witnessp (cdr (car wms))
                             (plaintext-member->value (car ms))
                             asg p)
           (ptx-mnew-witnessp (cdr wms) (cdr ms) asg p))))

  (define ptx-lnew-witnessp (wts es asg p)
    :measure (acl2-count wts)
    (if (atom wts)
        (atom es)
      (and (consp es)
           (ptx-new-witnessp (car wts) (car es) asg p)
           (ptx-lnew-witnessp (cdr wts) (cdr es) asg p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Openers of the funspec on constructors.

(defruled ptx-plaintext-new-of-literal
  (implies (literalp l)
  (equal (plaintext-new (plaintext-literal l))
         (b* ((r (literal-new l)))
           (if (reserrp r) r (plaintext-literal r)))))
  :expand ((plaintext-new (plaintext-literal l))))

(defruled ptx-plaintext-new-of-struct
  (implies (plaintext-member-listp ms)
  (equal (plaintext-new (plaintext-struct ms))
         (b* ((r (values-plaintext-members-new ms nil)))
           (if (reserrp r) r (plaintext-struct r)))))
  :expand ((plaintext-new (plaintext-struct ms))))

(defruled ptx-plaintext-new-of-array
  (implies (plaintext-listp es)
  (equal (plaintext-new (plaintext-array es))
         (b* ((r (values-plaintext-elements-new es)))
           (if (reserrp r) r (plaintext-array r)))))
  :expand ((plaintext-new (plaintext-array es))))

(defruled ptx-elements-new-of-cons
  (implies (and (plaintextp e) (plaintext-listp es))
  (equal (values-plaintext-elements-new (cons e es))
         (b* ((v (plaintext-new e))
              ((when (reserrp v)) v)
              (r (values-plaintext-elements-new es))
              ((when (reserrp r)) r))
           (cons v r))))
  :expand ((values-plaintext-elements-new (cons e es))))

(defruled ptx-elements-new-of-nil
  (equal (values-plaintext-elements-new nil) nil)
  :expand ((values-plaintext-elements-new nil)))

(defruled ptx-members-new-of-nil
  (equal (values-plaintext-members-new nil acc)
         (plaintext-member-list-fix acc))
  :expand ((values-plaintext-members-new nil acc)))

(local (in-theory (enable ptx-plaintext-new-of-literal
                          ptx-plaintext-new-of-struct
                          ptx-plaintext-new-of-array
                          ptx-elements-new-of-cons
                          ptx-elements-new-of-nil
                          ptx-members-new-of-nil
                          ptx-members-new-of-cons-nil)))

(define ptx-wms-fields (wms)
  (if (atom wms)
      nil
    (cons (identifier->field (identifier-fix (car (car wms))))
          (ptx-wms-fields (cdr wms)))))

(defrule ptx-member-fields-of-mval
  (equal (ptx-member-fields (ptx-mval wms asg))
         (ptx-wms-fields wms))
  :induct (len wms)
  :expand ((ptx-mval wms asg)
           (ptx-wms-fields wms)
           (:free (x y) (ptx-member-fields (cons x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(defthm-ptx-new-gadget-flag
  (defthm ptx-new-gadget-sound-lemma
    (implies (and (primep p)
                  (ptx-distinct (ptx-val wt asg))
                  (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p))
             (and (ptx-typed wt asg)
                  (equal (plaintext-new (ptx-val wt asg))
                         (ptx-val wt asg))))
    :flag ptx-new-gadget)
  (defthm ptx-mnew-gadget-sound-lemma
    (implies (and (primep p)
                  (no-duplicatesp-equal (ptx-member-fields (ptx-mval wms asg)))
                  (ptx-mdistinct (ptx-mval wms asg))
                  (r1cs::r1cs-constraints-holdp (ptx-mnew-gadget wms) asg p))
             (and (ptx-mtyped wms asg)
                  (equal (values-plaintext-members-new (ptx-mval wms asg) nil)
                         (ptx-mval wms asg))))
    :flag ptx-mnew-gadget)
  (defthm ptx-lnew-gadget-sound-lemma
    (implies (and (primep p)
                  (ptx-ldistinct (ptx-lval wts asg))
                  (r1cs::r1cs-constraints-holdp (ptx-lnew-gadget wts) asg p))
             (and (ptx-ltyped wts asg)
                  (equal (values-plaintext-elements-new (ptx-lval wts asg))
                         (ptx-lval wts asg))))
    :flag ptx-lnew-gadget)
  :hints (("Goal"
           :in-theory (enable ptx-leaf-new-sound ptx-member-fields)
           :expand ((ptx-wms-fields wms)
                    (ptx-new-gadget wt)
                    (ptx-mnew-gadget wms)
                    (ptx-lnew-gadget wts)
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

(defruled ptx-new-sound
  :short "R1CS-SOUND of Plaintext::new: from a satisfying assignment, every
          leaf satisfies Literal::new, the output wires denote a plaintext,
          and the funspec returns that plaintext."
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-distinct (ptx-val wt asg))
                (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p))
           (and (ptx-typed wt asg)
                (plaintextp (ptx-val wt asg))
                (equal (plaintext-new (ptx-val wt asg))
                       (ptx-val wt asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defruled ptx-wms-fields-when-witnessp
  (implies (ptx-mnew-witnessp wms ms asg p)
           (equal (ptx-wms-fields wms)
                  (ptx-member-fields ms)))
  :induct (ind wms ms)
  :expand ((ptx-mnew-witnessp wms ms asg p)
           (ptx-wms-fields wms)
           (ptx-member-fields ms))
  :prep-lemmas
  ((defun ind (x y)
     (if (atom x) y (ind (cdr x) (cdr y))))))

(defruled ptx-leaf-new-val-when-holds
  (implies (and (primep p)
                (ptx-leaf-new-witnessp w x asg p)
                (r1cs::r1cs-constraints-holdp (ptx-leaf-new-gadget w) asg p))
           (and (not (reserrp (literal-new x)))
                (equal (ptx-leaf-val w asg) (literal-new x))))
  :use (ptx-leaf-new-error ptx-leaf-new-complete))

(defrule ptx-mnew-witnessp-when-atom-ms
  (implies (and (consp wms) (atom ms))
           (not (ptx-mnew-witnessp wms ms asg p)))
  :expand ((ptx-mnew-witnessp wms ms asg p)))

(defrule ptx-lnew-witnessp-when-atom-es
  (implies (and (consp wts) (atom es))
           (not (ptx-lnew-witnessp wts es asg p)))
  :expand ((ptx-lnew-witnessp wts es asg p)))

(defthm-ptx-new-witnessp-flag
  (defthm ptx-new-gadget-complete-lemma
    (implies (and (primep p)
                  (plaintextp pt)
                  (ptx-distinct pt)
                  (ptx-new-witnessp wt pt asg p))
             (if (reserrp (plaintext-new pt))
                 (not (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p)
                    (equal (ptx-val wt asg) (plaintext-new pt)))))
    :flag ptx-new-witnessp)
  (defthm ptx-mnew-gadget-complete-lemma
    (implies (and (primep p)
                  (plaintext-member-listp ms)
                  (no-duplicatesp-equal (ptx-member-fields ms))
                  (ptx-mdistinct ms)
                  (ptx-mnew-witnessp wms ms asg p))
             (if (reserrp (values-plaintext-members-new ms nil))
                 (not (r1cs::r1cs-constraints-holdp (ptx-mnew-gadget wms) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-mnew-gadget wms) asg p)
                    (equal (ptx-mval wms asg)
                           (values-plaintext-members-new ms nil)))))
    :flag ptx-mnew-witnessp)
  (defthm ptx-lnew-gadget-complete-lemma
    (implies (and (primep p)
                  (plaintext-listp es)
                  (ptx-ldistinct es)
                  (ptx-lnew-witnessp wts es asg p))
             (if (reserrp (values-plaintext-elements-new es))
                 (not (r1cs::r1cs-constraints-holdp (ptx-lnew-gadget wts) asg p))
               (and (r1cs::r1cs-constraints-holdp (ptx-lnew-gadget wts) asg p)
                    (equal (ptx-lval wts asg)
                           (values-plaintext-elements-new es)))))
    :flag ptx-lnew-witnessp)
  :hints (("Goal"
           :in-theory (enable ptx-leaf-new-complete ptx-leaf-new-error
                              ptx-leaf-new-val-when-holds
                              ptx-wms-fields-when-witnessp)
           :expand ((ptx-new-gadget wt)
                    (ptx-mnew-gadget wms)
                    (ptx-lnew-gadget wts)
                    (ptx-new-witnessp wt pt asg p)
                    (ptx-mnew-witnessp wms ms asg p)
                    (ptx-lnew-witnessp wts es asg p)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)
                    (ptx-distinct pt)
                    (ptx-mdistinct ms)
                    (ptx-ldistinct es)
                    (ptx-member-fields ms)
                    (plaintext-new pt)
                    (values-plaintext-elements-new es)))))

(defruled ptx-new-complete
  :short "R1CS-COMPLETE of Plaintext::new: on a console plaintext (distinct
          member names), with the Literal::new witness on each leaf, the
          constraints hold and the output denotes the funspec's result when
          it succeeds, and do not hold when it fails."
  (implies (and (primep p)
                (ptx-wtp wt)
                (plaintextp pt)
                (ptx-distinct pt)
                (ptx-new-witnessp wt pt asg p))
           (if (reserrp (plaintext-new pt))
               (not (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p))
             (and (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p)
                  (equal (ptx-val wt asg) (plaintext-new pt)))))
  :use ptx-new-gadget-complete-lemma)
