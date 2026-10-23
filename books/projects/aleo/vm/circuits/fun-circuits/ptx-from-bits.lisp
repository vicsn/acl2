; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::from_bits_le / from_bits_be (and the _internal variants),
; Plaintext::from_fields and Plaintext::from
; (snarkVM circuit/program/src/data/plaintext/from_bits.rs, from_fields.rs).
;
; The shape of the result is decided at synthesis time: snarkVM reads the
; prefix bits, the literal size, the member / element counts and the
; identifier / member / element sizes with eject_value and emits no
; constraint tying those wires to the values read.  The model therefore
; parses two parallel lists: WS, the input Boolean terms, and HV, the host
; bits the synthesizer ejected (one per term).  Every branch, size and
; error (halt) is decided on HV; the only constraints are those of
; Literal::from_bits_le / _be on each literal (abstract, ptx-leaf-fb-*) and
; of Identifier::from_bits_le / _be on each member name (abstract,
; ptx-leaf-idfb-*).  A member name is the host identifier parsed from HV.
;
; Soundness holds under the condition that the assignment agrees with the
; synthesis-time values, (ptx-terms-val ws asg) = HV.  Nothing in the
; circuit enforces this: an assignment whose header bits differ from the
; ejected ones can still satisfy the constraints.  The circuit halts
; exactly when the funspec errs on HV.
;
; from_fields: each field is decomposed by Field::to_bits_le (abstract,
; ptx-leaf-fbits-*), 252 bits of each are kept, the bits up to and including
; the last set bit are dropped by inspecting ejected values (host), and the
; rest goes to from_bits_le.

(in-package "ALEOVM")

(include-book "ptx-tree")

(set-verify-guards-eagerness 0)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::open-small-nthcdr acl2::nthcdr-of-cdr)))

(defruledl ptx-nthcdr-of-cddr
  (equal (nthcdr n (cddr x))
         (nthcdr (+ 2 (nfix n)) x))
  :enable nthcdr)

(defruledl ptx-cddr-to-nthcdr
  (equal (cddr x) (nthcdr 2 x))
  :enable nthcdr)

(local (in-theory (e/d (ptx-nthcdr-of-cddr ptx-cddr-to-nthcdr) (nthcdr))))

(defrule ptx-holdp-of-true-list-fix
  (equal (r1cs::r1cs-constraints-holdp (true-list-fix cs) asg p)
         (r1cs::r1cs-constraints-holdp cs asg p))
  :induct (len cs)
  :enable (r1cs::r1cs-constraints-holdp true-list-fix))

;; Leaf interfaces.

(defconst *ptx-fb-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-leaf-fb-gadget * * *) => *)
   ((ptx-leaf-fb-out * * *) => *)
   ((ptx-leaf-fb-witnessp * * * * *) => *))

  (local (defun ptx-leaf-fb-gadget (vt dt bigp)
           (declare (ignore vt dt bigp))
           (list *ptx-fb-false-constraint*)))
  (local (defun ptx-leaf-fb-out (vt dt bigp)
           (declare (ignore vt dt bigp))
           nil))
  (local (defun ptx-leaf-fb-witnessp (vt dt bigp asg p)
           (declare (ignore vt dt bigp asg p))
           nil))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defruled ptx-leaf-fb-sound
    :short "Literal::from_bits_le / _be (variant VT, data DT): on a
            satisfying assignment the output leaf denotes the literal the
            funspec parses, when it parses one."
    (implies (and (primep p)
                  (r1cs::r1cs-constraints-holdp (ptx-leaf-fb-gadget vt dt bigp)
                                                asg p)
                  (not (reserrp (values-literal-from-bits
                                 (values-bits-to-nat (ptx-terms-val vt asg) bigp)
                                 (ptx-terms-val dt asg)
                                 bigp))))
             (equal (ptx-leaf-val (ptx-leaf-fb-out vt dt bigp) asg)
                    (values-literal-from-bits
                     (values-bits-to-nat (ptx-terms-val vt asg) bigp)
                     (ptx-terms-val dt asg)
                     bigp)))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-leaf-fb-complete
    (implies (and (primep p)
                  (ptx-leaf-fb-witnessp vt dt bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-leaf-fb-gadget vt dt bigp)
                                           asg p))))

(encapsulate
  (((ptx-leaf-idfb-gadget * *) => *)
   ((ptx-leaf-idfb-witnessp * * * *) => *))

  (local (defun ptx-leaf-idfb-gadget (it bigp)
           (declare (ignore it bigp))
           nil))
  (local (defun ptx-leaf-idfb-witnessp (it bigp asg p)
           (declare (ignore it bigp asg p))
           t))

  (defruled ptx-leaf-idfb-complete
    :short "Identifier::from_bits_le / _be: its constraints hold with its
            witness."
    (implies (and (primep p)
                  (ptx-leaf-idfb-witnessp it bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-leaf-idfb-gadget it bigp)
                                           asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf jobs: the parse returns the list of leaf circuits it instantiated.

(define ptx-job-gadget (job)
  :verify-guards nil
  (if (equal (car job) :lit)
      (ptx-leaf-fb-gadget (nth 1 job) (nth 2 job) (nth 3 job))
    (ptx-leaf-idfb-gadget (nth 1 job) (nth 2 job))))

(define ptx-job-witnessp (job asg p)
  :verify-guards nil
  (if (equal (car job) :lit)
      (ptx-leaf-fb-witnessp (nth 1 job) (nth 2 job) (nth 3 job) asg p)
    (ptx-leaf-idfb-witnessp (nth 1 job) (nth 2 job) asg p)))

(define ptx-jobs-gadget (jobs)
  :verify-guards nil
  (if (atom jobs)
      nil
    (append (ptx-job-gadget (car jobs))
            (ptx-jobs-gadget (cdr jobs))))
  ///
  (defrule ptx-jobs-gadget-of-append
    (equal (ptx-jobs-gadget (append xs ys))
           (append (ptx-jobs-gadget xs) (ptx-jobs-gadget ys))))
  (defrule ptx-jobs-gadget-of-cons
    (equal (ptx-jobs-gadget (cons x xs))
           (append (ptx-job-gadget x) (ptx-jobs-gadget xs))))
  (defrule ptx-jobs-gadget-of-nil
    (equal (ptx-jobs-gadget nil) nil)))

(define ptx-jobs-witnessp (jobs asg p)
  :verify-guards nil
  (if (atom jobs)
      t
    (and (ptx-job-witnessp (car jobs) asg p)
         (ptx-jobs-witnessp (cdr jobs) asg p))))

(defruled ptx-jobs-complete
  (implies (and (primep p)
                (ptx-jobs-witnessp jobs asg p))
           (r1cs::r1cs-constraints-holdp (ptx-jobs-gadget jobs) asg p))
  :induct (len jobs)
  :enable (ptx-jobs-witnessp ptx-jobs-gadget ptx-job-gadget ptx-job-witnessp
                             ptx-leaf-fb-complete ptx-leaf-idfb-complete
                             r1cs::r1cs-constraints-holdp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The parse.

(define ptx-wms-insert (name wt wms)
  :verify-guards nil
  :short "IndexMap::insert on wire members (by identifier field)."
  (cond ((atom wms) (list (cons name wt)))
        ((equal (identifier->field (identifier-fix (car (car wms))))
                (identifier->field name))
         (cons (cons (car (car wms)) wt) (cdr wms)))
        (t (cons (car wms) (ptx-wms-insert name wt (cdr wms))))))

(defrule ptx-mval-of-wms-insert
  (implies (identifierp name)
           (equal (ptx-mval (ptx-wms-insert name wt wms) asg)
                  (values-plaintext-members-insert name (ptx-val wt asg)
                                                   (ptx-mval wms asg))))
  :induct (ptx-wms-insert name wt wms)
  :enable (ptx-wms-insert values-plaintext-members-insert)
  :expand ((:free (a b) (ptx-mval (cons a b) asg))))

(defines ptx-fb
  :flag-local nil
  :short "Plaintext::from_bits_*_internal: :error (halt) or
          (cons jobs wire-tree)."

  (define ptx-fb (ws hv depth bigp)
  :verify-guards nil
    :measure (len hv)
    (b* (((when (> (nfix depth) (values-max-data-depth))) :error)
         ((unless (<= 2 (len hv))) :error)
         (b1 (first hv))
         (b2 (second hv))
         (hv (nthcdr 2 hv))
         (ws (nthcdr 2 ws)))
      (cond
       ((and (equal b1 0) (equal b2 0))
        (b* (((unless (<= 24 (len hv))) :error)
             (variant (values-bits-to-nat (take 8 hv) bigp))
             (size (values-bits-to-nat (take 16 (nthcdr 8 hv)) bigp))
             (vt (take 8 ws))
             (hv (nthcdr 24 hv))
             (ws (nthcdr 24 ws))
             ((unless (<= size (len hv))) :error)
             ((when (reserrp (values-literal-from-bits variant (take size hv) bigp)))
              :error))
          (cons (list (list :lit vt (take size ws) bigp))
                (cons :lit (ptx-leaf-fb-out vt (take size ws) bigp)))))
       ((and (equal b1 0) (equal b2 1))
        (b* (((unless (<= 8 (len hv))) :error)
             (n (values-bits-to-nat (take 8 hv) bigp))
             (r (ptx-fbm (nthcdr 8 ws) (nthcdr 8 hv) n (1+ (nfix depth)) bigp nil))
             ((when (equal r :error)) :error))
          (cons (car r) (cons :struct (cdr r)))))
       ((and (equal b1 1) (equal b2 0))
        (b* (((unless (<= 32 (len hv))) :error)
             (n (values-bits-to-nat (take 32 hv) bigp))
             (r (ptx-fbl (nthcdr 32 ws) (nthcdr 32 hv) n (1+ (nfix depth)) bigp))
             ((when (equal r :error)) :error))
          (cons (car r) (cons :array (cdr r)))))
       (t :error))))

  (define ptx-fbm (ws hv count depth bigp acc)
  :verify-guards nil
    :measure (len hv)
    (b* (((when (zp count)) (cons nil acc))
         ((unless (<= 8 (len hv))) :error)
         (id-size (values-bits-to-nat (take 8 hv) bigp))
         (hv (nthcdr 8 hv))
         (ws (nthcdr 8 ws))
         ((unless (<= id-size (len hv))) :error)
         (name (if bigp
                   (identifier-from-bits-be (take id-size hv))
                 (identifier-from-bits-le (take id-size hv))))
         ((when (reserrp name)) :error)
         (idjob (list :id (take id-size ws) bigp))
         (hv (nthcdr id-size hv))
         (ws (nthcdr id-size ws))
         ((unless (<= 16 (len hv))) :error)
         (msize (values-bits-to-nat (take 16 hv) bigp))
         (hv (nthcdr 16 hv))
         (ws (nthcdr 16 ws))
         ((unless (<= msize (len hv))) :error)
         (sub (ptx-fb (take msize ws) (take msize hv) depth bigp))
         ((when (equal sub :error)) :error)
         (rest (ptx-fbm (nthcdr msize ws) (nthcdr msize hv) (1- count) depth bigp
                        (ptx-wms-insert name (cdr sub) acc)))
         ((when (equal rest :error)) :error))
      (cons (cons idjob (append (car sub) (car rest)))
            (cdr rest))))

  (define ptx-fbl (ws hv count depth bigp)
  :verify-guards nil
    :measure (len hv)
    (b* (((when (zp count)) (cons nil nil))
         ((unless (<= 16 (len hv))) :error)
         (esize (values-bits-to-nat (take 16 hv) bigp))
         (hv (nthcdr 16 hv))
         (ws (nthcdr 16 ws))
         ((unless (<= esize (len hv))) :error)
         (sub (ptx-fb (take esize ws) (take esize hv) depth bigp))
         ((when (equal sub :error)) :error)
         (rest (ptx-fbl (nthcdr esize ws) (nthcdr esize hv) (1- count) depth bigp))
         ((when (equal rest :error)) :error))
      (cons (append (car sub) (car rest))
            (cons (cdr sub) (cdr rest)))))
  :hints (("Goal" :in-theory (enable acl2::len-of-nthcdr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The member accumulator does not affect whether the funspec errs.

(defun ptx-fbm-acc-ind (hv count depth bigp a1 a2)
  (declare (xargs :measure (len hv)
                  :hints (("Goal" :in-theory (enable acl2::len-of-nthcdr)))
                  :verify-guards nil))
  (b* (((when (zp count)) (list a1 a2))
       (hv (bit-list-fix hv))
       ((unless (<= 8 (len hv))) nil)
       (id-size (values-bits-to-nat (take 8 hv) bigp))
       (hv (nthcdr 8 hv))
       ((unless (<= id-size (len hv))) nil)
       (name (if bigp
                 (identifier-from-bits-be (take id-size hv))
               (identifier-from-bits-le (take id-size hv))))
       ((when (reserrp name)) nil)
       (hv (nthcdr id-size hv))
       ((unless (<= 16 (len hv))) nil)
       (msize (values-bits-to-nat (take 16 hv) bigp))
       (hv (nthcdr 16 hv))
       ((unless (<= msize (len hv))) nil)
       (value (values-plaintext-from-bits-internal (take msize hv) depth bigp))
       ((when (reserrp value)) nil))
    (ptx-fbm-acc-ind (nthcdr msize hv) (1- count) depth bigp
                     (values-plaintext-members-insert name value a1)
                     (values-plaintext-members-insert name value a2))))

(defruled ptx-members-from-bits-error-acc-lemma
  (equal (reserrp (values-plaintext-members-from-bits hv count depth bigp a1))
         (reserrp (values-plaintext-members-from-bits hv count depth bigp a2)))
  :induct (ptx-fbm-acc-ind hv count depth bigp a1 a2)
  :expand ((:free (bigp) (values-plaintext-members-from-bits hv count depth bigp a1))
           (:free (bigp) (values-plaintext-members-from-bits hv count depth bigp a2))))

(defrule ptx-members-from-bits-error-acc
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (reserrp (values-plaintext-members-from-bits
                            hv count depth bigp acc))
                  (reserrp (values-plaintext-members-from-bits
                            hv count depth bigp nil))))
  :use ((:instance ptx-members-from-bits-error-acc-lemma (a1 acc) (a2 nil))))

;; Openers.

(defruled ptx-members-from-bits-opener
  (implies (and (syntaxp (or (acl2::variablep hv) (and (eq (car hv) 'ptx-terms-val) (acl2::variablep (cadr hv))))) (not (zp count)) (bit-listp hv))
           (equal (values-plaintext-members-from-bits hv count depth bigp acc)
                  (b* (((unless (<= 8 (len hv))) (spec-error))
                       (id-size (values-bits-to-nat (take 8 hv) bigp))
                       (hv (nthcdr 8 hv))
                       ((unless (<= id-size (len hv))) (spec-error))
                       (name (if bigp
                                 (identifier-from-bits-be (take id-size hv))
                               (identifier-from-bits-le (take id-size hv))))
                       ((when (reserrp name)) name)
                       (hv (nthcdr id-size hv))
                       ((unless (<= 16 (len hv))) (spec-error))
                       (msize (values-bits-to-nat (take 16 hv) bigp))
                       (hv (nthcdr 16 hv))
                       ((unless (<= msize (len hv))) (spec-error))
                       (value (values-plaintext-from-bits-internal
                               (take msize hv) depth bigp))
                       ((when (reserrp value)) value))
                    (values-plaintext-members-from-bits
                     (nthcdr msize hv) (1- count) depth bigp
                     (values-plaintext-members-insert name value acc)))))
  :expand ((values-plaintext-members-from-bits hv count depth bigp acc)))

(defruled ptx-elements-from-bits-opener
  (implies (and (syntaxp (or (acl2::variablep hv) (and (eq (car hv) 'ptx-terms-val) (acl2::variablep (cadr hv))))) (not (zp count)) (bit-listp hv))
           (equal (values-plaintext-elements-from-bits hv count depth bigp)
                  (b* (((unless (<= 16 (len hv))) (spec-error))
                       (esize (values-bits-to-nat (take 16 hv) bigp))
                       (hv (nthcdr 16 hv))
                       ((unless (<= esize (len hv))) (spec-error))
                       (value (values-plaintext-from-bits-internal
                               (take esize hv) depth bigp))
                       ((when (reserrp value)) value)
                       (values (values-plaintext-elements-from-bits
                                (nthcdr esize hv) (1- count) depth bigp))
                       ((when (reserrp values)) values))
                    (cons value values))))
  :expand ((values-plaintext-elements-from-bits hv count depth bigp)))

(defrule ptx-members-from-bits-when-zp
  (implies (zp count)
           (equal (values-plaintext-members-from-bits hv count depth bigp acc)
                  (plaintext-member-list-fix acc)))
  :expand ((values-plaintext-members-from-bits hv count depth bigp acc)))

(defrule ptx-elements-from-bits-when-zp
  (implies (zp count)
           (equal (values-plaintext-elements-from-bits hv count depth bigp) nil))
  :expand ((values-plaintext-elements-from-bits hv count depth bigp)))

(defruled ptx-from-bits-internal-opener
  (implies (and (syntaxp (or (acl2::variablep hv) (and (eq (car hv) 'ptx-terms-val) (acl2::variablep (cadr hv))))) (bit-listp hv))
           (equal (values-plaintext-from-bits-internal hv depth bigp)
                  (b* (((when (> (nfix depth) (values-max-data-depth))) (spec-error))
                       ((unless (<= 2 (len hv))) (spec-error))
                       (b1 (first hv))
                       (b2 (second hv))
                       (hv (nthcdr 2 hv)))
                    (cond
                     ((and (equal b1 0) (equal b2 0))
                      (b* (((unless (<= 24 (len hv))) (spec-error))
                           (variant (values-bits-to-nat (take 8 hv) bigp))
                           (size (values-bits-to-nat (take 16 (nthcdr 8 hv)) bigp))
                           (hv (nthcdr 24 hv))
                           ((unless (<= size (len hv))) (spec-error))
                           (lit (values-literal-from-bits variant (take size hv) bigp))
                           ((when (reserrp lit)) lit))
                        (plaintext-literal lit)))
                     ((and (equal b1 0) (equal b2 1))
                      (b* (((unless (<= 8 (len hv))) (spec-error))
                           (n (values-bits-to-nat (take 8 hv) bigp))
                           (members (values-plaintext-members-from-bits
                                     (nthcdr 8 hv) n (1+ (nfix depth)) bigp nil))
                           ((when (reserrp members)) members))
                        (plaintext-struct members)))
                     ((and (equal b1 1) (equal b2 0))
                      (b* (((unless (<= 32 (len hv))) (spec-error))
                           (n (values-bits-to-nat (take 32 hv) bigp))
                           (elements (values-plaintext-elements-from-bits
                                      (nthcdr 32 hv) n (1+ (nfix depth)) bigp))
                           ((when (reserrp elements)) elements))
                        (plaintext-array elements)))
                     (t (spec-error))))))
  :expand ((values-plaintext-from-bits-internal hv depth bigp)))

;; Synthesis halts exactly when the funspec errs on the ejected bits.

(defthm-ptx-fb-flag
  (defthm ptx-fb-error
    (implies (bit-listp hv)
             (iff (equal (ptx-fb ws hv depth bigp) :error)
                  (reserrp (values-plaintext-from-bits-internal hv depth bigp))))
    :flag ptx-fb)
  (defthm ptx-fbm-error
    (implies (bit-listp hv)
             (iff (equal (ptx-fbm ws hv count depth bigp acc) :error)
                  (reserrp (values-plaintext-members-from-bits
                            hv count depth bigp nil))))
    :flag ptx-fbm)
  (defthm ptx-fbl-error
    (implies (bit-listp hv)
             (iff (equal (ptx-fbl ws hv count depth bigp) :error)
                  (reserrp (values-plaintext-elements-from-bits
                            hv count depth bigp))))
    :flag ptx-fbl)
  :hints (("Goal"
           :expand ((:free (bigp) (ptx-fb ws hv depth bigp))
                    (:free (bigp) (ptx-fbm ws hv count depth bigp acc))
                    (:free (bigp) (ptx-fbl ws hv count depth bigp)))
           :in-theory (enable ptx-members-from-bits-opener
                              ptx-elements-from-bits-opener
                              ptx-from-bits-internal-opener))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness: when the assignment agrees with the ejected bits, the output
;; wire tree denotes the funspec's result.

(defrule ptx-val-of-tagged
  (and (equal (ptx-val (cons :lit w) asg) (plaintext-literal (ptx-leaf-val w asg)))
       (equal (ptx-val (cons :struct wms) asg) (plaintext-struct (ptx-mval wms asg)))
       (equal (ptx-val (cons :array wts) asg) (plaintext-array (ptx-lval wts asg))))
  :expand ((ptx-val (cons :lit w) asg)
           (ptx-val (cons :struct wms) asg)
           (ptx-val (cons :array wts) asg)))

(defrule ptx-lval-of-cons
  (equal (ptx-lval (cons wt wts) asg)
         (cons (ptx-val wt asg) (ptx-lval wts asg)))
  :expand ((ptx-lval (cons wt wts) asg)))

(defrule ptx-job-gadget-of-lit
  (equal (ptx-job-gadget (list :lit vt dt bigp))
         (ptx-leaf-fb-gadget vt dt bigp))
  :enable ptx-job-gadget)

(defthm-ptx-fb-flag
  (defthm ptx-fb-sound
    (implies (and (primep p)
                  (bit-listp hv)
                  (equal (ptx-terms-val ws asg) hv)
                  (not (equal (ptx-fb ws hv depth bigp) :error))
                  (r1cs::r1cs-constraints-holdp
                   (ptx-jobs-gadget (car (ptx-fb ws hv depth bigp))) asg p))
             (equal (ptx-val (cdr (ptx-fb ws hv depth bigp)) asg)
                    (values-plaintext-from-bits-internal hv depth bigp)))
    :flag ptx-fb)
  (defthm ptx-fbm-sound
    (implies (and (primep p)
                  (bit-listp hv)
                  (equal (ptx-terms-val ws asg) hv)
                  (not (equal (ptx-fbm ws hv count depth bigp acc) :error))
                  (r1cs::r1cs-constraints-holdp
                   (ptx-jobs-gadget (car (ptx-fbm ws hv count depth bigp acc)))
                   asg p))
             (equal (ptx-mval (cdr (ptx-fbm ws hv count depth bigp acc)) asg)
                    (values-plaintext-members-from-bits
                     hv count depth bigp (ptx-mval acc asg))))
    :flag ptx-fbm)
  (defthm ptx-fbl-sound
    (implies (and (primep p)
                  (bit-listp hv)
                  (equal (ptx-terms-val ws asg) hv)
                  (not (equal (ptx-fbl ws hv count depth bigp) :error))
                  (r1cs::r1cs-constraints-holdp
                   (ptx-jobs-gadget (car (ptx-fbl ws hv count depth bigp))) asg p))
             (equal (ptx-lval (cdr (ptx-fbl ws hv count depth bigp)) asg)
                    (values-plaintext-elements-from-bits hv count depth bigp)))
    :flag ptx-fbl)
  :hints (("Goal"
           :expand ((:free (bigp) (ptx-fb ws hv depth bigp))
                    (:free (bigp) (ptx-fbm ws hv count depth bigp acc))
                    (:free (bigp) (ptx-fbl ws hv count depth bigp)))
           :in-theory (enable ptx-members-from-bits-opener
                              ptx-elements-from-bits-opener
                              ptx-from-bits-internal-opener
                              ptx-leaf-fb-sound
                              r1cs::r1cs-constraints-holdp-of-append))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plaintext::from_bits_le_internal / from_bits_be_internal and
;; FromBits::from_bits_le / from_bits_be (depth 0).

(defruled ptx-from-bits-internal-sound
  :short "R1CS-SOUND, under the condition that the input wires carry the
          bits ejected at synthesis time (HV)."
  (implies (and (primep p)
                (bit-listp hv)
                (equal (ptx-terms-val ws asg) hv))
           (b* ((r (ptx-fb ws hv depth bigp))
                (spec (values-plaintext-from-bits-internal hv depth bigp)))
             (and (iff (equal r :error) (reserrp spec))
                  (implies (and (not (equal r :error))
                                (r1cs::r1cs-constraints-holdp
                                 (ptx-jobs-gadget (car r)) asg p))
                           (equal (ptx-val (cdr r) asg) spec)))))
  :use (ptx-fb-error ptx-fb-sound))

(defruled ptx-from-bits-internal-complete
  :short "R1CS-COMPLETE: with each leaf circuit's witness the constraints
          hold, and (on the synthesis-time values) the output denotes the
          funspec's result."
  (implies (and (primep p)
                (bit-listp hv)
                (equal (ptx-terms-val ws asg) hv)
                (not (equal (ptx-fb ws hv depth bigp) :error))
                (ptx-jobs-witnessp (car (ptx-fb ws hv depth bigp)) asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (ptx-jobs-gadget (car (ptx-fb ws hv depth bigp))) asg p)
                (equal (ptx-val (cdr (ptx-fb ws hv depth bigp)) asg)
                       (values-plaintext-from-bits-internal hv depth bigp))))
  :use (ptx-fb-sound
        (:instance ptx-jobs-complete (jobs (car (ptx-fb ws hv depth bigp))))))

(defruled ptx-from-bits-le-sound
  (implies (and (primep p)
                (bit-listp hv)
                (equal (ptx-terms-val ws asg) hv))
           (b* ((r (ptx-fb ws hv 0 nil))
                (spec (plaintext-from-bits-le hv)))
             (and (iff (equal r :error) (reserrp spec))
                  (implies (and (not (equal r :error))
                                (r1cs::r1cs-constraints-holdp
                                 (ptx-jobs-gadget (car r)) asg p))
                           (equal (ptx-val (cdr r) asg) spec)))))
  :use (:instance ptx-from-bits-internal-sound (depth 0) (bigp nil))
  :enable (plaintext-from-bits-le plaintext-from-bits-le-internal))

(defruled ptx-from-bits-be-sound
  (implies (and (primep p)
                (bit-listp hv)
                (equal (ptx-terms-val ws asg) hv))
           (b* ((r (ptx-fb ws hv 0 t))
                (spec (plaintext-from-bits-be hv)))
             (and (iff (equal r :error) (reserrp spec))
                  (implies (and (not (equal r :error))
                                (r1cs::r1cs-constraints-holdp
                                 (ptx-jobs-gadget (car r)) asg p))
                           (equal (ptx-val (cdr r) asg) spec)))))
  :use (:instance ptx-from-bits-internal-sound (depth 0) (bigp t))
  :enable (plaintext-from-bits-be plaintext-from-bits-be-internal))

(defruled ptx-from-bits-internal-le-be-funspecs
  (and (equal (plaintext-from-bits-le-internal bits depth)
              (values-plaintext-from-bits-internal bits depth nil))
       (equal (plaintext-from-bits-be-internal bits depth)
              (values-plaintext-from-bits-internal bits depth t)))
  :enable (plaintext-from-bits-le-internal plaintext-from-bits-be-internal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plaintext::from_fields and From<Vec<Field>> / From<&[Field]>.

(encapsulate
  (((ptx-leaf-fbits-gadget *) => *)
   ((ptx-leaf-fbits-out *) => *)
   ((ptx-leaf-fbits-witnessp * * *) => *))

  (local (defun ptx-leaf-fbits-gadget (f)
           (declare (ignore f))
           (list *ptx-fb-false-constraint*)))
  (local (defun ptx-leaf-fbits-out (f)
           (declare (ignore f))
           nil))
  (local (defun ptx-leaf-fbits-witnessp (f asg p)
           (declare (ignore f asg p))
           nil))

  (local
   (defrule mod-1-when-big
     (implies (and (integerp p) (<= 2 p))
              (equal (mod 1 p) 1))
     :enable mod))

  (defruled ptx-leaf-fbits-sound
    :short "Field::to_bits_le on the field term F: 253 Boolean terms
            denoting the bits of F's value."
    (implies (and (primep p)
                  (r1cs::r1cs-constraints-holdp (ptx-leaf-fbits-gadget f) asg p))
             (equal (ptx-terms-val (ptx-leaf-fbits-out f) asg)
                    (values-field-to-bits-le (ptx-term-val f asg))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

  (defruled ptx-leaf-fbits-complete
    (implies (and (primep p)
                  (ptx-leaf-fbits-witnessp f asg p))
             (r1cs::r1cs-constraints-holdp (ptx-leaf-fbits-gadget f) asg p))))

(defrule ptx-len-of-leaf-fbits-out
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (ptx-leaf-fbits-gadget f) asg p))
           (equal (len (ptx-leaf-fbits-out f)) 253))
  :rule-classes nil
  :use (ptx-leaf-fbits-sound
        (:instance ptx-len-of-terms-val (xs (ptx-leaf-fbits-out f))))
  :disable ptx-len-of-terms-val)

(define ptx-fields-bits (fs)
  :verify-guards nil
  (if (atom fs)
      nil
    (append (take 252 (ptx-leaf-fbits-out (car fs)))
            (ptx-fields-bits (cdr fs)))))

(define ptx-fields-gadget (fs)
  :verify-guards nil
  (if (atom fs)
      nil
    (append (ptx-leaf-fbits-gadget (car fs))
            (ptx-fields-gadget (cdr fs)))))

(define ptx-fields-witnessp (fs asg p)
  :verify-guards nil
  (if (atom fs)
      t
    (and (ptx-leaf-fbits-witnessp (car fs) asg p)
         (ptx-fields-witnessp (cdr fs) asg p))))

(defruled ptx-fields-bits-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (ptx-fields-gadget fs) asg p))
           (equal (ptx-terms-val (ptx-fields-bits fs) asg)
                  (values-fields-to-data-bits (ptx-terms-val fs asg))))
  :induct (len fs)
  :enable (ptx-fields-bits ptx-fields-gadget values-fields-to-data-bits
                           r1cs::r1cs-constraints-holdp-of-append)
  :expand ((ptx-terms-val fs asg))
  :hints (("Subgoal *1/1"
           :use ((:instance ptx-leaf-fbits-sound (f (car fs)))
                 (:instance ptx-len-of-leaf-fbits-out (f (car fs)))))))

(defruled ptx-fields-gadget-complete
  (implies (and (primep p)
                (ptx-fields-witnessp fs asg p))
           (r1cs::r1cs-constraints-holdp (ptx-fields-gadget fs) asg p))
  :induct (len fs)
  :enable (ptx-fields-gadget ptx-fields-witnessp ptx-leaf-fbits-complete
                             r1cs::r1cs-constraints-holdp-of-append))

(define ptx-strip (rws rhv)
  :short "Drop the terms up to and including the last one whose ejected
          value is 1 (both lists reversed)."
  :verify-guards nil
  (cond ((atom rhv) nil)
        ((equal (car rhv) 1) (true-list-fix (cdr rws)))
        (t (ptx-strip (cdr rws) (cdr rhv)))))

(defrule ptx-terms-val-of-strip
  (implies (and (bit-listp rhv)
                (equal (ptx-terms-val rws asg) rhv))
           (equal (ptx-terms-val (ptx-strip rws rhv) asg)
                  (values-strip-terminus rhv)))
  :induct (ptx-strip rws rhv)
  :enable (ptx-strip values-strip-terminus ptx-terms-val)
  :expand ((ptx-terms-val rws asg)))

(defrule ptx-terms-val-of-rev
  (equal (ptx-terms-val (rev xs) asg)
         (rev (ptx-terms-val xs asg)))
  :induct (len xs)
  :enable (rev ptx-terms-val))

(define ptx-from-fields (fs hv)
  :short "Plaintext::from_fields on field terms FS, HV being the ejected
          values of the data bits: :error (halt) or (cons jobs wire-tree)."
  :verify-guards nil
  (b* (((when (> (len fs) (values-max-data-size-in-fields))) :error)
       (ws (ptx-fields-bits fs))
       (ws1 (rev (ptx-strip (rev ws) (rev hv))))
       (hv1 (rev (values-strip-terminus (rev hv)))))
    (ptx-fb ws1 hv1 0 nil)))

(define ptx-from-fields-gadget (fs hv)
  :verify-guards nil
  (b* ((r (ptx-from-fields fs hv)))
    (append (ptx-fields-gadget fs)
            (if (equal r :error) nil (ptx-jobs-gadget (car r))))))

(defrule ptx-bit-listp-of-fields-to-data-bits
  (bit-listp (values-fields-to-data-bits fs))
  :induct (len fs)
  :enable values-fields-to-data-bits)

(defruled ptx-from-fields-sound
  :short "R1CS-SOUND of Plaintext::from_fields (and From), under the
          condition that HV are the values of the data bits in the
          assignment."
  (implies (and (primep p)
                (values-field-listp (ptx-terms-val fs asg))
                (r1cs::r1cs-constraints-holdp (ptx-from-fields-gadget fs hv) asg p)
                (equal (ptx-terms-val (ptx-fields-bits fs) asg) hv))
           (b* ((r (ptx-from-fields fs hv))
                (spec (plaintext-from-fields (ptx-terms-val fs asg))))
             (and (equal (plaintext-from (ptx-terms-val fs asg)) spec)
                  (iff (equal r :error) (reserrp spec))
                  (implies (not (equal r :error))
                           (equal (ptx-val (cdr r) asg) spec)))))
  :use ((:instance ptx-fields-bits-sound)
        (:instance ptx-terms-val-of-strip
         (rws (rev (ptx-fields-bits fs))) (rhv (rev hv)))
        (:instance ptx-from-bits-le-sound
         (ws (rev (ptx-strip (rev (ptx-fields-bits fs)) (rev hv))))
         (hv (rev (values-strip-terminus (rev hv))))))
  :enable (ptx-from-fields ptx-from-fields-gadget plaintext-from-fields
                           plaintext-from r1cs::r1cs-constraints-holdp-of-append)
  :disable ptx-terms-val-of-strip)

(defruled ptx-from-fields-complete
  (implies (and (primep p)
                (ptx-fields-witnessp fs asg p)
                (not (equal (ptx-from-fields fs hv) :error))
                (ptx-jobs-witnessp (car (ptx-from-fields fs hv)) asg p))
           (r1cs::r1cs-constraints-holdp (ptx-from-fields-gadget fs hv) asg p))
  :use ((:instance ptx-fields-gadget-complete)
        (:instance ptx-jobs-complete (jobs (car (ptx-from-fields fs hv)))))
  :enable (ptx-from-fields-gadget r1cs::r1cs-constraints-holdp-of-append))
