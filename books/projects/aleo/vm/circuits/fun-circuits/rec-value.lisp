; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value = Plaintext | Record | Future | DynamicRecord | DynamicFuture
; (snarkVM circuit/program/src/data/value): the value wires, Value::new and
; Value::find (with Future::find), each a dispatch on the variant to the
; arm's circuit.
;
; A value wire is (kind . w):
;   (:plaintext . wt)        a ptx- plaintext wire tree,
;   (:record . rw)           rw = (pubp og data ng vbits obits ors nbits nrs
;                            vm vr), the rec-record wires,
;   (:future . fw)           a rec-future wire tree,
;   (:dynamic-record . drw)  drw = (og ng rt vbits bitss rss),
;   (:dynamic-future . dfw)  a rec-future DynamicFuture wire list,
;   (:owner-address . og)    the owner address find returns (a plaintext).
; An argument wire of a future is a value wire of the same kind.
(in-package "ALEOVM")

(include-book "rec-value-bridge")
(include-book "rec-future")
(set-verify-guards-eagerness 0)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Value wires.

(define rec-rw-pubp (w) (nth 0 w))
(define rec-rw-og (w) (nth 1 w))
(define rec-rw-data (w) (nth 2 w))
(define rec-rw-ng (w) (nth 3 w))
(define rec-rw-vbits (w) (nth 4 w))

(define rec-drw-og (w) (nth 0 w))
(define rec-drw-ng (w) (nth 1 w))
(define rec-drw-rt (w) (nth 2 w))
(define rec-drw-vbits (w) (nth 3 w))

(define rec-rval (w asg)
  (rec-record-of-wires (rec-rw-pubp w) (rec-rw-og w) (rec-rw-data w)
                       (rec-rw-ng w) (rec-rw-vbits w) asg))

(define rec-drval (w asg)
  (rec-dynamic-record-of-wires (nth 0 (rec-drw-og w)) (nth 1 (rec-drw-og w))
                               (rec-drw-rt w)
                               (nth 0 (rec-drw-ng w)) (nth 1 (rec-drw-ng w))
                               (rec-drw-vbits w) asg))

(define rec-vval (vw asg)
  :short "The value a value wire denotes (Value::eject_value)."
  (case (car vw)
    (:plaintext (value-plaintext (ptx-val (cdr vw) asg)))
    (:record (value-record (rec-rval (cdr vw) asg)))
    (:future (value-future (rec-fval (cdr vw) asg)))
    (:dynamic-record (value-dynamic-record (rec-drval (cdr vw) asg)))
    (:dynamic-future (value-dynamic-future (rec-dfval (cdr vw) asg)))
    (otherwise (value-plaintext
                (plaintext-literal (literal-address (rec-point-of (cdr vw) asg)))))))

(define rec-rwp (w)
  (and (booleanp (rec-rw-pubp w))
       (symbol-listp (rec-rw-og w)) (equal (len (rec-rw-og w)) 14)
       (symbol-listp (rec-rw-ng w)) (equal (len (rec-rw-ng w)) 14)
       (symbol-listp (rec-rw-vbits w)) (equal (len (rec-rw-vbits w)) 8)
       (rec-record-datawp (rec-rw-data w))))

(define rec-drwp (w)
  (and (symbol-listp (rec-drw-og w)) (equal (len (rec-drw-og w)) 14)
       (symbol-listp (rec-drw-ng w)) (equal (len (rec-drw-ng w)) 14)
       (symbolp (rec-drw-rt w))
       (symbol-listp (rec-drw-vbits w)) (equal (len (rec-drw-vbits w)) 8)))

(define rec-vwp (vw)
  (and (consp vw)
       (case (car vw)
         (:plaintext (ptx-wtp (cdr vw)))
         (:record (rec-rwp (cdr vw)))
         (:future (rec-fwp (cdr vw)))
         (:dynamic-record (rec-drwp (cdr vw)))
         (:dynamic-future (rec-dfwp (cdr vw)))
         (otherwise nil))))

(define rec-rbinds (w asg)
  (and (r1cs::valuation-binds-allp asg (rec-rw-og w))
       (r1cs::valuation-binds-allp asg (rec-rw-ng w))
       (r1cs::valuation-binds-allp asg (rec-rw-vbits w))))

(define rec-drbinds (w asg)
  (and (r1cs::valuation-binds-allp asg (rec-drw-og w))
       (r1cs::valuation-binds-allp asg (rec-drw-ng w))
       (r1cs::valuation-bindsp asg (rec-drw-rt w))
       (r1cs::valuation-binds-allp asg (rec-drw-vbits w))))

(define rec-dfbinds (w asg)
  (and (r1cs::valuation-bindsp asg (nth 0 w))
       (r1cs::valuation-bindsp asg (nth 1 w))
       (r1cs::valuation-bindsp asg (nth 2 w))
       (r1cs::valuation-bindsp asg (nth 3 w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Value::new: each arm's Inject.

(define rec-vnew-gadget (vw)
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (ptx-new-gadget w))
      (:record (rec-record-new-gadget (rec-rw-og w) (rec-rw-data w)
                                      (rec-rw-ng w) (rec-rw-vbits w)))
      (:future (rec-fnew-gadget w))
      (:dynamic-record (rec-dynamic-record-new-gadget
                        (rec-drw-og w) (rec-drw-ng w) (rec-drw-vbits w)))
      (otherwise (rec-dynamic-future-new-gadget)))))

(define rec-vnew-hyps (vw asg)
  :short "The arm's R1CS-SOUND-IF of Value::new: plaintext member names are
          distinct; a record's entry plaintexts have distinct member names and
          its entry names have distinct identifier fields (IndexMap keys)."
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (ptx-distinct (ptx-val w asg)))
      (:record (and (rec-rbinds w asg)
                    (rec-record-data-distinct (rec-rw-data w) asg)
                    (rec-vb-names-distinctp
                     (rec-record-data-eval (rec-rw-data w) asg))))
      (:future (rec-fdistinct w asg))
      (:dynamic-record (rec-drbinds w asg))
      (otherwise (rec-dfbinds w asg)))))

(in-theory (disable rec-record-of-wires))

(defrule rec-record-data-of-rec-record-of-wires
  (implies (rec-record-datawp data)
  (equal (record->data (rec-record-of-wires pubp og data ng vbits asg))
         (rec-record-data-eval data asg)))
  :enable rec-record-of-wires)

(defrule rec-recordp-of-rec-record-of-wires
  (implies (rec-record-datawp data)
           (recordp (rec-record-of-wires pubp og data ng vbits asg)))
  :enable rec-record-of-wires)

(defrule rec-recordp-of-rec-rval
  (implies (rec-rwp w) (recordp (rec-rval w asg)))
  :enable (rec-rval rec-rwp))

(defruled rec-value-new-sound-record
  (implies (and (equal (car vw) :record)
                (rec-rwp (cdr vw))
                (r1cs::r1cs-valuationp asg (base-prime))
                (rec-vnew-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vnew-gadget vw)
                                              asg (base-prime)))
           (equal (values-record-new (rec-rval (cdr vw) asg)) (rec-rval (cdr vw) asg)))
  :do-not-induct t
  :in-theory '(rec-vnew-gadget rec-vnew-hyps rec-rwp rec-rbinds rec-rval
               rec-record-data-of-rec-record-of-wires
               rec-recordp-of-rec-record-of-wires record-fix-when-recordp rec-recordp-of-rec-rval
               (:e base-prime) car-cons cdr-cons)
  :use ((:instance rec-record-new-sound
                   (pubp (rec-rw-pubp (cdr vw))) (og (rec-rw-og (cdr vw)))
                   (data (rec-rw-data (cdr vw))) (ng (rec-rw-ng (cdr vw)))
                   (vbits (rec-rw-vbits (cdr vw))))
        (:instance rec-vb-record-new
                   (r (rec-record-of-wires (rec-rw-pubp (cdr vw)) (rec-rw-og (cdr vw))
                                           (rec-rw-data (cdr vw)) (rec-rw-ng (cdr vw))
                                           (rec-rw-vbits (cdr vw)) asg)))))

(defruled rec-value-new-sound-dr
  (implies (and (equal (car vw) :dynamic-record)
                (rec-drwp (cdr vw))
                (r1cs::r1cs-valuationp asg (base-prime))
                (rec-vnew-hyps vw asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-vnew-gadget vw) asg (base-prime)))
           (equal (dynamic-record-new (rec-drval (cdr vw) asg)) (rec-drval (cdr vw) asg)))
  :do-not-induct t
  :enable (dynamic-record-new rec-drval))

(defruled rec-value-new-sound-ptx
  (implies (and (equal (car vw) :plaintext)
                (ptx-wtp (cdr vw))
                (rec-vnew-hyps vw asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-vnew-gadget vw) asg (base-prime)))
           (equal (plaintext-new (ptx-val (cdr vw) asg)) (ptx-val (cdr vw) asg)))
  :enable (rec-vnew-gadget rec-vnew-hyps primep-of-base-prime)
  :use (:instance ptx-new-sound (wt (cdr vw)) (p (base-prime))))

(defruled rec-value-new-sound-future
  (implies (and (equal (car vw) :future)
                (rec-fwp (cdr vw))
                (rec-vnew-hyps vw asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-vnew-gadget vw) asg (base-prime)))
           (equal (future-new (rec-fval (cdr vw) asg)) (rec-fval (cdr vw) asg)))
  :enable (rec-vnew-gadget rec-vnew-hyps primep-of-base-prime)
  :use (:instance rec-fnew-sound (fw (cdr vw)) (p (base-prime))))

(defruled rec-value-new-sound-df
  (equal (dynamic-future-new (rec-dfval w asg)) (rec-dfval w asg))
  :enable dynamic-future-new)

(defruled rec-value-new-sound
  :short "R1CS-SOUND of Value::new: the output wires (the input wires) denote
          a value that the funspec returns unchanged."
  (implies (and (equal p (base-prime))
                (rec-vwp vw)
                (r1cs::r1cs-valuationp asg p)
                (rec-vnew-hyps vw asg)
                (r1cs::r1cs-constraints-holdp (rec-vnew-gadget vw) asg p))
           (equal (value-new (rec-vval vw asg)) (rec-vval vw asg)))
  :do-not-induct t
  :in-theory (e/d (rec-vwp rec-vval value-new)
                  (rec-vnew-gadget rec-vnew-hyps))
  :use (rec-value-new-sound-ptx rec-value-new-sound-record
        rec-value-new-sound-future rec-value-new-sound-dr
        (:instance rec-value-new-sound-df (w (cdr vw)))))

(defruled rec-value-new-gadget-arms
  :short "Value::new adds no constraint to its arm's Inject, so its
          completeness is that of the arm: ptx-new-complete, rec-record-new-complete
          with rec-record-data-new-complete, rec-fnew-complete,
          rec-dynamic-record-new-complete, rec-dynamic-future-new-complete."
  (b* ((w (cdr vw)))
    (equal (rec-vnew-gadget vw)
           (case (car vw)
             (:plaintext (ptx-new-gadget w))
             (:record (rec-record-new-gadget (rec-rw-og w) (rec-rw-data w)
                                             (rec-rw-ng w) (rec-rw-vbits w)))
             (:future (rec-fnew-gadget w))
             (:dynamic-record (rec-dynamic-record-new-gadget
                               (rec-drw-og w) (rec-drw-ng w) (rec-drw-vbits w)))
             (otherwise nil))))
  :enable (rec-vnew-gadget rec-dynamic-future-new-gadget))

(defruled rec-value-new-complete
  :short "R1CS-COMPLETE of Value::new on its witness-carrying arms: a plaintext
          (ptx-new-witnessp) or a future (rec-fnew-witnessp) satisfies the
          constraints iff the funspec succeeds, and then the wires denote its
          result; a dynamic future always satisfies them."
  (implies (and (equal p (base-prime))
                (rec-vwp vw))
           (and (implies (and (equal (car vw) :plaintext)
                              (plaintextp pt) (ptx-distinct pt)
                              (ptx-new-witnessp (cdr vw) pt asg p))
                         (and (iff (r1cs::r1cs-constraints-holdp
                                    (rec-vnew-gadget vw) asg p)
                                   (not (reserrp (value-new (value-plaintext pt)))))
                              (implies (not (reserrp (value-new (value-plaintext pt))))
                                       (equal (rec-vval vw asg)
                                              (value-new (value-plaintext pt))))))
                (implies (and (equal (car vw) :future)
                              (futurep f)
                              (rec-fnew-witnessp (cdr vw) f asg p))
                         (and (iff (r1cs::r1cs-constraints-holdp
                                    (rec-vnew-gadget vw) asg p)
                                   (not (reserrp (value-new (value-future f)))))
                              (implies (not (reserrp (value-new (value-future f))))
                                       (equal (rec-vval vw asg)
                                              (value-new (value-future f))))))
                (implies (equal (car vw) :dynamic-future)
                         (r1cs::r1cs-constraints-holdp (rec-vnew-gadget vw) asg p))))
  :do-not-induct t
  :enable (rec-vnew-gadget rec-vwp rec-vval value-new primep-of-base-prime
           rec-dynamic-future-new-gadget)
  :use ((:instance ptx-new-complete (wt (cdr vw)))
        (:instance rec-fnew-complete (fw (cdr vw)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Future::find: a synthesis-time walk over the argument wires (indices are
; constants, member lookup is IndexMap::get on constant identifiers), no
; constraint.  An argument wire is a value wire of the same kind.

(define rec-ffind-aux (aw (path access-listp))
  :measure (len path)
  (b* (((when (endp path)) aw)
       (access (car path))
       (w (cdr aw)))
    (cond
     ((and (eq (car aw) :plaintext)
           (eq (car w) :struct)
           (acl2::access-case access :member))
      (b* ((member (ptx-wms-lookup (acl2::access-member->name access) (cdr w)))
           ((unless member) :error))
        (rec-ffind-aux (cons :plaintext member) (cdr path))))
     ((and (eq (car aw) :plaintext)
           (eq (car w) :array)
           (acl2::access-case access :index))
      (b* ((index (acl2::access-index->index access))
           ((unless (< index (len (cdr w)))) :error))
        (rec-ffind-aux (cons :plaintext (nth index (cdr w))) (cdr path))))
     ((and (eq (car aw) :future)
           (acl2::access-case access :index))
      (b* ((index (acl2::access-index->index access))
           ((unless (< index (len (cddr w)))) :error))
        (rec-ffind-aux (nth index (cddr w)) (cdr path))))
     (t :error))))

(define rec-ffind (fw (path access-listp))
  (if (endp path) :error (rec-ffind-aux (cons :future fw) path)))

(defruled rec-vval-of-argument-wire
  (implies (rec-awp aw)
           (equal (rec-vval aw asg)
                  (values-argument-to-value (rec-aval aw asg))))
  :expand ((rec-awp aw) (rec-aval aw asg))
  :enable (rec-vval values-argument-to-value))

(defrule rec-awp-nth-of-awsp
  (implies (and (rec-awsp aws) (< (nfix n) (len aws)))
           (rec-awp (nth n aws)))
  :induct (nth n aws)
  :expand ((rec-awsp aws))
  :enable nth)

(defrule rec-nth-of-avals
  (implies (< (nfix n) (len aws))
           (equal (nth n (rec-avals aws asg))
                  (rec-aval (nth n aws) asg)))
  :induct (nth n aws)
  :expand ((rec-avals aws asg))
  :enable nth)

(defruled ptx-wtp-nth-of-wtsp
  (implies (and (ptx-wtsp wts) (< (nfix n) (len wts)))
           (ptx-wtp (nth n wts)))
  :induct (nth n wts)
  :enable (nth ptx-wtsp))

(defruled rec-ffind-aux-sound
  (implies (rec-awp aw)
           (b* ((out (rec-ffind-aux aw path))
                (spec (values-future-find-aux (rec-aval aw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (rec-awp out)
                                (equal (rec-vval out asg) spec))))))
  :induct (rec-ffind-aux aw path)
  :in-theory (enable (:induction rec-ffind-aux))
  :expand ((rec-ffind-aux aw path)
           (:free (x) (values-future-find-aux x path))
           (rec-aval aw asg)
           (rec-awp aw)
           (:free (x) (rec-awp (cons :plaintext x)))
           (:free (x) (rec-aval (cons :plaintext x) asg))
           (ptx-val (cdr aw) asg)
           (ptx-wtp (cdr aw))
           (rec-fwp (cdr aw))
           (rec-fval (cdr aw) asg))
  :enable (rec-vval-of-argument-wire ptx-wtp-nth-of-wtsp spec-error))

(defruled rec-ffind-sound
  :short "R1CS-SOUND (and the success condition) of Future::find."
  (implies (rec-fwp fw)
           (b* ((out (rec-ffind fw path))
                (spec (future-find (rec-fval fw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (rec-awp out)
                                (equal (rec-vval out asg) spec))))))
  :do-not-induct t
  :enable (rec-ffind future-find spec-error)
  :use (:instance rec-ffind-aux-sound (aw (cons :future fw)))
  :expand ((rec-awp (cons :future fw)) (rec-aval (cons :future fw) asg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Value::find: dispatch, no constraint.  A record entry's plaintext is the
; plaintext wire tree of the entry wire; the owner (of a record or a dynamic
; record) is the address on the owner's point wires.

(define rec-vfind (vw (path access-listp))
  (b* ((w (cdr vw)))
    (case (car vw)
      (:plaintext (b* ((out (ptx-find w path)))
                    (if (equal out :error) :error (cons :plaintext out))))
      (:record (b* ((out (rec-record-find (rec-rw-data w) path)))
                 (cond ((equal out :error) :error)
                       ((equal out :owner) (cons :owner-address (rec-rw-og w)))
                       (t (cons :plaintext (cdr out))))))
      (:future (rec-ffind w path))
      (:dynamic-record (if (values-access-is-owner-p path)
                           (cons :owner-address (rec-drw-og w))
                         :error))
      (otherwise :error))))

(define rec-vfind-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(define rec-vfind-hyps (vw asg)
  :short "The owner point of a record or dynamic record is on the curve
          (what Address::new in Record::new / DynamicRecord::new establishes)."
  (b* ((w (cdr vw)))
    (case (car vw)
      (:record (groupp (rec-point-of (rec-rw-og w) asg)))
      (:dynamic-record (groupp (rec-point-of (rec-drw-og w) asg)))
      (otherwise t))))

(defruled rec-value-find-sound-ptx
  (implies (and (equal (car vw) :plaintext)
                (ptx-wtp (cdr vw)))
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :do-not-induct t
  :enable (rec-vfind rec-vval value-find)
  :use (:instance ptx-find-sound (wt (cdr vw)) (p (base-prime)))
  :expand ((r1cs::r1cs-constraints-holdp (ptx-find-gadget) asg (base-prime)))
  :hints ('(:in-theory (enable ptx-find-gadget))))

(defruled rec-value-find-sound-future
  (implies (and (equal (car vw) :future)
                (rec-fwp (cdr vw)))
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :do-not-induct t
  :enable (rec-vfind rec-vval value-find)
  :use (:instance rec-ffind-sound (fw (cdr vw))))

(defruled rec-value-find-sound-dr
  (implies (and (equal (car vw) :dynamic-record)
                (rec-vfind-hyps vw asg))
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :do-not-induct t
  :enable (rec-vfind rec-vval value-find rec-vfind-hyps dynamic-record-find
           rec-drval rec-dynamic-record-of-wires rec-point-of spec-error))

(defruled rec-value-find-sound-df
  (implies (equal (car vw) :dynamic-future)
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :enable (rec-vfind rec-vval value-find spec-error))

(defruled rec-owner-to-entry-plaintext
  (implies (groupp g)
           (and (equal (values-entry-plaintext (crypto-owner-to-entry (owner-public g)))
                       (plaintext-literal (literal-address g)))
                (equal (values-entry-plaintext (crypto-owner-to-entry (owner-private g)))
                       (plaintext-literal (literal-address g)))))
  :enable (crypto-owner-to-entry values-entry-plaintext))

(defruled rec-value-find-sound-record
  (implies (and (equal (car vw) :record)
                (rec-rwp (cdr vw))
                (rec-vfind-hyps vw asg)
                (access-listp path))
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :do-not-induct t
  :in-theory (e/d (rec-vfind rec-vval value-find rec-vfind-hyps rec-rwp rec-rval
                   rec-owner-to-entry-plaintext ptx-eval ptx-entry-plaintext-of-wrap
                   rec-record-of-wires rec-point-of)
                  (rec-record-find crypto-record-find values-record-find))
  :use ((:instance rec-record-find-sound
                   (pubp (rec-rw-pubp (cdr vw))) (og (rec-rw-og (cdr vw)))
                   (data (rec-rw-data (cdr vw))) (ng (rec-rw-ng (cdr vw)))
                   (vbits (rec-rw-vbits (cdr vw))))
        (:instance rec-vb-record-find (r (rec-rval (cdr vw) asg)))))

(defruled rec-value-find-sound
  :short "R1CS-SOUND (and the success condition) of Value::find: no
          constraint; the output wires denote the funspec's result, and the
          circuit halts exactly where the funspec errs."
  (implies (and (rec-vwp vw)
                (rec-vfind-hyps vw asg)
                (access-listp path)
                (r1cs::r1cs-constraints-holdp (rec-vfind-gadget) asg p))
           (b* ((out (rec-vfind vw path))
                (spec (value-find (rec-vval vw asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (rec-vval out asg) spec)))))
  :do-not-induct t
  :in-theory '(rec-vwp)
  :use (rec-value-find-sound-ptx rec-value-find-sound-record
        rec-value-find-sound-future rec-value-find-sound-dr
        rec-value-find-sound-df))

(defruled rec-value-find-complete
  (r1cs::r1cs-constraints-holdp (rec-vfind-gadget) asg p)
  :enable rec-vfind-gadget)
