; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Future / Argument wire trees and Future::new / Argument::new
; (snarkVM circuit/program/src/data/future/{mod.rs,argument.rs}).
;
; A future wire tree is (pid fname . aws): the program ID and function name
; are synthesis-time constants (ProgramID::constant, Identifier::constant);
; aws are argument wire trees:
;   (:plaintext . wt)        a ptx- plaintext wire tree,
;   (:future . fw)           a nested future wire tree,
;   (:dynamic-future . dfw)  dfw = (pn pw fn ck bitss rss): the four field
;                            wires of a DynamicFuture and the bit / range-check
;                            wires its write_bits uses.

(in-package "ALEOVM")

(include-book "rec-record")
(include-book "rec-dynamic-record-eq")
(include-book "prog-equal")

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture leaves.

(define rec-dfw-xs (dfw)
  (list (nth 0 dfw) (nth 1 dfw) (nth 2 dfw) (nth 3 dfw)))

(define rec-dfwp (dfw)
  (and (symbol-listp (rec-dfw-xs dfw))
       (rec-bits-shapep (rec-dfw-xs dfw) (nth 4 dfw) (nth 5 dfw))))

(define rec-dfval (dfw asg)
  (rec-dynamic-future-of-wires (nth 0 dfw) (nth 1 dfw) (nth 2 dfw) (nth 3 dfw)
                               asg))

(defrule rec-dynamic-futurep-of-dfval
  (dynamic-futurep (rec-dfval dfw asg))
  :enable rec-dfval)

(define rec-dftyped (dfw asg)
  (rec-bits-boundp asg (rec-dfw-xs dfw) (nth 4 dfw) (nth 5 dfw)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Wire trees.

(defines rec-fwp
  (define rec-fwp (x)
    :measure (acl2-count x)
    (and (consp x) (consp (cdr x))
         (program-idp (car x))
         (identifierp (cadr x))
         (rec-awsp (cddr x))))
  (define rec-awp (x)
    :measure (acl2-count x)
    (and (consp x)
         (case (car x)
           (:plaintext (ptx-wtp (cdr x)))
           (:future (rec-fwp (cdr x)))
           (:dynamic-future (rec-dfwp (cdr x)))
           (otherwise nil))))
  (define rec-awsp (x)
    :measure (acl2-count x)
    (if (atom x)
        (null x)
      (and (rec-awp (car x))
           (rec-awsp (cdr x))))))

(defines rec-fval
  :flag-local nil
  (define rec-fval (fw asg)
    :measure (acl2-count fw)
    (if (consp fw)
        (future (car fw) (cadr fw) (rec-avals (cddr fw) asg))
      (future nil nil nil)))
  (define rec-aval (aw asg)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (argument-plaintext (ptx-val (cdr aw) asg)))
      (:future (argument-future (rec-fval (cdr aw) asg)))
      (otherwise (argument-dynamic-future (rec-dfval (cdr aw) asg)))))
  (define rec-avals (aws asg)
    :measure (acl2-count aws)
    (if (atom aws)
        nil
      (cons (rec-aval (car aws) asg)
            (rec-avals (cdr aws) asg))))
  ///
  (defrule rec-futurep-of-fval
    (futurep (rec-fval fw asg))
    :expand ((rec-fval fw asg)))
  (defrule rec-argumentp-of-aval
    (argumentp (rec-aval aw asg))
    :expand ((rec-aval aw asg)))
  (defrule rec-argument-listp-of-avals
    (argument-listp (rec-avals aws asg))
    :induct (len aws)
    :expand ((rec-avals aws asg)))
  (defrule rec-len-of-avals
    (equal (len (rec-avals aws asg)) (len aws))
    :induct (len aws)
    :expand ((rec-avals aws asg))))

(defines rec-ftyped
  (define rec-ftyped (fw asg)
    :measure (acl2-count fw)
    (and (consp fw) (rec-atyped-list (cddr fw) asg)))
  (define rec-atyped (aw asg)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-typed (cdr aw) asg))
      (:future (rec-ftyped (cdr aw) asg))
      (otherwise (rec-dftyped (cdr aw) asg))))
  (define rec-atyped-list (aws asg)
    :measure (acl2-count aws)
    (if (atom aws)
        t
      (and (rec-atyped (car aws) asg)
           (rec-atyped-list (cdr aws) asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Future::new / Argument::new.

(defines rec-fnew-gadget
  (define rec-fnew-gadget (fw)
    :measure (acl2-count fw)
    (and (consp fw) (rec-asnew-gadget (cddr fw))))
  (define rec-anew-gadget (aw)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-new-gadget (cdr aw)))
      (:future (rec-fnew-gadget (cdr aw)))
      (otherwise (rec-dynamic-future-new-gadget))))
  (define rec-asnew-gadget (aws)
    :measure (acl2-count aws)
    (if (atom aws)
        nil
      (append (rec-anew-gadget (car aws))
              (rec-asnew-gadget (cdr aws))))))

(defines rec-fdistinct
  :short "Each plaintext argument has distinct member names (ptx-distinct)."
  (define rec-fdistinct (fw asg)
    :measure (acl2-count fw)
    (and (consp fw) (rec-asdistinct (cddr fw) asg)))
  (define rec-adistinct (aw asg)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-distinct (ptx-val (cdr aw) asg)))
      (:future (rec-fdistinct (cdr aw) asg))
      (otherwise t)))
  (define rec-asdistinct (aws asg)
    :measure (acl2-count aws)
    (if (atom aws)
        t
      (and (rec-adistinct (car aws) asg)
           (rec-asdistinct (cdr aws) asg)))))

(defines rec-ptyped
  :short "The plaintext arguments are typed (what Plaintext::new establishes)."
  (define rec-ptyped (fw asg)
    :measure (acl2-count fw)
    (and (consp fw) (rec-aptyped-list (cddr fw) asg)))
  (define rec-aptyped (aw asg)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-typed (cdr aw) asg))
      (:future (rec-ptyped (cdr aw) asg))
      (otherwise t)))
  (define rec-aptyped-list (aws asg)
    :measure (acl2-count aws)
    (if (atom aws)
        t
      (and (rec-aptyped (car aws) asg)
           (rec-aptyped-list (cdr aws) asg)))))

(defrule rec-list-fns-of-atom
  (implies (atom aws)
           (and (equal (rec-avals aws asg) nil)
                (equal (rec-atyped-list aws asg) t)
                (equal (rec-aptyped-list aws asg) t)
                (equal (rec-asdistinct aws asg) t)
                (equal (rec-asnew-gadget aws) nil)))
  :enable (rec-avals rec-atyped-list rec-aptyped-list rec-asdistinct
           rec-asnew-gadget))

(defruled rec-ptx-new-sound-rw
  (implies (and (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p)
                (primep p)
                (ptx-wtp wt)
                (ptx-distinct (ptx-val wt asg)))
           (and (ptx-typed wt asg)
                (equal (plaintext-new (ptx-val wt asg))
                       (ptx-val wt asg))))
  :use ptx-new-sound)

(defthm-rec-fval-flag
  (defthm rec-fnew-sound
    (implies (and (primep p)
                  (rec-fwp fw)
                  (rec-fdistinct fw asg)
                  (r1cs::r1cs-constraints-holdp (rec-fnew-gadget fw) asg p))
             (and (rec-ptyped fw asg)
                  (equal (future-new (rec-fval fw asg)) (rec-fval fw asg))))
    :flag rec-fval)
  (defthm rec-anew-sound
    (implies (and (primep p)
                  (rec-awp aw)
                  (rec-adistinct aw asg)
                  (r1cs::r1cs-constraints-holdp (rec-anew-gadget aw) asg p))
             (and (rec-aptyped aw asg)
                  (equal (argument-new (rec-aval aw asg)) (rec-aval aw asg))))
    :flag rec-aval)
  (defthm rec-asnew-sound
    (implies (and (primep p)
                  (rec-awsp aws)
                  (rec-asdistinct aws asg)
                  (r1cs::r1cs-constraints-holdp (rec-asnew-gadget aws) asg p))
             (and (rec-aptyped-list aws asg)
                  (equal (values-arguments-new (rec-avals aws asg))
                         (rec-avals aws asg))))
    :flag rec-avals)
  :hints (("Goal"
           :in-theory (enable future-new argument-new values-arguments-new
                              dynamic-future-new rec-dynamic-future-new-gadget
                              rec-ptx-new-sound-rw
                              r1cs::r1cs-constraints-holdp-of-append)
           :expand ((rec-fwp fw) (rec-awp aw) (rec-awsp aws)
                    (rec-fval fw asg) (rec-aval aw asg) (rec-avals aws asg)
                    (rec-fdistinct fw asg) (rec-adistinct aw asg)
                    (rec-asdistinct aws asg)
                    (rec-fnew-gadget fw) (rec-anew-gadget aw)
                    (rec-asnew-gadget aws)
                    (rec-ptyped fw asg) (rec-aptyped aw asg)
                    (rec-aptyped-list aws asg)))))

(in-theory (disable rec-fnew-sound rec-anew-sound rec-asnew-sound))

(defines rec-fnew-witnessp
  :short "The console future f the wires carry: the constant program ID and
          function name are f's, each plaintext argument carries Plaintext::new's
          witness for f's plaintext (ptx-new-witnessp, distinct member names),
          and each DynamicFuture argument's wires hold f's dynamic future."
  :flag-local nil
  (define rec-fnew-witnessp (fw f asg p)
    :measure (acl2-count fw)
    (and (consp fw)
         (equal (car fw) (future->program-id f))
         (equal (cadr fw) (future->function-name f))
         (rec-asnew-witnessp (cddr fw) (future->arguments f) asg p)))
  (define rec-anew-witnessp (aw a asg p)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (and (argument-case a :plaintext)
                       (ptx-distinct (argument-plaintext->get a))
                       (ptx-new-witnessp (cdr aw) (argument-plaintext->get a)
                                         asg p)))
      (:future (and (argument-case a :future)
                    (rec-fnew-witnessp (cdr aw) (argument-future->get a) asg p)))
      (otherwise (and (argument-case a :dynamic-future)
                      (equal (rec-dfval (cdr aw) asg)
                             (argument-dynamic-future->get a))))))
  (define rec-asnew-witnessp (aws as asg p)
    :measure (acl2-count aws)
    (if (atom aws)
        (atom as)
      (and (consp as)
           (rec-anew-witnessp (car aws) (car as) asg p)
           (rec-asnew-witnessp (cdr aws) (cdr as) asg p)))))

(defrule rec-asnew-witnessp-of-atom
  (and (implies (atom aws)
                (equal (rec-asnew-witnessp aws as asg p) (atom as)))
       (implies (and (consp aws) (atom as))
                (not (rec-asnew-witnessp aws as asg p))))
  :expand ((rec-asnew-witnessp aws as asg p)))

(defruled rec-ptx-new-complete-rw
  (implies (and (ptx-new-witnessp wt pt asg p)
                (primep p)
                (ptx-wtp wt)
                (plaintextp pt)
                (ptx-distinct pt))
           (and (iff (r1cs::r1cs-constraints-holdp (ptx-new-gadget wt) asg p)
                     (not (reserrp (plaintext-new pt))))
                (implies (not (reserrp (plaintext-new pt)))
                         (equal (ptx-val wt asg) (plaintext-new pt)))))
  :use ptx-new-complete)

(defthm-rec-fnew-witnessp-flag
  (defthm rec-fnew-complete
    (implies (and (primep p)
                  (rec-fwp fw)
                  (futurep f)
                  (rec-fnew-witnessp fw f asg p))
             (and (iff (r1cs::r1cs-constraints-holdp (rec-fnew-gadget fw) asg p)
                       (not (reserrp (future-new f))))
                  (implies (not (reserrp (future-new f)))
                           (equal (rec-fval fw asg) (future-new f)))))
    :flag rec-fnew-witnessp)
  (defthm rec-anew-complete
    (implies (and (primep p)
                  (rec-awp aw)
                  (argumentp a)
                  (rec-anew-witnessp aw a asg p))
             (and (iff (r1cs::r1cs-constraints-holdp (rec-anew-gadget aw) asg p)
                       (not (reserrp (argument-new a))))
                  (implies (not (reserrp (argument-new a)))
                           (equal (rec-aval aw asg) (argument-new a)))))
    :flag rec-anew-witnessp)
  (defthm rec-asnew-complete
    (implies (and (primep p)
                  (rec-awsp aws)
                  (argument-listp as)
                  (rec-asnew-witnessp aws as asg p))
             (and (iff (r1cs::r1cs-constraints-holdp (rec-asnew-gadget aws) asg p)
                       (not (reserrp (values-arguments-new as))))
                  (implies (not (reserrp (values-arguments-new as)))
                           (equal (rec-avals aws asg)
                                  (values-arguments-new as)))))
    :flag rec-asnew-witnessp)
  :hints (("Goal"
           :in-theory (enable future-new argument-new values-arguments-new
                              dynamic-future-new rec-dynamic-future-new-gadget
                              rec-ptx-new-complete-rw
                              r1cs::r1cs-constraints-holdp-of-append)
           :expand ((rec-fwp fw) (rec-awp aw) (rec-awsp aws)
                    (rec-fval fw asg) (rec-aval aw asg) (rec-avals aws asg)
                    (rec-fnew-witnessp fw f asg p) (rec-anew-witnessp aw a asg p)
                    (rec-asnew-witnessp aws as asg p)
                    (rec-fnew-gadget fw) (rec-anew-gadget aw)
                    (rec-asnew-gadget aws)))))

(in-theory (disable rec-fnew-complete rec-anew-complete rec-asnew-complete))
