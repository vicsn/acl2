; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unconditional forms of the enforce_in_group soundness and
; unsatisfiability theorems and of the group, address and signature arms of
; Literal::new soundness.  Each is the stored formula of the conditional
; theorem with the hypothesis (edwards-bls12-cofactor-clears) replaced by T,
; which edwards-bls12-cofactor-clears-holds discharges.

(in-package "ALEOVM")

(include-book "group-cofactor-clears")
(include-book "group-enforce-in-group-complete")
(include-book "literal-new-r1cs")

(defun subst-tree-equal (new old tree)
  (declare (xargs :mode :program))
  (cond ((equal tree old) new)
        ((atom tree) tree)
        (t (cons (subst-tree-equal new old (car tree))
                 (subst-tree-equal new old (cdr tree))))))

(defmacro drop-cofactor-hyp (new old)
  `(make-event
    (let ((f (acl2::formula ',old nil (w state))))
      (acl2::value
       (list 'defthm ',new
             (subst-tree-equal ''t '(edwards-bls12-cofactor-clears) f)
             :rule-classes nil
             :hints '(("Goal"
                       :use (,old edwards-bls12-cofactor-clears-holds)
                       :in-theory (theory 'minimal-theory))))))))

(drop-cofactor-hyp group-enforce-in-group-sound-unconditional
                   group-enforce-in-group-sound)

(drop-cofactor-hyp group-enforce-in-group-unsat-when-not-groupp-unconditional
                   group-enforce-in-group-unsat-when-not-groupp)

(drop-cofactor-hyp literal-group-new-sound-unconditional
                   literal-group-new-sound)

(drop-cofactor-hyp literal-address-new-sound-unconditional
                   literal-address-new-sound)

(drop-cofactor-hyp literal-signature-new-sound-unconditional
                   literal-signature-new-sound)

(assert-event
 (not (acl2::ffnnamep-lst
       'edwards-bls12-cofactor-clears
       (list
        (acl2::formula 'group-enforce-in-group-sound-unconditional nil (w state))
        (acl2::formula 'group-enforce-in-group-unsat-when-not-groupp-unconditional nil (w state))
        (acl2::formula 'literal-group-new-sound-unconditional nil (w state))
        (acl2::formula 'literal-address-new-sound-unconditional nil (w state))
        (acl2::formula 'literal-signature-new-sound-unconditional nil (w state))))))
