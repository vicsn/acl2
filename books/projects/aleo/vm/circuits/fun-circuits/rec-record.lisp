; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record<Plaintext>::new (snarkVM circuit/program/src/data/record/mod.rs,
; Inject): Owner::new (Address::new on the owner address, either variant),
; Identifier::constant on each entry name and Entry::new on each entry,
; Group::new on the nonce, U8::new on the version, in that order.
;
; A record wire is the owner tag pubp, the 14 wires og of the owner's
; Address::new, the data as a list of (name . entry-wire) with constant
; names (entry wires as in ptx-entry), the 14 wires ng of the nonce's
; Group::new, and the 8 version bit wires.

(in-package "ALEOVM")

(include-book "rec-dynamic-record")
(include-book "ptx-entry")

(set-verify-guards-eagerness 0)

(define rec-record-datawp (data)
  (if (atom data)
      (null data)
    (and (consp (car data))
         (identifierp (caar data))
         (ptx-ewtp (cdar data))
         (rec-record-datawp (cdr data)))))

(define rec-record-data-eval (data asg)
  (if (atom data)
      nil
    (cons (record-entry (caar data) (ptx-eval (cdar data) asg))
          (rec-record-data-eval (cdr data) asg))))

(define rec-record-data-distinct (data asg)
  (if (atom data)
      t
    (and (ptx-distinct (ptx-val (cdr (cdar data)) asg))
         (rec-record-data-distinct (cdr data) asg))))

(define rec-record-data-new-gadget (data)
  (if (atom data)
      nil
    (append (ptx-entry-new-gadget (cdar data))
            (rec-record-data-new-gadget (cdr data)))))

(define rec-record-data-newp (data)
  :short "Entry::new returns each entry unchanged."
  (if (atom data)
      t
    (and (equal (entry-new (record-entry->entry (car data)))
                (record-entry->entry (car data)))
         (rec-record-data-newp (cdr data)))))

(defrule rec-record-entry-listp-of-data-eval
  (implies (rec-record-datawp data)
           (record-entry-listp (rec-record-data-eval data asg)))
  :enable (rec-record-datawp rec-record-data-eval))

(defruled rec-record-data-new-sound
  (implies (and (primep p)
                (rec-record-datawp data)
                (rec-record-data-distinct data asg)
                (r1cs::r1cs-constraints-holdp (rec-record-data-new-gadget data)
                                              asg p))
           (rec-record-data-newp (rec-record-data-eval data asg)))
  :induct (rec-record-datawp data)
  :enable (rec-record-datawp rec-record-data-eval rec-record-data-distinct
           rec-record-data-new-gadget rec-record-data-newp
           r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use (:instance ptx-entry-new-sound (ew (cdar data))))))

(define rec-record-data-new-witnessp (data pts asg p)
  :short "Each entry wire carries the witness of its plaintext, and no
          plaintext makes Plaintext::new halt."
  (if (atom data)
      (atom pts)
    (and (consp pts)
         (plaintextp (car pts))
         (ptx-distinct (car pts))
         (ptx-new-witnessp (cdr (cdar data)) (car pts) asg p)
         (not (reserrp (plaintext-new (car pts))))
         (rec-record-data-new-witnessp (cdr data) (cdr pts) asg p))))

(defruled rec-record-data-new-complete
  (implies (and (primep p)
                (rec-record-datawp data)
                (rec-record-data-new-witnessp data pts asg p))
           (r1cs::r1cs-constraints-holdp (rec-record-data-new-gadget data)
                                         asg p))
  :induct (rec-record-data-new-witnessp data pts asg p)
  :enable (rec-record-datawp rec-record-data-new-witnessp
           rec-record-data-new-gadget
           r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use (:instance ptx-entry-new-complete
                           (ew (cdar data)) (pt (car pts))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rec-record-new-gadget ((og symbol-listp) data (ng symbol-listp)
                               (vbits symbol-listp))
  :short "Constraints of @('Record<Plaintext>::new')."
  (append (rec-enforce-in-group og)
          (rec-record-data-new-gadget data)
          (rec-enforce-in-group ng)
          (int-new-gadget vbits (base-prime))))

(define rec-point-of (g asg)
  (ecurve::point-finite (lookup-equal (nth 0 g) asg)
                        (lookup-equal (nth 1 g) asg)))

(define rec-owner-input (pubp pt)
  :short "The console owner Owner::new receives."
  (if pubp pt (plaintext-literal (literal-address pt))))

(define rec-record-of-wires (pubp og data ng vbits asg)
  (b* ((pt (rec-point-of og asg)))
    (record (if pubp (owner-public pt) (owner-private pt))
            (rec-record-data-eval data asg)
            (rec-point-of ng asg)
            (lebits=>nat (lookup-equal-list vbits asg)))))

(defmacro rec-record-new-hyps (&rest more)
  `(and (booleanp pubp)
        (symbol-listp og) (equal (len og) 14)
        (symbol-listp ng) (equal (len ng) 14)
        (symbol-listp vbits) (equal (len vbits) 8)
        (rec-record-datawp data)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-binds-allp asg og)
        (r1cs::valuation-binds-allp asg ng)
        (r1cs::valuation-binds-allp asg vbits)
        ,@more))

(defruled rec-record-new-sound
  (b* ((owner (rec-point-of og asg))
       (nonce (rec-point-of ng asg))
       (vvals (lookup-equal-list vbits asg))
       (data$ (rec-record-data-eval data asg)))
    (implies (rec-record-new-hyps
              (rec-record-data-distinct data asg)
              (r1cs::r1cs-constraints-holdp
               (rec-record-new-gadget og data ng vbits) asg (base-prime)))
             (and (groupp owner)
                  (groupp nonce)
                  (bit-listp vvals)
                  (rec-record-data-newp data$)
                  (equal (crypto-record-new pubp (rec-owner-input pubp owner)
                                            data$ nonce (lebits=>nat vvals))
                         (rec-record-of-wires pubp og data ng vbits asg)))))
  :do-not-induct t
  :enable (rec-record-new-gadget rec-record-of-wires rec-owner-input
           rec-point-of crypto-record-new crypto-owner-new
           r1cs::r1cs-constraints-holdp-of-append
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p)
  :use ((:instance rec-enforce-in-group-sound (g og))
        (:instance rec-enforce-in-group-sound (g ng))
        (:instance rec-record-data-new-sound (p (base-prime)))
        (:instance int-new-gadget-sound
                   (xs vbits) (p (base-prime)) (n 8) (signedp nil))))

(defruled rec-record-new-complete
  :short "The constraints hold iff each component's gadget holds: owner and
          nonce by group-enforce-in-group-gadget-complete, the version by
          int-new-gadget-complete, and the data by
          rec-record-data-new-complete."
  (equal (r1cs::r1cs-constraints-holdp
          (rec-record-new-gadget og data ng vbits) asg (base-prime))
         (and (r1cs::r1cs-constraints-holdp (rec-enforce-in-group og)
                                            asg (base-prime))
              (r1cs::r1cs-constraints-holdp (rec-record-data-new-gadget data)
                                            asg (base-prime))
              (r1cs::r1cs-constraints-holdp (rec-enforce-in-group ng)
                                            asg (base-prime))
              (r1cs::r1cs-constraints-holdp (int-new-gadget vbits (base-prime))
                                            asg (base-prime))))
  :enable (rec-record-new-gadget r1cs::r1cs-constraints-holdp-of-append))
