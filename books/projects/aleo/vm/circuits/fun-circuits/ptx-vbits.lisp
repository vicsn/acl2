; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext and Entry write_bits_le / _be, write_bits_raw_le / _be,
; to_fields, to_fields_raw, size_in_fields and num_randomizers over a leaf
; interface with the hypotheses the per-type Literal::write_bits theorems
; need: the prime is the base prime, the assignment is a valuation, and
; the public unit wire ptx-one holds 1 (Field::write_bits uses
; Circuit::one() in its range check).  Coverage of the leaf's wires is
; part of the leaf's typed predicate.  The circuit and the proofs are
; those of ptx-bits.lisp and ptx-entry.lisp; their interface stays as it
; is, since rec-record-bits.lisp builds on it.

(in-package "ALEOVM")

(include-book "ptx-entry")

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-vbits-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

(local (in-theory (enable ptx-entry-plaintext-of-wrap
                          ptx-entry-vis-bits-of-wrap
                          ptx-eval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf interface: Literal::write_bits_le / _be.

(defconst *ptx-vfalse-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-vleaf-bits-gadget * *) => *)
   ((ptx-vleaf-bits-out * *) => *)
   ((ptx-vleaf-bits-witnessp * * * *) => *))

  (local (defun ptx-vleaf-bits-gadget (w bigp)
           (declare (ignore w bigp))
           (list *ptx-vfalse-constraint*)))
  (local (defun ptx-vleaf-bits-out (w bigp) (declare (ignore w bigp)) nil))
  (local (defun ptx-vleaf-bits-witnessp (w bigp asg p)
           (declare (ignore w bigp asg p))
           nil))

  (defruled ptx-vleaf-bits-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-leaf-typed w asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vleaf-bits-gadget w bigp)
                                                asg p))
             (equal (ptx-terms-val (ptx-vleaf-bits-out w bigp) asg)
                    (if bigp
                        (literal-to-bits-be (ptx-leaf-val w asg))
                      (literal-to-bits-le (ptx-leaf-val w asg)))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep)
    :prep-lemmas
    ((defrule mod-1-when-big
       (implies (and (integerp p) (<= 2 p))
                (equal (mod 1 p) 1))
       :enable mod)))

  (defruled ptx-vleaf-bits-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-leaf-typed w asg)
                  (ptx-vleaf-bits-witnessp w bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-vleaf-bits-gadget w bigp)
                                           asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; write_bits_le / write_bits_be.

(defines ptx-vbits-out
  :flag-local nil
  :short "The output bit terms of Plaintext::write_bits_le (@('bigp') nil)
          or write_bits_be."

  (define ptx-vbits-out (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (append (list 0 1)
                       (values-uint-to-bits (len (cdr wt)) 8 bigp)
                       (ptx-vmbits-out (cdr wt) bigp)))
      (:array (append (list 1 0)
                      (values-uint-to-bits (len (cdr wt)) 32 bigp)
                      (ptx-vlbits-out (cdr wt) bigp)))
      (otherwise (append (list 0 0)
                         (values-uint-to-bits (ptx-leaf-variant (cdr wt)) 8 bigp)
                         (values-uint-to-bits (ptx-leaf-size (cdr wt)) 16 bigp)
                         (ptx-vleaf-bits-out (cdr wt) bigp)))))

  (define ptx-vmbits-out (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (b* ((name (identifier-fix (car (car wms))))
           (value-bits (ptx-vbits-out (cdr (car wms)) bigp)))
        (append (values-uint-to-bits (identifier-size-in-bits name) 8 bigp)
                (values-identifier-to-bits name bigp)
                (values-uint-to-bits (len value-bits) 16 bigp)
                value-bits
                (ptx-vmbits-out (cdr wms) bigp)))))

  (define ptx-vlbits-out (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (b* ((value-bits (ptx-vbits-out (car wts) bigp)))
        (append (values-uint-to-bits (len value-bits) 16 bigp)
                value-bits
                (ptx-vlbits-out (cdr wts) bigp))))))

(defines ptx-vbits-gadget
  :flag-local nil
  :short "The constraints of Plaintext::write_bits_le / _be: those of the
          leaves, in order."

  (define ptx-vbits-gadget (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-vmbits-gadget (cdr wt) bigp))
      (:array (ptx-vlbits-gadget (cdr wt) bigp))
      (otherwise (ptx-vleaf-bits-gadget (cdr wt) bigp))))

  (define ptx-vmbits-gadget (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-vbits-gadget (cdr (car wms)) bigp)
              (ptx-vmbits-gadget (cdr wms) bigp))))

  (define ptx-vlbits-gadget (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-vbits-gadget (car wts) bigp)
              (ptx-vlbits-gadget (cdr wts) bigp)))))

(defines ptx-vbits-witnessp
  :flag-local nil
  :short "Every leaf carries the witness of its Literal::write_bits."

  (define ptx-vbits-witnessp (wt bigp asg p)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-vmbits-witnessp (cdr wt) bigp asg p))
      (:array (ptx-vlbits-witnessp (cdr wt) bigp asg p))
      (otherwise (and (ptx-vleaf-bits-witnessp (cdr wt) bigp asg p) t))))

  (define ptx-vmbits-witnessp (wms bigp asg p)
    :measure (acl2-count wms)
    (if (atom wms)
        t
      (and (ptx-vbits-witnessp (cdr (car wms)) bigp asg p)
           (ptx-vmbits-witnessp (cdr wms) bigp asg p))))

  (define ptx-vlbits-witnessp (wts bigp asg p)
    :measure (acl2-count wts)
    (if (atom wts)
        t
      (and (ptx-vbits-witnessp (car wts) bigp asg p)
           (ptx-vlbits-witnessp (cdr wts) bigp asg p)))))

(local (in-theory (disable values-uint-to-bits)))

(local (in-theory (enable ptx-to-bits-of-literal ptx-to-bits-of-struct
                          ptx-to-bits-of-array ptx-members-to-bits-of-cons
                          ptx-members-to-bits-of-nil ptx-elements-to-bits-of-cons
                          ptx-elements-to-bits-of-nil ptx-to-bits-raw-of-literal
                          ptx-to-bits-raw-of-struct ptx-to-bits-raw-of-array
                          ptx-members-to-bits-raw-of-cons
                          ptx-members-to-bits-raw-of-nil
                          ptx-elements-to-bits-raw-of-cons
                          ptx-elements-to-bits-raw-of-nil)))

(defthm-ptx-vbits-out-flag
  (defthm ptx-vbits-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-typed wt asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt bigp) asg p))
             (equal (ptx-terms-val (ptx-vbits-out wt bigp) asg)
                    (values-plaintext-to-bits (ptx-val wt asg) bigp)))
    :flag ptx-vbits-out)
  (defthm ptx-vmbits-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-mtyped wms asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vmbits-gadget wms bigp) asg p))
             (equal (ptx-terms-val (ptx-vmbits-out wms bigp) asg)
                    (values-plaintext-members-to-bits (ptx-mval wms asg) bigp)))
    :flag ptx-vmbits-out)
  (defthm ptx-vlbits-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-ltyped wts asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vlbits-gadget wts bigp) asg p))
             (equal (ptx-terms-val (ptx-vlbits-out wts bigp) asg)
                    (values-plaintext-elements-to-bits (ptx-lval wts asg) bigp)))
    :flag ptx-vlbits-out)
  :hints (("Goal"
           :in-theory (enable ptx-vleaf-bits-sound
                              ptx-leaf-variant-correct
                              ptx-leaf-size-correct)
           :expand ((ptx-vbits-out wt bigp)
                    (ptx-vmbits-out wms bigp)
                    (ptx-vlbits-out wts bigp)
                    (ptx-vbits-gadget wt bigp)
                    (ptx-vmbits-gadget wms bigp)
                    (ptx-vlbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)))))

(defthm-ptx-vbits-gadget-flag
  (defthm ptx-vbits-gadget-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-typed wt asg)
                  (ptx-vbits-witnessp wt bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt bigp) asg p))
    :flag ptx-vbits-gadget)
  (defthm ptx-vmbits-gadget-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-mtyped wms asg)
                  (ptx-vmbits-witnessp wms bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-vmbits-gadget wms bigp) asg p))
    :flag ptx-vmbits-gadget)
  (defthm ptx-vlbits-gadget-complete
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-ltyped wts asg)
                  (ptx-vlbits-witnessp wts bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-vlbits-gadget wts bigp) asg p))
    :flag ptx-vlbits-gadget)
  :hints (("Goal"
           :in-theory (enable ptx-vleaf-bits-complete)
           :expand ((ptx-vbits-gadget wt bigp)
                    (ptx-vmbits-gadget wms bigp)
                    (ptx-vlbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (:free (p) (ptx-vbits-witnessp wt bigp asg p))
                    (:free (p) (ptx-vmbits-witnessp wms bigp asg p))
                    (:free (p) (ptx-vlbits-witnessp wts bigp asg p))))))

(defruled ptx-vwrite-bits-le-sound
  :short "R1CS-SOUND of Plaintext::write_bits_le, given Literal::new on each
          leaf: the output terms evaluate to the funspec of the plaintext
          the input wires denote."
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-vbits-out wt nil) asg)
                       (plaintext-to-bits-le (ptx-val wt asg)))))
  :enable plaintext-to-bits-le)

(defruled ptx-vwrite-bits-be-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt t) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-vbits-out wt t) asg)
                       (plaintext-to-bits-be (ptx-val wt asg)))))
  :enable plaintext-to-bits-be)

(defruled ptx-vwrite-bits-complete
  :short "R1CS-COMPLETE of Plaintext::write_bits_le / _be: with the leaf
          witnesses the constraints hold and the output is the funspec's."
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (ptx-vbits-witnessp wt bigp asg p))
           (and (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt bigp) asg p)
                (equal (ptx-terms-val (ptx-vbits-out wt bigp) asg)
                       (values-plaintext-to-bits (ptx-val wt asg) bigp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; write_bits_raw_le / write_bits_raw_be: the leaf bits only.
;; The constraints are the same leaf constraints, in the same order.

(defines ptx-vraw-out
  :flag-local nil

  (define ptx-vraw-out (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-vmraw-out (cdr wt) bigp))
      (:array (ptx-vlraw-out (cdr wt) bigp))
      (otherwise (ptx-vleaf-bits-out (cdr wt) bigp))))

  (define ptx-vmraw-out (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-vraw-out (cdr (car wms)) bigp)
              (ptx-vmraw-out (cdr wms) bigp))))

  (define ptx-vlraw-out (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-vraw-out (car wts) bigp)
              (ptx-vlraw-out (cdr wts) bigp)))))

(defthm-ptx-vraw-out-flag
  (defthm ptx-vraw-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-typed wt asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt bigp) asg p))
             (equal (ptx-terms-val (ptx-vraw-out wt bigp) asg)
                    (values-plaintext-to-bits-raw (ptx-val wt asg) bigp)))
    :flag ptx-vraw-out)
  (defthm ptx-vmraw-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-mtyped wms asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vmbits-gadget wms bigp) asg p))
             (equal (ptx-terms-val (ptx-vmraw-out wms bigp) asg)
                    (values-plaintext-members-to-bits-raw (ptx-mval wms asg) bigp)))
    :flag ptx-vmraw-out)
  (defthm ptx-vlraw-out-sound
    (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (ptx-ltyped wts asg)
                  (r1cs::r1cs-constraints-holdp (ptx-vlbits-gadget wts bigp) asg p))
             (equal (ptx-terms-val (ptx-vlraw-out wts bigp) asg)
                    (values-plaintext-elements-to-bits-raw (ptx-lval wts asg) bigp)))
    :flag ptx-vlraw-out)
  :hints (("Goal"
           :in-theory (enable ptx-vleaf-bits-sound)
           :expand ((ptx-vraw-out wt bigp)
                    (ptx-vmraw-out wms bigp)
                    (ptx-vlraw-out wts bigp)
                    (ptx-vbits-gadget wt bigp)
                    (ptx-vmbits-gadget wms bigp)
                    (ptx-vlbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)))))

(defruled ptx-vwrite-bits-raw-le-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-vraw-out wt nil) asg)
                       (plaintext-to-bits-raw-le (ptx-val wt asg)))))
  :enable plaintext-to-bits-raw-le)

(defruled ptx-vwrite-bits-raw-be-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt t) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-vraw-out wt t) asg)
                       (plaintext-to-bits-raw-be (ptx-val wt asg)))))
  :enable plaintext-to-bits-raw-be)

(defruled ptx-vwrite-bits-raw-complete
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (ptx-vbits-witnessp wt bigp asg p))
           (and (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt bigp) asg p)
                (equal (ptx-terms-val (ptx-vraw-out wt bigp) asg)
                       (values-plaintext-to-bits-raw (ptx-val wt asg) bigp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Packing into fields: bits.chunks(252).map(Field::from_bits_le).
;; Each output field is the linear combination sum_i 2^i b_i of its chunk.

(defruled ptx-vto-fields-sound
  :short "R1CS-SOUND of Plaintext::to_fields, given Literal::new on each
          leaf.  The constraints are those of write_bits_le."
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (b* ((out (ptx-to-fields-out (append (ptx-vbits-out wt nil) (list 1))))
                (spec (plaintext-to-fields (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (append (ptx-vbits-out wt nil) (list 1)))))
  :enable (plaintext-to-fields ptx-vwrite-bits-le-sound plaintext-to-bits-le))

(defruled ptx-vto-fields-raw-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (b* ((out (ptx-to-fields-out (ptx-vraw-out wt nil)))
                (spec (plaintext-to-fields-raw (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (ptx-vraw-out wt nil))))
  :enable (plaintext-to-fields-raw plaintext-to-bits-raw-le))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; size_in_fields and num_randomizers: a host value from the length of
;; to_bits_le, whose constraints (ptx-vbits-gadget wt nil) are emitted.

(define ptx-vsize-in-fields (wt)
  (b* ((num-bits (+ (len (ptx-vbits-out wt nil)) 1))
       (num-fields (ceiling num-bits 252)))
    (if (<= num-fields (values-max-data-size-in-fields))
        num-fields
      :error)))

(defruled ptx-vsize-in-fields-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (b* ((out (ptx-vsize-in-fields wt))
                (spec (plaintext-size-in-fields (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ((:instance ptx-vwrite-bits-le-sound)
        (:instance ptx-len-of-terms-val (xs (ptx-vbits-out wt nil))))
  :disable ptx-len-of-terms-val
  :enable (ptx-vsize-in-fields plaintext-size-in-fields spec-error))

(defruled ptx-vnum-randomizers-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-vbits-gadget wt nil) asg p))
           (b* ((out (ptx-vsize-in-fields wt))
                (spec (plaintext-num-randomizers (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ptx-vsize-in-fields-sound
  :enable plaintext-num-randomizers)


(define ptx-ventry-bits-out (ew bigp)
  (append (ptx-vis-bits (car ew)) (ptx-vbits-out (cdr ew) bigp)))

(define ptx-ventry-bits-gadget (ew bigp)
  (ptx-vbits-gadget (cdr ew) bigp))

(defruled ptx-ventry-write-bits-le-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-ventry-bits-gadget ew nil) asg p))
           (and (equal (ptx-terms-val (ptx-ventry-bits-out ew nil) asg)
                       (entry-to-bits-le (ptx-eval ew asg)))
                (equal (ptx-terms-val (ptx-ventry-bits-out ew nil) asg)
                       (entry-write-bits-le-with-visibility-as-mode
                        (ptx-eval ew asg)))))
  :use ((:instance ptx-vwrite-bits-le-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-bits-out ptx-ventry-bits-gadget entry-to-bits-le
                    entry-write-bits-le-with-visibility-as-mode))

(defruled ptx-ventry-write-bits-be-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-ventry-bits-gadget ew t) asg p))
           (equal (ptx-terms-val (ptx-ventry-bits-out ew t) asg)
                  (entry-to-bits-be (ptx-eval ew asg))))
  :use ((:instance ptx-vwrite-bits-be-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-bits-out ptx-ventry-bits-gadget entry-to-bits-be))

(defruled ptx-ventry-write-bits-complete
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (ptx-vbits-witnessp (cdr ew) bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-ventry-bits-gadget ew bigp) asg p))
  :use ((:instance ptx-vwrite-bits-complete (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-bits-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::to_fields (= to_fields_with_visibility_as_mode with
;; Mode::Constant): write_bits_le, a constant 1, packed with
;; Field::from_bits_le per chunk (linear, no constraints).

(define ptx-ventry-to-fields-out (ew)
  (ptx-to-fields-out (append (ptx-ventry-bits-out ew nil) (list 1))))

(defruled ptx-ventry-to-fields-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-ventry-bits-gadget ew nil) asg p))
           (b* ((out (ptx-ventry-to-fields-out ew))
                (spec (entry-to-fields (ptx-eval ew asg))))
             (and (equal spec
                         (entry-to-fields-with-visibility-as-mode
                          (ptx-eval ew asg)))
                  (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (append (ptx-ventry-bits-out ew nil) (list 1))))
        ptx-ventry-write-bits-le-sound)
  :enable (ptx-ventry-to-fields-out entry-to-fields
                                   entry-to-fields-with-visibility-as-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::num_randomizers: a synthesis-time constant.

(define ptx-ventry-num-randomizers (ew)
  (if (equal (car ew) :private) (ptx-vsize-in-fields (cdr ew)) 0))

(defruled ptx-ventry-num-randomizers-sound
  (implies (and (primep p)
                  (equal p (base-prime))
                  (r1cs::r1cs-valuationp asg p)
                  (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-ventry-bits-gadget ew nil) asg p))
           (b* ((out (ptx-ventry-num-randomizers ew))
                (spec (entry-num-randomizers (ptx-eval ew asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ((:instance ptx-vsize-in-fields-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-ventry-num-randomizers entry-num-randomizers
                    ptx-entry-wrap ptx-ventry-bits-gadget))
