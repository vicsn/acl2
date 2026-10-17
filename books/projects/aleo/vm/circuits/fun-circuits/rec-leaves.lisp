; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; HeaderLeaf, TransactionLeaf, TransitionLeaf write_bits_le/be
; (snarkVM circuit/program/src/state_path/helpers/*_leaf.rs).
; Each writes its integer fields then its field id.  Integer::write_bits_le/be
; copies the integer's bit wires and adds no constraint; Field::write_bits_le/be
; is fb-field-write-bits-le-gadget on the id.  So the circuit is exactly the id's
; field gadget, and the output wires are the integer bit wires followed by the
; field bit wires (each reversed in the big-endian form).
; Integer wires come from Integer::new, which makes each bit boolean
; (R1CS-SOUND-IF); the integer value is lebits=>nat of its bit wires.

(in-package "ALEOVM")

(include-book "fb-field-bits")
(include-book "fb2-field-bits")
(include-book "../fun-specs/values-value")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled rec-lebits=>nat-bound
  (implies (bit-listp bs)
           (< (lebits=>nat bs) (expt 2 (len bs))))
  :use (:instance acl2::lebits=>nat-upper-bound (digits bs))
  :enable acl2::bit-list-fix)

(defruled rec-values-nat-to-lebits-of-lebits=>nat
  (implies (and (bit-listp bs)
                (equal n (len bs)))
           (equal (values-nat-to-lebits n (lebits=>nat bs)) bs))
  :enable (values-nat-to-lebits
           rec-lebits=>nat-bound
           acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix))

(defruled rec-values-uint-to-bits-of-lebits=>nat
  (implies (and (bit-listp bs)
                (equal n (len bs)))
           (and (equal (values-uint-to-bits (lebits=>nat bs) n nil) bs)
                (equal (values-uint-to-bits (lebits=>nat bs) n t) (rev bs))))
  :enable (values-uint-to-bits
           values-int-to-bits-le
           values-int-to-bits-be
           values-nat-to-bebits
           rec-values-nat-to-lebits-of-lebits=>nat))

(defruled rec-unsigned-byte-p-of-lebits=>nat
  (implies (and (bit-listp bs)
                (equal n (len bs)))
           (unsigned-byte-p n (lebits=>nat bs)))
  :use rec-lebits=>nat-bound)

(defruled rec-values-field-to-bits
  (implies (fieldp x)
           (and (equal (values-field-to-bits x nil) (field-bits-le x))
                (equal (values-field-to-bits x t) (rev (field-bits-le x)))))
  :enable (values-field-to-bits
           values-field-to-bits-le
           values-field-to-bits-be
           values-nat-to-lebits
           field-bits-le
           fieldp
           pfield::fep
           fb-base-prime-below-2-253))

(defruled rec-field-bits-when-gadget
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (symbolp u)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (equal (len bits) (integer-length (base-prime)))
                (equal (len rs) (bits-lt-prime-rlen (base-prime)))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget x bits rs u (base-prime))
                 asg (base-prime)))
           (and (fieldp (lookup-equal x asg))
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (lookup-equal x asg)))))
  :enable (field-write-bits-le-funspec fieldp r1cs::fep-of-lookup-equal)
  :use (:instance fb-field-write-bits-le-gadget-sound
                  (p (base-prime)) (acc nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hypotheses common to every leaf theorem: the id's field gadget wires.

(defmacro rec-field-hyps ()
  '(and (symbolp x)
        (symbol-listp bits)
        (symbol-listp rs)
        (symbolp u)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-bindsp asg x)
        (r1cs::valuation-binds-allp asg bits)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)
        (equal (len bits) (integer-length (base-prime)))
        (equal (len rs) (bits-lt-prime-rlen (base-prime)))))

(defmacro rec-field-complete-hyps ()
  '(and (rec-field-hyps)
        (fieldp (lookup-equal x asg))
        (equal (lookup-equal-list bits asg)
               (field-bits-le (lookup-equal x asg)))
        (equal (lookup-equal-list rs asg)
               (fb-bits-lte-const-witness
                (lookup-equal-list bits asg)
                (nat=>lebits* (1- (base-prime)))))))

(defruled rec-field-gadget-complete
  (implies (rec-field-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (fb-field-write-bits-le-gadget x bits rs u (base-prime))
            asg (base-prime)))
  :use (:instance fb2-field-write-bits-le-gadget-complete (p (base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; HeaderLeaf { index: U8, id: Field }

(define rec-header-leaf-write-bits-gadget ((x symbolp)
                                           (bits symbol-listp)
                                           (rs symbol-listp)
                                           (u symbolp))
  :guard (and (equal (len bits) (integer-length (base-prime)))
              (equal (len rs) (bits-lt-prime-rlen (base-prime))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('HeaderLeaf::write_bits_le') and
          @('write_bits_be'): the id's field gadget only."
  (fb-field-write-bits-le-gadget x bits rs u (base-prime)))

(defruled rec-header-leaf-write-bits-sound
  (b* ((ivals (lookup-equal-list idx asg))
       (fvals (lookup-equal-list bits asg))
       (leaf (header-leaf (lebits=>nat ivals) (lookup-equal x asg))))
    (implies (and (rec-field-hyps)
                  (bit-listp ivals)
                  (equal (len ivals) 8)
                  (r1cs::r1cs-constraints-holdp
                   (rec-header-leaf-write-bits-gadget x bits rs u) asg (base-prime)))
             (and (header-leafp leaf)
                  (equal (header-leaf->index leaf) (lebits=>nat ivals))
                  (equal (header-leaf->id leaf) (lookup-equal x asg))
                  (equal (append ivals fvals) (header-leaf-to-bits-le leaf))
                  (equal (append (rev ivals) (rev fvals))
                         (header-leaf-to-bits-be leaf)))))
  :enable (rec-header-leaf-write-bits-gadget
           header-leaf-to-bits-le header-leaf-to-bits-be
           values-header-leaf-to-bits
           rec-values-uint-to-bits-of-lebits=>nat
           rec-values-field-to-bits
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p acl2::ubyte16-fix acl2::ubyte16p)
  :use rec-field-bits-when-gadget)

(defruled rec-header-leaf-write-bits-complete
  (implies (rec-field-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (rec-header-leaf-write-bits-gadget x bits rs u) asg (base-prime)))
  :enable rec-header-leaf-write-bits-gadget
  :use rec-field-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TransactionLeaf { variant: U8, index: U16, id: Field }

(define rec-transaction-leaf-write-bits-gadget ((x symbolp)
                                                (bits symbol-listp)
                                                (rs symbol-listp)
                                                (u symbolp))
  :guard (and (equal (len bits) (integer-length (base-prime)))
              (equal (len rs) (bits-lt-prime-rlen (base-prime))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('TransactionLeaf::write_bits_le') and
          @('write_bits_be'): the id's field gadget only."
  (fb-field-write-bits-le-gadget x bits rs u (base-prime)))

(defruled rec-transaction-leaf-write-bits-sound
  (b* ((vvals (lookup-equal-list var asg))
       (ivals (lookup-equal-list idx asg))
       (fvals (lookup-equal-list bits asg))
       (leaf (transaction-leaf (lebits=>nat vvals)
                               (lebits=>nat ivals)
                               (lookup-equal x asg))))
    (implies (and (rec-field-hyps)
                  (bit-listp vvals)
                  (equal (len vvals) 8)
                  (bit-listp ivals)
                  (equal (len ivals) 16)
                  (r1cs::r1cs-constraints-holdp
                   (rec-transaction-leaf-write-bits-gadget x bits rs u)
                   asg (base-prime)))
             (and (transaction-leafp leaf)
                  (equal (transaction-leaf->variant leaf) (lebits=>nat vvals))
                  (equal (transaction-leaf->index leaf) (lebits=>nat ivals))
                  (equal (transaction-leaf->id leaf) (lookup-equal x asg))
                  (equal (append vvals ivals fvals)
                         (transaction-leaf-to-bits-le leaf))
                  (equal (append (rev vvals) (rev ivals) (rev fvals))
                         (transaction-leaf-to-bits-be leaf)))))
  :enable (rec-transaction-leaf-write-bits-gadget
           transaction-leaf-to-bits-le transaction-leaf-to-bits-be
           values-transaction-leaf-to-bits
           rec-values-uint-to-bits-of-lebits=>nat
           rec-values-field-to-bits
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p acl2::ubyte16-fix acl2::ubyte16p)
  :use rec-field-bits-when-gadget)

(defruled rec-transaction-leaf-write-bits-complete
  (implies (rec-field-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (rec-transaction-leaf-write-bits-gadget x bits rs u)
            asg (base-prime)))
  :enable rec-transaction-leaf-write-bits-gadget
  :use rec-field-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TransitionLeaf { version: U8, index: U8, variant: U8, id: Field }

(define rec-transition-leaf-write-bits-gadget ((x symbolp)
                                               (bits symbol-listp)
                                               (rs symbol-listp)
                                               (u symbolp))
  :guard (and (equal (len bits) (integer-length (base-prime)))
              (equal (len rs) (bits-lt-prime-rlen (base-prime))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('TransitionLeaf::write_bits_le') and
          @('write_bits_be'): the id's field gadget only."
  (fb-field-write-bits-le-gadget x bits rs u (base-prime)))

(defruled rec-transition-leaf-write-bits-sound
  (b* ((evals (lookup-equal-list ver asg))
       (ivals (lookup-equal-list idx asg))
       (vvals (lookup-equal-list var asg))
       (fvals (lookup-equal-list bits asg))
       (leaf (transition-leaf (lebits=>nat evals)
                              (lebits=>nat ivals)
                              (lebits=>nat vvals)
                              (lookup-equal x asg))))
    (implies (and (rec-field-hyps)
                  (bit-listp evals)
                  (equal (len evals) 8)
                  (bit-listp ivals)
                  (equal (len ivals) 8)
                  (bit-listp vvals)
                  (equal (len vvals) 8)
                  (r1cs::r1cs-constraints-holdp
                   (rec-transition-leaf-write-bits-gadget x bits rs u)
                   asg (base-prime)))
             (and (transition-leafp leaf)
                  (equal (transition-leaf->version leaf) (lebits=>nat evals))
                  (equal (transition-leaf->index leaf) (lebits=>nat ivals))
                  (equal (transition-leaf->variant leaf) (lebits=>nat vvals))
                  (equal (transition-leaf->id leaf) (lookup-equal x asg))
                  (equal (append evals ivals vvals fvals)
                         (transition-leaf-to-bits-le leaf))
                  (equal (append (rev evals) (rev ivals) (rev vvals) (rev fvals))
                         (transition-leaf-to-bits-be leaf)))))
  :enable (rec-transition-leaf-write-bits-gadget
           transition-leaf-to-bits-le transition-leaf-to-bits-be
           values-transition-leaf-to-bits
           rec-values-uint-to-bits-of-lebits=>nat
           rec-values-field-to-bits
           rec-unsigned-byte-p-of-lebits=>nat
           acl2::ubyte8-fix acl2::ubyte8p acl2::ubyte16-fix acl2::ubyte16p)
  :use rec-field-bits-when-gadget)

(defruled rec-transition-leaf-write-bits-complete
  (implies (rec-field-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (rec-transition-leaf-write-bits-gadget x bits rs u)
            asg (base-prime)))
  :enable rec-transition-leaf-write-bits-gadget
  :use rec-field-gadget-complete)
