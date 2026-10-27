; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The concrete Literal wire representation of ptx-glit.lisp extended with
; the Identifier arm (prefix ptx-i-, over ptx-a-), for all four leaf
; interfaces, and the Plaintext / Entry theorems instantiated with it.
;
; An Identifier leaf wire is (:identifier bitrows witrows partial uscore
; islet): the per-byte bit wires and witness wires of
; IdentifierLiteral::new and its three first-byte wires.  The literal is
; the identifier of the bytes the bit rows decode to; the leaf is typed
; when the bit rows hold bits and the assignment covers all its wires.
;
;   Literal::new          literal-identifier-new-gadget (identifier-list-
;                         sound / identifier-new-complete); the bit rows
;                         hold bits by its boolean checks
;                         (ptx-i-rows-bitsp-when-new);
;   write_bits_le / _be   no constraint (the bits are the bit wires); the
;                         output is the flattened bit rows, reversed for be;
;   is_equal / _not_equal IdentifierLiteral::is_equal compares to_field,
;                         which is the linear combination sum 2^i b_i of the
;                         bit wires (not an allocated wire), so the gadget
;                         is rec-lc-neq-gadget (rec-dynamic-record-eq) on the
;                         two linear combinations, with fresh wires m, r;
;                         the output is r (is_not_equal) or 1 - r
;                         (is_equal).  rec-lc-neq-gadget-bit forces r.

(in-package "ALEOVM")

(include-book "ptx-glit")
(include-book "rec-dynamic-record-eq")
(include-book "identifier-new-complete")
(include-book "fsa-identifier-literal-bits")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-i-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Row lemmas.

(defun ptx-i-induct (b w)
  (if (atom b) (list b w) (ptx-i-induct (cdr b) (cdr w))))

(defruled ptx-i-lookup-equal-list-of-append
  (equal (lookup-equal-list (append a b) asg)
         (append (lookup-equal-list a asg) (lookup-equal-list b asg)))
  :induct (len a)
  :enable lookup-equal-list)

(defruled ptx-i-rows-boundp
  (implies (and (equal (len b) (len w))
                (r1cs::valuation-binds-allp asg (fsa-id-flatten b))
                (r1cs::valuation-binds-allp asg (fsa-id-flatten w)))
           (id-rows-boundp b w asg))
  :induct (ptx-i-induct b w)
  :enable (id-rows-boundp fsa-id-flatten ptx-g-binds-allp-of-append len))

(defruled ptx-i-symbol-listp-of-flatten
  (and (implies (id-bitrows-p b) (symbol-listp (fsa-id-flatten b)))
       (implies (id-witrows-p b) (symbol-listp (fsa-id-flatten b))))
  :induct (len b)
  :enable (fsa-id-flatten id-bitrows-p id-witrows-p))

(defruled ptx-i-bit-listp-of-flatten
  (implies (id-rows-bitsp b asg)
           (bit-listp (lookup-equal-list (fsa-id-flatten b) asg)))
  :induct (len b)
  :enable (fsa-id-flatten id-rows-bitsp ptx-i-lookup-equal-list-of-append))

(defun ptx-i-lit-of (b asg)
  (make-identifier-literal :bytes (id-decode-rows b asg)))

(defruled ptx-i-bytes-of-lit
  (implies (id-bitrows-p b)
           (and (identifier-literalp (ptx-i-lit-of b asg))
                (equal (identifier-literal->bytes (ptx-i-lit-of b asg))
                       (id-decode-rows b asg))
                (equal (len (id-decode-rows b asg)) (len b))))
  :do-not-induct t
  :use (:instance id-decode-rows-facts (bitrows b)))

(defruled ptx-i-bits-matchp
  (implies (and (id-bitrows-p b)
                (id-rows-bitsp b asg))
           (id-bits-matchp (identifier-literal->bytes (ptx-i-lit-of b asg))
                           b asg))
  :use ((:instance id-decode-rows-matchp (bitrows b)) ptx-i-bytes-of-lit)
  :disable ptx-i-lit-of)

(defruled ptx-i-dot-is-to-field
  (implies (and (id-bitrows-p b)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (fsa-id-flatten b))
                (id-rows-bitsp b asg))
           (equal (r1cs::dot-product (pow2sum-vector (fsa-id-flatten b) 0)
                                     asg (base-prime))
                  (identifier-literal-to-field (ptx-i-lit-of b asg))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat
         (xs (fsa-id-flatten b)) (i 0) (p (base-prime)))
        (:instance fsa-identifier-to-field-wire-sound
         (x (ptx-i-lit-of b asg)) (bitrows b) (p (base-prime)))
        ptx-i-bits-matchp ptx-i-bytes-of-lit ptx-i-bit-listp-of-flatten
        ptx-i-symbol-listp-of-flatten)
  :enable (values-lebits-to-field identifier-to-field-gadget)
  :disable (ptx-i-lit-of identifier-literal-to-field))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Identifier arm over the wires.

(defun ptx-i-shapep (w)
  (and (eq (car w) :identifier)
       (id-bitrows-p (second w))
       (id-witrows-p (third w))
       (consp (second w))
       (consp (third w))
       (equal (len (third w)) (len (second w)))
       (symbolp (fourth w))
       (symbolp (fifth w))
       (symbolp (sixth w))))

(defun ptx-i-vars (w)
  (append (fsa-id-flatten (second w))
          (fsa-id-flatten (third w))
          (list (fourth w) (fifth w) (sixth w))))

(defun ptx-i-dot (w asg)
  (r1cs::dot-product (pow2sum-vector (fsa-id-flatten (second w)) 0)
                     asg (base-prime)))

(defruled ptx-i-rows-bitsp-when-new
  (implies (and (ptx-i-shapep w)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (ptx-i-vars w))
                (r1cs::r1cs-constraints-holdp
                 (literal-identifier-new-gadget (second w) (third w) (fourth w)
                                                (fifth w) (sixth w)
                                                (base-prime))
                 asg (base-prime)))
           (id-rows-bitsp (second w) asg))
  :do-not-induct t
  :use ((:instance id-new-gadget-pieces
         (bitrows (second w)) (witrows (third w)) (partial (fourth w))
         (uscore (fifth w)) (islet (sixth w)) (p (base-prime)))
        (:instance id-bitrows-bound-from-rows
         (bitrows (second w)) (witrows (third w)))
        (:instance id-bit-checks-to-rows-bitsp
         (bitrows (second w)) (p (base-prime)))
        (:instance ptx-i-rows-boundp (b (second w)) (w (third w))))
  :enable (literal-identifier-new-gadget ptx-g-binds-allp-of-append)
  :disable (identifier-new-gadget id-bit-checks))

;; The leaf.

(defun ptx-i-leaf-val (w asg)
  (if (eq (car w) :identifier)
      (literal-identifier (ptx-i-lit-of (second w) asg))
    (ptx-a-leaf-val w asg)))

(defun ptx-i-leaf-typed (w asg)
  (if (eq (car w) :identifier)
      (and (ptx-i-shapep w)
           (r1cs::valuation-binds-allp asg (ptx-i-vars w))
           (id-rows-bitsp (second w) asg))
    (ptx-a-leaf-typed w asg)))

(defun ptx-i-leaf-variant (w)
  (if (eq (car w) :identifier) 17 (ptx-a-leaf-variant w)))

(defun ptx-i-leaf-size (w)
  (if (eq (car w) :identifier) 248 (ptx-a-leaf-size w)))

(defun ptx-i-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :identifier)) (ptx-a-leaf-bits-gadget w bigp))
        ((ptx-i-shapep w) (identifier-write-bits-le-gadget))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-i-leaf-bits-out (w bigp)
  (if (eq (car w) :identifier)
      (if bigp
          (rev (fsa-id-flatten (second w)))
        (fsa-id-flatten (second w)))
    (ptx-a-leaf-bits-out w bigp)))

(defun ptx-i-leaf-bits-witnessp (w bigp asg p)
  (if (eq (car w) :identifier)
      t
    (ptx-a-leaf-bits-witnessp w bigp asg p)))

(defun ptx-i-leaf-new-gadget (w)
  (cond ((not (eq (car w) :identifier)) (ptx-a-leaf-new-gadget w))
        ((ptx-i-shapep w)
         (literal-identifier-new-gadget (second w) (third w) (fourth w)
                                        (fifth w) (sixth w) (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-i-leaf-new-vars (w)
  (cond ((not (eq (car w) :identifier)) (ptx-a-leaf-new-vars w))
        ((ptx-i-shapep w) (ptx-i-vars w))
        (t nil)))

(defun ptx-i-new-wits (w asg)
  (b* ((bytes (id-decode-rows (second w) asg))
       (first (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
    (and (id-wits-matchp bytes (third w) asg)
         (equal (lookup-equal (fourth w) asg) (nth 0 first))
         (equal (lookup-equal (fifth w) asg) (nth 1 first))
         (equal (lookup-equal (sixth w) asg) (nth 2 first)))))

(defun ptx-i-leaf-new-witnessp (w x asg p)
  (if (eq (car w) :identifier)
      (and (r1cs::r1cs-valuationp asg p)
           (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars w))
           (ptx-i-leaf-typed w asg)
           (equal (ptx-i-leaf-val w asg) x)
           (ptx-i-new-wits w asg))
    (ptx-a-leaf-new-witnessp w x asg p)))

(defun ptx-i-eq-okp (wa wb names)
  (and (ptx-i-shapep wa) (ptx-i-shapep wb) (ptx-d-names-okp names)))

(defun ptx-i-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :identifier))
         (ptx-a-leaf-eq-gadget wa wb neq names))
        ((ptx-i-eq-okp wa wb names)
         (rec-lc-neq-gadget (pow2sum-vector (fsa-id-flatten (second wa)) 0)
                            (pow2sum-vector (fsa-id-flatten (second wb)) 0)
                            (car names) (cadr names) (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-i-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :identifier))
         (ptx-a-leaf-eq-out wa wb neq names))
        ((ptx-i-eq-okp wa wb names) (ptx-c-zout (cadr names) neq))
        (t 0)))

(defun ptx-i-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :identifier)) (ptx-a-leaf-eq-nvars wa wb neq))
        (t 2)))

(defun ptx-i-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :identifier))
         (ptx-a-leaf-eq-witnessp wa wb neq names asg p))
        (t (b* ((da (ptx-i-dot wa asg))
                (db (ptx-i-dot wb asg)))
             (and (ptx-d-names-okp names)
                  (r1cs::valuation-bindsp asg (car names))
                  (r1cs::valuation-bindsp asg (cadr names))
                  (equal (lookup-equal (cadr names) asg)
                         (if (equal da db) 0 1))
                  (equal (lookup-equal (car names) asg)
                         (rec-neq-mult da db)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lemmas.

(defruled ptx-i-leaf-when-not-identifier
  (implies (not (eq (car w) :identifier))
           (and (equal (ptx-i-leaf-typed w asg) (ptx-a-leaf-typed w asg))
                (equal (ptx-i-leaf-val w asg) (ptx-a-leaf-val w asg))
                (equal (ptx-i-leaf-new-gadget w) (ptx-a-leaf-new-gadget w))
                (equal (ptx-i-leaf-new-vars w) (ptx-a-leaf-new-vars w))
                (equal (ptx-i-leaf-new-witnessp w x asg p)
                       (ptx-a-leaf-new-witnessp w x asg p))
                (equal (ptx-i-leaf-bits-gadget w bigp)
                       (ptx-a-leaf-bits-gadget w bigp))
                (equal (ptx-i-leaf-bits-out w bigp)
                       (ptx-a-leaf-bits-out w bigp))
                (equal (ptx-i-leaf-bits-witnessp w bigp asg p)
                       (ptx-a-leaf-bits-witnessp w bigp asg p)))))

(defruled ptx-i-literal-facts
  (and (literalp (literal-identifier x))
       (equal (literal-variant (literal-identifier x)) 17)
       (equal (literal-size-in-bits (literal-identifier x)) 248)
       (equal (literal-kind (literal-identifier x)) :identifier))
  :enable (literal-variant literal-size-in-bits))

(defruled ptx-i-leaf-constraints
  (and (literalp (ptx-i-leaf-val w asg))
       (implies (ptx-i-leaf-typed w asg)
                (equal (literal-variant (ptx-i-leaf-val w asg))
                       (ptx-i-leaf-variant w)))
       (implies (ptx-i-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-i-leaf-val w asg))
                       (ptx-i-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-i-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use (ptx-a-leaf-constraints ptx-i-leaf-when-not-identifier)
  :enable ptx-i-literal-facts
  :disable (ptx-a-leaf-val ptx-a-leaf-typed equal-of-literal-boolean
                           ptx-i-lit-of))

;; The ptx-vbits constraints.

(defruled ptx-i-leaf-bits-sound-identifier
  (implies (and (eq (car w) :identifier)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-i-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-i-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-i-leaf-val w asg))
                    (literal-to-bits-le (ptx-i-leaf-val w asg)))))
  :do-not-induct t
  :use ((:instance ptx-i-bits-matchp (b (second w)))
        (:instance ptx-i-bytes-of-lit (b (second w)))
        (:instance ptx-i-symbol-listp-of-flatten (b (second w)))
        (:instance lit-literal-write-bits-le-identifier-sound
         (x (ptx-i-lit-of (second w) asg)) (bitrows (second w)))
        (:instance lit-literal-write-bits-be-identifier-sound
         (x (ptx-i-lit-of (second w) asg)) (bitrows (second w))))
  :enable (identifier-write-bits-le-gadget identifier-write-bits-be-gadget)
  :disable (ptx-i-lit-of ptx-i-vars))

(defruled ptx-i-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-i-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-i-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-i-leaf-val w asg))
                    (literal-to-bits-le (ptx-i-leaf-val w asg)))))
  :use (ptx-i-leaf-bits-sound-identifier ptx-a-leaf-bits-sound
        ptx-i-leaf-when-not-identifier)
  :disable (ptx-i-shapep ptx-a-leaf-val ptx-a-leaf-typed ptx-i-leaf-typed
                         ptx-i-leaf-val ptx-i-leaf-bits-gadget
                         ptx-i-leaf-bits-out ptx-a-leaf-bits-gadget
                         ptx-a-leaf-bits-out))

(defruled ptx-i-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-i-leaf-typed w asg)
                (ptx-i-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-a-leaf-bits-complete ptx-i-leaf-when-not-identifier)
  :enable identifier-write-bits-le-gadget
  :disable (ptx-a-leaf-val ptx-a-leaf-typed ptx-a-leaf-bits-gadget
                           ptx-a-leaf-bits-witnessp))

;; The ptx-vnew constraints.

(defrule ptx-i-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-i-leaf-new-vars w))
  :enable (ptx-a-leaf-new-vars ptx-i-symbol-listp-of-flatten))

(defruled ptx-i-leaf-new-sound-identifier
  (implies (and (eq (car w) :identifier)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget w) asg p))
           (and (ptx-i-leaf-typed w asg)
                (equal (literal-new (ptx-i-leaf-val w asg))
                       (ptx-i-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-i-rows-bitsp-when-new
        (:instance ptx-i-rows-boundp (b (second w)) (w (third w)))
        (:instance literal-identifier-new-sound
         (bitrows (second w)) (witrows (third w)) (partial (fourth w))
         (uscore (fifth w)) (islet (sixth w))))
  :enable ptx-g-binds-allp-of-append
  :disable (ptx-i-rows-bitsp-when-new literal-identifier-new-gadget))

(defruled ptx-i-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget w) asg p))
           (and (ptx-i-leaf-typed w asg)
                (equal (literal-new (ptx-i-leaf-val w asg))
                       (ptx-i-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-a-leaf-new-sound ptx-i-leaf-when-not-identifier
        ptx-i-leaf-new-sound-identifier)
  :disable (ptx-a-leaf-typed ptx-a-leaf-val ptx-a-leaf-new-gadget
                             ptx-a-leaf-new-vars ptx-i-leaf-typed
                             ptx-i-leaf-val ptx-i-leaf-new-gadget
                             ptx-i-leaf-new-vars))

(defruled ptx-i-leaf-new-complete-identifier
  (implies (and (eq (car w) :identifier)
                (equal p (base-prime))
                (ptx-i-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget w) asg p)
                (equal (ptx-i-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use ((:instance ptx-i-bits-matchp (b (second w)))
        (:instance ptx-i-bytes-of-lit (b (second w)))
        (:instance ptx-i-rows-boundp (b (second w)) (w (third w)))
        (:instance literal-identifier-new-complete
         (bytes (id-decode-rows (second w) asg))
         (bitrows (second w)) (witrows (third w)) (partial (fourth w))
         (uscore (fifth w)) (islet (sixth w))))
  :enable (ptx-g-binds-allp-of-append ptx-i-literal-facts)
  :disable (ptx-i-lit-of literal-identifier-new-gadget id-wits-matchp
                         id-bits-matchp id-first-wits equal-of-literal-identifier))

(defruled ptx-i-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-i-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget w) asg p)
                (equal (ptx-i-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use ((:instance ptx-a-leaf-new-complete)
        ptx-i-leaf-new-complete-identifier
        ptx-i-leaf-when-not-identifier)
  :disable (ptx-a-leaf-val ptx-a-leaf-typed ptx-a-leaf-new-gadget
                           ptx-a-leaf-new-vars ptx-a-leaf-new-witnessp
                           ptx-i-leaf-val ptx-i-leaf-typed
                           ptx-i-leaf-new-gadget ptx-i-leaf-new-witnessp))

(defruled ptx-i-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-i-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget w)
                                              asg p)))
  :do-not-induct t
  :use ((:instance ptx-a-leaf-new-error)
        ptx-i-leaf-new-sound-identifier
        (:instance ptx-i-leaf-constraints)
        ptx-i-leaf-when-not-identifier)
  :disable (ptx-i-leaf-val ptx-i-leaf-typed ptx-i-leaf-new-gadget
                           ptx-i-leaf-new-vars ptx-a-leaf-new-gadget
                           ptx-a-leaf-new-witnessp ptx-a-leaf-val
                           ptx-i-new-wits))

;; The ptx-vequal constraints.

(defrule ptx-i-natp-of-leaf-eq-nvars
  (natp (ptx-i-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defrule ptx-i-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-i-leaf-eq-out wa wb neq names))
                             (ptx-i-leaf-eq-out wa wb neq names)))
  :use ptx-a-sparse-vectorp-of-leaf-eq-out
  :enable ptx-d-sparse-vectorp-of-zout
  :disable (ptx-c-zout ptx-a-sparse-vectorp-of-leaf-eq-out ptx-a-leaf-eq-out))

(defruled ptx-i-kind-of-leaf-val
  (implies (ptx-i-leaf-typed w asg)
           (equal (literal-kind (ptx-i-leaf-val w asg)) (car w)))
  :use ptx-a-kind-of-leaf-val
  :enable ptx-i-literal-facts
  :disable (ptx-a-leaf-val ptx-a-leaf-typed ptx-i-lit-of))

(defruled ptx-i-leaf-eq-sound-identifier
  (implies (and (equal (car wa) :identifier)
                (equal (car wb) :identifier)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-i-leaf-typed wa asg)
                (ptx-i-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-i-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-i-leaf-val wa asg)
                                                   (ptx-i-leaf-val wb asg)))
                     (values-literal-equalp (ptx-i-leaf-val wa asg)
                                            (ptx-i-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-i-dot-is-to-field (b (second wa)))
        (:instance ptx-i-dot-is-to-field (b (second wb)))
        (:instance ptx-i-bytes-of-lit (b (second wa)))
        (:instance ptx-i-bytes-of-lit (b (second wb)))
        (:instance ptx-i-symbol-listp-of-flatten (b (second wa)))
        (:instance ptx-i-symbol-listp-of-flatten (b (second wb)))
        (:instance rec-lc-neq-gadget-bit
         (va (pow2sum-vector (fsa-id-flatten (second wa)) 0))
         (vb (pow2sum-vector (fsa-id-flatten (second wb)) 0))
         (m (car names)) (r (cadr names)))
        (:instance ptx-c-bval-of-zout (z (cadr names))))
  :enable (ptx-c-bindsp-of-car-and-cadr ptx-g-binds-allp-of-append
           values-literal-equalp identifier-literal-is-equal
           values-bool-to-bit)
  :disable (ptx-c-zout rec-lc-neq-gadget-bit ptx-i-lit-of
                       identifier-literal-to-field rec-lc-neq-gadget
                       ptx-i-dot-is-to-field))

(defruled ptx-i-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (and (equal (ptx-i-leaf-eq-out wa wb neq names) (if neq 1 0))
                (equal (ptx-i-leaf-eq-gadget wa wb neq names)
                       (lit-literal-equal-mismatch-gadget)))))

(defruled ptx-i-leaf-eq-when-not-identifier
  (implies (not (equal (car wa) :identifier))
           (and (equal (ptx-i-leaf-eq-gadget wa wb neq names)
                       (ptx-a-leaf-eq-gadget wa wb neq names))
                (equal (ptx-i-leaf-eq-out wa wb neq names)
                       (ptx-a-leaf-eq-out wa wb neq names))
                (equal (ptx-i-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-a-leaf-eq-witnessp wa wb neq names asg p))))
  :enable (ptx-a-leaf-eq-gadget ptx-a-leaf-eq-out ptx-a-leaf-eq-witnessp))

(defruled ptx-i-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-i-leaf-typed wa asg)
                (ptx-i-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-i-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-i-leaf-val wa asg)
                                                   (ptx-i-leaf-val wb asg)))
                     (values-literal-equalp (ptx-i-leaf-val wa asg)
                                            (ptx-i-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-i-kind-of-leaf-val (w wa))
        (:instance ptx-i-kind-of-leaf-val (w wb))
        (:instance ptx-i-leaf-constraints (w wa))
        (:instance ptx-i-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-i-leaf-val wa asg)) (y (ptx-i-leaf-val wb asg)))
        ptx-i-leaf-eq-sound-identifier
        (:instance ptx-a-leaf-eq-sound)
        (:instance ptx-i-leaf-when-not-identifier (w wa))
        (:instance ptx-i-leaf-when-not-identifier (w wb))
        ptx-i-leaf-eq-when-not-identifier)
  :enable (values-bool-to-bit ptx-i-leaf-eq-out-when-mismatch)
  :disable (ptx-i-leaf-eq-gadget ptx-i-leaf-eq-out ptx-i-leaf-typed
                                 ptx-i-leaf-val ptx-a-leaf-eq-gadget
                                 ptx-a-leaf-eq-out ptx-a-leaf-val
                                 ptx-a-leaf-typed))

(defruled ptx-i-leaf-eq-complete-identifier
  (implies (and (equal (car wa) :identifier)
                (equal (car wb) :identifier)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-i-leaf-typed wa asg)
                (ptx-i-leaf-typed wb asg)
                (ptx-i-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-i-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance ptx-i-symbol-listp-of-flatten (b (second wa)))
        (:instance ptx-i-symbol-listp-of-flatten (b (second wb)))
        (:instance rec-lc-neq-gadget-complete
         (va (pow2sum-vector (fsa-id-flatten (second wa)) 0))
         (vb (pow2sum-vector (fsa-id-flatten (second wb)) 0))
         (m (car names)) (r (cadr names))))
  :disable (rec-lc-neq-gadget-complete rec-lc-neq-gadget rec-neq-mult))

(defruled ptx-i-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-i-leaf-typed wa asg)
                (ptx-i-leaf-typed wb asg)
                (ptx-i-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-i-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-i-leaf-eq-complete-identifier
        (:instance ptx-a-leaf-eq-complete)
        (:instance ptx-i-leaf-when-not-identifier (w wa))
        (:instance ptx-i-leaf-when-not-identifier (w wb))
        ptx-i-leaf-eq-when-not-identifier)
  :enable (lit-literal-equal-mismatch-complete ptx-i-leaf-eq-out-when-mismatch)
  :disable (lit-literal-equal-mismatch-gadget
            ptx-i-leaf-eq-gadget ptx-i-leaf-eq-witnessp ptx-i-leaf-typed
            ptx-i-leaf-val ptx-a-leaf-eq-gadget ptx-a-leaf-eq-witnessp
            ptx-a-leaf-typed ptx-a-leaf-val))

(in-theory (disable ptx-i-leaf-val ptx-i-leaf-typed ptx-i-leaf-variant
                    ptx-i-leaf-size ptx-i-leaf-bits-gadget ptx-i-leaf-bits-out
                    ptx-i-leaf-bits-witnessp ptx-i-leaf-new-gadget
                    ptx-i-leaf-new-vars ptx-i-leaf-new-witnessp
                    ptx-i-leaf-eq-gadget ptx-i-leaf-eq-out ptx-i-leaf-eq-nvars
                    ptx-i-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Plaintext / Entry theorems instantiated with the leaf covering every
;; Literal type except String (out of scope) and Signature.

(ptx-gen-copy "PTX-I-")
(ptx-gen-instances "PTX-I-")
