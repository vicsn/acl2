; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The concrete Literal wire representation of ptx-dlit.lisp extended with
; the Scalar arm, and with a write_bits completeness witness for Field
; leaves, for all four leaf interfaces; and the Plaintext / Entry theorems
; functionally instantiated with it.
;
; Field write_bits completeness: the witness of a Field leaf (:field x bits
; rs) is bits = field-bits-le x and rs = the canonical bits-lte-const fold
; witness; rec-field-gadget-complete (from fb2-field-write-bits-le-gadget-
; complete) proves the gadget holds.
;
; A Scalar leaf wire is (:scalar s xs rs): s the scalar wire, xs its 251
; bit wires and rs the 250 range-check wires of Scalar::new (snarkVM keeps
; the bits of a scalar, so the same wires serve write_bits).
;
;   Literal::new          literal-scalar-new-gadget s xs rs; its witness is
;                         xs = scalar-bits-le s and rs = the canonical
;                         bits-lte-const fold witness;
;   write_bits_le / _be   scalar-write-bits-le-gadget s xs rs (the same
;                         constraints); the output is xs, reversed for be;
;   is_equal / _not_equal crv-scalar-is-not-equal-gadget a b m r, which is
;                         crv-field-is-not-equal-gadget, so r is forced to
;                         be a bit (ptx-e-scalar-neq-r-bitp).
;
; The file also defines ptx-gen-copy / ptx-gen-instance, the copier of
; ptx-dlit.lisp parameterized by the name prefix, for the later ptx-*lit
; books.

(in-package "ALEOVM")

(include-book "ptx-dlit")
(include-book "rec-leaves")
(include-book "scalar-write-bits-r1cs")
(include-book "literal-new-r1cs")
(include-book "lit-literal-dispatch")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-e-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Scalar arm over the wires.

(defun ptx-e-scalar-shapep (w)
  (and (eq (car w) :scalar)
       (symbolp (second w))
       (symbol-listp (third w))
       (equal (len (third w)) 251)
       (symbol-listp (fourth w))
       (equal (len (fourth w)) 250)))

(defun ptx-e-scalar-vars (w)
  (cons (second w) (append (third w) (fourth w))))

(defun ptx-e-scalar-witnessp (w asg)
  (and (equal (lookup-equal-list (third w) asg)
              (scalar-bits-le (lookup-equal (second w) asg)))
       (equal (lookup-equal-list (fourth w) asg)
              (crv-bits-lte-const-witness
               (lookup-equal-list (third w) asg)
               (scalar-modulus-minus-one-bits)))))

(defun ptx-e-field-witnessp (w asg)
  (and (equal (lookup-equal-list (third w) asg)
              (field-bits-le (lookup-equal (second w) asg)))
       (equal (lookup-equal-list (fourth w) asg)
              (fb-bits-lte-const-witness
               (lookup-equal-list (third w) asg)
               (nat=>lebits* (1- (base-prime)))))))

(defruled ptx-e-scalar-neq-r-bitp
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-not-equal-gadget x y m r p) asg p))
           (bitp (lookup-equal r asg)))
  :use ptx-d-field-neq-r-bitp
  :enable (crv-scalar-is-not-equal-gadget crv-scalar-is-equal-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The leaf.

(defun ptx-e-leaf-val (w asg)
  (if (eq (car w) :scalar)
      (literal-scalar (lookup-equal (second w) asg))
    (ptx-d-leaf-val w asg)))

(defun ptx-e-leaf-typed (w asg)
  (if (eq (car w) :scalar)
      (and (ptx-e-scalar-shapep w)
           (scalarp (lookup-equal (second w) asg))
           (r1cs::valuation-binds-allp asg (ptx-e-scalar-vars w)))
    (ptx-d-leaf-typed w asg)))

(defun ptx-e-leaf-variant (w)
  (if (eq (car w) :scalar) 14 (ptx-d-leaf-variant w)))

(defun ptx-e-leaf-size (w)
  (if (eq (car w) :scalar) 251 (ptx-d-leaf-size w)))

(defun ptx-e-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :scalar)) (ptx-d-leaf-bits-gadget w bigp))
        ((ptx-e-scalar-shapep w)
         (scalar-write-bits-le-gadget (second w) (third w) (fourth w)
                                      (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-e-leaf-bits-out (w bigp)
  (if (eq (car w) :scalar)
      (if bigp (rev (third w)) (third w))
    (ptx-d-leaf-bits-out w bigp)))

(defun ptx-e-leaf-bits-witnessp (w bigp asg p)
  (case (car w)
    (:scalar (ptx-e-scalar-witnessp w asg))
    (:field (ptx-e-field-witnessp w asg))
    (otherwise (ptx-d-leaf-bits-witnessp w bigp asg p))))

(defun ptx-e-leaf-new-gadget (w)
  (cond ((not (eq (car w) :scalar)) (ptx-d-leaf-new-gadget w))
        ((ptx-e-scalar-shapep w)
         (literal-scalar-new-gadget (second w) (third w) (fourth w)
                                    (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-e-leaf-new-vars (w)
  (cond ((not (eq (car w) :scalar)) (ptx-d-leaf-new-vars w))
        ((ptx-e-scalar-shapep w) (ptx-e-scalar-vars w))
        (t nil)))

(defun ptx-e-leaf-new-witnessp (w x asg p)
  (and (r1cs::r1cs-valuationp asg p)
       (r1cs::valuation-binds-allp asg (ptx-e-leaf-new-vars w))
       (ptx-e-leaf-typed w asg)
       (equal (ptx-e-leaf-val w asg) x)
       (or (not (eq (car w) :scalar))
           (ptx-e-scalar-witnessp w asg))))

(defun ptx-e-scalar-eq-okp (wa wb names)
  (and (ptx-e-scalar-shapep wa) (ptx-e-scalar-shapep wb)
       (ptx-d-names-okp names)))

(defun ptx-e-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :scalar)) (ptx-d-leaf-eq-gadget wa wb neq names))
        ((ptx-e-scalar-eq-okp wa wb names)
         (crv-scalar-is-not-equal-gadget (second wa) (second wb)
                                         (car names) (cadr names) (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-e-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :scalar)) (ptx-d-leaf-eq-out wa wb neq names))
        ((ptx-e-scalar-eq-okp wa wb names) (ptx-c-zout (cadr names) neq))
        (t 0)))

(defun ptx-e-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :scalar)) (ptx-d-leaf-eq-nvars wa wb neq))
        (t 2)))

(defun ptx-e-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :scalar))
         (ptx-d-leaf-eq-witnessp wa wb neq names asg p))
        (t (b* ((x (lookup-equal (second wa) asg))
                (y (lookup-equal (second wb) asg)))
             (and (ptx-d-names-okp names)
                  (r1cs::valuation-bindsp asg (car names))
                  (r1cs::valuation-bindsp asg (cadr names))
                  (equal (lookup-equal (cadr names) asg)
                         (if (equal x y) 0 1))
                  (equal (lookup-equal (car names) asg)
                         (if (equal x y)
                             0
                           (pfield::inv (pfield::sub x y (base-prime))
                                        (base-prime)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ptx-e-leaf-when-not-scalar
  (implies (not (eq (car w) :scalar))
           (and (equal (ptx-e-leaf-typed w asg) (ptx-d-leaf-typed w asg))
                (equal (ptx-e-leaf-val w asg) (ptx-d-leaf-val w asg)))))

;; The ptx-tree constraints.

(defruled ptx-e-scalar-literal-facts
  (and (literalp (literal-scalar x))
       (equal (literal-variant (literal-scalar x)) 14)
       (equal (literal-size-in-bits (literal-scalar x)) 251)
       (equal (literal-kind (literal-scalar x)) :scalar)
       (equal (literal-new (literal-scalar x)) (literal-scalar x)))
  :enable (literal-variant literal-size-in-bits literal-new))

(defruled ptx-e-leaf-constraints
  (and (literalp (ptx-e-leaf-val w asg))
       (implies (ptx-e-leaf-typed w asg)
                (equal (literal-variant (ptx-e-leaf-val w asg))
                       (ptx-e-leaf-variant w)))
       (implies (ptx-e-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-e-leaf-val w asg))
                       (ptx-e-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-e-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use (ptx-d-leaf-constraints ptx-e-leaf-when-not-scalar)
  :enable ptx-e-scalar-literal-facts
  :disable (ptx-d-leaf-val ptx-d-leaf-typed equal-of-literal-boolean))

;; The ptx-vbits constraints.

(defruled ptx-e-leaf-bits-sound-scalar
  (implies (and (eq (car w) :scalar)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-e-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-e-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-e-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-e-leaf-val w asg))
                    (literal-to-bits-le (ptx-e-leaf-val w asg)))))
  :do-not-induct t
  :use ((:instance lit-literal-write-bits-le-scalar-sound
         (s (second w)) (xs (third w)) (rs (fourth w)))
        (:instance lit-literal-write-bits-be-scalar-sound
         (s (second w)) (xs (third w)) (rs (fourth w))))
  :enable ptx-c-bindsp-when-lookup)

(defruled ptx-e-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-e-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-e-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-e-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-e-leaf-val w asg))
                    (literal-to-bits-le (ptx-e-leaf-val w asg)))))
  :use (ptx-e-leaf-bits-sound-scalar ptx-d-leaf-bits-sound
        ptx-e-leaf-when-not-scalar)
  :disable (ptx-e-scalar-shapep ptx-d-leaf-val ptx-d-leaf-typed
                                ptx-e-leaf-typed ptx-e-leaf-val))

(defruled ptx-e-leaf-bits-complete-scalar
  (implies (and (eq (car w) :scalar)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-e-leaf-typed w asg)
                (ptx-e-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-e-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-complete
         (s (second w)) (xs (third w)) (rs (fourth w)) (acc nil)))
  :enable ptx-c-bindsp-when-lookup)

(defruled ptx-e-leaf-bits-complete-field
  (implies (and (eq (car w) :field)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-e-leaf-typed w asg)
                (ptx-e-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-e-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use ((:instance rec-field-gadget-complete
         (x (second w)) (bits (third w)) (rs (fourth w)) (u 'ptx-one)))
  :enable (ptx-d-integer-length-of-base-prime ptx-c-bindsp-when-lookup
           ptx-d-leaf-typed ptx-d-leaf-bits-gadget))

(defruled ptx-e-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-e-leaf-typed w asg)
                (ptx-e-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-e-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-e-leaf-bits-complete-scalar ptx-e-leaf-bits-complete-field
        ptx-d-leaf-bits-complete ptx-e-leaf-when-not-scalar)
  :disable (ptx-e-scalar-shapep ptx-d-leaf-val ptx-d-leaf-typed
                                ptx-e-leaf-typed ptx-e-leaf-val
                                ptx-e-scalar-witnessp ptx-e-field-witnessp
                                ptx-d-leaf-bits-gadget ptx-d-leaf-bits-witnessp))

;; The ptx-vnew constraints.

(defrule ptx-e-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-e-leaf-new-vars w))
  :enable ptx-d-leaf-new-vars)

(defruled ptx-e-literal-new-of-leaf-val
  (equal (literal-new (ptx-e-leaf-val w asg))
         (ptx-e-leaf-val w asg))
  :use ptx-d-literal-new-of-leaf-val
  :enable ptx-e-scalar-literal-facts
  :disable ptx-d-leaf-val)

(defruled ptx-e-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-e-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-e-leaf-new-gadget w) asg p))
           (and (ptx-e-leaf-typed w asg)
                (equal (literal-new (ptx-e-leaf-val w asg))
                       (ptx-e-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-d-leaf-new-sound ptx-e-leaf-when-not-scalar
        (:instance literal-scalar-new-sound
         (s (second w)) (xs (third w)) (rs (fourth w))))
  :enable (ptx-e-literal-new-of-leaf-val ptx-c-bindsp-when-lookup)
  :disable (ptx-d-leaf-typed ptx-d-leaf-val ptx-d-leaf-new-gadget
                             ptx-d-leaf-new-vars))

(defruled ptx-e-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-e-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-e-leaf-new-gadget w) asg p)
                (equal (ptx-e-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use ((:instance ptx-d-leaf-new-complete)
        (:instance literal-scalar-new-complete
         (x (literal-scalar (lookup-equal (second w) asg)))
         (s (second w)) (xs (third w)) (rs (fourth w))))
  :enable (ptx-e-literal-new-of-leaf-val ptx-d-leaf-new-witnessp
           ptx-e-scalar-literal-facts ptx-c-bindsp-when-lookup)
  :disable (ptx-d-leaf-val ptx-d-leaf-typed ptx-d-leaf-new-gadget
                           ptx-d-leaf-new-vars))

(defruled ptx-e-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-e-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-e-leaf-new-gadget w)
                                              asg p)))
  :use ((:instance ptx-e-leaf-constraints))
  :enable ptx-e-literal-new-of-leaf-val
  :disable (ptx-e-leaf-val ptx-e-leaf-typed ptx-e-leaf-new-gadget))

;; The ptx-vequal constraints.

(defrule ptx-e-natp-of-leaf-eq-nvars
  (natp (ptx-e-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defrule ptx-e-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-e-leaf-eq-out wa wb neq names))
                             (ptx-e-leaf-eq-out wa wb neq names)))
  :use ptx-d-sparse-vectorp-of-leaf-eq-out
  :enable ptx-d-sparse-vectorp-of-zout
  :disable (ptx-c-zout ptx-d-sparse-vectorp-of-leaf-eq-out ptx-d-leaf-eq-out))

(defruled ptx-e-kind-of-leaf-val
  (implies (ptx-e-leaf-typed w asg)
           (equal (literal-kind (ptx-e-leaf-val w asg)) (car w)))
  :use ptx-d-kind-of-leaf-val
  :enable ptx-e-scalar-literal-facts
  :disable (ptx-d-leaf-val ptx-d-leaf-typed))

(defruled ptx-e-leaf-eq-sound-scalar
  (implies (and (equal (car wa) :scalar)
                (equal (car wb) :scalar)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-e-leaf-typed wa asg)
                (ptx-e-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-e-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-e-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-e-leaf-val wa asg)
                                                   (ptx-e-leaf-val wb asg)))
                     (values-literal-equalp (ptx-e-leaf-val wa asg)
                                            (ptx-e-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-e-scalar-neq-r-bitp
         (x (second wa)) (y (second wb)) (m (car names)) (r (cadr names)))
        (:instance crv-scalar-is-not-equal-gadget-sound
         (a (second wa)) (b (second wb)) (m (car names)) (r (cadr names)))
        (:instance lit-literal-is-not-equal-scalar-bridge
         (a (lookup-equal (second wa) asg)) (b (lookup-equal (second wb) asg)))
        (:instance ptx-c-bval-of-zout (z (cadr names))))
  :enable (ptx-c-bindsp-of-car-and-cadr ptx-c-bindsp-when-lookup
           literal-is-not-equal values-bool-to-bit scalar-is-not-equal-funspec
           boolean-not-funspec)
  :disable (ptx-c-zout ptx-e-scalar-neq-r-bitp
                       crv-scalar-is-not-equal-gadget-sound
                       lit-literal-is-not-equal-scalar-bridge))

(defruled ptx-e-leaf-eq-when-not-scalar
  (implies (not (equal (car wa) :scalar))
           (and (equal (ptx-e-leaf-eq-gadget wa wb neq names)
                       (ptx-d-leaf-eq-gadget wa wb neq names))
                (equal (ptx-e-leaf-eq-out wa wb neq names)
                       (ptx-d-leaf-eq-out wa wb neq names))
                (equal (ptx-e-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-d-leaf-eq-witnessp wa wb neq names asg p))))
  :enable (ptx-d-leaf-eq-gadget ptx-d-leaf-eq-out ptx-d-leaf-eq-witnessp))

(defruled ptx-e-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (and (equal (ptx-e-leaf-eq-out wa wb neq names) (if neq 1 0))
                (equal (ptx-e-leaf-eq-gadget wa wb neq names)
                       (lit-literal-equal-mismatch-gadget)))))

(defruled ptx-e-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-e-leaf-typed wa asg)
                (ptx-e-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-e-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-e-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-e-leaf-val wa asg)
                                                   (ptx-e-leaf-val wb asg)))
                     (values-literal-equalp (ptx-e-leaf-val wa asg)
                                            (ptx-e-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-e-kind-of-leaf-val (w wa))
        (:instance ptx-e-kind-of-leaf-val (w wb))
        (:instance ptx-e-leaf-constraints (w wa))
        (:instance ptx-e-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-e-leaf-val wa asg)) (y (ptx-e-leaf-val wb asg)))
        ptx-e-leaf-eq-sound-scalar
        (:instance ptx-d-leaf-eq-sound)
        (:instance ptx-e-leaf-when-not-scalar (w wa))
        (:instance ptx-e-leaf-when-not-scalar (w wb))
        ptx-e-leaf-eq-when-not-scalar)
  :enable (values-bool-to-bit ptx-e-leaf-eq-out-when-mismatch)
  :disable (ptx-e-leaf-eq-gadget ptx-e-leaf-eq-out ptx-e-leaf-typed
                                 ptx-e-leaf-val ptx-d-leaf-eq-gadget
                                 ptx-d-leaf-eq-out ptx-d-leaf-val
                                 ptx-d-leaf-typed))

(defruled ptx-e-leaf-eq-complete-scalar
  (implies (and (equal (car wa) :scalar)
                (equal (car wb) :scalar)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-e-leaf-typed wa asg)
                (ptx-e-leaf-typed wb asg)
                (ptx-e-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-e-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance crv-scalar-is-not-equal-gadget-complete
         (a (second wa)) (b (second wb)) (m (car names)) (r (cadr names))))
  :enable ptx-c-bindsp-when-lookup
  :disable crv-scalar-is-not-equal-gadget-complete)

(defruled ptx-e-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-e-leaf-typed wa asg)
                (ptx-e-leaf-typed wb asg)
                (ptx-e-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-e-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-e-leaf-eq-complete-scalar
        (:instance ptx-d-leaf-eq-complete)
        (:instance ptx-e-leaf-when-not-scalar (w wa))
        (:instance ptx-e-leaf-when-not-scalar (w wb))
        ptx-e-leaf-eq-when-not-scalar)
  :enable (lit-literal-equal-mismatch-complete ptx-e-leaf-eq-out-when-mismatch)
  :disable (lit-literal-equal-mismatch-gadget
            ptx-e-leaf-eq-gadget ptx-e-leaf-eq-witnessp ptx-e-leaf-typed
                                 ptx-e-leaf-val ptx-d-leaf-eq-gadget
                                 ptx-d-leaf-eq-witnessp ptx-d-leaf-typed
                                 ptx-d-leaf-val))

(in-theory (disable ptx-e-leaf-val ptx-e-leaf-typed ptx-e-leaf-variant
                    ptx-e-leaf-size ptx-e-leaf-bits-gadget ptx-e-leaf-bits-out
                    ptx-e-leaf-bits-witnessp ptx-e-leaf-new-gadget
                    ptx-e-leaf-new-vars ptx-e-leaf-new-witnessp
                    ptx-e-leaf-eq-gadget ptx-e-leaf-eq-out ptx-e-leaf-eq-nvars
                    ptx-e-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The copier, parameterized by the prefix: ptx-X becomes <prefix>X, and the
;; leaf interfaces become <prefix>leaf-*.

(defconst *ptx-gen-leaf-names*
  '((ptx-leaf-val . "LEAF-VAL")
    (ptx-leaf-typed . "LEAF-TYPED")
    (ptx-leaf-variant . "LEAF-VARIANT")
    (ptx-leaf-size . "LEAF-SIZE")
    (ptx-vleaf-bits-gadget . "LEAF-BITS-GADGET")
    (ptx-vleaf-bits-out . "LEAF-BITS-OUT")
    (ptx-vleaf-bits-witnessp . "LEAF-BITS-WITNESSP")
    (ptx-vleaf-new-gadget . "LEAF-NEW-GADGET")
    (ptx-vleaf-new-vars . "LEAF-NEW-VARS")
    (ptx-vleaf-new-witnessp . "LEAF-NEW-WITNESSP")
    (ptx-vleaf-eq-gadget . "LEAF-EQ-GADGET")
    (ptx-vleaf-eq-out . "LEAF-EQ-OUT")
    (ptx-vleaf-eq-nvars . "LEAF-EQ-NVARS")
    (ptx-vleaf-eq-witnessp . "LEAF-EQ-WITNESSP")))

(defconst *ptx-gen-lemmas*
  '("LEAF-CONSTRAINTS" "LEAF-BITS-SOUND" "LEAF-BITS-COMPLETE"
    "LEAF-NEW-SOUND" "LEAF-NEW-COMPLETE" "LEAF-NEW-ERROR"
    "LEAF-EQ-SOUND" "LEAF-EQ-COMPLETE"))

(defun ptx-gen-sym (prefix str)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string prefix str) 'ptx-gen-sym))

(defun ptx-gen-name (prefix fn)
  (declare (xargs :mode :program))
  (ptx-gen-sym prefix (subseq (symbol-name fn) 4 nil)))

(defun ptx-gen-leaves (prefix pairs)
  (declare (xargs :mode :program))
  (if (endp pairs)
      nil
    (cons (cons (caar pairs) (ptx-gen-sym prefix (cdar pairs)))
          (ptx-gen-leaves prefix (cdr pairs)))))

(defun ptx-gen-syms (prefix strs)
  (declare (xargs :mode :program))
  (if (endp strs)
      nil
    (cons (ptx-gen-sym prefix (car strs))
          (ptx-gen-syms prefix (cdr strs)))))

(defun ptx-gen-alist (prefix fns)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (cons (cons (car fns) (ptx-gen-name prefix (car fns)))
          (ptx-gen-alist prefix (cdr fns)))))

(defun ptx-gen-full-alist (prefix)
  (declare (xargs :mode :program))
  (append (ptx-gen-leaves prefix *ptx-gen-leaf-names*)
          (ptx-gen-alist prefix (ptx-c-flatten *ptx-d-cliques*))))

(defmacro ptx-gen-copy (prefix)
  `(make-event
    (cons 'progn (ptx-d-copy-events *ptx-d-cliques* (ptx-gen-full-alist ,prefix)
                                    (w state)))))

(defun ptx-gen-instance-event (prefix thm wrld)
  (declare (xargs :mode :program))
  (b* ((alist (ptx-gen-full-alist prefix))
       (formula (acl2::sublis-fn-simple alist (acl2::formula thm nil wrld))))
    `(defthm ,(ptx-gen-name prefix thm)
       ,formula
       :hints (("Goal"
                :do-not-induct t
                :use ((:functional-instance ,thm ,@(ptx-c-fi-pairs alist)))
                :in-theory (enable ,@(ptx-gen-syms prefix *ptx-gen-lemmas*))))
       :rule-classes nil)))

(defmacro ptx-gen-instance (prefix thm)
  `(make-event (ptx-gen-instance-event ,prefix ',thm (w state))))

(defmacro ptx-gen-instances (prefix)
  `(progn
     (ptx-gen-instance ,prefix ptx-vwrite-bits-le-sound)
     (ptx-gen-instance ,prefix ptx-vwrite-bits-be-sound)
     (ptx-gen-instance ,prefix ptx-vwrite-bits-complete)
     (ptx-gen-instance ,prefix ptx-vwrite-bits-raw-le-sound)
     (ptx-gen-instance ,prefix ptx-vwrite-bits-raw-be-sound)
     (ptx-gen-instance ,prefix ptx-vwrite-bits-raw-complete)
     (ptx-gen-instance ,prefix ptx-vto-fields-sound)
     (ptx-gen-instance ,prefix ptx-vto-fields-raw-sound)
     (ptx-gen-instance ,prefix ptx-vsize-in-fields-sound)
     (ptx-gen-instance ,prefix ptx-vnum-randomizers-sound)
     (ptx-gen-instance ,prefix ptx-ventry-write-bits-le-sound)
     (ptx-gen-instance ,prefix ptx-ventry-write-bits-be-sound)
     (ptx-gen-instance ,prefix ptx-ventry-write-bits-complete)
     (ptx-gen-instance ,prefix ptx-ventry-to-fields-sound)
     (ptx-gen-instance ,prefix ptx-ventry-num-randomizers-sound)
     (ptx-gen-instance ,prefix ptx-vnew-sound)
     (ptx-gen-instance ,prefix ptx-vnew-complete)
     (ptx-gen-instance ,prefix ptx-ventry-new-sound)
     (ptx-gen-instance ,prefix ptx-ventry-new-complete)
     (ptx-gen-instance ,prefix ptx-veq-sound)
     (ptx-gen-instance ,prefix ptx-veq-complete)
     (ptx-gen-instance ,prefix ptx-ventry-eq-sound)
     (ptx-gen-instance ,prefix ptx-ventry-eq-complete)))

(ptx-gen-copy "PTX-E-")
(ptx-gen-instances "PTX-E-")
