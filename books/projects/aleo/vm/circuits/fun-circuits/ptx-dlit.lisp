; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The concrete Literal wire representation of ptx-lit.lisp extended with
; the Field arm, for all four leaf interfaces (ptx-tree, ptx-vbits,
; ptx-vnew, ptx-vequal), and the Plaintext / Entry theorems functionally
; instantiated with it.
;
; A Field leaf wire is (:field x bits rs): x the field wire, bits the 253
; wires and rs the range-check wires that Field::write_bits allocates
; (snarkVM caches the bits of a field, so the same wires serve every
; write_bits of the leaf).  The leaf is typed when x holds a base field
; element and the assignment covers x, bits and rs.
;
;   Literal::new          literal-field-new-gadget (no constraint);
;   write_bits_le / _be   fb-field-write-bits-le-gadget x bits rs ptx-one
;                         (the be gadget is the same); the output is bits,
;                         reversed for be.  There is no prior completeness
;                         theorem for this gadget, so the write_bits leaf
;                         witness of a Field leaf is false: the instantiated
;                         write_bits completeness theorems cover plaintexts
;                         without Field leaves;
;   is_equal / _not_equal crv-field-is-not-equal-gadget x y m r with fresh
;                         wires m, r; the output is r (is_not_equal) or
;                         1 - r (is_equal).  The constraints
;                         (x - y) m = r, (x - y)(1 - r) = 0 force r to be a
;                         bit (ptx-d-field-neq-r-bitp), which discharges
;                         the bitp hypothesis of
;                         crv-field-is-not-equal-gadget-sound.
;
; Boolean and Integer leaves are as in ptx-lit.lisp / ptx-vlit.lisp.

(in-package "ALEOVM")

(include-book "ptx-vlit")
(include-book "ptx-vbits")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-d-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Field arm over the wires.

(defun ptx-d-field-shapep (w)
  (and (eq (car w) :field)
       (symbolp (second w))
       (symbol-listp (third w))
       (equal (len (third w)) 253)
       (symbol-listp (fourth w))
       (equal (len (fourth w)) (bits-lt-prime-rlen (base-prime)))))

(defun ptx-d-field-vars (w)
  (cons (second w) (append (third w) (fourth w))))

(defruled ptx-d-integer-length-of-base-prime
  (equal (integer-length (base-prime)) 253)
  :enable ((:e base-prime) (:e integer-length)))

(defruled ptx-d-oddp-of-base-prime
  (oddp (base-prime))
  :enable ((:e base-prime) (:e oddp)))

(defruled ptx-d-field-neq-r-bitp
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (crv-field-is-not-equal-gadget x y m r p) asg p))
           (bitp (lookup-equal r asg)))
  :do-not-induct t
  :cases ((equal (pfield::sub (lookup-equal x asg) (lookup-equal y asg) p) 0))
  :use (crv-field-is-not-equal-gadget-to-spec
        (:instance pfield::equal-of-0-and-mul
         (x (pfield::sub (lookup-equal x asg) (lookup-equal y asg) p))
         (y (pfield::sub 1 (lookup-equal r asg) p)))
        (:instance pfield::equal-of-0-and-sub
         (x 1) (y (lookup-equal r asg))))
  :enable (bitp r1cs::fep-of-lookup-equal)
  :disable (pfield::equal-of-0-and-mul pfield::equal-of-0-and-sub
            (:definition pfield::sub)
            pfield::mul-of-sub-arg1 pfield::mul-of-sub-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The leaf.

(defun ptx-d-leaf-val (w asg)
  (if (eq (car w) :field)
      (literal-field (lookup-equal (second w) asg))
    (ptx-c-leaf-val w asg)))

(defun ptx-d-leaf-typed (w asg)
  (if (eq (car w) :field)
      (and (ptx-d-field-shapep w)
           (fieldp (lookup-equal (second w) asg))
           (r1cs::valuation-binds-allp asg (ptx-d-field-vars w)))
    (ptx-c-leaf-typed w asg)))

(defun ptx-d-leaf-variant (w)
  (if (eq (car w) :field) 2 (ptx-c-leaf-variant w)))

(defun ptx-d-leaf-size (w)
  (if (eq (car w) :field) 253 (ptx-c-leaf-size w)))

(defun ptx-d-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :field)) (ptx-c-leaf-bits-gadget w bigp))
        ((ptx-d-field-shapep w)
         (fb-field-write-bits-le-gadget (second w) (third w) (fourth w)
                                        'ptx-one (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-d-leaf-bits-out (w bigp)
  (if (eq (car w) :field)
      (if bigp (rev (third w)) (third w))
    (ptx-c-leaf-bits-out w bigp)))

(defun ptx-d-leaf-bits-witnessp (w bigp asg p)
  (if (eq (car w) :field)
      nil
    (ptx-c-leaf-bits-witnessp w bigp asg p)))

(defun ptx-d-leaf-new-gadget (w)
  (cond ((not (eq (car w) :field)) (ptx-c-leaf-new-gadget w))
        ((ptx-d-field-shapep w) (literal-field-new-gadget))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-d-leaf-new-vars (w)
  (cond ((not (eq (car w) :field)) (ptx-c-leaf-new-vars w))
        ((ptx-d-field-shapep w) (ptx-d-field-vars w))
        (t nil)))

(defun ptx-d-leaf-new-witnessp (w x asg p)
  (and (r1cs::r1cs-valuationp asg p)
       (r1cs::valuation-binds-allp asg (ptx-d-leaf-new-vars w))
       (ptx-d-leaf-typed w asg)
       (equal (ptx-d-leaf-val w asg) x)))

(defun ptx-d-names-okp (names)
  (and (consp names) (symbolp (car names))
       (consp (cdr names)) (symbolp (cadr names))))

(defun ptx-d-field-eq-okp (wa wb names)
  (and (ptx-d-field-shapep wa) (ptx-d-field-shapep wb) (ptx-d-names-okp names)))

(defun ptx-d-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :field)) (ptx-c-leaf-eq-gadget wa wb neq names))
        ((ptx-d-field-eq-okp wa wb names)
         (crv-field-is-not-equal-gadget (second wa) (second wb)
                                        (car names) (cadr names) (base-prime)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-d-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :field)) (ptx-c-leaf-eq-out wa wb neq names))
        ((ptx-d-field-eq-okp wa wb names) (ptx-c-zout (cadr names) neq))
        (t 0)))

(defun ptx-d-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :field)) (ptx-c-leaf-eq-nvars wa wb neq))
        (t 2)))

(defun ptx-d-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :field))
         (ptx-c-leaf-eq-witnessp wa wb neq names asg p))
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

;; The ptx-tree constraints.

(defruled ptx-d-field-literal-facts
  (and (equal (literal-variant (literal-field x)) 2)
       (equal (literal-size-in-bits (literal-field x)) 253))
  :enable (literal-variant literal-size-in-bits))

(defruled ptx-d-leaf-constraints
  (and (literalp (ptx-d-leaf-val w asg))
       (implies (ptx-d-leaf-typed w asg)
                (equal (literal-variant (ptx-d-leaf-val w asg))
                       (ptx-d-leaf-variant w)))
       (implies (ptx-d-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-d-leaf-val w asg))
                       (ptx-d-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-d-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use ptx-c-leaf-constraints
  :enable ptx-d-field-literal-facts
  :disable (ptx-d-field-shapep ptx-d-field-vars equal-of-literal-boolean))

;; The ptx-vbits constraints.

(defruled ptx-d-leaf-bits-sound-field
  (implies (and (eq (car w) :field)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-d-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-d-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-d-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-d-leaf-val w asg))
                    (literal-to-bits-le (ptx-d-leaf-val w asg)))))
  :do-not-induct t
  :use ((:instance lit-literal-write-bits-le-field-sound
         (x (second w)) (bits (third w)) (rs (fourth w)) (u 'ptx-one))
        (:instance lit-literal-write-bits-be-field-sound
         (x (second w)) (bits (third w)) (rs (fourth w)) (u 'ptx-one)))
  :enable (ptx-d-integer-length-of-base-prime ptx-d-oddp-of-base-prime
           fb-field-write-bits-be-gadget ptx-c-bindsp-when-lookup))

(defruled ptx-d-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-d-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-d-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-d-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-d-leaf-val w asg))
                    (literal-to-bits-le (ptx-d-leaf-val w asg)))))
  :use (ptx-d-leaf-bits-sound-field ptx-c-leaf-bits-sound)
  :disable ptx-d-field-shapep)

(defruled ptx-d-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-d-leaf-typed w asg)
                (ptx-d-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-d-leaf-bits-gadget w bigp)
                                         asg p))
  :use ptx-c-leaf-bits-complete)

;; The ptx-vnew constraints.

(defruled ptx-d-leaf-when-not-field
  (implies (not (eq (car w) :field))
           (and (equal (ptx-d-leaf-typed w asg) (ptx-c-leaf-typed w asg))
                (equal (ptx-d-leaf-val w asg) (ptx-c-leaf-val w asg)))))

(defrule ptx-d-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-d-leaf-new-vars w)))

(defruled ptx-d-literal-new-of-leaf-val
  (equal (literal-new (ptx-d-leaf-val w asg))
         (ptx-d-leaf-val w asg))
  :use ptx-c-literal-new-of-leaf-val
  :enable literal-new)

(defruled ptx-d-field-typed-from-new
  (implies (and (eq (car w) :field)
                (ptx-d-field-shapep w)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (ptx-d-field-vars w)))
           (ptx-d-leaf-typed w asg))
  :enable (fieldp r1cs::fep-of-lookup-equal))

(defruled ptx-d-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-d-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-d-leaf-new-gadget w) asg p))
           (and (ptx-d-leaf-typed w asg)
                (equal (literal-new (ptx-d-leaf-val w asg))
                       (ptx-d-leaf-val w asg))))
  :use (ptx-c-leaf-new-sound ptx-d-field-typed-from-new)
  :enable (ptx-d-literal-new-of-leaf-val ptx-d-leaf-when-not-field)
  :disable (ptx-d-field-shapep ptx-d-field-vars ptx-d-leaf-typed
                               ptx-d-leaf-val))

(defruled ptx-d-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-d-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-d-leaf-new-gadget w) asg p)
                (equal (ptx-d-leaf-val w asg) (literal-new x))))
  :use ((:instance ptx-c-leaf-new-complete)
        (:instance ptx-c-leaf-new-holds))
  :enable (ptx-d-literal-new-of-leaf-val literal-field-new-gadget
                                         ptx-c-leaf-new-witnessp)
  :disable (ptx-d-field-shapep ptx-d-field-vars ptx-d-leaf-val
                               ptx-c-leaf-new-gadget))

(defruled ptx-d-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-d-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-d-leaf-new-gadget w)
                                              asg p)))
  :use ((:instance ptx-d-leaf-constraints))
  :enable ptx-d-literal-new-of-leaf-val
  :disable (ptx-d-leaf-val ptx-d-leaf-typed ptx-d-leaf-new-gadget))

;; The ptx-vequal constraints.

(defrule ptx-d-natp-of-leaf-eq-nvars
  (natp (ptx-d-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defruled ptx-d-sparse-vectorp-of-zout
  (implies (symbolp z)
           (and (consp (ptx-c-zout z neq))
                (r1cs::sparse-vectorp (ptx-c-zout z neq))))
  :enable (ptx-one-minus ptx-neg r1cs::sparse-vectorp
                         r1cs::sparse-vector-elementp))

(defrule ptx-d-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-d-leaf-eq-out wa wb neq names))
                             (ptx-d-leaf-eq-out wa wb neq names)))
  :use ptx-c-sparse-vectorp-of-leaf-eq-out
  :enable ptx-d-sparse-vectorp-of-zout
  :disable (ptx-c-zout ptx-c-sparse-vectorp-of-leaf-eq-out))

(defruled ptx-d-kind-of-leaf-val
  (implies (ptx-d-leaf-typed w asg)
           (equal (literal-kind (ptx-d-leaf-val w asg)) (car w)))
  :use ptx-c-kind-of-leaf-val)

(defruled ptx-d-leaf-eq-sound-field
  (implies (and (equal (car wa) :field)
                (equal (car wb) :field)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-d-leaf-typed wa asg)
                (ptx-d-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-d-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-d-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-d-leaf-val wa asg)
                                                   (ptx-d-leaf-val wb asg)))
                     (values-literal-equalp (ptx-d-leaf-val wa asg)
                                            (ptx-d-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-d-field-neq-r-bitp
         (x (second wa)) (y (second wb)) (m (car names)) (r (cadr names)))
        (:instance crv-field-is-not-equal-gadget-sound
         (x (second wa)) (y (second wb)) (m (car names)) (r (cadr names)))
        (:instance lit-literal-is-not-equal-field-bridge
         (a (lookup-equal (second wa) asg)) (b (lookup-equal (second wb) asg)))
        (:instance ptx-c-bval-of-zout (z (cadr names))))
  :enable (ptx-c-bindsp-of-car-and-cadr ptx-c-bindsp-when-lookup
           literal-is-not-equal values-bool-to-bit field-is-not-equal-funspec
           boolean-not-funspec)
  :disable (ptx-c-zout ptx-d-field-neq-r-bitp crv-field-is-not-equal-gadget-sound
                       lit-literal-is-not-equal-field-bridge))

(defruled ptx-d-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (and (equal (ptx-d-leaf-eq-out wa wb neq names) (if neq 1 0))
                (equal (ptx-d-leaf-eq-gadget wa wb neq names)
                       (lit-literal-equal-mismatch-gadget)))))

(defruled ptx-d-leaf-eq-when-not-field
  (implies (and (equal (car wa) (car wb))
                (not (equal (car wa) :field)))
           (and (equal (ptx-d-leaf-eq-gadget wa wb neq names)
                       (ptx-c-leaf-eq-gadget wa wb neq names))
                (equal (ptx-d-leaf-eq-out wa wb neq names)
                       (ptx-c-leaf-eq-out wa wb neq names))
                (equal (ptx-d-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-c-leaf-eq-witnessp wa wb neq names asg p)))))

(defruled ptx-d-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-d-leaf-typed wa asg)
                (ptx-d-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-d-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-d-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-d-leaf-val wa asg)
                                                   (ptx-d-leaf-val wb asg)))
                     (values-literal-equalp (ptx-d-leaf-val wa asg)
                                            (ptx-d-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-d-kind-of-leaf-val (w wa))
        (:instance ptx-d-kind-of-leaf-val (w wb))
        (:instance ptx-d-leaf-constraints (w wa))
        (:instance ptx-d-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-d-leaf-val wa asg)) (y (ptx-d-leaf-val wb asg)))
        ptx-d-leaf-eq-sound-field
        (:instance ptx-c-leaf-eq-sound)
        (:instance ptx-d-leaf-when-not-field (w wa))
        (:instance ptx-d-leaf-when-not-field (w wb))
        ptx-d-leaf-eq-when-not-field)
  :enable (values-bool-to-bit ptx-d-leaf-eq-out-when-mismatch)
  :disable (ptx-d-leaf-eq-gadget ptx-d-leaf-eq-out ptx-d-leaf-typed
                                 ptx-d-leaf-val ptx-c-leaf-eq-gadget
                                 ptx-c-leaf-eq-out))

(defruled ptx-d-leaf-eq-complete-field
  (implies (and (equal (car wa) :field)
                (equal (car wb) :field)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ptx-d-leaf-typed wa asg)
                (ptx-d-leaf-typed wb asg)
                (ptx-d-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-d-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance crv-field-is-not-equal-gadget-complete
         (x (second wa)) (y (second wb)) (m (car names)) (r (cadr names))))
  :disable crv-field-is-not-equal-gadget-complete)

(defruled ptx-d-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-d-leaf-typed wa asg)
                (ptx-d-leaf-typed wb asg)
                (ptx-d-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-d-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-d-leaf-eq-complete-field
        (:instance ptx-c-leaf-eq-complete)
        (:instance ptx-d-leaf-when-not-field (w wa))
        (:instance ptx-d-leaf-when-not-field (w wb))
        ptx-d-leaf-eq-when-not-field)
  :enable (lit-literal-equal-mismatch-complete ptx-d-leaf-eq-out-when-mismatch)
  :disable (ptx-d-leaf-eq-gadget ptx-d-leaf-eq-witnessp ptx-d-leaf-typed
                                 ptx-d-leaf-val ptx-c-leaf-eq-gadget
                                 lit-literal-equal-mismatch-gadget))

(in-theory (disable ptx-d-leaf-val ptx-d-leaf-typed ptx-d-leaf-variant
                    ptx-d-leaf-size ptx-d-leaf-bits-gadget ptx-d-leaf-bits-out
                    ptx-d-leaf-bits-witnessp ptx-d-leaf-new-gadget
                    ptx-d-leaf-new-vars ptx-d-leaf-new-witnessp
                    ptx-d-leaf-eq-gadget ptx-d-leaf-eq-out ptx-d-leaf-eq-nvars
                    ptx-d-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Copies of the ptx- functions that call the leaf interfaces, with the
;; concrete leaf functions (ptx-X becomes ptx-d-X), and the functional
;; instances.

(defconst *ptx-d-cliques*
  (append '((ptx-val ptx-mval ptx-lval)
            (ptx-typed ptx-mtyped ptx-ltyped)
            (ptx-eval)
            (ptx-vbits-out ptx-vmbits-out ptx-vlbits-out)
            (ptx-vbits-gadget ptx-vmbits-gadget ptx-vlbits-gadget)
            (ptx-vbits-witnessp ptx-vmbits-witnessp ptx-vlbits-witnessp)
            (ptx-vraw-out ptx-vmraw-out ptx-vlraw-out)
            (ptx-vsize-in-fields)
            (ptx-ventry-bits-out)
            (ptx-ventry-bits-gadget)
            (ptx-ventry-to-fields-out)
            (ptx-ventry-num-randomizers))
          *ptx-c-vcliques*))

(defconst *ptx-d-leaves*
  '((ptx-leaf-val . ptx-d-leaf-val)
    (ptx-leaf-typed . ptx-d-leaf-typed)
    (ptx-leaf-variant . ptx-d-leaf-variant)
    (ptx-leaf-size . ptx-d-leaf-size)
    (ptx-vleaf-bits-gadget . ptx-d-leaf-bits-gadget)
    (ptx-vleaf-bits-out . ptx-d-leaf-bits-out)
    (ptx-vleaf-bits-witnessp . ptx-d-leaf-bits-witnessp)
    (ptx-vleaf-new-gadget . ptx-d-leaf-new-gadget)
    (ptx-vleaf-new-vars . ptx-d-leaf-new-vars)
    (ptx-vleaf-new-witnessp . ptx-d-leaf-new-witnessp)
    (ptx-vleaf-eq-gadget . ptx-d-leaf-eq-gadget)
    (ptx-vleaf-eq-out . ptx-d-leaf-eq-out)
    (ptx-vleaf-eq-nvars . ptx-d-leaf-eq-nvars)
    (ptx-vleaf-eq-witnessp . ptx-d-leaf-eq-witnessp)))

(defun ptx-d-name (fn)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string "PTX-D-" (subseq (symbol-name fn) 4 nil))
   'ptx-d-name))

(defun ptx-d-alist (fns)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (cons (cons (car fns) (ptx-d-name (car fns)))
          (ptx-d-alist (cdr fns)))))

(defun ptx-d-full-alist ()
  (declare (xargs :mode :program))
  (append *ptx-d-leaves* (ptx-d-alist (ptx-c-flatten *ptx-d-cliques*))))

(defun ptx-d-defun (fn recp alist wrld)
  (declare (xargs :mode :program))
  (b* ((formals (acl2::formals fn wrld))
       (body (acl2::sublis-fn-simple
              alist (getpropc fn 'acl2::unnormalized-body nil wrld))))
    `(defun ,(cdr (assoc-eq fn alist)) ,formals
       (declare (xargs ,@(and recp `(:measure (acl2-count ,(car formals))))
                       :verify-guards nil)
                (ignorable ,@formals))
       ,body)))

(defun ptx-d-defuns (fns recp alist wrld)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (cons (ptx-d-defun (car fns) recp alist wrld)
          (ptx-d-defuns (cdr fns) recp alist wrld))))

(defun ptx-d-copy-events (cliques alist wrld)
  (declare (xargs :mode :program))
  (if (endp cliques)
      nil
    (b* ((clique (car cliques))
         (recp (getpropc (car clique) 'acl2::recursivep nil wrld))
         (defs (ptx-d-defuns clique recp alist wrld)))
      (cons (if (cdr defs) `(mutual-recursion ,@defs) (car defs))
            (ptx-d-copy-events (cdr cliques) alist wrld)))))

(make-event
 `(progn ,@(ptx-d-copy-events *ptx-d-cliques* (ptx-d-full-alist) (w state))))

(defun ptx-d-instance-event (thm wrld)
  (declare (xargs :mode :program))
  (b* ((alist (ptx-d-full-alist))
       (formula (acl2::sublis-fn-simple alist (acl2::formula thm nil wrld))))
    `(defthm ,(ptx-d-name thm)
       ,formula
       :hints (("Goal"
                :do-not-induct t
                :use ((:functional-instance ,thm ,@(ptx-c-fi-pairs alist)))
                :in-theory (enable ptx-d-leaf-constraints
                                   ptx-d-leaf-bits-sound
                                   ptx-d-leaf-bits-complete
                                   ptx-d-leaf-new-sound
                                   ptx-d-leaf-new-complete
                                   ptx-d-leaf-new-error
                                   ptx-d-leaf-eq-sound
                                   ptx-d-leaf-eq-complete)))
       :rule-classes nil)))

(defmacro ptx-d-instance (thm)
  `(make-event (ptx-d-instance-event ',thm (w state))))

(ptx-d-instance ptx-vwrite-bits-le-sound)
(ptx-d-instance ptx-vwrite-bits-be-sound)
(ptx-d-instance ptx-vwrite-bits-complete)
(ptx-d-instance ptx-vwrite-bits-raw-le-sound)
(ptx-d-instance ptx-vwrite-bits-raw-be-sound)
(ptx-d-instance ptx-vwrite-bits-raw-complete)
(ptx-d-instance ptx-vto-fields-sound)
(ptx-d-instance ptx-vto-fields-raw-sound)
(ptx-d-instance ptx-vsize-in-fields-sound)
(ptx-d-instance ptx-vnum-randomizers-sound)
(ptx-d-instance ptx-ventry-write-bits-le-sound)
(ptx-d-instance ptx-ventry-write-bits-be-sound)
(ptx-d-instance ptx-ventry-write-bits-complete)
(ptx-d-instance ptx-ventry-to-fields-sound)
(ptx-d-instance ptx-ventry-num-randomizers-sound)
(ptx-d-instance ptx-vnew-sound)
(ptx-d-instance ptx-vnew-complete)
(ptx-d-instance ptx-ventry-new-sound)
(ptx-d-instance ptx-ventry-new-complete)
(ptx-d-instance ptx-veq-sound)
(ptx-d-instance ptx-veq-complete)
(ptx-d-instance ptx-ventry-eq-sound)
(ptx-d-instance ptx-ventry-eq-complete)
