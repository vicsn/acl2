; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A concrete Signature leaf, added to the leaf of ptx-ilit.lisp, for all
; four leaf interfaces; and the Plaintext / Entry theorems instantiated with
; it.  With it the leaf covers every Literal type in scope (String is not a
; formalisation target).
;
; A Signature leaf wire is (:signature sc sr gpk gpr vs asg0): sc, sr the
; Scalar leaf wires of the challenge and the response, gpk, gpr the Group
; leaf wires of pk_sig and pr_sig, and vs, asg0 the variable supply and the
; synthesis assignment from which ComputeKey::from synthesizes sk_prf =
; hash_to_scalar_psd4(pk_sig.x, pr_sig.x) (key-ck-from-gadget, unit wire
; ptx-one).  The literal is the signature of the challenge, the response and
; values-compute-key-from of the two points.
;
;   Literal::new          Scalar::new twice, Group::new twice, then the
;                         hash_to_scalar constraints.  Soundness of the
;                         hash (key-ck-from-sound-any) needs the unit wire
;                         to hold 1, which the new interface does not
;                         assume, so the leaf's typed predicate records,
;                         under that condition, that the sk_prf bits are
;                         bits and that (pk_sig, pr_sig, sk_prf) is
;                         compute-key-from-funspec of the two points;
;   write_bits_le / _be   the challenge, response, pk_sig and pr_sig arms
;                         (Signature::write_bits; ComputeKey::write_bits
;                         writes pk_sig and pr_sig);
;   is_equal / _not_equal (c == c') & (r == r') & ((pk == pk') & (pr == pr')
;                         & (sk == sk')), each & a Boolean AND with a fresh
;                         output wire.  sk is Scalar::from_bits_le of the 250
;                         hash bits, a linear combination, so sk == sk' is
;                         rec-lc-neq-gadget on the two combinations.  With
;                         the unit wire at 1 the sk bits are the hash of the
;                         x-coordinates, so the conjunction is the equality
;                         of the two signature values.
;
; The completeness witnesses of a Signature leaf are false: the instantiated
; completeness theorems cover plaintexts without Signature leaves.

(in-package "ALEOVM")

(include-book "ptx-ilit")
(include-book "key-h2s-any")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (in-theory (disable (:e base-prime) hpos-lc-eval-decomp)))

(local (defrule ptx-s-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shape and values.

(defun ptx-s-pkx (w) (nth 0 (second (nth 3 w))))
(defun ptx-s-prx (w) (nth 0 (second (nth 4 w))))

(defun ptx-s-hw (w)
  (b* (((mv bs rs x &) (key-ck-from-wires (ptx-s-pkx w) (ptx-s-prx w)
                                          (nth 5 w) (nth 6 w))))
    (list bs rs x)))

(defun ptx-s-bs (w) (first (ptx-s-hw w)))
(defun ptx-s-rs (w) (second (ptx-s-hw w)))
(defun ptx-s-x (w) (third (ptx-s-hw w)))

(defun ptx-s-hcs (w)
  (b* (((mv & cs & &) (key-ck-from-gadget (ptx-s-pkx w) (ptx-s-prx w) 'ptx-one
                                          (nth 5 w) (nth 6 w))))
    cs))

(defun ptx-s-shapep (w)
  (and (eq (car w) :signature)
       (ptx-e-scalar-shapep (nth 1 w))
       (ptx-e-scalar-shapep (nth 2 w))
       (ptx-g-shapep (nth 3 w))
       (ptx-g-shapep (nth 4 w))
       (symbolp (ptx-s-x w))
       (not (equal (ptx-s-x w) 'ptx-one))
       (symbol-listp (ptx-s-bs w))
       (symbol-listp (ptx-s-rs w))
       (not (member-equal (ptx-s-x w) (ptx-s-bs w)))
       (not (member-equal (ptx-s-x w) (ptx-s-rs w)))
       (equal (len (ptx-s-bs w)) (integer-length (base-prime)))
       (equal (len (ptx-s-rs w)) (bits-lt-prime-rlen (base-prime)))))

(defun ptx-s-c (w asg) (lookup-equal (second (nth 1 w)) asg))
(defun ptx-s-r (w asg) (lookup-equal (second (nth 2 w)) asg))
(defun ptx-s-pk (w asg) (ptx-g-pt (nth 3 w) asg))
(defun ptx-s-pr (w asg) (ptx-g-pt (nth 4 w) asg))

(defun ptx-s-sig (w asg)
  (make-signature :challenge (ptx-s-c w asg)
                  :response (ptx-s-r w asg)
                  :compute-key (values-compute-key-from (ptx-s-pk w asg)
                                                        (ptx-s-pr w asg))))

(defun ptx-s-sk-wires (w asg)
  (key-sk-of-wires (ptx-s-bs w) asg))

(defun ptx-s-sk-okp (w asg)
  (implies (and (r1cs::valuation-bindsp asg 'ptx-one)
                (equal (lookup-equal 'ptx-one asg) 1))
           (and (bit-listp (lookup-equal-list (ptx-s-bs w) asg))
                (equal (list (ptx-s-pk w asg) (ptx-s-pr w asg)
                             (ptx-s-sk-wires w asg))
                       (compute-key-from-funspec (ptx-s-pk w asg)
                                                 (ptx-s-pr w asg))))))

(defun ptx-s-subs-typedp (w asg)
  (and (ptx-i-leaf-typed (nth 1 w) asg)
       (ptx-i-leaf-typed (nth 2 w) asg)
       (ptx-i-leaf-typed (nth 3 w) asg)
       (ptx-i-leaf-typed (nth 4 w) asg)))

;; The leaf.

(defun ptx-s-leaf-val (w asg)
  (if (eq (car w) :signature)
      (literal-signature (ptx-s-sig w asg))
    (ptx-i-leaf-val w asg)))

(defun ptx-s-leaf-typed (w asg)
  (if (eq (car w) :signature)
      (and (ptx-s-shapep w)
           (ptx-s-subs-typedp w asg)
           (ptx-s-sk-okp w asg))
    (ptx-i-leaf-typed w asg)))

(defun ptx-s-leaf-variant (w)
  (if (eq (car w) :signature) 15 (ptx-i-leaf-variant w)))

(defun ptx-s-leaf-size (w)
  (if (eq (car w) :signature) 1008 (ptx-i-leaf-size w)))

(defun ptx-s-leaf-bits-gadget (w bigp)
  (cond ((not (eq (car w) :signature)) (ptx-i-leaf-bits-gadget w bigp))
        ((ptx-s-shapep w)
         (append (ptx-i-leaf-bits-gadget (nth 1 w) bigp)
                 (ptx-i-leaf-bits-gadget (nth 2 w) bigp)
                 (ptx-i-leaf-bits-gadget (nth 3 w) bigp)
                 (ptx-i-leaf-bits-gadget (nth 4 w) bigp)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-s-leaf-bits-out (w bigp)
  (if (eq (car w) :signature)
      (append (ptx-i-leaf-bits-out (nth 1 w) bigp)
              (ptx-i-leaf-bits-out (nth 2 w) bigp)
              (ptx-i-leaf-bits-out (nth 3 w) bigp)
              (ptx-i-leaf-bits-out (nth 4 w) bigp))
    (ptx-i-leaf-bits-out w bigp)))

(defun ptx-s-leaf-bits-witnessp (w bigp asg p)
  (if (eq (car w) :signature)
      nil
    (ptx-i-leaf-bits-witnessp w bigp asg p)))

(defun ptx-s-leaf-new-gadget (w)
  (cond ((not (eq (car w) :signature)) (ptx-i-leaf-new-gadget w))
        ((ptx-s-shapep w)
         (append (ptx-i-leaf-new-gadget (nth 1 w))
                 (ptx-i-leaf-new-gadget (nth 2 w))
                 (ptx-i-leaf-new-gadget (nth 3 w))
                 (ptx-i-leaf-new-gadget (nth 4 w))
                 (ptx-s-hcs w)))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-s-leaf-new-vars (w)
  (cond ((not (eq (car w) :signature)) (ptx-i-leaf-new-vars w))
        ((ptx-s-shapep w)
         (append (ptx-i-leaf-new-vars (nth 1 w))
                 (ptx-i-leaf-new-vars (nth 2 w))
                 (ptx-i-leaf-new-vars (nth 3 w))
                 (ptx-i-leaf-new-vars (nth 4 w))
                 (ptx-s-bs w)
                 (ptx-s-rs w)))
        (t nil)))

(defun ptx-s-leaf-new-witnessp (w x asg p)
  (if (eq (car w) :signature)
      nil
    (ptx-i-leaf-new-witnessp w x asg p)))

;; is_equal: the names are 2, 2, 5, 5 for the four component equalities,
;; then m, r for sk, then the four AND outputs.

(defun ptx-s-sv (x)
  (if (consp x) x (list (list x 1))))

(defun ptx-s-and-gadget (a b z)
  (list (r1cs::make-r1cs-constraint :a (ptx-s-sv a) :b (ptx-s-sv b)
                                    :c (list (list 1 z)))))

(defun ptx-s-skv (w)
  (pow2sum-vector (take 250 (ptx-s-bs w)) 0))

(defun ptx-s-eq-okp (wa wb names)
  (and (ptx-s-shapep wa) (ptx-s-shapep wb)
       (symbol-listp names) (<= 20 (len names))))

(defun ptx-s-sub-outs (wa wb names)
  (list (ptx-i-leaf-eq-out (nth 1 wa) (nth 1 wb) nil (take 2 names))
        (ptx-i-leaf-eq-out (nth 2 wa) (nth 2 wb) nil (take 2 (nthcdr 2 names)))
        (ptx-i-leaf-eq-out (nth 3 wa) (nth 3 wb) nil (take 5 (nthcdr 4 names)))
        (ptx-i-leaf-eq-out (nth 4 wa) (nth 4 wb) nil (take 5 (nthcdr 9 names)))))

(defun ptx-s-eq-gadget-of (wa wb names)
  (b* (((list oc or opk opr) (ptx-s-sub-outs wa wb names))
       (m (nth 14 names)) (r (nth 15 names))
       (z1 (nth 16 names)) (z2 (nth 17 names))
       (z3 (nth 18 names)) (z4 (nth 19 names)))
    (append (ptx-i-leaf-eq-gadget (nth 1 wa) (nth 1 wb) nil (take 2 names))
            (ptx-i-leaf-eq-gadget (nth 2 wa) (nth 2 wb) nil
                                  (take 2 (nthcdr 2 names)))
            (ptx-i-leaf-eq-gadget (nth 3 wa) (nth 3 wb) nil
                                  (take 5 (nthcdr 4 names)))
            (ptx-i-leaf-eq-gadget (nth 4 wa) (nth 4 wb) nil
                                  (take 5 (nthcdr 9 names)))
            (rec-lc-neq-gadget (ptx-s-skv wa) (ptx-s-skv wb) m r (base-prime))
            (ptx-s-and-gadget oc or z1)
            (ptx-s-and-gadget opk opr z2)
            (ptx-s-and-gadget (list (list 1 z2)) (ptx-c-zout r nil) z3)
            (ptx-s-and-gadget (list (list 1 z1)) (list (list 1 z3)) z4))))

(defun ptx-s-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (eq (car wa) :signature))
         (ptx-i-leaf-eq-gadget wa wb neq names))
        ((ptx-s-eq-okp wa wb names) (ptx-s-eq-gadget-of wa wb names))
        (t (list *ptx-c-false-constraint*))))

(defun ptx-s-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (eq (car wa) :signature))
         (ptx-i-leaf-eq-out wa wb neq names))
        ((ptx-s-eq-okp wa wb names) (ptx-c-zout (nth 19 names) (not neq)))
        (t 0)))

(defun ptx-s-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((not (eq (car wa) :signature)) (ptx-i-leaf-eq-nvars wa wb neq))
        (t 20)))

(defun ptx-s-leaf-eq-witnessp (wa wb neq names asg p)
  (cond ((not (equal (car wa) (car wb))) t)
        ((not (eq (car wa) :signature))
         (ptx-i-leaf-eq-witnessp wa wb neq names asg p))
        (t nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lemmas.

(defruled ptx-s-scalar-sub
  (implies (equal (car v) :scalar)
           (and (equal (ptx-i-leaf-val v asg)
                       (literal-scalar (lookup-equal (second v) asg)))
                (equal (ptx-i-leaf-typed v asg)
                       (and (ptx-e-scalar-shapep v)
                            (scalarp (lookup-equal (second v) asg))
                            (r1cs::valuation-binds-allp asg (ptx-e-scalar-vars v))
                            t))))
  :enable (ptx-i-leaf-val ptx-a-leaf-val ptx-g-leaf-val ptx-e-leaf-val
           ptx-i-leaf-typed ptx-a-leaf-typed ptx-g-leaf-typed ptx-e-leaf-typed)
  :disable (ptx-e-scalar-shapep ptx-e-scalar-vars))

(defruled ptx-s-group-sub
  (implies (equal (car v) :group)
           (and (equal (ptx-i-leaf-val v asg)
                       (literal-group (ptx-g-pt v asg)))
                (equal (ptx-i-leaf-typed v asg)
                       (and (ptx-g-shapep v)
                            (groupp (ptx-g-pt v asg))
                            (r1cs::valuation-binds-allp asg (ptx-g-vars v))
                            t))))
  :enable (ptx-i-leaf-val ptx-a-leaf-val ptx-g-leaf-val
           ptx-i-leaf-typed ptx-a-leaf-typed ptx-g-leaf-typed)
  :disable (ptx-g-shapep ptx-g-vars ptx-g-pt))

(defruled ptx-s-leaf-when-not-signature
  (implies (not (eq (car w) :signature))
           (and (equal (ptx-s-leaf-typed w asg) (ptx-i-leaf-typed w asg))
                (equal (ptx-s-leaf-val w asg) (ptx-i-leaf-val w asg))
                (equal (ptx-s-leaf-new-gadget w) (ptx-i-leaf-new-gadget w))
                (equal (ptx-s-leaf-new-vars w) (ptx-i-leaf-new-vars w))
                (equal (ptx-s-leaf-new-witnessp w x asg p)
                       (ptx-i-leaf-new-witnessp w x asg p))
                (equal (ptx-s-leaf-bits-gadget w bigp)
                       (ptx-i-leaf-bits-gadget w bigp))
                (equal (ptx-s-leaf-bits-out w bigp)
                       (ptx-i-leaf-bits-out w bigp))
                (equal (ptx-s-leaf-bits-witnessp w bigp asg p)
                       (ptx-i-leaf-bits-witnessp w bigp asg p)))))

(defruled ptx-s-literal-facts
  (and (literalp (literal-signature x))
       (equal (literal-variant (literal-signature x)) 15)
       (equal (literal-size-in-bits (literal-signature x)) 1008)
       (equal (literal-kind (literal-signature x)) :signature))
  :enable (literal-variant literal-size-in-bits))

(defruled ptx-s-leaf-constraints
  (and (literalp (ptx-s-leaf-val w asg))
       (implies (ptx-s-leaf-typed w asg)
                (equal (literal-variant (ptx-s-leaf-val w asg))
                       (ptx-s-leaf-variant w)))
       (implies (ptx-s-leaf-typed w asg)
                (equal (literal-size-in-bits (ptx-s-leaf-val w asg))
                       (ptx-s-leaf-size w)))
       (implies (and (consp w)
                     (eq (car w) :boolean)
                     (bitp (lookup-equal (cdr w) asg)))
                (equal (ptx-s-leaf-val w asg)
                       (literal-boolean (lookup-equal (cdr w) asg)))))
  :use (ptx-i-leaf-constraints ptx-s-leaf-when-not-signature)
  :enable ptx-s-literal-facts
  :disable (ptx-i-leaf-val ptx-i-leaf-typed ptx-s-sig ptx-s-shapep
                           ptx-s-subs-typedp ptx-s-sk-okp equal-of-literal-boolean))

;; The ptx-vbits constraints.

(defruled ptx-s-sig-bits
  (implies (and (scalarp c) (scalarp r) (groupp pk) (groupp pr))
           (b* ((sig (make-signature :challenge c :response r
                                     :compute-key (values-compute-key-from pk pr))))
             (and (equal (literal-to-bits-le (literal-signature sig))
                         (append (literal-to-bits-le (literal-scalar c))
                                 (literal-to-bits-le (literal-scalar r))
                                 (literal-to-bits-le (literal-group pk))
                                 (literal-to-bits-le (literal-group pr))))
                  (equal (literal-to-bits-be (literal-signature sig))
                         (append (literal-to-bits-be (literal-scalar c))
                                 (literal-to-bits-be (literal-scalar r))
                                 (literal-to-bits-be (literal-group pk))
                                 (literal-to-bits-be (literal-group pr)))))))
  :enable (literal-to-bits-le literal-to-bits-be values-signature-to-bits-le
           values-signature-to-bits-be values-compute-key-from))
(defruled ptx-s-typed-split
  (implies (and (eq (car w) :signature)
                (ptx-s-leaf-typed w asg))
           (and (ptx-s-shapep w)
                (ptx-s-sk-okp w asg)
                (ptx-i-leaf-typed (nth 1 w) asg)
                (ptx-i-leaf-typed (nth 2 w) asg)
                (ptx-i-leaf-typed (nth 3 w) asg)
                (ptx-i-leaf-typed (nth 4 w) asg)
                (equal (car (nth 1 w)) :scalar)
                (equal (car (nth 2 w)) :scalar)
                (equal (car (nth 3 w)) :group)
                (equal (car (nth 4 w)) :group)
                (scalarp (ptx-s-c w asg))
                (scalarp (ptx-s-r w asg))
                (groupp (ptx-s-pk w asg))
                (groupp (ptx-s-pr w asg))
                (equal (ptx-i-leaf-val (nth 1 w) asg) (literal-scalar (ptx-s-c w asg)))
                (equal (ptx-i-leaf-val (nth 2 w) asg) (literal-scalar (ptx-s-r w asg)))
                (equal (ptx-i-leaf-val (nth 3 w) asg) (literal-group (ptx-s-pk w asg)))
                (equal (ptx-i-leaf-val (nth 4 w) asg) (literal-group (ptx-s-pr w asg)))))
  :do-not-induct t
  :use ((:instance ptx-s-scalar-sub (v (nth 1 w)))
        (:instance ptx-s-scalar-sub (v (nth 2 w)))
        (:instance ptx-s-group-sub (v (nth 3 w)))
        (:instance ptx-s-group-sub (v (nth 4 w))))
  :in-theory '(ptx-s-leaf-typed ptx-s-subs-typedp ptx-s-c ptx-s-r ptx-s-pk ptx-s-pr
               ptx-s-shapep ptx-e-scalar-shapep ptx-g-shapep))

(defruled ptx-s-shapep-car
  (implies (ptx-s-shapep w) (equal (car w) :signature))
  :rule-classes :forward-chaining)

(defruled ptx-s-bits-split
  (implies (and (ptx-s-shapep w)
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-bits-gadget w bigp) asg p))
           (and (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget (nth 1 w) bigp) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget (nth 2 w) bigp) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget (nth 3 w) bigp) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-bits-gadget (nth 4 w) bigp) asg p)))
  :do-not-induct t
  :in-theory '(ptx-s-leaf-bits-gadget r1cs::r1cs-constraints-holdp-of-append
               (:t ptx-s-shapep) ptx-s-shapep-car))

(defruled ptx-s-leaf-bits-sound-signature
  (implies (and (eq (car w) :signature)
                (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-s-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-s-leaf-val w asg))
                    (literal-to-bits-le (ptx-s-leaf-val w asg)))))
  :do-not-induct t
  :use (ptx-s-typed-split ptx-s-bits-split
        (:instance ptx-i-leaf-bits-sound (w (nth 1 w)))
        (:instance ptx-i-leaf-bits-sound (w (nth 2 w)))
        (:instance ptx-i-leaf-bits-sound (w (nth 3 w)))
        (:instance ptx-i-leaf-bits-sound (w (nth 4 w)))
        (:instance ptx-s-sig-bits
         (c (ptx-s-c w asg)) (r (ptx-s-r w asg))
         (pk (ptx-s-pk w asg)) (pr (ptx-s-pr w asg))))
  :in-theory '(ptx-s-leaf-bits-out ptx-s-leaf-val ptx-s-sig ptx-terms-val-of-append
               (:t ptx-s-shapep)))

;; The ptx-vnew constraints.

(defruled ptx-s-new-split
  (implies (and (ptx-s-shapep w)
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w) asg p)
                (r1cs::valuation-binds-allp asg (ptx-s-leaf-new-vars w)))
           (and (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget (nth 1 w)) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget (nth 2 w)) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget (nth 3 w)) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-i-leaf-new-gadget (nth 4 w)) asg p)
                (r1cs::r1cs-constraints-holdp (ptx-s-hcs w) asg p)
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars (nth 1 w)))
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars (nth 2 w)))
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars (nth 3 w)))
                (r1cs::valuation-binds-allp asg (ptx-i-leaf-new-vars (nth 4 w)))
                (r1cs::valuation-binds-allp asg (ptx-s-bs w))
                (r1cs::valuation-binds-allp asg (ptx-s-rs w))))
  :do-not-induct t
  :in-theory '(ptx-s-leaf-new-gadget ptx-s-leaf-new-vars
               r1cs::r1cs-constraints-holdp-of-append ptx-g-binds-allp-of-append
               (:t ptx-s-shapep) ptx-s-shapep-car))

(defruled ptx-s-nth-0 (equal (nth 0 x) (car x)))

(defruled ptx-s-car-sym
  (implies (and (symbol-listp x) (equal (len x) 14)) (symbolp (car x))))

(defruled ptx-s-sk-okp-of-hcs
  (implies (and (ptx-s-shapep w)
                (r1cs::r1cs-valuationp asg (base-prime))
                (ptx-i-leaf-typed (nth 3 w) asg)
                (ptx-i-leaf-typed (nth 4 w) asg)
                (r1cs::valuation-binds-allp asg (ptx-s-bs w))
                (r1cs::valuation-binds-allp asg (ptx-s-rs w))
                (r1cs::r1cs-constraints-holdp (ptx-s-hcs w) asg (base-prime)))
           (ptx-s-sk-okp w asg))
  :do-not-induct t
  :use ((:instance ptx-s-group-sub (v (nth 3 w)))
        (:instance ptx-s-group-sub (v (nth 4 w)))
        (:instance values-edwards-bls12-pointp-when-groupp (x (ptx-s-pk w asg)))
        (:instance values-edwards-bls12-pointp-when-groupp (x (ptx-s-pr w asg)))
        (:instance r1cs::valuation-bindsp-of-car-when-valuation-binds-allp
         (vars (second (nth 3 w))) (valuation asg))
        (:instance r1cs::valuation-bindsp-of-car-when-valuation-binds-allp
         (vars (second (nth 4 w))) (valuation asg))
        (:instance key-ck-from-sound-any
         (px (ptx-s-pkx w)) (rx (ptx-s-prx w))
         (py (nth 1 (second (nth 3 w)))) (ry (nth 1 (second (nth 4 w))))
         (u 'ptx-one) (vs (nth 5 w)) (asg (nth 6 w)) (asgx asg)))
  :in-theory '(ptx-s-sk-okp ptx-s-shapep ptx-s-hw ptx-s-bs ptx-s-rs ptx-s-x ptx-s-hcs
               ptx-s-pk ptx-s-pr ptx-g-pt ptx-s-pkx ptx-s-prx ptx-s-sk-wires
               ptx-g-vars ptx-g-shapep hpos-aleo-rate-p
               ptx-g-binds-allp-of-append (:e symbolp) (:e hpos-aleo-rate-p) (:e not) (:e member-equal) ptx-s-nth-0 ptx-s-car-sym len car-cons cdr-cons))

(defruled ptx-s-literal-new-sig
  (implies (and (scalarp c) (scalarp r) (groupp pk) (groupp pr))
           (b* ((lit (literal-signature
                      (make-signature :challenge c :response r
                                      :compute-key (values-compute-key-from pk pr)))))
             (equal (literal-new lit) lit)))
  :enable (literal-new values-signature-new values-compute-key-from))

(defruled ptx-s-new-typed
  (implies (and (ptx-s-shapep w)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-s-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w) asg p))
           (ptx-s-leaf-typed w asg))
  :do-not-induct t
  :use (ptx-s-new-split ptx-s-sk-okp-of-hcs
        (:instance ptx-i-leaf-new-sound (w (nth 1 w)))
        (:instance ptx-i-leaf-new-sound (w (nth 2 w)))
        (:instance ptx-i-leaf-new-sound (w (nth 3 w)))
        (:instance ptx-i-leaf-new-sound (w (nth 4 w))))
  :in-theory '(ptx-s-leaf-typed ptx-s-subs-typedp ptx-s-shapep-car))

(defruled ptx-s-new-id
  (implies (and (eq (car w) :signature)
                (ptx-s-leaf-typed w asg))
           (equal (literal-new (ptx-s-leaf-val w asg))
                  (ptx-s-leaf-val w asg)))
  :do-not-induct t
  :use (ptx-s-typed-split
        (:instance ptx-s-literal-new-sig
         (c (ptx-s-c w asg)) (r (ptx-s-r w asg))
         (pk (ptx-s-pk w asg)) (pr (ptx-s-pr w asg))))
  :in-theory '(ptx-s-leaf-val ptx-s-sig))

(defruled ptx-s-leaf-new-sound-signature
  (implies (and (eq (car w) :signature)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-s-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w) asg p))
           (and (ptx-s-leaf-typed w asg)
                (equal (literal-new (ptx-s-leaf-val w asg))
                       (ptx-s-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-s-new-typed ptx-s-new-id ptx-s-primep-of-base-prime
        (:instance ptx-c-false-constraint-fails (p (base-prime))))
  :in-theory '(ptx-s-leaf-new-gadget))
(defruled ptx-s-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-s-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w) asg p))
           (and (ptx-s-leaf-typed w asg)
                (equal (literal-new (ptx-s-leaf-val w asg))
                       (ptx-s-leaf-val w asg))))
  :do-not-induct t
  :use (ptx-s-leaf-new-sound-signature ptx-s-leaf-when-not-signature
        ptx-i-leaf-new-sound)
  :in-theory nil)

(defruled ptx-s-leaf-bits-sound
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed w asg)
                (r1cs::r1cs-constraints-holdp (ptx-s-leaf-bits-gadget w bigp)
                                              asg p))
           (equal (ptx-terms-val (ptx-s-leaf-bits-out w bigp) asg)
                  (if bigp
                      (literal-to-bits-be (ptx-s-leaf-val w asg))
                    (literal-to-bits-le (ptx-s-leaf-val w asg)))))
  :do-not-induct t
  :use (ptx-s-leaf-bits-sound-signature ptx-s-leaf-when-not-signature
        ptx-i-leaf-bits-sound)
  :in-theory nil)

;; The ptx-vequal constraints.

(defruled ptx-s-symbolp-of-nth
  (implies (symbol-listp x) (symbolp (nth k x)))
  :enable nth)

(defruled ptx-s-bindsp-of-nth
  (implies (and (r1cs::valuation-binds-allp asg x)
                (< (nfix k) (len x)))
           (r1cs::valuation-bindsp asg (nth k x)))
  :enable (nth r1cs::valuation-binds-allp))

(defruled ptx-s-binds-allp-of-take
  (implies (and (r1cs::valuation-binds-allp asg x)
                (<= (nfix k) (len x)))
           (r1cs::valuation-binds-allp asg (take k x)))
  :enable (take r1cs::valuation-binds-allp))

(defruled ptx-s-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg x)
           (r1cs::valuation-binds-allp asg (nthcdr k x)))
  :enable (nthcdr r1cs::valuation-binds-allp))

(defun ptx-s-bvp (x)
  (if (consp x) (r1cs::sparse-vectorp x) (bitp x)))

(defruled ptx-s-and-sound
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp z)
                (r1cs::valuation-bindsp asg z)
                (ptx-s-bvp a)
                (ptx-s-bvp b)
                (bitp (ptx-bval a asg p))
                (bitp (ptx-bval b asg p))
                (r1cs::r1cs-constraints-holdp (ptx-s-and-gadget a b z) asg p))
           (equal (lookup-equal z asg)
                  (if (and (equal (ptx-bval a asg p) 1)
                           (equal (ptx-bval b asg p) 1))
                      1
                    0)))
  :do-not-induct t
  :cases ((consp a))
  :enable (ptx-s-and-gadget ptx-s-sv ptx-bval r1cs::r1cs-constraint-holdsp
           rec-dot-of-var bitp r1cs::dot-product r1cs::sparse-vectorp
           r1cs::sparse-vector-elementp))

(defruled ptx-s-sub-equalp
  (and (implies (and (scalarp a) (scalarp b))
                (equal (values-literal-equalp (literal-scalar a) (literal-scalar b))
                       (equal a b)))
       (implies (and (groupp a) (groupp b))
                (equal (values-literal-equalp (literal-group a) (literal-group b))
                       (equal a b))))
  :enable values-literal-equalp)

(defruled ptx-s-sig-equalp
  (implies (and (scalarp c1) (scalarp c2) (scalarp r1) (scalarp r2)
                (groupp pk1) (groupp pk2) (groupp pr1) (groupp pr2))
           (equal (values-literal-equalp
                   (literal-signature
                    (make-signature :challenge c1 :response r1
                                    :compute-key (values-compute-key-from pk1 pr1)))
                   (literal-signature
                    (make-signature :challenge c2 :response r2
                                    :compute-key (values-compute-key-from pk2 pr2))))
                  (and (equal c1 c2) (equal r1 r2) (equal pk1 pk2) (equal pr1 pr2))))
  :enable (values-literal-equalp values-signature-equalp values-compute-key-from))

(defruled ptx-s-skv-dot
  (implies (and (ptx-s-shapep w)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (ptx-s-bs w))
                (bit-listp (lookup-equal-list (ptx-s-bs w) asg)))
           (and (r1cs::sparse-vectorp (ptx-s-skv w))
                (equal (r1cs::dot-product (ptx-s-skv w) asg (base-prime))
                       (ptx-s-sk-wires w asg))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat
         (xs (take 250 (ptx-s-bs w))) (i 0) (p (base-prime)))
        (:instance lookup-equal-list-of-take
         (i 250) (keys (ptx-s-bs w)) (alist asg))
        (:instance ptx-s-binds-allp-of-take (k 250) (x (ptx-s-bs w))))
  :enable (ptx-s-sk-wires key-sk-of-wires (:e base-prime) (:e expt))
  :disable (ptx-s-bs pow2sum-vector-to-mod-of-lebits=>nat ptx-s-hw
                     ptx-s-binds-allp-of-take))

(defthm ptx-s-caddr-of-list
  (implies (equal (list a b c) x) (equal c (caddr x)))
  :rule-classes nil)

(defruled ptx-s-sk-equal
  (implies (and (ptx-s-sk-okp wa asg)
                (ptx-s-sk-okp wb asg)
                (r1cs::valuation-bindsp asg 'ptx-one)
                (equal (lookup-equal 'ptx-one asg) 1)
                (equal (ptx-s-pk wa asg) (ptx-s-pk wb asg))
                (equal (ptx-s-pr wa asg) (ptx-s-pr wb asg)))
           (equal (ptx-s-sk-wires wa asg) (ptx-s-sk-wires wb asg)))
  :do-not-induct t
  :use ((:instance ptx-s-caddr-of-list
         (a (ptx-s-pk wa asg)) (b (ptx-s-pr wa asg)) (c (ptx-s-sk-wires wa asg))
         (x (compute-key-from-funspec (ptx-s-pk wa asg) (ptx-s-pr wa asg))))
        (:instance ptx-s-caddr-of-list
         (a (ptx-s-pk wb asg)) (b (ptx-s-pr wb asg)) (c (ptx-s-sk-wires wb asg))
         (x (compute-key-from-funspec (ptx-s-pk wb asg) (ptx-s-pr wb asg)))))
  :in-theory '(ptx-s-sk-okp))

(defruled ptx-s-bindsp-of-one
  (implies (equal (lookup-equal v asg) 1)
           (r1cs::valuation-bindsp asg v))
  :enable (r1cs::valuation-bindsp lookup-equal))

(defruled ptx-s-eq-split
  (implies (r1cs::r1cs-constraints-holdp (ptx-s-eq-gadget-of wa wb names) asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget (nth 1 wa) (nth 1 wb) nil (take 2 names)) asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget (nth 2 wa) (nth 2 wb) nil
                                       (take 2 (nthcdr 2 names))) asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget (nth 3 wa) (nth 3 wb) nil
                                       (take 5 (nthcdr 4 names))) asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget (nth 4 wa) (nth 4 wb) nil
                                       (take 5 (nthcdr 9 names))) asg p)
                (r1cs::r1cs-constraints-holdp
                 (rec-lc-neq-gadget (ptx-s-skv wa) (ptx-s-skv wb)
                                    (nth 14 names) (nth 15 names) (base-prime))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-and-gadget
                  (ptx-i-leaf-eq-out (nth 1 wa) (nth 1 wb) nil (take 2 names))
                  (ptx-i-leaf-eq-out (nth 2 wa) (nth 2 wb) nil (take 2 (nthcdr 2 names)))
                  (nth 16 names))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-and-gadget
                  (ptx-i-leaf-eq-out (nth 3 wa) (nth 3 wb) nil (take 5 (nthcdr 4 names)))
                  (ptx-i-leaf-eq-out (nth 4 wa) (nth 4 wb) nil (take 5 (nthcdr 9 names)))
                  (nth 17 names))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-and-gadget (list (list 1 (nth 17 names)))
                                   (ptx-c-zout (nth 15 names) nil)
                                   (nth 18 names))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-and-gadget (list (list 1 (nth 16 names)))
                                   (list (list 1 (nth 18 names)))
                                   (nth 19 names))
                 asg p)))
  :do-not-induct t
  :in-theory '(ptx-s-eq-gadget-of ptx-s-sub-outs r1cs::r1cs-constraints-holdp-of-append
               car-cons cdr-cons))

(defruled ptx-s-sub-eq
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp sub)
                (r1cs::valuation-binds-allp asg sub)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-i-leaf-typed va asg)
                (ptx-i-leaf-typed vb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-i-leaf-eq-gadget va vb nil sub) asg p))
           (and (ptx-s-bvp (ptx-i-leaf-eq-out va vb nil sub))
                (equal (ptx-bval (ptx-i-leaf-eq-out va vb nil sub) asg p)
                       (if (values-literal-equalp (ptx-i-leaf-val va asg)
                                                  (ptx-i-leaf-val vb asg))
                           1 0))))
  :do-not-induct t
  :use ((:instance ptx-i-leaf-eq-sound (wa va) (wb vb) (neq nil) (names sub))
        (:instance ptx-i-sparse-vectorp-of-leaf-eq-out (wa va) (wb vb) (neq nil)
                   (names sub)))
  :in-theory '(ptx-s-bvp values-bool-to-bit (:e bitp) ptx-bval-of-atom))

(defruled ptx-s-names-facts
  (implies (and (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (<= 20 (len names)))
           (and (symbol-listp (take 2 names))
                (symbol-listp (take 2 (nthcdr 2 names)))
                (symbol-listp (take 5 (nthcdr 4 names)))
                (symbol-listp (take 5 (nthcdr 9 names)))
                (r1cs::valuation-binds-allp asg (take 2 names))
                (r1cs::valuation-binds-allp asg (take 2 (nthcdr 2 names)))
                (r1cs::valuation-binds-allp asg (take 5 (nthcdr 4 names)))
                (r1cs::valuation-binds-allp asg (take 5 (nthcdr 9 names)))
                (symbolp (nth 14 names)) (symbolp (nth 15 names))
                (symbolp (nth 16 names)) (symbolp (nth 17 names))
                (symbolp (nth 18 names)) (symbolp (nth 19 names))
                (r1cs::valuation-bindsp asg (nth 14 names))
                (r1cs::valuation-bindsp asg (nth 15 names))
                (r1cs::valuation-bindsp asg (nth 16 names))
                (r1cs::valuation-bindsp asg (nth 17 names))
                (r1cs::valuation-bindsp asg (nth 18 names))
                (r1cs::valuation-bindsp asg (nth 19 names))))
  :do-not-induct t
  :enable (ptx-s-symbolp-of-nth ptx-s-bindsp-of-nth ptx-s-binds-allp-of-take
           ptx-s-binds-allp-of-nthcdr))

(defruled ptx-s-binds-when-bits
  (implies (bit-listp (lookup-equal-list xs asg))
           (r1cs::valuation-binds-allp asg xs))
  :induct (len xs)
  :enable (r1cs::valuation-binds-allp lookup-equal-list r1cs::valuation-bindsp
           lookup-equal bit-listp))

(defruled ptx-s-bvp-of-zout
  (implies (symbolp z)
           (and (consp (ptx-c-zout z nil))
                (ptx-s-bvp (ptx-c-zout z nil))))
  :enable (ptx-c-zout ptx-one-minus ptx-neg r1cs::sparse-vectorp
           r1cs::sparse-vector-elementp))

(defruled ptx-s-comp-eqs
  (implies (and (eq (car wa) :signature)
                (eq (car wb) :signature)
                (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (<= 20 (len names))
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed wa asg)
                (ptx-s-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp (ptx-s-eq-gadget-of wa wb names) asg p))
           (b* ((oc (ptx-i-leaf-eq-out (nth 1 wa) (nth 1 wb) nil (take 2 names)))
                (or (ptx-i-leaf-eq-out (nth 2 wa) (nth 2 wb) nil
                                       (take 2 (nthcdr 2 names))))
                (opk (ptx-i-leaf-eq-out (nth 3 wa) (nth 3 wb) nil
                                        (take 5 (nthcdr 4 names))))
                (opr (ptx-i-leaf-eq-out (nth 4 wa) (nth 4 wb) nil
                                        (take 5 (nthcdr 9 names)))))
             (and (ptx-s-bvp oc) (ptx-s-bvp or) (ptx-s-bvp opk) (ptx-s-bvp opr)
                  (equal (ptx-bval oc asg p)
                         (if (equal (ptx-s-c wa asg) (ptx-s-c wb asg)) 1 0))
                  (equal (ptx-bval or asg p)
                         (if (equal (ptx-s-r wa asg) (ptx-s-r wb asg)) 1 0))
                  (equal (ptx-bval opk asg p)
                         (if (equal (ptx-s-pk wa asg) (ptx-s-pk wb asg)) 1 0))
                  (equal (ptx-bval opr asg p)
                         (if (equal (ptx-s-pr wa asg) (ptx-s-pr wb asg)) 1 0)))))
  :do-not-induct t
  :use (ptx-s-eq-split ptx-s-names-facts
        (:instance ptx-s-typed-split (w wa))
        (:instance ptx-s-typed-split (w wb))
        (:instance ptx-s-sub-eq (va (nth 1 wa)) (vb (nth 1 wb)) (sub (take 2 names)))
        (:instance ptx-s-sub-eq (va (nth 2 wa)) (vb (nth 2 wb))
                   (sub (take 2 (nthcdr 2 names))))
        (:instance ptx-s-sub-eq (va (nth 3 wa)) (vb (nth 3 wb))
                   (sub (take 5 (nthcdr 4 names))))
        (:instance ptx-s-sub-eq (va (nth 4 wa)) (vb (nth 4 wb))
                   (sub (take 5 (nthcdr 9 names))))
        (:instance ptx-s-sub-equalp (a (ptx-s-c wa asg)) (b (ptx-s-c wb asg)))
        (:instance ptx-s-sub-equalp (a (ptx-s-r wa asg)) (b (ptx-s-r wb asg)))
        (:instance ptx-s-sub-equalp (a (ptx-s-pk wa asg)) (b (ptx-s-pk wb asg)))
        (:instance ptx-s-sub-equalp (a (ptx-s-pr wa asg)) (b (ptx-s-pr wb asg))))
  :in-theory nil)

(defmacro ptx-s-eq-hyps ()
  '(and (eq (car wa) :signature)
        (eq (car wb) :signature)
        (primep p)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (symbol-listp names)
        (r1cs::valuation-binds-allp asg names)
        (<= 20 (len names))
        (equal (lookup-equal 'ptx-one asg) 1)
        (ptx-s-leaf-typed wa asg)
        (ptx-s-leaf-typed wb asg)
        (r1cs::r1cs-constraints-holdp (ptx-s-eq-gadget-of wa wb names) asg p)))

(defruled ptx-s-z1
  (implies (ptx-s-eq-hyps)
           (equal (lookup-equal (nth 16 names) asg)
                  (if (and (equal (ptx-s-c wa asg) (ptx-s-c wb asg))
                           (equal (ptx-s-r wa asg) (ptx-s-r wb asg)))
                      1 0)))
  :do-not-induct t
  :use (ptx-s-comp-eqs ptx-s-eq-split ptx-s-names-facts
        (:instance ptx-s-and-sound
         (a (ptx-i-leaf-eq-out (nth 1 wa) (nth 1 wb) nil (take 2 names)))
         (b (ptx-i-leaf-eq-out (nth 2 wa) (nth 2 wb) nil (take 2 (nthcdr 2 names))))
         (z (nth 16 names))))
  :in-theory '((:e bitp)))

(defruled ptx-s-z2
  (implies (ptx-s-eq-hyps)
           (equal (lookup-equal (nth 17 names) asg)
                  (if (and (equal (ptx-s-pk wa asg) (ptx-s-pk wb asg))
                           (equal (ptx-s-pr wa asg) (ptx-s-pr wb asg)))
                      1 0)))
  :do-not-induct t
  :use (ptx-s-comp-eqs ptx-s-eq-split ptx-s-names-facts
        (:instance ptx-s-and-sound
         (a (ptx-i-leaf-eq-out (nth 3 wa) (nth 3 wb) nil (take 5 (nthcdr 4 names))))
         (b (ptx-i-leaf-eq-out (nth 4 wa) (nth 4 wb) nil (take 5 (nthcdr 9 names))))
         (z (nth 17 names))))
  :in-theory '((:e bitp)))

(defruled ptx-s-rbit
  (implies (ptx-s-eq-hyps)
           (equal (lookup-equal (nth 15 names) asg)
                  (if (equal (ptx-s-sk-wires wa asg) (ptx-s-sk-wires wb asg))
                      0 1)))
  :do-not-induct t
  :use (ptx-s-eq-split ptx-s-names-facts
        (:instance ptx-s-typed-split (w wa))
        (:instance ptx-s-typed-split (w wb))
        (:instance ptx-s-binds-when-bits (xs (ptx-s-bs wa)))
        (:instance ptx-s-binds-when-bits (xs (ptx-s-bs wb)))
        (:instance ptx-s-bindsp-of-one (v 'ptx-one))
        (:instance ptx-s-skv-dot (w wa))
        (:instance ptx-s-skv-dot (w wb))
        (:instance rec-lc-neq-gadget-bit
         (va (ptx-s-skv wa)) (vb (ptx-s-skv wb))
         (m (nth 14 names)) (r (nth 15 names))))
  :in-theory '(ptx-s-sk-okp))

(defruled ptx-s-z3
  (implies (ptx-s-eq-hyps)
           (equal (lookup-equal (nth 18 names) asg)
                  (if (and (equal (ptx-s-pk wa asg) (ptx-s-pk wb asg))
                           (equal (ptx-s-pr wa asg) (ptx-s-pr wb asg)))
                      1 0)))
  :do-not-induct t
  :use (ptx-s-z2 ptx-s-rbit ptx-s-eq-split ptx-s-names-facts
        (:instance ptx-s-typed-split (w wa))
        (:instance ptx-s-typed-split (w wb))
        (:instance ptx-s-bindsp-of-one (v 'ptx-one))
        ptx-s-sk-equal
        (:instance ptx-s-bvp-of-zout (z (nth 15 names)))
        (:instance ptx-c-bval-of-zout (z (nth 15 names)) (neq nil))
        (:instance rec-dot-of-var (m (nth 17 names)))
        (:instance ptx-s-and-sound
         (a (list (list 1 (nth 17 names)))) (b (ptx-c-zout (nth 15 names) nil))
         (z (nth 18 names))))
  :in-theory '(ptx-s-bvp ptx-bval r1cs::sparse-vectorp r1cs::sparse-vector-elementp
               (:e bitp) car-cons cdr-cons (:e integerp) (:e consp) len r1cs::pseudo-varp (:e len) (:e zp) (:e fix) (:e binary-+)))

(defruled ptx-s-z4
  (implies (ptx-s-eq-hyps)
           (equal (lookup-equal (nth 19 names) asg)
                  (if (and (equal (ptx-s-c wa asg) (ptx-s-c wb asg))
                           (equal (ptx-s-r wa asg) (ptx-s-r wb asg))
                           (equal (ptx-s-pk wa asg) (ptx-s-pk wb asg))
                           (equal (ptx-s-pr wa asg) (ptx-s-pr wb asg)))
                      1 0)))
  :do-not-induct t
  :use (ptx-s-z1 ptx-s-z3 ptx-s-eq-split ptx-s-names-facts
        (:instance rec-dot-of-var (m (nth 16 names)))
        (:instance rec-dot-of-var (m (nth 18 names)))
        (:instance ptx-s-and-sound
         (a (list (list 1 (nth 16 names)))) (b (list (list 1 (nth 18 names))))
         (z (nth 19 names))))
  :in-theory '(ptx-s-bvp ptx-bval r1cs::sparse-vectorp r1cs::sparse-vector-elementp
               (:e bitp) car-cons cdr-cons (:e integerp) (:e consp) len r1cs::pseudo-varp (:e len) (:e zp) (:e fix) (:e binary-+)))

(defruled ptx-s-leaf-eq-sound-signature
  (implies (and (eq (car wa) :signature)
                (eq (car wb) :signature)
                (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed wa asg)
                (ptx-s-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-s-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-s-leaf-val wa asg)
                                                   (ptx-s-leaf-val wb asg)))
                     (values-literal-equalp (ptx-s-leaf-val wa asg)
                                            (ptx-s-leaf-val wb asg))))))
  :do-not-induct t
  :cases ((ptx-s-eq-okp wa wb names))
  :hints (("Subgoal 2"
           :use ((:instance ptx-c-false-constraint-fails (p (base-prime)))
                 (:instance ptx-s-typed-split (w wa))
                 (:instance ptx-s-typed-split (w wb)))
           :in-theory '(ptx-s-leaf-eq-gadget ptx-s-eq-okp))
          ("Subgoal 1"
           :use (ptx-s-z4 ptx-s-names-facts
                 (:instance ptx-s-typed-split (w wa))
                 (:instance ptx-s-typed-split (w wb))
                 (:instance ptx-c-bval-of-zout (z (nth 19 names)) (neq (not neq)))
                 (:instance ptx-s-sig-equalp
                  (c1 (ptx-s-c wa asg)) (r1 (ptx-s-r wa asg))
                  (pk1 (ptx-s-pk wa asg)) (pr1 (ptx-s-pr wa asg))
                  (c2 (ptx-s-c wb asg)) (r2 (ptx-s-r wb asg))
                  (pk2 (ptx-s-pk wb asg)) (pr2 (ptx-s-pr wb asg))))
           :in-theory '(ptx-s-leaf-eq-gadget ptx-s-leaf-eq-out ptx-s-leaf-val
                        ptx-s-sig ptx-s-eq-okp values-bool-to-bit (:e bitp)
                        not (:e not)))))

(defruled ptx-s-leaf-eq-when-not-signature
  (implies (not (equal (car wa) :signature))
           (and (equal (ptx-s-leaf-eq-gadget wa wb neq names)
                       (ptx-i-leaf-eq-gadget wa wb neq names))
                (equal (ptx-s-leaf-eq-out wa wb neq names)
                       (ptx-i-leaf-eq-out wa wb neq names))
                (equal (ptx-s-leaf-eq-witnessp wa wb neq names asg p)
                       (ptx-i-leaf-eq-witnessp wa wb neq names asg p))))
  :use ptx-i-leaf-eq-out-when-mismatch
  :enable ptx-i-leaf-eq-witnessp
  :disable (ptx-i-leaf-eq-gadget ptx-i-leaf-eq-out lit-literal-equal-mismatch-gadget))

(defruled ptx-s-kind-of-leaf-val
  (implies (ptx-s-leaf-typed w asg)
           (equal (literal-kind (ptx-s-leaf-val w asg)) (car w)))
  :do-not-induct t
  :use (ptx-i-kind-of-leaf-val ptx-s-leaf-when-not-signature)
  :in-theory '(ptx-s-leaf-val ptx-s-literal-facts))

(defruled ptx-s-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed wa asg)
                (ptx-s-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-s-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-s-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-s-leaf-val wa asg)
                                                   (ptx-s-leaf-val wb asg)))
                     (values-literal-equalp (ptx-s-leaf-val wa asg)
                                            (ptx-s-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-s-kind-of-leaf-val (w wa))
        (:instance ptx-s-kind-of-leaf-val (w wb))
        (:instance ptx-s-leaf-constraints (w wa))
        (:instance ptx-s-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-s-leaf-val wa asg)) (y (ptx-s-leaf-val wb asg)))
        ptx-s-leaf-eq-sound-signature
        ptx-i-leaf-eq-sound
        (:instance ptx-s-leaf-when-not-signature (w wa))
        (:instance ptx-s-leaf-when-not-signature (w wb))
        ptx-s-leaf-eq-when-not-signature)
  :in-theory '(values-bool-to-bit ptx-bval-of-atom (:e bitp) (:e values-bool-to-bit)
               ptx-s-leaf-eq-out (:e not)))

(defruled ptx-s-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-s-leaf-typed wa asg)
                (ptx-s-leaf-typed wb asg)
                (ptx-s-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-s-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use (ptx-i-leaf-eq-complete
        (:instance ptx-s-leaf-when-not-signature (w wa))
        (:instance ptx-s-leaf-when-not-signature (w wb))
        ptx-s-leaf-eq-when-not-signature)
  :enable (lit-literal-equal-mismatch-complete ptx-i-leaf-eq-out-when-mismatch)
  :disable (lit-literal-equal-mismatch-gadget ptx-i-leaf-eq-complete
            ptx-s-leaf-typed ptx-s-leaf-val))

(defruled ptx-s-leaf-bits-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-s-leaf-typed w asg)
                (ptx-s-leaf-bits-witnessp w bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-s-leaf-bits-gadget w bigp)
                                         asg p))
  :do-not-induct t
  :use (ptx-i-leaf-bits-complete ptx-s-leaf-when-not-signature)
  :in-theory '(ptx-s-leaf-bits-witnessp))

(defruled ptx-s-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-s-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w) asg p)
                (equal (ptx-s-leaf-val w asg) (literal-new x))))
  :do-not-induct t
  :use (ptx-i-leaf-new-complete ptx-s-leaf-when-not-signature)
  :in-theory '(ptx-s-leaf-new-witnessp))

(defruled ptx-s-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-s-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-s-leaf-new-gadget w)
                                              asg p)))
  :do-not-induct t
  :use (ptx-i-leaf-new-error ptx-s-leaf-when-not-signature)
  :in-theory '(ptx-s-leaf-new-witnessp))

(defrule ptx-s-natp-of-leaf-eq-nvars
  (natp (ptx-s-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription)

(defrule ptx-s-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-s-leaf-eq-out wa wb neq names))
                             (ptx-s-leaf-eq-out wa wb neq names)))
  :use (ptx-i-sparse-vectorp-of-leaf-eq-out
        (:instance ptx-d-sparse-vectorp-of-zout (z (nth 19 names)) (neq (not neq)))
        (:instance ptx-s-symbolp-of-nth (k 19) (x names)))
  :in-theory '(ptx-s-leaf-eq-out ptx-s-eq-okp (:e r1cs::sparse-vectorp) (:e consp) not))

(defrule ptx-s-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-s-leaf-new-vars w))
  :enable ptx-s-shapep
  :disable (ptx-i-leaf-new-vars ptx-s-hw))

(in-theory (disable ptx-s-leaf-val ptx-s-leaf-typed ptx-s-leaf-variant
                    ptx-s-leaf-size ptx-s-leaf-bits-gadget ptx-s-leaf-bits-out
                    ptx-s-leaf-bits-witnessp ptx-s-leaf-new-gadget
                    ptx-s-leaf-new-vars ptx-s-leaf-new-witnessp
                    ptx-s-leaf-eq-gadget ptx-s-leaf-eq-out ptx-s-leaf-eq-nvars
                    ptx-s-leaf-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Plaintext / Entry theorems instantiated with the leaf covering every
;; Literal type except String (out of scope).

(ptx-gen-copy "PTX-S-")
(ptx-gen-instances "PTX-S-")
