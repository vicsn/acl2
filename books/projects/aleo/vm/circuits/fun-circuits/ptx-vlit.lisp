; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The concrete Literal wire representation of ptx-lit.lisp (Boolean and
; the ten Integer arms) for Literal::new and Literal::is_equal /
; is_not_equal, and the Plaintext / Entry theorems of ptx-vnew.lisp and
; ptx-vequal.lisp functionally instantiated with it.
;
; Literal::new on a leaf is the arm of literal-new-r1cs.lisp:
; literal-boolean-new-gadget (one boolean check) or
; literal-integer-new-gadget (a boolean check per bit).  A leaf wire of
; the wrong shape (not a symbol, or not n symbols) is a synthesis-time
; impossibility and gets the unsatisfiable constraint 0 * 0 = 1.
;
; Literal::is_equal / is_not_equal on two leaves:
;   different variants   no constraint, constant output (lit-literal-equal);
;   two Booleans         lit-boolean-is-not-equal-gadget (xor) with the
;                        fresh output wire z;
;   two Integers         int-is-not-equal-gadget with fresh wires z, w and
;                        the unit wire ptx-one;
; the output is z for is_not_equal and 1 - z for is_equal.  The integer
; gadget begins with a boolean check of z, and int-is-not-equal-gadget-sound
; does not assume z is a bit; the is_equal arm is derived from it, so no
; hypothesis about z remains.  The other hypotheses are the base prime,
; a valuation covering the fresh wires, and ptx-one = 1.

(in-package "ALEOVM")

(include-book "ptx-lit")
(include-book "ptx-vnew")
(include-book "ptx-vequal")

(set-verify-guards-eagerness 0)
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (in-theory (disable (:e base-prime))))

(local (defrule ptx-c-primep-of-base-prime
         (primep (base-prime))
         :use primep-of-base-prime))

(local (defrule ptx-c-mod-1-when-big
         (implies (and (integerp p) (<= 2 p))
                  (equal (mod 1 p) 1))
         :enable mod))

(defconst *ptx-c-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(defruled ptx-c-false-constraint-fails
  (implies (primep p)
           (not (r1cs::r1cs-constraints-holdp (list *ptx-c-false-constraint*)
                                              asg p)))
  :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep))

(defrule ptx-c-false-constraint-fails-base
  (and (not (r1cs::r1cs-constraints-holdp (list *ptx-c-false-constraint*)
                                          asg (base-prime)))
       (not (r1cs::r1cs-constraint-holdsp *ptx-c-false-constraint*
                                          asg (base-prime))))
  :use ((:instance ptx-c-false-constraint-fails (p (base-prime))))
  :enable r1cs::r1cs-constraints-holdp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wires bound by a typed leaf.

(defruled ptx-c-bindsp-when-lookup
  (implies (lookup-equal v asg)
           (r1cs::valuation-bindsp asg v))
  :induct (len asg)
  :enable (lookup-equal assoc-equal r1cs::valuation-bindsp))

(defruled ptx-c-binds-allp-when-bit-listp
  (implies (bit-listp (lookup-equal-list xs asg))
           (r1cs::valuation-binds-allp asg xs))
  :induct (len xs)
  :enable (lookup-equal-list r1cs::valuation-binds-allp
                             ptx-c-bindsp-when-lookup))

(defruled ptx-c-bindsp-when-bitp
  (implies (bitp (lookup-equal v asg))
           (r1cs::valuation-bindsp asg v))
  :enable (ptx-c-bindsp-when-lookup bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal::new.

(defun ptx-c-leaf-shapep (w)
  (b* ((info (assoc-equal (car w) *ptx-c-ints*)))
    (cond ((eq (car w) :boolean) (symbolp (cdr w)))
          (info (and (symbol-listp (cdr w))
                     (equal (len (cdr w)) (third info))))
          (t nil))))

(defun ptx-c-leaf-new-gadget (w)
  (cond ((not (ptx-c-leaf-shapep w)) (list *ptx-c-false-constraint*))
        ((eq (car w) :boolean)
         (literal-boolean-new-gadget (cdr w) (base-prime)))
        (t (literal-integer-new-gadget (cdr w) (base-prime)))))

(defun ptx-c-leaf-new-vars (w)
  (cond ((not (ptx-c-leaf-shapep w)) nil)
        ((eq (car w) :boolean) (list (cdr w)))
        (t (cdr w))))

(defun ptx-c-leaf-new-witnessp (w x asg p)
  (and (r1cs::r1cs-valuationp asg p)
       (r1cs::valuation-binds-allp asg (ptx-c-leaf-new-vars w))
       (ptx-c-leaf-typed w asg)
       (equal (ptx-c-leaf-val w asg) x)))

(defruled ptx-c-literal-new-of-leaf-val
  (equal (literal-new (ptx-c-leaf-val w asg))
         (ptx-c-leaf-val w asg))
  :enable (ptx-c-leaf-val literal-new))

(defruled ptx-c-typed-iff-shape
  (equal (ptx-c-leaf-typed w asg)
         (and (ptx-c-leaf-shapep w)
              (if (eq (car w) :boolean)
                  (bitp (lookup-equal (cdr w) asg))
                (bit-listp (lookup-equal-list (cdr w) asg)))))
  :enable ptx-c-leaf-typed)

(defruled ptx-c-leaf-new-holds
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (ptx-c-leaf-new-vars w)))
           (equal (r1cs::r1cs-constraints-holdp (ptx-c-leaf-new-gadget w)
                                                asg (base-prime))
                  (ptx-c-leaf-typed w asg)))
  :enable (ptx-c-typed-iff-shape
           literal-boolean-new-gadget-to-bitp
           literal-integer-new-gadget-to-bit-listp
           ptx-c-false-constraint-fails))

(defrule ptx-c-symbol-listp-of-leaf-new-vars
  (symbol-listp (ptx-c-leaf-new-vars w)))

(in-theory (disable ptx-c-leaf-new-gadget ptx-c-leaf-new-vars ptx-c-leaf-shapep))

(defruled ptx-c-leaf-new-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (ptx-c-leaf-new-vars w))
                (r1cs::r1cs-constraints-holdp (ptx-c-leaf-new-gadget w) asg p))
           (and (ptx-c-leaf-typed w asg)
                (equal (literal-new (ptx-c-leaf-val w asg))
                       (ptx-c-leaf-val w asg))))
  :enable (ptx-c-leaf-new-holds ptx-c-literal-new-of-leaf-val))

(defruled ptx-c-leaf-new-complete
  (implies (and (equal p (base-prime))
                (ptx-c-leaf-new-witnessp w x asg p)
                (not (reserrp (literal-new x))))
           (and (r1cs::r1cs-constraints-holdp (ptx-c-leaf-new-gadget w) asg p)
                (equal (ptx-c-leaf-val w asg) (literal-new x))))
  :enable (ptx-c-leaf-new-holds ptx-c-literal-new-of-leaf-val
                                ptx-c-leaf-new-witnessp))

(defruled ptx-c-leaf-new-error
  (implies (and (equal p (base-prime))
                (ptx-c-leaf-new-witnessp w x asg p)
                (reserrp (literal-new x)))
           (not (r1cs::r1cs-constraints-holdp (ptx-c-leaf-new-gadget w)
                                              asg p)))
  :use ((:instance ptx-c-leaf-constraints))
  :enable (ptx-c-literal-new-of-leaf-val ptx-c-leaf-new-witnessp))

(in-theory (disable ptx-c-leaf-new-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal::is_equal / is_not_equal.

(defun ptx-c-names-okp (wa names)
  (if (eq (car wa) :boolean)
      (and (consp names) (symbolp (car names)))
    (and (consp names) (symbolp (car names))
         (consp (cdr names)) (symbolp (cadr names)))))

(defun ptx-c-zout (z neq)
  (if neq
      (list (list 1 z))
    (ptx-one-minus (list (list 1 z)))))

(defun ptx-c-leaf-eq-gadget (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (lit-literal-equal-mismatch-gadget))
        ((not (and (ptx-c-leaf-shapep wa) (ptx-c-leaf-shapep wb)
                   (ptx-c-names-okp wa names)))
         (list *ptx-c-false-constraint*))
        ((eq (car wa) :boolean)
         (lit-boolean-is-not-equal-gadget (cdr wa) (cdr wb) (car names)
                                          (base-prime)))
        (t (int-is-not-equal-gadget (cdr wa) (cdr wb) (car names) (cadr names)
                                    'ptx-one (base-prime)))))

(defun ptx-c-leaf-eq-out (wa wb neq names)
  (cond ((not (equal (car wa) (car wb))) (if neq 1 0))
        ((not (and (ptx-c-leaf-shapep wa) (ptx-c-leaf-shapep wb)
                   (ptx-c-names-okp wa names)))
         0)
        (t (ptx-c-zout (car names) neq))))

(defun ptx-c-leaf-eq-nvars (wa wb neq)
  (cond ((not (equal (car wa) (car wb))) 0)
        ((eq (car wa) :boolean) 1)
        (t 2)))

(defun ptx-c-int-neq-witness (xs ys signedp n asg)
  (b* ((x (lebits->int (lookup-equal-list xs asg) signedp))
       (y (lebits->int (lookup-equal-list ys asg) signedp)))
    (if (equal x y)
        0
      (pfield::inv (pfield::sub (int-spec-unsigned x n)
                                (int-spec-unsigned y n)
                                (base-prime))
                   (base-prime)))))

(defun ptx-c-leaf-eq-witnessp (wa wb neq names asg p)
  (b* ((info (assoc-equal (car wa) *ptx-c-ints*)))
    (cond ((not (equal (car wa) (car wb))) t)
          ((not (ptx-c-names-okp wa names)) nil)
          ((eq (car wa) :boolean)
           (and (r1cs::valuation-bindsp asg (car names))
                (equal (lookup-equal (car names) asg)
                       (bitxor (lookup-equal (cdr wa) asg)
                               (lookup-equal (cdr wb) asg)))))
          (t (and (r1cs::valuation-bindsp asg (car names))
                  (r1cs::valuation-bindsp asg (cadr names))
                  (r1cs::valuation-bindsp asg 'ptx-one)
                  (equal (lookup-equal 'ptx-one asg) 1)
                  (equal (lookup-equal (car names) asg)
                         (int-is-not-equal-spec
                          (lebits->int (lookup-equal-list (cdr wa) asg) (second info))
                          (lebits->int (lookup-equal-list (cdr wb) asg) (second info))
                          (second info) (third info)))
                  (equal (lookup-equal (cadr names) asg)
                         (ptx-c-int-neq-witness (cdr wa) (cdr wb) (second info)
                                                (third info) asg)))))))

;; The output linear combination.

(defruled ptx-c-bval-of-zout
  (implies (and (symbolp z)
                (bitp (lookup-equal z asg)))
           (equal (ptx-bval (ptx-c-zout z neq) asg (base-prime))
                  (if neq
                      (lookup-equal z asg)
                    (if (equal (lookup-equal z asg) 1) 0 1))))
  :enable (ptx-bval ptx-one-minus ptx-dot-product-of-singleton bitp
                    r1cs::sparse-vectorp r1cs::sparse-vector-elementp))

(defrule ptx-c-sparse-vectorp-of-leaf-eq-out
  (r1cs::sparse-vectorp (and (consp (ptx-c-leaf-eq-out wa wb neq names))
                             (ptx-c-leaf-eq-out wa wb neq names)))
  :enable (ptx-one-minus ptx-neg r1cs::sparse-vectorp
                         r1cs::sparse-vector-elementp))

;; Kinds and the mismatch arm.

(defruled ptx-c-kind-of-leaf-val
  (implies (ptx-c-leaf-typed w asg)
           (equal (literal-kind (ptx-c-leaf-val w asg)) (car w)))
  :use ptx-c-kind-when-typed
  :enable (ptx-c-leaf-val ptx-c-leaf-typed))

(defruled ptx-c-literal-equalp-when-kinds-differ
  (implies (and (literalp x) (literalp y)
                (not (equal (literal-kind x) (literal-kind y))))
           (not (values-literal-equalp x y)))
  :enable values-literal-equalp)

;; The Boolean arm.

(defruled ptx-c-leaf-eq-sound-boolean
  (implies (and (equal (car wa) :boolean)
                (equal (car wb) :boolean)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-c-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-c-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-c-leaf-val wa asg)
                                                   (ptx-c-leaf-val wb asg)))
                     (values-literal-equalp (ptx-c-leaf-val wa asg)
                                            (ptx-c-leaf-val wb asg))))))
  :use ((:instance lit-literal-is-not-equal-boolean-sound
         (a (cdr wa)) (b (cdr wb)) (out (car names)))
        (:instance ptx-c-bval-of-zout (z (car names))))
  :enable (ptx-c-leaf-typed ptx-c-leaf-val ptx-c-leaf-shapep
                            ptx-c-bindsp-when-bitp literal-is-not-equal
                            values-bool-to-bit ptx-c-false-constraint-fails)
  :disable ptx-c-zout)

;; The Integer arms.

(defruled ptx-c-bindsp-of-car-and-cadr
  (implies (r1cs::valuation-binds-allp asg names)
           (and (implies (consp names)
                         (r1cs::valuation-bindsp asg (car names)))
                (implies (consp (cdr names))
                         (r1cs::valuation-bindsp asg (cadr names)))))
  :enable r1cs::valuation-binds-allp)

;; int-is-not-equal-gadget-sound over the wires, at any width: z is the
;; not-equal bit of the decoded integers.  No hypothesis on z beyond its
;; binding.

(defruled ptx-c-int-neq-wires
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (integer-widthp n)
                (symbol-listp xs)
                (symbol-listp ys)
                (equal (len xs) n)
                (equal (len ys) n)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (symbolp z)
                (symbolp w)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (equal (lookup-equal 'ptx-one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-is-not-equal-gadget xs ys z w 'ptx-one p) asg p))
           (equal (lookup-equal z asg)
                  (if (equal (lebits->int (lookup-equal-list xs asg) signedp)
                             (lebits->int (lookup-equal-list ys asg) signedp))
                      0
                    1)))
  :do-not-induct t
  :use ((:instance int-is-not-equal-gadget-sound
         (one 'ptx-one)
         (x (lebits->int (lookup-equal-list xs asg) signedp))
         (y (lebits->int (lookup-equal-list ys asg) signedp)))
        (:instance int-valuep-of-lebits->int
         (bits (lookup-equal-list xs asg)))
        (:instance int-valuep-of-lebits->int
         (bits (lookup-equal-list ys asg)))
        (:instance ptx-c-int->lebits-of-lebits->int
         (bits (lookup-equal-list xs asg)))
        (:instance ptx-c-int->lebits-of-lebits->int
         (bits (lookup-equal-list ys asg))))
  :enable (ptx-c-binds-allp-when-bit-listp ptx-c-bindsp-when-lookup
           int-is-not-equal-spec int-spec-bool posp-when-integer-widthp)
  :disable (int-is-not-equal-gadget-sound))

(defmacro ptx-c-int-equalp-arm (kind lit signedp n bridge)
  (b* ((name (intern-in-package-of-symbol
              (concatenate 'string "PTX-C-INT-EQUALP-" (symbol-name kind))
              'ptx-c-int-equalp-arm)))
    `(defruled ,name
       (implies (and (bit-listp a) (equal (len a) ,n)
                     (bit-listp b) (equal (len b) ,n))
                (equal (values-literal-equalp (,lit (lebits->int a ,signedp))
                                              (,lit (lebits->int b ,signedp)))
                       (equal (lebits->int a ,signedp)
                              (lebits->int b ,signedp))))
       :do-not-induct t
       :use ((:instance ,bridge (a (lebits->int a ,signedp))
                        (b (lebits->int b ,signedp)))
             (:instance int-valuep-of-lebits->int (bits a) (signedp ,signedp) (n ,n))
             (:instance int-valuep-of-lebits->int (bits b) (signedp ,signedp) (n ,n)))
       :enable (literal-is-not-equal values-bool-to-bit int-is-not-equal-spec
                int-spec-bool)
       :disable (,bridge))))

(ptx-c-int-equalp-arm i8 literal-i8 t 8 lit-literal-is-not-equal-i8-bridge)
(ptx-c-int-equalp-arm i16 literal-i16 t 16 lit-literal-is-not-equal-i16-bridge)
(ptx-c-int-equalp-arm i32 literal-i32 t 32 lit-literal-is-not-equal-i32-bridge)
(ptx-c-int-equalp-arm i64 literal-i64 t 64 lit-literal-is-not-equal-i64-bridge)
(ptx-c-int-equalp-arm i128 literal-i128 t 128 lit-literal-is-not-equal-i128-bridge)
(ptx-c-int-equalp-arm u8 literal-u8 nil 8 lit-literal-is-not-equal-u8-bridge)
(ptx-c-int-equalp-arm u16 literal-u16 nil 16 lit-literal-is-not-equal-u16-bridge)
(ptx-c-int-equalp-arm u32 literal-u32 nil 32 lit-literal-is-not-equal-u32-bridge)
(ptx-c-int-equalp-arm u64 literal-u64 nil 64 lit-literal-is-not-equal-u64-bridge)
(ptx-c-int-equalp-arm u128 literal-u128 nil 128 lit-literal-is-not-equal-u128-bridge)

(defun ptx-c-int-decode (w asg)
  (lebits->int (lookup-equal-list (cdr w) asg)
               (second (assoc-equal (car w) *ptx-c-ints*))))

(defruled ptx-c-int-equalp
  (implies (and (equal (car wb) (car wa))
                (not (equal (car wa) :boolean))
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg))
           (equal (values-literal-equalp (ptx-c-leaf-val wa asg)
                                         (ptx-c-leaf-val wb asg))
                  (equal (ptx-c-int-decode wa asg)
                         (ptx-c-int-decode wb asg))))
  :do-not-induct t
  :use ((:instance ptx-c-kind-when-typed (w wa)))
  :enable (ptx-c-leaf-typed ptx-c-leaf-val
           ptx-c-int-equalp-i8 ptx-c-int-equalp-i16 ptx-c-int-equalp-i32
           ptx-c-int-equalp-i64 ptx-c-int-equalp-i128 ptx-c-int-equalp-u8
           ptx-c-int-equalp-u16 ptx-c-int-equalp-u32 ptx-c-int-equalp-u64
           ptx-c-int-equalp-u128))

(defruled ptx-c-int-shape-facts
  (implies (and (not (equal (car w) :boolean))
                (ptx-c-leaf-typed w asg))
           (and (integer-widthp (third (assoc-equal (car w) *ptx-c-ints*)))
                (symbol-listp (cdr w))
                (equal (len (cdr w)) (third (assoc-equal (car w) *ptx-c-ints*)))
                (bit-listp (lookup-equal-list (cdr w) asg))
                (ptx-c-leaf-shapep w)))
  :use ptx-c-kind-when-typed
  :enable (ptx-c-leaf-typed ptx-c-leaf-shapep))

(defruled ptx-c-leaf-eq-sound-int
  (implies (and (equal (car wb) (car wa))
                (not (equal (car wa) :boolean))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-c-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-c-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-c-leaf-val wa asg)
                                                   (ptx-c-leaf-val wb asg)))
                     (values-literal-equalp (ptx-c-leaf-val wa asg)
                                            (ptx-c-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-c-int-shape-facts (w wa))
        (:instance ptx-c-int-shape-facts (w wb))
        ptx-c-int-equalp
        (:instance ptx-c-int-neq-wires
         (xs (cdr wa)) (ys (cdr wb)) (z (car names)) (w (cadr names))
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*))))
        (:instance ptx-c-bval-of-zout (z (car names))))
  :enable (ptx-c-bindsp-of-car-and-cadr values-bool-to-bit)
  :disable (ptx-c-zout ptx-c-leaf-typed ptx-c-leaf-val ptx-c-leaf-shapep))

(defruled ptx-c-leaf-eq-out-when-mismatch
  (implies (not (equal (car wa) (car wb)))
           (equal (ptx-c-leaf-eq-out wa wb neq names) (if neq 1 0))))

(defruled ptx-c-leaf-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg names)
                (equal (lookup-equal 'ptx-one asg) 1)
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg)
                (r1cs::r1cs-constraints-holdp
                 (ptx-c-leaf-eq-gadget wa wb neq names) asg p))
           (equal (ptx-bval (ptx-c-leaf-eq-out wa wb neq names) asg p)
                  (values-bool-to-bit
                   (if neq
                       (not (values-literal-equalp (ptx-c-leaf-val wa asg)
                                                   (ptx-c-leaf-val wb asg)))
                     (values-literal-equalp (ptx-c-leaf-val wa asg)
                                            (ptx-c-leaf-val wb asg))))))
  :do-not-induct t
  :use ((:instance ptx-c-kind-of-leaf-val (w wa))
        (:instance ptx-c-kind-of-leaf-val (w wb))
        (:instance ptx-c-leaf-constraints (w wa))
        (:instance ptx-c-leaf-constraints (w wb))
        (:instance ptx-c-literal-equalp-when-kinds-differ
         (x (ptx-c-leaf-val wa asg)) (y (ptx-c-leaf-val wb asg)))
        ptx-c-leaf-eq-sound-boolean
        ptx-c-leaf-eq-sound-int)
  :enable (values-bool-to-bit ptx-c-leaf-eq-out-when-mismatch)
  :disable (ptx-c-leaf-eq-gadget ptx-c-leaf-eq-out))

(defruled ptx-c-leaf-eq-complete-int
  (implies (and (equal (car wb) (car wa))
                (not (equal (car wa) :boolean))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg)
                (ptx-c-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-c-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance ptx-c-int-shape-facts (w wa))
        (:instance ptx-c-int-shape-facts (w wb))
        (:instance int-is-not-equal-gadget-complete
         (xs (cdr wa)) (ys (cdr wb)) (z (car names)) (w (cadr names))
         (one 'ptx-one)
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*)))
         (x (ptx-c-int-decode wa asg))
         (y (ptx-c-int-decode wb asg)))
        (:instance int-valuep-of-lebits->int
         (bits (lookup-equal-list (cdr wa) asg))
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*))))
        (:instance int-valuep-of-lebits->int
         (bits (lookup-equal-list (cdr wb) asg))
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*))))
        (:instance ptx-c-int->lebits-of-lebits->int
         (bits (lookup-equal-list (cdr wa) asg))
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*))))
        (:instance ptx-c-int->lebits-of-lebits->int
         (bits (lookup-equal-list (cdr wb) asg))
         (n (third (assoc-equal (car wa) *ptx-c-ints*)))
         (signedp (second (assoc-equal (car wa) *ptx-c-ints*)))))
  :enable (ptx-c-binds-allp-when-bit-listp posp-when-integer-widthp)
  :disable (ptx-c-leaf-typed ptx-c-leaf-val ptx-c-leaf-shapep
                             int-is-not-equal-gadget-complete))

(defruled ptx-c-leaf-eq-complete
  (implies (and (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-c-leaf-typed wa asg)
                (ptx-c-leaf-typed wb asg)
                (ptx-c-leaf-eq-witnessp wa wb neq names asg p))
           (r1cs::r1cs-constraints-holdp
            (ptx-c-leaf-eq-gadget wa wb neq names) asg p))
  :do-not-induct t
  :use ((:instance lit-literal-boolean-equal-complete
         (a (cdr wa)) (b (cdr wb)) (out (car names)))
        ptx-c-leaf-eq-complete-int)
  :enable (lit-literal-equal-mismatch-complete ptx-c-leaf-typed
           ptx-c-leaf-shapep ptx-c-bindsp-when-bitp)
  :disable (lit-literal-equal-mismatch-gadget))

(in-theory (disable ptx-c-leaf-eq-gadget ptx-c-leaf-eq-out ptx-c-leaf-eq-nvars
                    ptx-c-leaf-eq-witnessp))

(defrule ptx-c-natp-of-leaf-eq-nvars
  (natp (ptx-c-leaf-eq-nvars wa wb neq))
  :rule-classes :type-prescription
  :enable ptx-c-leaf-eq-nvars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Copies of the ptx-vnew / ptx-vequal functions with the concrete leaf, and
;; the functional instances.

(defconst *ptx-c-vcliques*
  '((ptx-vnew-gadget ptx-vmnew-gadget ptx-vlnew-gadget)
    (ptx-vnew-vars ptx-vmnew-vars ptx-vlnew-vars)
    (ptx-vnew-witnessp ptx-vmnew-witnessp ptx-vlnew-witnessp)
    (ptx-vkind)
    (ptx-veq-count ptx-vmeq-count ptx-vleq-count)
    (ptx-veq ptx-vmeq ptx-vleq)
    (ptx-veq-witnessp ptx-vmeq-witnessp ptx-vleq-witnessp)
    (ptx-ventry-new-gadget)
    (ptx-ventry-new-vars)
    (ptx-ventry-eq)
    (ptx-ventry-eq-witnessp)))

(defconst *ptx-c-vleaves*
  '((ptx-vleaf-new-gadget . ptx-c-leaf-new-gadget)
    (ptx-vleaf-new-vars . ptx-c-leaf-new-vars)
    (ptx-vleaf-new-witnessp . ptx-c-leaf-new-witnessp)
    (ptx-vleaf-eq-gadget . ptx-c-leaf-eq-gadget)
    (ptx-vleaf-eq-out . ptx-c-leaf-eq-out)
    (ptx-vleaf-eq-nvars . ptx-c-leaf-eq-nvars)
    (ptx-vleaf-eq-witnessp . ptx-c-leaf-eq-witnessp)))

(defun ptx-c-valist ()
  (declare (xargs :mode :program))
  (append *ptx-c-vleaves*
          (ptx-c-alist (append *ptx-c-leaves*
                               (ptx-c-flatten *ptx-c-cliques*)
                               (ptx-c-flatten *ptx-c-vcliques*)))))

(make-event
 `(progn ,@(ptx-c-copy-events *ptx-c-vcliques* (ptx-c-valist) (w state))))

(defun ptx-c-vinstance-event (thm wrld)
  (declare (xargs :mode :program))
  (b* ((alist (ptx-c-valist))
       (formula (acl2::sublis-fn-simple alist (acl2::formula thm nil wrld))))
    `(defthm ,(ptx-c-name thm)
       ,formula
       :hints (("Goal"
                :do-not-induct t
                :use ((:functional-instance ,thm ,@(ptx-c-fi-pairs alist)))
                :in-theory (enable ptx-c-leaf-constraints
                                   ptx-c-leaf-bits-sound
                                   ptx-c-leaf-bits-complete
                                   ptx-c-leaf-bits-gadget
                                   ptx-c-leaf-bits-witnessp
                                   lit-literal-write-bits-empty-gadget
                                   ptx-c-leaf-new-sound
                                   ptx-c-leaf-new-complete
                                   ptx-c-leaf-new-error
                                   ptx-c-leaf-eq-sound
                                   ptx-c-leaf-eq-complete)))
       :rule-classes nil)))

(defmacro ptx-c-vinstance (thm)
  `(make-event (ptx-c-vinstance-event ',thm (w state))))

(ptx-c-vinstance ptx-vnew-sound)
(ptx-c-vinstance ptx-vnew-complete)
(ptx-c-vinstance ptx-ventry-new-sound)
(ptx-c-vinstance ptx-ventry-new-complete)
(ptx-c-vinstance ptx-veq-sound)
(ptx-c-vinstance ptx-veq-complete)
(ptx-c-vinstance ptx-ventry-eq-sound)
(ptx-c-vinstance ptx-ventry-eq-complete)
