; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Future::is_equal / is_not_equal and Argument::is_equal / is_not_equal
; (snarkVM circuit/program/src/data/future/{equal.rs,argument.rs}).
;
; Future: if the argument counts differ the result is the constant false
; (true for is_not_equal).  Otherwise acc starts at the constant true (false)
; and folds acc &= arg_eq (acc |= arg_neq) over the arguments; the result is
; (pid_eq & fname_eq) & acc, where the program ID and function name are
; constants, so the outer AND folds without a constraint.
; Argument: different kinds give a constant; plaintexts use ptx-eq; futures
; recurse; dynamic futures use DynamicFuture::is_equal (11 fresh wires; the
; is_not_equal output is 1 - z).

(in-package "ALEOVM")

(include-book "rec-future")
(include-book "rec-record-eq")

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture leaves: names 0..10 are mn rn mw rw mf rf mc rc z1 z2 z.

(define rec-dfeq-gadget (da db names)
  (dynamic-future-is-equal-gadget
   (nth 0 da) (nth 0 db) (nth 0 names) (nth 1 names)
   (nth 1 da) (nth 1 db) (nth 2 names) (nth 3 names)
   (nth 2 da) (nth 2 db) (nth 4 names) (nth 5 names)
   (nth 3 da) (nth 3 db) (nth 6 names) (nth 7 names)
   (nth 8 names) (nth 9 names) (nth 10 names) (base-prime)))

(define rec-dfeq (da db neq names)
  (cons (rec-dfeq-gadget da db names) (rec-bit-term neq (nth 10 names))))

(define rec-dfnamesp (names asg)
  (and (symbolp (nth 0 names)) (r1cs::valuation-bindsp asg (nth 0 names))
       (symbolp (nth 1 names)) (r1cs::valuation-bindsp asg (nth 1 names))
       (symbolp (nth 2 names)) (r1cs::valuation-bindsp asg (nth 2 names))
       (symbolp (nth 3 names)) (r1cs::valuation-bindsp asg (nth 3 names))
       (symbolp (nth 4 names)) (r1cs::valuation-bindsp asg (nth 4 names))
       (symbolp (nth 5 names)) (r1cs::valuation-bindsp asg (nth 5 names))
       (symbolp (nth 6 names)) (r1cs::valuation-bindsp asg (nth 6 names))
       (symbolp (nth 7 names)) (r1cs::valuation-bindsp asg (nth 7 names))
       (symbolp (nth 8 names)) (r1cs::valuation-bindsp asg (nth 8 names))
       (symbolp (nth 9 names)) (r1cs::valuation-bindsp asg (nth 9 names))
       (symbolp (nth 10 names)) (r1cs::valuation-bindsp asg (nth 10 names))))

(define rec-dfneq-witp (x y m r asg)
  :short "snarkVM's Field::is_not_equal witnesses: the bit and the multiplier."
  (b* ((xv (lookup-equal x asg))
       (yv (lookup-equal y asg)))
    (and (equal (lookup-equal r asg) (field-is-not-equal-funspec xv yv))
         (equal (lookup-equal m asg)
                (if (equal xv yv)
                    1
                  (pfield::inv (pfield::sub xv yv (base-prime)) (base-prime)))))))

(define rec-dfeq-witnessp (da db names asg)
  (b* ((rn (nth 1 names)) (rw (nth 3 names)) (rf (nth 5 names))
       (rc (nth 7 names)) (z1 (nth 8 names)) (z2 (nth 9 names))
       (z (nth 10 names)))
    (and (rec-dfneq-witp (nth 0 da) (nth 0 db) (nth 0 names) rn asg)
         (rec-dfneq-witp (nth 1 da) (nth 1 db) (nth 2 names) rw asg)
         (rec-dfneq-witp (nth 2 da) (nth 2 db) (nth 4 names) rf asg)
         (rec-dfneq-witp (nth 3 da) (nth 3 db) (nth 6 names) rc asg)
         (equal (lookup-equal z1 asg)
                (boolean-and-funspec
                 (boolean-not-funspec (lookup-equal rn asg))
                 (boolean-not-funspec (lookup-equal rw asg))))
         (equal (lookup-equal z2 asg)
                (boolean-and-funspec
                 (lookup-equal z1 asg)
                 (boolean-not-funspec (lookup-equal rf asg))))
         (equal (lookup-equal z asg)
                (boolean-and-funspec
                 (lookup-equal z2 asg)
                 (boolean-not-funspec (lookup-equal rc asg)))))))

(defruled rec-dfw-facts
  (implies (and (rec-dfwp dfw) (rec-dftyped dfw asg))
           (and (symbolp (nth 0 dfw)) (r1cs::valuation-bindsp asg (nth 0 dfw))
                (symbolp (nth 1 dfw)) (r1cs::valuation-bindsp asg (nth 1 dfw))
                (symbolp (nth 2 dfw)) (r1cs::valuation-bindsp asg (nth 2 dfw))
                (symbolp (nth 3 dfw)) (r1cs::valuation-bindsp asg (nth 3 dfw))))
  :enable (rec-dfwp rec-dftyped rec-dfw-xs rec-bits-boundp))

(defruled rec-dfval-fields
  (equal (rec-dfval dfw asg)
         (dynamic-future (lookup-equal (nth 0 dfw) asg)
                         (lookup-equal (nth 1 dfw) asg)
                         (lookup-equal (nth 2 dfw) asg)
                         (lookup-equal (nth 3 dfw) asg)))
  :enable (rec-dfval rec-dynamic-future-of-wires))

(defrule rec-blcp-of-dfeq
  (implies (rec-dfnamesp names asg)
           (ptx-blcp (cdr (rec-dfeq da db neq names))))
  :enable (rec-dfeq rec-dfnamesp))

(defruled rec-dfeq-bits
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (rec-dfwp da) (rec-dfwp db)
                (rec-dftyped da asg) (rec-dftyped db asg)
                (rec-dfnamesp names asg)
                (r1cs::r1cs-constraints-holdp (rec-dfeq-gadget da db names)
                                              asg (base-prime)))
           (and (bitp (lookup-equal (nth 1 names) asg))
                (bitp (lookup-equal (nth 3 names) asg))
                (bitp (lookup-equal (nth 5 names) asg))
                (bitp (lookup-equal (nth 7 names) asg))))
  :use ((:instance rec-dfw-facts (dfw da))
        (:instance rec-dfw-facts (dfw db))
        (:instance rec-neq-gadget-bit (x (nth 0 da)) (y (nth 0 db))
                   (m (nth 0 names)) (r (nth 1 names)))
        (:instance rec-neq-gadget-bit (x (nth 1 da)) (y (nth 1 db))
                   (m (nth 2 names)) (r (nth 3 names)))
        (:instance rec-neq-gadget-bit (x (nth 2 da)) (y (nth 2 db))
                   (m (nth 4 names)) (r (nth 5 names)))
        (:instance rec-neq-gadget-bit (x (nth 3 da)) (y (nth 3 db))
                   (m (nth 6 names)) (r (nth 7 names))))
  :in-theory '(rec-dfeq-gadget rec-dfnamesp dynamic-future-is-equal-gadget
               r1cs::r1cs-constraints-holdp-of-append bitp
               (bitp) (equal) (base-prime)))

(defruled rec-dfeq-z
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (rec-dfwp da) (rec-dfwp db)
                (rec-dftyped da asg) (rec-dftyped db asg)
                (rec-dfnamesp names asg)
                (r1cs::r1cs-constraints-holdp (rec-dfeq-gadget da db names)
                                              asg (base-prime)))
           (equal (lookup-equal (nth 10 names) asg)
                  (dynamic-future-is-equal (rec-dfval da asg)
                                           (rec-dfval db asg))))
  :use (rec-dfeq-bits
        (:instance rec-dfw-facts (dfw da))
        (:instance rec-dfw-facts (dfw db))
        (:instance dynamic-future-is-equal-gadget-sound
                   (xn (nth 0 da)) (yn (nth 0 db))
                   (mn (nth 0 names)) (rn (nth 1 names))
                   (xw (nth 1 da)) (yw (nth 1 db))
                   (mw (nth 2 names)) (rw (nth 3 names))
                   (xf (nth 2 da)) (yf (nth 2 db))
                   (mf (nth 4 names)) (rf (nth 5 names))
                   (xc (nth 3 da)) (yc (nth 3 db))
                   (mc (nth 6 names)) (rc (nth 7 names))
                   (z1 (nth 8 names)) (z2 (nth 9 names)) (z (nth 10 names))
                   (p (base-prime))
                   (a (rec-dfval da asg)) (b (rec-dfval db asg))))
  :in-theory '(rec-dfeq-gadget rec-dfnamesp rec-dfval-fields fieldp
               values-field-fix
               dynamic-future->program-name-of-dynamic-future
               dynamic-future->program-network-of-dynamic-future
               dynamic-future->function-name-of-dynamic-future
               dynamic-future->checksum-of-dynamic-future
               dynamic-futurep-of-dynamic-future
               r1cs::fep-of-lookup-equal primep-of-base-prime))

(defruled rec-dfeq-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-dfwp da) (rec-dfwp db)
                (rec-dftyped da asg) (rec-dftyped db asg)
                (rec-dfnamesp names asg)
                (r1cs::r1cs-constraints-holdp (car (rec-dfeq da db neq names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-dfeq da db neq names)) asg p)
                  (ptx-eq-spec neq (equal (dynamic-future-is-equal
                                           (rec-dfval da asg) (rec-dfval db asg))
                                          1))))
  :use (rec-dfeq-z
        (:instance rec-bit-term-val (negp neq) (z (nth 10 names))))
  :enable (rec-dfeq rec-dfnamesp crypto-bit-not values-bool-to-bit)
  :prep-lemmas
  ((defrule bitp-of-dynamic-future-is-equal-local
     (bitp (dynamic-future-is-equal x y))
     :enable (dynamic-future-is-equal values-bool-to-bit))))

(defruled rec-dfeq-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (rec-dfwp da) (rec-dfwp db)
                (rec-dftyped da asg) (rec-dftyped db asg)
                (rec-dfnamesp names asg)
                (rec-dfeq-witnessp da db names asg))
           (r1cs::r1cs-constraints-holdp (car (rec-dfeq da db neq names))
                                         asg p))
  :use ((:instance rec-dfw-facts (dfw da))
        (:instance rec-dfw-facts (dfw db))
        (:instance dynamic-future-is-equal-gadget-complete
                   (xn (nth 0 da)) (yn (nth 0 db))
                   (mn (nth 0 names)) (rn (nth 1 names))
                   (xw (nth 1 da)) (yw (nth 1 db))
                   (mw (nth 2 names)) (rw (nth 3 names))
                   (xf (nth 2 da)) (yf (nth 2 db))
                   (mf (nth 4 names)) (rf (nth 5 names))
                   (xc (nth 3 da)) (yc (nth 3 db))
                   (mc (nth 6 names)) (rc (nth 7 names))
                   (z1 (nth 8 names)) (z2 (nth 9 names)) (z (nth 10 names))
                   (p (base-prime))
                   (a (rec-dfval da asg)) (b (rec-dfval db asg))))
  :in-theory '(rec-dfeq rec-dfeq-gadget car-cons rec-dfnamesp rec-dfval-fields
               fieldp values-field-fix rec-dfeq-witnessp rec-dfneq-witp
               dynamic-future->program-name-of-dynamic-future
               dynamic-future->program-network-of-dynamic-future
               dynamic-future->function-name-of-dynamic-future
               dynamic-future->checksum-of-dynamic-future
               dynamic-futurep-of-dynamic-future
               r1cs::fep-of-lookup-equal primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Variable counts and the circuit.

(defines rec-feq-count
  (define rec-feq-count (fa fb neq)
    :measure (acl2-count fa)
    (if (or (atom fa) (not (equal (len (cddr fa)) (len (cddr fb)))))
        0
      (rec-aseq-count (cddr fa) (cddr fb) neq)))
  (define rec-aeq-count (aa ab neq)
    :measure (acl2-count aa)
    (cond ((atom aa) 0)
          ((not (equal (car aa) (car ab))) 0)
          ((equal (car aa) :plaintext) (ptx-eq-count (cdr aa) (cdr ab) neq))
          ((equal (car aa) :future) (rec-feq-count (cdr aa) (cdr ab) neq))
          (t 11)))
  (define rec-aseq-count (as bs neq)
    :measure (acl2-count as)
    (if (or (atom as) (atom bs))
        0
      (+ (nfix (rec-aeq-count (car as) (car bs) neq))
         1
         (rec-aseq-count (cdr as) (cdr bs) neq)))))

(defines rec-feq
  :flag-local nil
  (define rec-feq (fa fb neq names)
    :short "(cons constraints output-term)."
    :measure (acl2-count fa)
    (b* (((when (or (atom fa) (not (equal (len (cddr fa)) (len (cddr fb))))))
          (cons nil (if neq 1 0)))
         (r (rec-aseq (cddr fa) (cddr fb) neq (if neq 0 1) names))
         (c (ptx-eq-spec neq (and (equal (program-id-is-equal (car fa) (car fb)) 1)
                                  (equal (identifier-is-equal (cadr fa) (cadr fb))
                                         1))))
         (r2 (ptx-bop neq c (cdr r) nil)))
      (cons (append (car r) (car r2)) (cdr r2))))
  (define rec-aeq (aa ab neq names)
    :measure (acl2-count aa)
    (cond ((or (atom aa) (not (equal (car aa) (car ab))))
           (cons nil (if neq 1 0)))
          ((equal (car aa) :plaintext) (ptx-eq (cdr aa) (cdr ab) neq names))
          ((equal (car aa) :future) (rec-feq (cdr aa) (cdr ab) neq names))
          (t (rec-dfeq (cdr aa) (cdr ab) neq names))))
  (define rec-aseq (as bs neq acc names)
    :measure (acl2-count as)
    (b* (((when (or (atom as) (atom bs))) (cons nil acc))
         (sub (rec-aeq (car as) (car bs) neq names))
         (k (nfix (rec-aeq-count (car as) (car bs) neq)))
         (r (ptx-bop neq acc (cdr sub) (nth k names)))
         (rest (rec-aseq (cdr as) (cdr bs) neq (cdr r)
                         (nthcdr (1+ k) names))))
      (cons (append (car sub) (car r) (car rest)) (cdr rest)))))

(defines rec-feq-namesp
  :short "The DynamicFuture leaves' wires are bound."
  (define rec-feq-namesp (fa fb neq names asg)
    :measure (acl2-count fa)
    (if (or (atom fa) (not (equal (len (cddr fa)) (len (cddr fb)))))
        t
      (rec-aseq-namesp (cddr fa) (cddr fb) neq names asg)))
  (define rec-aeq-namesp (aa ab neq names asg)
    :measure (acl2-count aa)
    (cond ((or (atom aa) (not (equal (car aa) (car ab)))) t)
          ((equal (car aa) :plaintext) t)
          ((equal (car aa) :future) (rec-feq-namesp (cdr aa) (cdr ab) neq names asg))
          (t (rec-dfnamesp names asg))))
  (define rec-aseq-namesp (as bs neq names asg)
    :measure (acl2-count as)
    (if (or (atom as) (atom bs))
        t
      (and (rec-aeq-namesp (car as) (car bs) neq names asg)
           (rec-aseq-namesp (cdr as) (cdr bs) neq
                            (nthcdr (1+ (nfix (rec-aeq-count (car as) (car bs) neq)))
                                    names)
                            asg)))))

(defines rec-feq-witnessp
  :short "snarkVM's witness values for the fresh wires."
  :flag-local nil
  (define rec-feq-witnessp (fa fb neq names asg)
    :measure (acl2-count fa)
    (if (or (atom fa) (not (equal (len (cddr fa)) (len (cddr fb)))))
        t
      (rec-aseq-witnessp (cddr fa) (cddr fb) neq (if neq 0 1) names asg)))
  (define rec-aeq-witnessp (aa ab neq names asg)
    :measure (acl2-count aa)
    (cond ((or (atom aa) (not (equal (car aa) (car ab)))) t)
          ((equal (car aa) :plaintext)
           (and (ptx-eq-witnessp (cdr aa) (cdr ab) neq names asg (base-prime)) t))
          ((equal (car aa) :future)
           (rec-feq-witnessp (cdr aa) (cdr ab) neq names asg))
          (t (rec-dfeq-witnessp (cdr aa) (cdr ab) names asg))))
  (define rec-aseq-witnessp (as bs neq acc names asg)
    :measure (acl2-count as)
    (if (or (atom as) (atom bs))
        t
      (b* ((sub (rec-aeq (car as) (car bs) neq names))
           (k (nfix (rec-aeq-count (car as) (car bs) neq)))
           (r (ptx-bop neq acc (cdr sub) (nth k names))))
        (and (rec-aeq-witnessp (car as) (car bs) neq names asg)
             (ptx-bop-witnessp neq acc (cdr sub) (nth k names) asg (base-prime))
             (rec-aseq-witnessp (cdr as) (cdr bs) neq (cdr r)
                                (nthcdr (1+ k) names) asg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Soundness.

(defrule rec-blcp-of-atom
  (implies (atom x) (ptx-blcp x))
  :enable ptx-blcp)

(defrule rec-aseq-fns-of-atom
  (implies (or (atom as) (atom bs))
           (and (equal (rec-aseq as bs neq acc names) (cons nil acc))
                (equal (rec-aseq-namesp as bs neq names asg) t)
                (equal (rec-aseq-witnessp as bs neq acc names asg) t)))
  :enable (rec-aseq rec-aseq-namesp rec-aseq-witnessp))

(defthm-rec-feq-flag
  (defthm rec-blcp-of-feq
    (implies (and (symbol-listp names) (rec-feq-namesp fa fb neq names asg))
             (ptx-blcp (cdr (rec-feq fa fb neq names))))
    :flag rec-feq)
  (defthm rec-blcp-of-aeq
    (implies (and (symbol-listp names) (rec-aeq-namesp aa ab neq names asg))
             (ptx-blcp (cdr (rec-aeq aa ab neq names))))
    :flag rec-aeq)
  (defthm rec-blcp-of-aseq
    (implies (and (symbol-listp names) (ptx-blcp acc)
                  (rec-aseq-namesp as bs neq names asg))
             (ptx-blcp (cdr (rec-aseq as bs neq acc names))))
    :flag rec-aseq)
  :hints (("Goal"
           :in-theory (disable ptx-bop rec-dfeq)
           :expand ((:free (neq) (rec-feq fa fb neq names))
                    (:free (neq) (rec-aeq aa ab neq names))
                    (:free (neq acc) (rec-aseq as bs neq acc names))
                    (:free (neq) (rec-feq-namesp fa fb neq names asg))
                    (:free (neq) (rec-aeq-namesp aa ab neq names asg))
                    (:free (neq) (rec-aseq-namesp as bs neq names asg))))))

(defrule rec-fval-parts
  (implies (rec-fwp fw)
           (and (equal (future->program-id (rec-fval fw asg)) (car fw))
                (equal (future->function-name (rec-fval fw asg)) (cadr fw))
                (equal (future->arguments (rec-fval fw asg))
                       (rec-avals (cddr fw) asg))))
  :expand ((rec-fval fw asg) (rec-fwp fw)))

(defrule rec-aval-parts
  (and (equal (argument-kind (rec-aval aw asg))
              (case (car aw)
                (:plaintext :plaintext)
                (:future :future)
                (otherwise :dynamic-future)))
       (implies (equal (car aw) :plaintext)
                (equal (argument-plaintext->get (rec-aval aw asg))
                       (ptx-val (cdr aw) asg)))
       (implies (equal (car aw) :future)
                (equal (argument-future->get (rec-aval aw asg))
                       (rec-fval (cdr aw) asg)))
       (implies (and (not (equal (car aw) :plaintext))
                     (not (equal (car aw) :future)))
                (equal (argument-dynamic-future->get (rec-aval aw asg))
                       (rec-dfval (cdr aw) asg))))
  :expand ((rec-aval aw asg)))

(defrule rec-avals-of-cons
  (equal (rec-avals (cons a b) asg)
         (cons (rec-aval a asg) (rec-avals b asg)))
  :expand ((rec-avals (cons a b) asg)))

(defrule rec-future-equalp-of-fval
  (implies (and (rec-fwp fa) (rec-fwp fb))
           (equal (values-future-equalp (rec-fval fa asg) (rec-fval fb asg))
                  (and (equal (len (cddr fa)) (len (cddr fb)))
                       (equal (program-id-is-equal (car fa) (car fb)) 1)
                       (equal (identifier-is-equal (cadr fa) (cadr fb)) 1)
                       (values-arguments-equalp (rec-avals (cddr fa) asg)
                                                (rec-avals (cddr fb) asg)))))
  :expand ((values-future-equalp (rec-fval fa asg) (rec-fval fb asg))))

(defrule rec-argument-equalp-of-aval
  (implies (and (rec-awp aa) (rec-awp ab))
           (equal (values-argument-equalp (rec-aval aa asg) (rec-aval ab asg))
                  (cond ((not (equal (car aa) (car ab))) nil)
                        ((equal (car aa) :plaintext)
                         (values-plaintext-equalp (ptx-val (cdr aa) asg)
                                                  (ptx-val (cdr ab) asg)))
                        ((equal (car aa) :future)
                         (values-future-equalp (rec-fval (cdr aa) asg)
                                               (rec-fval (cdr ab) asg)))
                        (t (equal (dynamic-future-is-equal
                                   (rec-dfval (cdr aa) asg)
                                   (rec-dfval (cdr ab) asg))
                                  1)))))
  :expand ((values-argument-equalp (rec-aval aa asg) (rec-aval ab asg))
           (rec-awp aa) (rec-awp ab)))

(defrule rec-arguments-equalp-of-avals
  (and (implies (or (atom as) (atom bs))
                (equal (values-arguments-equalp (rec-avals as asg)
                                                (rec-avals bs asg))
                       t))
       (implies (and (consp as) (consp bs))
                (equal (values-arguments-equalp (rec-avals as asg)
                                                (rec-avals bs asg))
                       (and (values-argument-equalp (rec-aval (car as) asg)
                                                    (rec-aval (car bs) asg))
                            (values-arguments-equalp (rec-avals (cdr as) asg)
                                                     (rec-avals (cdr bs) asg))))))
  :expand ((rec-avals as asg) (rec-avals bs asg))
  :enable values-arguments-equalp)

(defrule rec-arguments-equalp-when-atom
  (implies (or (atom xs) (atom ys))
           (equal (values-arguments-equalp xs ys) t))
  :enable values-arguments-equalp)

(defmacro rec-feq-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (symbol-listp names)))

(defthm-rec-feq-flag
  (defthm rec-feq-sound
    (implies (and (rec-feq-hyps)
                  (rec-fwp fa) (rec-fwp fb)
                  (rec-ftyped fa asg) (rec-ftyped fb asg)
                  (rec-feq-namesp fa fb neq names asg)
                  (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                                asg p))
             (equal (ptx-bval (cdr (rec-feq fa fb neq names)) asg p)
                    (ptx-eq-spec neq (values-future-equalp (rec-fval fa asg)
                                                           (rec-fval fb asg)))))
    :flag rec-feq)
  (defthm rec-aeq-sound
    (implies (and (rec-feq-hyps)
                  (rec-awp aa) (rec-awp ab)
                  (rec-atyped aa asg) (rec-atyped ab asg)
                  (rec-aeq-namesp aa ab neq names asg)
                  (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                                asg p))
             (equal (ptx-bval (cdr (rec-aeq aa ab neq names)) asg p)
                    (ptx-eq-spec neq (values-argument-equalp (rec-aval aa asg)
                                                             (rec-aval ab asg)))))
    :flag rec-aeq)
  (defthm rec-aseq-sound
    (implies (and (rec-feq-hyps)
                  (rec-awsp as) (rec-awsp bs)
                  (rec-atyped-list as asg) (rec-atyped-list bs asg)
                  (rec-aseq-namesp as bs neq names asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car (rec-aseq as bs neq acc names))
                                                asg p))
             (equal (ptx-bval (cdr (rec-aseq as bs neq acc names)) asg p)
                    (ptx-bop-spec neq (ptx-bval acc asg p)
                                  (ptx-eq-spec neq (values-arguments-equalp
                                                    (rec-avals as asg)
                                                    (rec-avals bs asg))))))
    :flag rec-aseq)
  :hints (("Goal"
           :in-theory (e/d (rec-dfeq-sound ptx-bop-spec bitand bitor
                            primep-of-base-prime
                            r1cs::r1cs-constraints-holdp-of-append)
                           (ptx-bop rec-dfeq))
           :expand ((:free (neq) (rec-feq fa fb neq names))
                    (:free (neq) (rec-aeq aa ab neq names))
                    (:free (neq acc) (rec-aseq as bs neq acc names))
                    (:free (neq) (rec-feq-namesp fa fb neq names asg))
                    (:free (neq) (rec-aeq-namesp aa ab neq names asg))
                    (:free (neq) (rec-aseq-namesp as bs neq names asg))
                    (rec-fwp fa) (rec-fwp fb)
                    (rec-awp aa) (rec-awp ab)
                    (rec-awsp as) (rec-awsp bs)
                    (rec-ftyped fa asg) (rec-ftyped fb asg)
                    (rec-atyped aa asg) (rec-atyped ab asg)
                    (rec-atyped-list as asg) (rec-atyped-list bs asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Completeness.

(defrule rec-car-of-bop-when-const
  (implies (atom x) (equal (car (ptx-bop neq x y z)) nil))
  :enable (ptx-bop ptx-and ptx-or))

(defrule rec-constraints-holdp-of-true-list-fix
  (equal (r1cs::r1cs-constraints-holdp (true-list-fix x) asg p)
         (r1cs::r1cs-constraints-holdp x asg p))
  :induct (len x)
  :enable (r1cs::r1cs-constraints-holdp true-list-fix))

(defthm-rec-feq-flag
  (defthm rec-feq-complete
    (implies (and (rec-feq-hyps)
                  (rec-fwp fa) (rec-fwp fb)
                  (rec-ftyped fa asg) (rec-ftyped fb asg)
                  (rec-feq-namesp fa fb neq names asg)
                  (rec-feq-witnessp fa fb neq names asg))
             (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                           asg p))
    :flag rec-feq)
  (defthm rec-aeq-complete
    (implies (and (rec-feq-hyps)
                  (rec-awp aa) (rec-awp ab)
                  (rec-atyped aa asg) (rec-atyped ab asg)
                  (rec-aeq-namesp aa ab neq names asg)
                  (rec-aeq-witnessp aa ab neq names asg))
             (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                           asg p))
    :flag rec-aeq)
  (defthm rec-aseq-complete
    (implies (and (rec-feq-hyps)
                  (rec-awsp as) (rec-awsp bs)
                  (rec-atyped-list as asg) (rec-atyped-list bs asg)
                  (rec-aseq-namesp as bs neq names asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (rec-aseq-witnessp as bs neq acc names asg))
             (r1cs::r1cs-constraints-holdp (car (rec-aseq as bs neq acc names))
                                           asg p))
    :flag rec-aseq)
  :hints (("Goal"
           :in-theory (e/d (rec-dfeq-sound rec-dfeq-complete
                            primep-of-base-prime
                            r1cs::r1cs-constraints-holdp-of-append)
                           (ptx-bop ptx-bop-witnessp rec-dfeq))
           :expand ((:free (neq) (rec-feq fa fb neq names))
                    (:free (neq) (rec-aeq aa ab neq names))
                    (:free (neq acc) (rec-aseq as bs neq acc names))
                    (:free (neq) (rec-feq-namesp fa fb neq names asg))
                    (:free (neq) (rec-aeq-namesp aa ab neq names asg))
                    (:free (neq) (rec-aseq-namesp as bs neq names asg))
                    (:free (neq) (rec-feq-witnessp fa fb neq names asg))
                    (:free (neq) (rec-aeq-witnessp aa ab neq names asg))
                    (:free (neq acc) (rec-aseq-witnessp as bs neq acc names asg))
                    (rec-fwp fa) (rec-fwp fb)
                    (rec-awp aa) (rec-awp ab)
                    (rec-awsp as) (rec-awsp bs)
                    (rec-ftyped fa asg) (rec-ftyped fb asg)
                    (rec-atyped aa asg) (rec-atyped ab asg)
                    (rec-atyped-list as asg) (rec-atyped-list bs asg)))))

(in-theory (disable rec-feq-sound rec-aeq-sound rec-aseq-sound
                    rec-feq-complete rec-aeq-complete rec-aseq-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Rows.

(defmacro rec-future-eq-hyps ()
  '(and (rec-feq-hyps)
        (rec-fwp fa) (rec-fwp fb)
        (rec-ftyped fa asg) (rec-ftyped fb asg)
        (rec-feq-namesp fa fb neq names asg)))

(defmacro rec-argument-eq-hyps ()
  '(and (rec-feq-hyps)
        (rec-awp aa) (rec-awp ab)
        (rec-atyped aa asg) (rec-atyped ab asg)
        (rec-aeq-namesp aa ab neq names asg)))

(defruled rec-future-is-equal-sound
  (implies (and (not neq)
                (rec-future-eq-hyps)
                (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-feq fa fb neq names)) asg p)
                  (future-is-equal (rec-fval fa asg) (rec-fval fb asg))))
  :use rec-feq-sound
  :enable future-is-equal)

(defruled rec-future-is-not-equal-sound
  (implies (and neq
                (rec-future-eq-hyps)
                (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-feq fa fb neq names)) asg p)
                  (future-is-not-equal (rec-fval fa asg) (rec-fval fb asg))))
  :use rec-feq-sound
  :enable future-is-not-equal)

(defruled rec-future-is-equal-complete
  (implies (and (not neq)
                (rec-future-eq-hyps)
                (rec-feq-witnessp fa fb neq names asg))
           (and (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                              asg p)
                (equal (ptx-bval (cdr (rec-feq fa fb neq names)) asg p)
                       (future-is-equal (rec-fval fa asg) (rec-fval fb asg)))))
  :use (rec-feq-complete rec-future-is-equal-sound))

(defruled rec-future-is-not-equal-complete
  (implies (and neq
                (rec-future-eq-hyps)
                (rec-feq-witnessp fa fb neq names asg))
           (and (r1cs::r1cs-constraints-holdp (car (rec-feq fa fb neq names))
                                              asg p)
                (equal (ptx-bval (cdr (rec-feq fa fb neq names)) asg p)
                       (future-is-not-equal (rec-fval fa asg) (rec-fval fb asg)))))
  :use (rec-feq-complete rec-future-is-not-equal-sound))

(defruled rec-argument-is-equal-sound
  (implies (and (not neq)
                (rec-argument-eq-hyps)
                (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-aeq aa ab neq names)) asg p)
                  (argument-is-equal (rec-aval aa asg) (rec-aval ab asg))))
  :use rec-aeq-sound
  :enable argument-is-equal)

(defruled rec-argument-is-not-equal-sound
  (implies (and neq
                (rec-argument-eq-hyps)
                (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-aeq aa ab neq names)) asg p)
                  (argument-is-not-equal (rec-aval aa asg) (rec-aval ab asg))))
  :use rec-aeq-sound
  :enable argument-is-not-equal)

(defruled rec-argument-is-equal-complete
  (implies (and (not neq)
                (rec-argument-eq-hyps)
                (rec-aeq-witnessp aa ab neq names asg))
           (and (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                              asg p)
                (equal (ptx-bval (cdr (rec-aeq aa ab neq names)) asg p)
                       (argument-is-equal (rec-aval aa asg) (rec-aval ab asg)))))
  :use (rec-aeq-complete rec-argument-is-equal-sound))

(defruled rec-argument-is-not-equal-complete
  (implies (and neq
                (rec-argument-eq-hyps)
                (rec-aeq-witnessp aa ab neq names asg))
           (and (r1cs::r1cs-constraints-holdp (car (rec-aeq aa ab neq names))
                                              asg p)
                (equal (ptx-bval (cdr (rec-aeq aa ab neq names)) asg p)
                       (argument-is-not-equal (rec-aval aa asg) (rec-aval ab asg)))))
  :use (rec-aeq-complete rec-argument-is-not-equal-sound))
