; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record<Plaintext>::is_equal (neq nil) / is_not_equal (neq t)
; (snarkVM circuit/program/src/data/record/equal.rs), over the record wires
; of rec-record.lisp.
;
; Different data lengths give the constant false (true).  Otherwise, with
; & (|) for is_equal (is_not_equal), starting from the constant true (false):
;   acc = acc & name_a.is_equal(name_b) & entry_a.is_equal(entry_b)
; for each entry pair (names are constants), then
;   owner.is_equal(..) & acc & nonce.is_equal(..) & version.is_equal(..).
; Owner::is_equal is Address::is_equal when the variants agree (a private
; owner is an address literal) and the constant false otherwise;
; Group/Address::is_not_equal is 1 - is_equal; U8::is_equal is
; Field::is_equal of the bit sums, i.e. 1 - r of rec-lc-neq-gadget.
; The Boolean folds are ptx-bop (constants fold, two variables allocate one
; AND / OR constraint).

(in-package "ALEOVM")

(include-book "rec-record-bits")
(include-book "rec-dynamic-record-eq")

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Bit facts.

(define rec-nspec (neq b)
  :short "The is_equal bit b as seen by is_equal (b) or is_not_equal (!b)."
  (if neq (crypto-bit-not b) b))

(defrule rec-bitp-of-nspec
  (implies (bitp b) (bitp (rec-nspec neq b)))
  :enable (rec-nspec crypto-bit-not))

(defruled rec-bop-fold
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (ptx-bop-spec neq (ptx-bop-spec neq a (rec-nspec neq b))
                                (rec-nspec neq c))
                  (ptx-bop-spec neq a (rec-nspec neq (crypto-bit-and b c)))))
  :enable (ptx-bop-spec rec-nspec crypto-bit-and crypto-bit-not bitp))

(defruled rec-bop-unit
  (implies (bitp a)
           (equal (ptx-bop-spec neq (if neq 0 1) a) a))
  :enable (ptx-bop-spec bitp))

(defruled rec-bop-first
  (implies (and (bitp a) (bitp b))
           (equal (ptx-bop-spec neq (rec-nspec neq a) (rec-nspec neq b))
                  (rec-nspec neq (crypto-bit-and a b))))
  :enable (ptx-bop-spec rec-nspec crypto-bit-and crypto-bit-not bitp))

(defruled rec-crypto-entry-is-equal
  (implies (and (entryp a) (entryp b))
           (and (equal (crypto-entry-is-equal a b) (entry-is-equal a b))
                (equal (entry-is-not-equal a b)
                       (crypto-bit-not (entry-is-equal a b)))))
  :enable (crypto-entry-is-equal entry-is-equal entry-is-not-equal
           values-entry-equalp values-entry-plaintext values-bool-to-bit
           crypto-bit-not entry-kind))

(defruled rec-name-bit
  (implies (and (identifierp a) (identifierp b))
           (equal (ptx-name-bit a b neq)
                  (rec-nspec neq (crypto-bit-eq (identifier->field a)
                                                (identifier->field b)))))
  :enable (ptx-name-bit rec-nspec crypto-bit-eq crypto-bit-not))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The data fold.

(define rec-entry-eq-count (ea eb neq)
  (if (equal (car ea) (car eb)) (ptx-eq-count (cdr ea) (cdr eb) neq) 0))

(define rec-deq (das dbs neq acc names)
  (b* (((when (or (atom das) (atom dbs))) (cons nil acc))
       (r1 (ptx-bop neq acc (ptx-name-bit (caar das) (caar dbs) neq) nil))
       (sub (ptx-entry-eq (cdar das) (cdar dbs) neq names))
       (k (rec-entry-eq-count (cdar das) (cdar dbs) neq))
       (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names)))
       (rest (rec-deq (cdr das) (cdr dbs) neq (cdr r2) (nthcdr (1+ k) names))))
    (cons (append (car r1) (car sub) (car r2) (car rest))
          (cdr rest))))

(define rec-deq-witnessp (das dbs neq acc names asg p)
  (b* (((when (or (atom das) (atom dbs))) t)
       (r1 (ptx-bop neq acc (ptx-name-bit (caar das) (caar dbs) neq) nil))
       (sub (ptx-entry-eq (cdar das) (cdar dbs) neq names))
       (k (rec-entry-eq-count (cdar das) (cdar dbs) neq))
       (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names))))
    (and (ptx-entry-eq-witnessp (cdar das) (cdar dbs) neq names asg p)
         (ptx-bop-witnessp neq (cdr r1) (cdr sub) (nth k names) asg p)
         (rec-deq-witnessp (cdr das) (cdr dbs) neq (cdr r2)
                           (nthcdr (1+ k) names) asg p))))

(defrule rec-blcp-of-entry-eq
  (implies (symbol-listp names)
           (ptx-blcp (cdr (ptx-entry-eq ea eb neq names))))
  :enable ptx-entry-eq)

(defrule rec-blcp-of-deq
  (implies (and (symbol-listp names) (ptx-blcp acc))
           (ptx-blcp (cdr (rec-deq das dbs neq acc names))))
  :induct (rec-deq das dbs neq acc names)
  :enable rec-deq
  :disable (ptx-name-bit ptx-bop))

(defruled rec-entry-eq-bit
  (implies (and (primep p)
                (symbol-listp names)
                (ptx-ewtp ea) (ptx-ewtp eb)
                (ptx-typed (cdr ea) asg)
                (ptx-typed (cdr eb) asg)
                (r1cs::r1cs-constraints-holdp (car (ptx-entry-eq ea eb neq names))
                                              asg p))
           (equal (ptx-bval (cdr (ptx-entry-eq ea eb neq names)) asg p)
                  (rec-nspec neq (crypto-entry-is-equal (ptx-eval ea asg)
                                                        (ptx-eval eb asg)))))
  :use ptx-entry-eq-sound
  :enable (rec-crypto-entry-is-equal rec-nspec))

(defruled rec-bval-of-name-bit
  (and (equal (ptx-bval (ptx-name-bit ida idb neq) asg p)
              (ptx-name-bit ida idb neq))
       (bitp (ptx-name-bit ida idb neq)))
  :enable (ptx-bval ptx-name-bit))

(defruled rec-deq-step
  (b* ((r1 (ptx-bop neq acc (ptx-name-bit ida idb neq) nil))
       (sub (ptx-entry-eq ea eb neq names))
       (k (rec-entry-eq-count ea eb neq))
       (r2 (ptx-bop neq (cdr r1) (cdr sub) (nth k names))))
    (implies (and (primep p)
                  (symbol-listp names)
                  (identifierp ida) (identifierp idb)
                  (ptx-ewtp ea) (ptx-ewtp eb)
                  (ptx-typed (cdr ea) asg)
                  (ptx-typed (cdr eb) asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (r1cs::r1cs-constraints-holdp (car r1) asg p)
                  (r1cs::r1cs-constraints-holdp (car sub) asg p)
                  (r1cs::r1cs-constraints-holdp (car r2) asg p))
             (and (ptx-blcp (cdr r2))
                  (equal (ptx-bval (cdr r2) asg p)
                         (ptx-bop-spec
                          neq (ptx-bval acc asg p)
                          (rec-nspec neq
                                     (crypto-bit-and
                                      (crypto-bit-eq (identifier->field ida)
                                                     (identifier->field idb))
                                      (crypto-entry-is-equal
                                       (ptx-eval ea asg) (ptx-eval eb asg)))))))))
  :do-not-induct t
  :use ((:instance rec-entry-eq-bit)
        (:instance ptx-bop-sound-rw
                   (x acc) (y (ptx-name-bit ida idb neq)) (z nil))
        (:instance ptx-bop-sound-rw
                   (x (cdr (ptx-bop neq acc (ptx-name-bit ida idb neq) nil)))
                   (y (cdr (ptx-entry-eq ea eb neq names)))
                   (z (nth (rec-entry-eq-count ea eb neq) names)))
        (:instance rec-name-bit (a ida) (b idb))
        (:instance rec-bop-fold
                   (a (ptx-bval acc asg p))
                   (b (crypto-bit-eq (identifier->field ida)
                                     (identifier->field idb)))
                   (c (crypto-entry-is-equal (ptx-eval ea asg)
                                             (ptx-eval eb asg)))))
  :in-theory (e/d (rec-bval-of-name-bit)
                  (ptx-bop ptx-name-bit ptx-entry-eq ptx-bop-sound-rw
                   rec-bop-fold rec-nspec ptx-bop-spec)))

(defruled rec-deq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (rec-record-datawp das) (rec-record-datawp dbs)
                (rec-record-data-typed das asg)
                (rec-record-data-typed dbs asg)
                (equal (len das) (len dbs))
                (ptx-blcp acc)
                (bitp (ptx-bval acc asg p))
                (r1cs::r1cs-constraints-holdp (car (rec-deq das dbs neq acc names))
                                              asg p))
           (equal (ptx-bval (cdr (rec-deq das dbs neq acc names)) asg p)
                  (ptx-bop-spec neq (ptx-bval acc asg p)
                                (rec-nspec neq
                                           (crypto-record-data-is-equal
                                            (rec-record-data-eval das asg)
                                            (rec-record-data-eval dbs asg))))))
  :induct (rec-deq das dbs neq acc names)
  :in-theory (e/d (rec-deq rec-record-datawp rec-record-data-typed
                   rec-record-data-eval crypto-record-data-is-equal
                   r1cs::r1cs-constraints-holdp-of-append)
                  (ptx-name-bit ptx-bop ptx-entry-eq rec-nspec ptx-bop-spec))
  :hints (("Subgoal *1/2"
           :use ((:instance rec-deq-step (ida (caar das)) (idb (caar dbs))
                            (ea (cdar das)) (eb (cdar dbs)))
                 (:instance rec-bop-fold
                            (a (ptx-bval acc asg p))
                            (b (crypto-bit-and
                                (crypto-bit-eq (identifier->field (caar das))
                                               (identifier->field (caar dbs)))
                                (crypto-entry-is-equal
                                 (ptx-eval (cdar das) asg)
                                 (ptx-eval (cdar dbs) asg))))
                            (c (crypto-record-data-is-equal
                                (rec-record-data-eval (cdr das) asg)
                                (rec-record-data-eval (cdr dbs) asg))))))
          ("Subgoal *1/1" :use (:instance rec-bop-unit (a (ptx-bval acc asg p)))
           :in-theory (enable rec-deq rec-record-data-eval
                              crypto-record-data-is-equal
                              ptx-bop-spec rec-nspec crypto-bit-not
                              bitand bitor))))

(defruled rec-bop-witnessp-of-name-bit
  (ptx-bop-witnessp neq x (ptx-name-bit ida idb neq2) z asg p)
  :enable ptx-name-bit)

(defruled rec-deq-step-complete
  (b* ((r1 (ptx-bop neq acc (ptx-name-bit ida idb neq) nil))
       (sub (ptx-entry-eq ea eb neq names))
       (k (rec-entry-eq-count ea eb neq)))
    (implies (and (primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (symbol-listp names)
                  (ptx-ewtp ea) (ptx-ewtp eb)
                  (ptx-typed (cdr ea) asg)
                  (ptx-typed (cdr eb) asg)
                  (ptx-blcp acc)
                  (bitp (ptx-bval acc asg p))
                  (ptx-entry-eq-witnessp ea eb neq names asg p)
                  (ptx-bop-witnessp neq (cdr r1) (cdr sub) (nth k names) asg p))
             (and (r1cs::r1cs-constraints-holdp (car r1) asg p)
                  (r1cs::r1cs-constraints-holdp (car sub) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (car (ptx-bop neq (cdr r1) (cdr sub) (nth k names))) asg p))))
  :do-not-induct t
  :use ((:instance ptx-entry-eq-complete)
        (:instance ptx-entry-eq-sound)
        (:instance rec-entry-eq-bit)
        (:instance ptx-bop-complete-rw
                   (x acc) (y (ptx-name-bit ida idb neq)) (z nil))
        (:instance ptx-bop-sound-rw
                   (x acc) (y (ptx-name-bit ida idb neq)) (z nil))
        (:instance ptx-bop-complete-rw
                   (x (cdr (ptx-bop neq acc (ptx-name-bit ida idb neq) nil)))
                   (y (cdr (ptx-entry-eq ea eb neq names)))
                   (z (nth (rec-entry-eq-count ea eb neq) names)))
        (:instance rec-bop-witnessp-of-name-bit (x acc) (z nil) (neq2 neq)))
  :in-theory (e/d (rec-bval-of-name-bit)
                  (ptx-bop ptx-name-bit ptx-entry-eq ptx-bop-sound-rw
                   ptx-bop-complete-rw ptx-bop-witnessp rec-nspec ptx-bop-spec)))

(defruled rec-deq-complete
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (rec-record-datawp das) (rec-record-datawp dbs)
                (rec-record-data-typed das asg)
                (rec-record-data-typed dbs asg)
                (ptx-blcp acc)
                (bitp (ptx-bval acc asg p))
                (rec-deq-witnessp das dbs neq acc names asg p))
           (r1cs::r1cs-constraints-holdp (car (rec-deq das dbs neq acc names))
                                         asg p))
  :induct (rec-deq das dbs neq acc names)
  :in-theory (e/d (rec-deq rec-deq-witnessp rec-record-datawp
                   rec-record-data-typed r1cs::r1cs-constraints-holdp-of-append)
                  (ptx-name-bit ptx-bop ptx-bop-witnessp ptx-entry-eq
                   ptx-entry-eq-witnessp))
  :hints (("Subgoal *1/2"
           :use ((:instance rec-deq-step-complete
                            (ida (caar das)) (idb (caar dbs))
                            (ea (cdar das)) (eb (cdar dbs)))
                 (:instance rec-deq-step
                            (ida (caar das)) (idb (caar dbs))
                            (ea (cdar das)) (eb (cdar dbs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Single-wire Boolean terms.

(define rec-bit-term (negp z)
  :short "The term of a Boolean wire z (negp nil) or of !z = 1 - z (negp t)."
  (if negp (ptx-one-minus (list (list 1 z))) (list (list 1 z))))

(defrule rec-blcp-of-bit-term
  (implies (symbolp z) (ptx-blcp (rec-bit-term negp z)))
  :enable (rec-bit-term ptx-blcp ptx-one-minus ptx-neg
           r1cs::sparse-vectorp r1cs::sparse-vector-elementp))

(defruled rec-bit-term-val
  (implies (and (symbolp z)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal z asg)))
           (equal (ptx-bval (rec-bit-term negp z) asg (base-prime))
                  (if negp
                      (crypto-bit-not (lookup-equal z asg))
                    (lookup-equal z asg))))
  :enable (rec-bit-term ptx-bval ptx-one-minus ptx-neg crypto-bit-not bitp
           r1cs::dot-product primep-of-base-prime
           r1cs::fep-of-lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The circuit.

(define rec-grp-gadget (ga gb e)
  :short "Group::is_equal of two points injected with 14-wire Group::new
          lists ga, gb; e = (mx rx my ry out)."
  (crv-group-is-equal-gadget (nth 0 ga) (nth 1 ga) (nth 0 gb) (nth 1 gb)
                             (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e)
                             (base-prime)))

(define rec-record-eq (pa oga da nga va pb ogb db ngb vb oe ne vm vr
                          za zb zc names neq)
  :short "(cons constraints output-term)."
  (b* (((unless (equal (len da) (len db))) (cons nil (if neq 1 0)))
       (d (rec-deq da db neq (if neq 0 1) names))
       ((mv ogad oterm) (if (equal (and pa t) (and pb t))
                            (mv (rec-grp-gadget oga ogb oe)
                                (rec-bit-term neq (nth 4 oe)))
                          (mv nil (if neq 1 0))))
       (r1 (ptx-bop neq oterm (cdr d) za))
       (ngad (rec-grp-gadget nga ngb ne))
       (r2 (ptx-bop neq (cdr r1) (rec-bit-term neq (nth 4 ne)) zb))
       (vgad (rec-lc-neq-gadget (pow2sum-vector va 0) (pow2sum-vector vb 0)
                                vm vr (base-prime)))
       (r3 (ptx-bop neq (cdr r2) (rec-bit-term (not neq) vr) zc)))
    (cons (append (car d) ogad (car r1) ngad (car r2) vgad (car r3))
          (cdr r3))))

(defmacro rec-record-eq-hyps (&rest more)
  `(and (booleanp pa) (booleanp pb) (booleanp neq)
        (symbol-listp oga) (equal (len oga) 14)
        (symbol-listp ogb) (equal (len ogb) 14)
        (symbol-listp nga) (equal (len nga) 14)
        (symbol-listp ngb) (equal (len ngb) 14)
        (symbol-listp va) (equal (len va) 8)
        (symbol-listp vb) (equal (len vb) 8)
        (symbol-listp oe) (equal (len oe) 5)
        (symbol-listp ne) (equal (len ne) 5)
        (symbolp vm) (symbolp vr) (symbolp za) (symbolp zb) (symbolp zc)
        (symbol-listp names)
        (rec-record-datawp da) (rec-record-datawp db)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-binds-allp asg oga)
        (r1cs::valuation-binds-allp asg ogb)
        (r1cs::valuation-binds-allp asg nga)
        (r1cs::valuation-binds-allp asg ngb)
        (r1cs::valuation-binds-allp asg va)
        (r1cs::valuation-binds-allp asg vb)
        (r1cs::valuation-binds-allp asg oe)
        (r1cs::valuation-binds-allp asg ne)
        (r1cs::valuation-binds-allp asg (list vm vr za zb zc))
        (groupp (rec-point-of oga asg)) (groupp (rec-point-of ogb asg))
        (groupp (rec-point-of nga asg)) (groupp (rec-point-of ngb asg))
        (bit-listp (lookup-equal-list va asg))
        (bit-listp (lookup-equal-list vb asg))
        (rec-record-data-typed da asg)
        (rec-record-data-typed db asg)
        ,@more))

(defruled rec-natp-of-lookup-nth
  (implies (and (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg g)
                (< (nfix i) (len g)))
           (natp (lookup-equal (nth i g) asg)))
  :use rec-valuation-bindsp-of-nth)

(defruled rec-grp-gadget-bit
  (implies (and (symbol-listp ga) (equal (len ga) 14)
                (symbol-listp gb) (equal (len gb) 14)
                (symbol-listp e) (equal (len e) 5)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg ga)
                (r1cs::valuation-binds-allp asg gb)
                (r1cs::valuation-binds-allp asg e)
                (groupp (rec-point-of ga asg)) (groupp (rec-point-of gb asg))
                (r1cs::r1cs-constraints-holdp (rec-grp-gadget ga gb e)
                                              asg (base-prime)))
           (equal (lookup-equal (nth 4 e) asg)
                  (crypto-bit-eq (rec-point-of ga asg) (rec-point-of gb asg))))
  :do-not-induct t
  :use ((:instance crv-group-is-equal-wire-sound
                   (x1 (nth 0 ga)) (y1 (nth 1 ga)) (x2 (nth 0 gb)) (y2 (nth 1 gb))
                   (mx (nth 0 e)) (rx (nth 1 e)) (my (nth 2 e)) (ry (nth 3 e))
                   (out (nth 4 e)) (p (base-prime))
                   (p1 (rec-point-of ga asg)) (p2 (rec-point-of gb asg)))
        (:instance rec-natp-of-lookup-nth (g ga) (i 0) (p (base-prime)))
        (:instance rec-natp-of-lookup-nth (g ga) (i 1) (p (base-prime)))
        (:instance rec-natp-of-lookup-nth (g gb) (i 0) (p (base-prime)))
        (:instance rec-natp-of-lookup-nth (g gb) (i 1) (p (base-prime)))
        (:instance rec-valuation-bindsp-of-nth (g ga) (i 0))
        (:instance rec-valuation-bindsp-of-nth (g ga) (i 1))
        (:instance rec-valuation-bindsp-of-nth (g gb) (i 0))
        (:instance rec-valuation-bindsp-of-nth (g gb) (i 1))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 0))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 1))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 2))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 3))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 4)))
  :enable (rec-grp-gadget rec-point-of group-is-equal-funspec crypto-bit-eq
           curve-edwards-bls12-pointp-when-groupp r1cs::fep-of-lookup-equal primep-of-base-prime)
  :disable (lookup-equal-of-nth nth))

(defruled rec-version-bit
  (implies (and (symbol-listp va) (equal (len va) 8)
                (symbol-listp vb) (equal (len vb) 8)
                (symbolp vm) (symbolp vr)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg va)
                (r1cs::valuation-binds-allp asg vb)
                (r1cs::valuation-bindsp asg vm)
                (r1cs::valuation-bindsp asg vr)
                (bit-listp (lookup-equal-list va asg))
                (bit-listp (lookup-equal-list vb asg))
                (r1cs::r1cs-constraints-holdp
                 (rec-lc-neq-gadget (pow2sum-vector va 0) (pow2sum-vector vb 0)
                                    vm vr (base-prime))
                 asg (base-prime)))
           (equal (crypto-bit-not (lookup-equal vr asg))
                  (crypto-bit-eq (lebits=>nat (lookup-equal-list va asg))
                                 (lebits=>nat (lookup-equal-list vb asg)))))
  :use ((:instance rec-lc-neq-gadget-bit
                   (va (pow2sum-vector va 0)) (vb (pow2sum-vector vb 0))
                   (m vm) (r vr))
        (:instance rec-u8-dot (vs va))
        (:instance rec-u8-dot (vs vb)))
  :enable (crypto-bit-not crypto-bit-eq))

(defruled rec-owner-eq-bit
  (implies (and (booleanp pa) (booleanp pb)
                (groupp g1) (groupp g2))
           (equal (crypto-owner-is-equal (if pa (owner-public g1) (owner-private g1))
                                         (if pb (owner-public g2) (owner-private g2)))
                  (if (equal pa pb) (crypto-bit-eq g1 g2) 0)))
  :enable (crypto-owner-is-equal crypto-plaintext-is-equal crypto-bit-eq))

;; The terms of the group and version comparisons.
(defruled rec-grp-term
  (implies (and (symbol-listp ga) (equal (len ga) 14)
                (symbol-listp gb) (equal (len gb) 14)
                (symbol-listp e) (equal (len e) 5)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg ga)
                (r1cs::valuation-binds-allp asg gb)
                (r1cs::valuation-binds-allp asg e)
                (groupp (rec-point-of ga asg)) (groupp (rec-point-of gb asg))
                (r1cs::r1cs-constraints-holdp (rec-grp-gadget ga gb e)
                                              asg (base-prime)))
           (equal (ptx-bval (rec-bit-term neq (nth 4 e)) asg (base-prime))
                  (rec-nspec neq (crypto-bit-eq (rec-point-of ga asg)
                                                (rec-point-of gb asg)))))
  :do-not-induct t
  :use (rec-grp-gadget-bit
        (:instance rec-bit-term-val (negp neq) (z (nth 4 e)))
        (:instance rec-valuation-bindsp-of-nth (g e) (i 4)))
  :enable (rec-nspec))

(defruled rec-version-term
  (implies (and (symbol-listp va) (equal (len va) 8)
                (symbol-listp vb) (equal (len vb) 8)
                (symbolp vm) (symbolp vr)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg va)
                (r1cs::valuation-binds-allp asg vb)
                (r1cs::valuation-bindsp asg vm)
                (r1cs::valuation-bindsp asg vr)
                (bit-listp (lookup-equal-list va asg))
                (bit-listp (lookup-equal-list vb asg))
                (r1cs::r1cs-constraints-holdp
                 (rec-lc-neq-gadget (pow2sum-vector va 0) (pow2sum-vector vb 0)
                                    vm vr (base-prime))
                 asg (base-prime)))
           (equal (ptx-bval (rec-bit-term (not neq) vr) asg (base-prime))
                  (rec-nspec neq (crypto-bit-eq
                                  (lebits=>nat (lookup-equal-list va asg))
                                  (lebits=>nat (lookup-equal-list vb asg))))))
  :do-not-induct t
  :use (rec-version-bit
        (:instance rec-lc-neq-gadget-bit
                   (va (pow2sum-vector va 0)) (vb (pow2sum-vector vb 0))
                   (m vm) (r vr))
        (:instance rec-bit-term-val (negp (not neq)) (z vr)))
  :enable (rec-nspec crypto-bit-not crypto-bit-eq))

(defruled rec-len-of-data-eval
  (equal (len (rec-record-data-eval data asg)) (len data))
  :induct (len data)
  :enable rec-record-data-eval)

(defruled rec-record-eq-fold
  (implies (and (bitp o) (bitp d) (bitp n) (bitp v))
           (equal (ptx-bop-spec
                   neq
                   (ptx-bop-spec
                    neq
                    (ptx-bop-spec neq (rec-nspec neq o)
                                  (ptx-bop-spec neq (if neq 0 1)
                                                (rec-nspec neq d)))
                    (rec-nspec neq n))
                   (rec-nspec neq v))
                  (rec-nspec neq (crypto-bit-and
                                  (crypto-bit-and (crypto-bit-and o d) n)
                                  v))))
  :enable (ptx-bop-spec rec-nspec crypto-bit-and crypto-bit-not bitp))

(defruled rec-chain-val
  (b* ((r1 (ptx-bop neq x0 d za))
       (r2 (ptx-bop neq (cdr r1) tn zb))
       (r3 (ptx-bop neq (cdr r2) tv zc)))
    (implies (and (primep p)
                  (symbolp za) (symbolp zb) (symbolp zc)
                  (ptx-blcp x0) (ptx-blcp d) (ptx-blcp tn) (ptx-blcp tv)
                  (bitp (ptx-bval x0 asg p)) (bitp (ptx-bval d asg p))
                  (bitp (ptx-bval tn asg p)) (bitp (ptx-bval tv asg p))
                  (r1cs::r1cs-constraints-holdp (car r1) asg p)
                  (r1cs::r1cs-constraints-holdp (car r2) asg p)
                  (r1cs::r1cs-constraints-holdp (car r3) asg p))
             (equal (ptx-bval (cdr r3) asg p)
                    (ptx-bop-spec
                     neq
                     (ptx-bop-spec
                      neq
                      (ptx-bop-spec neq (ptx-bval x0 asg p) (ptx-bval d asg p))
                      (ptx-bval tn asg p))
                     (ptx-bval tv asg p)))))
  :do-not-induct t
  :use ((:instance ptx-bop-sound-rw (x x0) (y d) (z za))
        (:instance ptx-bop-sound-rw (x (cdr (ptx-bop neq x0 d za))) (y tn) (z zb))
        (:instance ptx-bop-sound-rw
                   (x (cdr (ptx-bop neq (cdr (ptx-bop neq x0 d za)) tn zb)))
                   (y tv) (z zc)))
  :in-theory (e/d (ptx-blcp-of-bop ptx-bitp-of-bop-spec)
                  (ptx-bop ptx-bop-spec ptx-bop-sound-rw)))

(defruled rec-bval-of-const
  (and (equal (ptx-bval 0 asg p) 0)
       (equal (ptx-bval 1 asg p) 1)
       (ptx-blcp 0) (ptx-blcp 1))
  :enable (ptx-bval ptx-blcp))

(defruled rec-record-eq-val
  (b* ((c (rec-record-eq pa oga da nga va pb ogb db ngb vb oe ne vm vr
                         za zb zc names neq)))
    (implies (rec-record-eq-hyps
              (equal (len da) (len db))
              (r1cs::r1cs-constraints-holdp (car c) asg (base-prime)))
             (equal (ptx-bval (cdr c) asg (base-prime))
                    (ptx-bop-spec
                     neq
                     (ptx-bop-spec
                      neq
                      (ptx-bop-spec
                       neq
                       (rec-nspec neq (if (equal pa pb)
                                          (crypto-bit-eq (rec-point-of oga asg)
                                                         (rec-point-of ogb asg))
                                        0))
                       (ptx-bop-spec neq (if neq 0 1)
                                     (rec-nspec neq
                                                (crypto-record-data-is-equal
                                                 (rec-record-data-eval da asg)
                                                 (rec-record-data-eval db asg)))))
                      (rec-nspec neq (crypto-bit-eq (rec-point-of nga asg)
                                                    (rec-point-of ngb asg))))
                     (rec-nspec neq (crypto-bit-eq
                                     (lebits=>nat (lookup-equal-list va asg))
                                     (lebits=>nat (lookup-equal-list vb asg))))))))
  :do-not-induct t
  :use ((:instance rec-chain-val
                   (p (base-prime))
                   (x0 (if (equal pa pb) (rec-bit-term neq (nth 4 oe)) (if neq 1 0)))
                   (d (cdr (rec-deq da db neq (if neq 0 1) names)))
                   (tn (rec-bit-term neq (nth 4 ne)))
                   (tv (rec-bit-term (not neq) vr)))
        (:instance rec-deq-sound (das da) (dbs db) (p (base-prime))
                   (acc (if neq 0 1)))
        (:instance rec-grp-term (ga oga) (gb ogb) (e oe))
        (:instance rec-grp-term (ga nga) (gb ngb) (e ne))
        (:instance rec-version-term)
        (:instance rec-valuation-bindsp-of-nth (g oe) (i 4))
        (:instance rec-valuation-bindsp-of-nth (g ne) (i 4)))
  :in-theory (e/d (rec-record-eq r1cs::r1cs-constraints-holdp-of-append
                   r1cs::valuation-binds-allp rec-bval-of-const
                   rec-blcp-of-bit-term rec-blcp-of-deq
                   rec-bitp-of-nspec ptx-bitp-of-bop-spec
                   primep-of-base-prime)
                  (ptx-bop rec-deq rec-grp-gadget rec-lc-neq-gadget
                   rec-bit-term ptx-bop-spec rec-nspec crypto-bit-eq
                   rec-point-of rec-record-data-eval
                   crypto-record-data-is-equal)))

(defruled rec-record-spec-val
  (b* ((ra (rec-record-of-wires pa oga da nga va asg))
       (rb (rec-record-of-wires pb ogb db ngb vb asg)))
    (implies (and (booleanp pa) (booleanp pb)
                  (groupp (rec-point-of oga asg)) (groupp (rec-point-of ogb asg))
                  (groupp (rec-point-of nga asg)) (groupp (rec-point-of ngb asg))
                  (bit-listp (lookup-equal-list va asg))
                  (bit-listp (lookup-equal-list vb asg))
                  (equal (len (lookup-equal-list va asg)) 8)
                  (equal (len (lookup-equal-list vb asg)) 8)
                  (rec-record-datawp da) (rec-record-datawp db)
                  (equal (len da) (len db)))
             (equal (crypto-record-is-equal ra rb)
                    (crypto-bit-and
                     (crypto-bit-and
                      (crypto-bit-and
                       (if (equal pa pb)
                           (crypto-bit-eq (rec-point-of oga asg)
                                          (rec-point-of ogb asg))
                         0)
                       (crypto-record-data-is-equal
                        (rec-record-data-eval da asg)
                        (rec-record-data-eval db asg)))
                      (crypto-bit-eq (rec-point-of nga asg)
                                     (rec-point-of ngb asg)))
                     (crypto-bit-eq
                      (lebits=>nat (lookup-equal-list va asg))
                      (lebits=>nat (lookup-equal-list vb asg)))))))
  :do-not-induct t
  :use ((:instance rec-owner-eq-bit (g1 (rec-point-of oga asg))
                   (g2 (rec-point-of ogb asg)))
        (:instance rec-len-of-data-eval (data da))
        (:instance rec-len-of-data-eval (data db))
        (:instance rec-ubyte8p-of-lebits=>nat (bs (lookup-equal-list va asg)))
        (:instance rec-ubyte8p-of-lebits=>nat (bs (lookup-equal-list vb asg))))
  :in-theory (e/d (crypto-record-is-equal rec-record-of-wires)
                  (crypto-bit-eq crypto-bit-and crypto-owner-is-equal
                   rec-point-of crypto-record-data-is-equal)))

(defruled rec-record-eq-sound
  (b* ((ra (rec-record-of-wires pa oga da nga va asg))
       (rb (rec-record-of-wires pb ogb db ngb vb asg))
       (c (rec-record-eq pa oga da nga va pb ogb db ngb vb oe ne vm vr
                         za zb zc names neq)))
    (implies (rec-record-eq-hyps
              (r1cs::r1cs-constraints-holdp (car c) asg (base-prime)))
             (equal (ptx-bval (cdr c) asg (base-prime))
                    (if neq
                        (crypto-record-is-not-equal ra rb)
                      (crypto-record-is-equal ra rb)))))
  :do-not-induct t
  :cases ((equal (len da) (len db)))
  :hints (("Subgoal 2"
           :in-theory (enable rec-record-eq crypto-record-is-equal
                              crypto-record-is-not-equal rec-record-of-wires
                              crypto-bit-not ptx-bval)
           :use ((:instance rec-len-of-data-eval (data da))
                 (:instance rec-len-of-data-eval (data db))))
          ("Subgoal 1"
           :in-theory (e/d (crypto-record-is-not-equal rec-bitp-of-nspec
                            ptx-bitp-of-bop-spec)
                           (rec-record-eq crypto-record-is-equal ptx-bop-spec
                            rec-nspec crypto-bit-eq crypto-bit-and
                            rec-record-of-wires rec-point-of
                            crypto-record-data-is-equal))
           :use ((:instance rec-record-eq-val)
                 (:instance rec-record-spec-val)
                 (:instance rec-record-eq-fold
                            (o (if (equal pa pb)
                                   (crypto-bit-eq (rec-point-of oga asg)
                                                  (rec-point-of ogb asg))
                                 0))
                            (d (crypto-record-data-is-equal
                                (rec-record-data-eval da asg)
                                (rec-record-data-eval db asg)))
                            (n (crypto-bit-eq (rec-point-of nga asg)
                                              (rec-point-of ngb asg)))
                            (v (crypto-bit-eq
                                (lebits=>nat (lookup-equal-list va asg))
                                (lebits=>nat (lookup-equal-list vb asg)))))
                 (:instance rec-nspec (b (crypto-record-is-equal
                                          (rec-record-of-wires pa oga da nga va asg)
                                          (rec-record-of-wires pb ogb db ngb vb asg))))))))

(defruled rec-record-eq-complete
  :short "The constraints hold when the data fold's witnesses hold
          (rec-deq-complete), the owner and nonce Group::is_equal and the
          version comparison hold (crv-group-is-equal-gadget-complete,
          rec-lc-neq-gadget-complete), and each non-folded AND / OR variable
          holds its value."
  (b* ((d (rec-deq da db neq (if neq 0 1) names))
       (oterm (if (equal pa pb) (rec-bit-term neq (nth 4 oe)) (if neq 1 0)))
       (r1 (ptx-bop neq oterm (cdr d) za))
       (r2 (ptx-bop neq (cdr r1) (rec-bit-term neq (nth 4 ne)) zb))
       (c (rec-record-eq pa oga da nga va pb ogb db ngb vb oe ne vm vr
                         za zb zc names neq)))
    (implies (rec-record-eq-hyps
              (equal (len da) (len db))
              (rec-deq-witnessp da db neq (if neq 0 1) names asg (base-prime))
              (implies (equal pa pb)
                       (r1cs::r1cs-constraints-holdp
                        (rec-grp-gadget oga ogb oe) asg (base-prime)))
              (r1cs::r1cs-constraints-holdp
               (rec-grp-gadget nga ngb ne) asg (base-prime))
              (r1cs::r1cs-constraints-holdp
               (rec-lc-neq-gadget (pow2sum-vector va 0) (pow2sum-vector vb 0)
                                  vm vr (base-prime))
               asg (base-prime))
              (ptx-bop-witnessp neq oterm (cdr d) za asg (base-prime))
              (ptx-bop-witnessp neq (cdr r1) (rec-bit-term neq (nth 4 ne)) zb
                                asg (base-prime))
              (ptx-bop-witnessp neq (cdr r2) (rec-bit-term (not neq) vr) zc
                                asg (base-prime)))
             (r1cs::r1cs-constraints-holdp (car c) asg (base-prime))))
  :do-not-induct t
  :in-theory (e/d (rec-record-eq r1cs::r1cs-constraints-holdp-of-append
                   r1cs::valuation-binds-allp)
                  (ptx-bop rec-deq rec-grp-gadget rec-lc-neq-gadget
                   rec-bit-term ptx-bop-witnessp))
  :use ((:instance rec-deq-complete (das da) (dbs db) (p (base-prime))
                   (acc (if neq 0 1)))
        (:instance rec-deq-sound (das da) (dbs db) (p (base-prime))
                   (acc (if neq 0 1)))
        (:instance rec-grp-term (ga oga) (gb ogb) (e oe))
        (:instance rec-grp-term (ga nga) (gb ngb) (e ne))
        (:instance rec-version-term)))
