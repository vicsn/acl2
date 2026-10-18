; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS for the unsigned integer division gadget snarkVM emits when
; 2*n+1 is below the bit length of the base prime.  The proved widths
; are 8, 16, 32, and 64.  The gadget is unsigned-small-div-gadget.
; In int-div.lisp the unsigned wrappers for div, div_checked,
; div_wrapped, rem, unsigned_division_via_witness, and modulo are
; definitionally this gadget.  That book does not certify, so this
; book includes the gadget directly.
;
; Quotient bits and remainder bits are boolean-checked.  Dividend bits
; and divisor bits are not.  The existing soundness theorems assume
; int-valuep or bit-listp of those inputs, so this lowering is not
; R1CS-SOUND.  There is no completeness proof, so it is not
; R1CS-COMPLETE.  Signed division and width 128 are different circuits.
;
; The ground relation INT_UNSIGNED_DIV_<n> has no free variables on
; these four widths.  definition-satp of that relation, on the wire
; lookups, is equivalent to r1cs-constraints-holdp of
; unsigned-small-div-gadget.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-div")
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/proof-support" :dir :system)
(include-book "projects/pfcs/semantics" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(include-book "std/strings/decimal" :dir :system)

(define int-div-sym-name ((x symbolp))
  :returns (name pfcs::namep)
  (pfcs::name-simple (symbol-name x)))

(define int-div-bool-pfcs ((x symbolp))
  :returns (constr pfcs::constraintp)
  (pfcs::make-constraint-equal
   :left (pfcs::make-expression-mul
          :arg1 (pfcs::make-expression-sub
                 :arg1 (pfcs::expression-const 1)
                 :arg2 (pfcs::expression-var (int-div-sym-name x)))
          :arg2 (pfcs::expression-var (int-div-sym-name x)))
   :right (pfcs::expression-const 0)))

(define int-div-names ((xs symbol-listp))
  :returns (names pfcs::name-listp)
  (cond ((endp xs) nil)
        (t (cons (int-div-sym-name (car xs))
                 (int-div-names (cdr xs)))))
  ///
  (defret len-of-int-div-names
    (equal (len names) (len xs))
    :hints (("Goal" :in-theory (enable int-div-names)))))

(define int-div-names-match ((xs symbol-listp)
                             (vals true-listp)
                             (pasg pfcs::assignmentp))
  (if (endp xs)
      t
    (and (equal (cdr (omap::assoc (int-div-sym-name (car xs)) pasg))
                (car vals))
         (consp (omap::assoc (int-div-sym-name (car xs)) pasg))
         (int-div-names-match (cdr xs) (cdr vals) pasg)))
  ///
  (defrule int-div-names-match-of-cdr
    (implies (int-div-names-match xs vals pasg)
             (int-div-names-match (cdr xs) (cdr vals) pasg))))

(defruled int-div-names-match-of-update-other
  (implies (and (int-div-names-match xs vals pasg)
                (not (member-equal key (int-div-names xs))))
           (int-div-names-match xs vals (omap::update key val pasg)))
  :hints (("Goal"
           :in-theory (enable int-div-names-match
                              int-div-names
                              omap::assoc-of-update))))

(local
 (defun int-div-cdr2 (xs vals)
   (if (or (endp xs) (endp vals))
       nil
     (int-div-cdr2 (cdr xs) (cdr vals)))))

(defruled int-div-names-match-of-from-lists
  (implies (and (symbol-listp xs)
                (equal (len xs) (len vals))
                (no-duplicatesp-equal (int-div-names xs)))
           (int-div-names-match xs vals
                                (omap::from-lists (int-div-names xs) vals)))
  :hints (("Goal"
           :induct (int-div-cdr2 xs vals)
           :in-theory (enable int-div-names-match
                              int-div-names
                              int-div-sym-name
                              omap::from-lists
                              no-duplicatesp-equal
                              omap::assoc-of-update
                              int-div-names-match-of-update-other))))

(define int-div-pow2-expr ((xs symbol-listp) (i natp))
  :returns (expr pfcs::expressionp)
  (cond ((endp xs) (pfcs::expression-const 0))
        (t (pfcs::make-expression-add
            :arg1 (pfcs::make-expression-mul
                   :arg1 (pfcs::expression-const (expt 2 (nfix i)))
                   :arg2 (pfcs::expression-var (int-div-sym-name (car xs))))
            :arg2 (int-div-pow2-expr (cdr xs) (1+ (nfix i))))))
  ///
  (defret expressionp-of-int-div-pow2-expr
    (pfcs::expressionp expr)))

(defruled int-div-pow2-expr-eval
  (implies (and (primep p)
                (natp i)
                (symbol-listp xs)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg))
           (equal (pfcs::eval-expr (int-div-pow2-expr xs i) pasg p)
                  (r1cs::dot-product (pow2sum-vector xs i) asg p)))
  :hints (("Goal"
           :in-theory (enable int-div-pow2-expr
                              int-div-names-match
                              int-div-sym-name
                              pow2sum-vector
                              r1cs::dot-product
                              pfcs::eval-expr
                              lookup-equal-list
                              nfix))))

(defruled int-div-bool-one-iff
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (equal (cdr (omap::assoc (int-div-sym-name x) pasg))
                       (lookup-equal x asg))
                (consp (omap::assoc (int-div-sym-name x) pasg)))
           (equal (pfcs::constraint-satp (int-div-bool-pfcs x) defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget x p) asg p)))
  :do-not-induct t
  :enable (int-div-bool-pfcs
           int-div-sym-name
           boolean-check-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfcs::constraint-satp-of-equal
           pfcs::constraint-equal-satp
           pfcs::eval-expr
           pfield::sub))

(define int-div-neg-pow2-expr ((xs symbol-listp) (i natp) (p primep))
  :returns (expr pfcs::expressionp)
  (cond ((endp xs) (pfcs::expression-const 0))
        (t (pfcs::make-expression-add
            :arg1 (pfcs::make-expression-mul
                   :arg1 (pfcs::expression-const
                          (- (expt 2 (nfix i))))
                   :arg2 (pfcs::expression-var (int-div-sym-name (car xs))))
            :arg2 (int-div-neg-pow2-expr (cdr xs) (1+ (nfix i)) p)))))

(defruled int-div-mul-of-+-prime
  (implies (and (posp p)
                (integerp y))
           (equal (pfield::mul x (+ p y) p)
                  (pfield::mul x y p)))
  :hints (("Goal"
           :in-theory (e/d (pfield::mul
                            acl2::mod-of-+-of-*-same-arg1-arg1
                            acl2::commutativity-of-*)
                           (acl2::mod-of-+-of-*-same-arg1-arg2
                            acl2::mod-of-+-of-*-same-arg2-arg1
                            acl2::mod-of-+-of-*-same-arg2-arg2)))))

(defruled int-div-neg-pow2-expr-eval
  (implies (and (primep p)
                (natp i)
                (symbol-listp xs)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg))
           (equal (pfcs::eval-expr (int-div-neg-pow2-expr xs i p) pasg p)
                  (r1cs::dot-product (pow2sum-neg-prime-vector xs i p) asg p)))
  :hints (("Goal"
           :in-theory (enable int-div-neg-pow2-expr
                              int-div-names-match
                              int-div-sym-name
                              pow2sum-neg-prime-vector
                              pow2sum-vector
                              vector-neg-prime
                              r1cs::dot-product
                              pfcs::eval-expr
                              lookup-equal-list
                              nfix
                              acl2::mod-of-mod-same-arg2
                              int-div-mul-of-+-prime))))

(define int-div-bool-pfcs-list ((xs symbol-listp))
  :returns (constrs pfcs::constraint-listp)
  (cond ((endp xs) nil)
        (t (cons (int-div-bool-pfcs (car xs))
                 (int-div-bool-pfcs-list (cdr xs))))))

(defruled int-div-bool-list-iff
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg))
           (equal (pfcs::constraint-list-satp
                   (int-div-bool-pfcs-list xs) defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget-list xs p) asg p)))
  :hints (("Goal"
           :in-theory (enable int-div-bool-pfcs-list
                              int-div-names-match
                              boolean-check-gadget-list
                              r1cs::r1cs-constraints-holdp
                              lookup-equal-list
                              pfcs::constraint-list-satp-of-cons
                              pfcs::constraint-list-satp-of-nil
                              int-div-bool-one-iff
                              r1cs::valuation-bindsp-when-valuation-binds-allp))))

(defruled pfcs-constraint-list-satp-of-append
  (equal (pfcs::constraint-list-satp (append a b) defs pasg p)
         (and (pfcs::constraint-list-satp a defs pasg p)
              (pfcs::constraint-list-satp b defs pasg p)))
  :hints (("Goal"
           :in-theory (enable append
                              pfcs::constraint-list-satp-of-cons
                              pfcs::constraint-list-satp-of-nil
                              pfcs::constraint-list-satp-of-atom))))

(define int-div-mul-pfcs ((qs symbol-listp) (ys symbol-listp) (m symbolp))
  :returns (constr pfcs::constraintp)
  (pfcs::make-constraint-equal
   :left (pfcs::make-expression-mul
          :arg1 (int-div-pow2-expr qs 0)
          :arg2 (int-div-pow2-expr ys 0))
   :right (pfcs::expression-var (int-div-sym-name m))))

(defruled int-div-mul-iff
  (implies (and (primep p)
                (symbol-listp qs)
                (symbol-listp ys)
                (symbolp m)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg m)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match qs (lookup-equal-list qs asg) pasg)
                (int-div-names-match ys (lookup-equal-list ys asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name m) pasg))
                       (lookup-equal m asg))
                (consp (omap::assoc (int-div-sym-name m) pasg)))
           (equal (pfcs::constraint-satp (int-div-mul-pfcs qs ys m) defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (bits-mul-field-gadget qs ys m p) asg p)))
  :do-not-induct t
  :enable (int-div-mul-pfcs
           bits-mul-field-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul
           pfcs::constraint-satp-of-equal
           pfcs::constraint-equal-satp
           pfcs::eval-expr
           int-div-pow2-expr-eval
           int-div-sym-name
           nfix))

(define int-div-add-pfcs ((m symbolp) (rs symbol-listp) (xs symbol-listp))
  :returns (constr pfcs::constraintp)
  (pfcs::make-constraint-equal
   :left (pfcs::make-expression-mul
          :arg1 (int-div-pow2-expr xs 0)
          :arg2 (pfcs::expression-const 1))
   :right (pfcs::make-expression-add
           :arg1 (pfcs::expression-var (int-div-sym-name m))
           :arg2 (int-div-pow2-expr rs 0))))

(defruled int-div-add-iff
  (implies (and (primep p)
                (symbolp m)
                (symbol-listp rs)
                (symbol-listp xs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg xs)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match rs (lookup-equal-list rs asg) pasg)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name m) pasg))
                       (lookup-equal m asg))
                (consp (omap::assoc (int-div-sym-name m) pasg)))
           (equal (pfcs::constraint-satp (int-div-add-pfcs m rs xs) defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (field-bits-add-bits-gadget m rs xs p) asg p)))
  :do-not-induct t
  :enable (int-div-add-pfcs
           field-bits-add-bits-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul
           pfcs::constraint-satp-of-equal
           pfcs::constraint-equal-satp
           pfcs::eval-expr
           int-div-pow2-expr-eval
           int-div-sym-name
           nfix))

(define int-div-lt-sum-expr ((xs symbol-listp) (ys symbol-listp) (p primep))
  :returns (expr pfcs::expressionp)
  (pfcs::make-expression-add
   :arg1 (int-div-pow2-expr xs 0)
   :arg2 (pfcs::make-expression-add
          :arg1 (int-div-neg-pow2-expr ys 0 p)
          :arg2 (pfcs::expression-const (expt 2 (len xs))))))

(define int-div-lt-pfcs ((xs symbol-listp)
                         (ys symbol-listp)
                         (zs symbol-listp)
                         (z symbolp)
                         (p primep))
  :returns (constr pfcs::constraintp)
  (pfcs::make-constraint-equal
   :left (pfcs::make-expression-mul
          :arg1 (int-div-lt-sum-expr xs ys p)
          :arg2 (pfcs::expression-const 1))
   :right (int-div-pow2-expr (append zs (list z)) 0)))

(defruled int-div-names-match-of-append
  (implies (equal (len xs) (len vals1))
           (equal (int-div-names-match (append xs ys)
                                       (append vals1 vals2)
                                       pasg)
                  (and (int-div-names-match xs vals1 pasg)
                       (int-div-names-match ys vals2 pasg))))
  :hints (("Goal" :in-theory (enable int-div-names-match append len))))

(defruled int-div-names-match-of-append-when-pieces
  (implies (and (int-div-names-match xs vals1 pasg)
                (int-div-names-match ys vals2 pasg)
                (equal (len xs) (len vals1)))
           (int-div-names-match (append xs ys)
                                (append vals1 vals2)
                                pasg))
  :hints (("Goal" :in-theory (enable int-div-names-match-of-append))))

(defruled int-div-names-match-of-singleton
  (implies (and (equal (cdr (omap::assoc (int-div-sym-name x) pasg)) v)
                (consp (omap::assoc (int-div-sym-name x) pasg)))
           (int-div-names-match (list x) (list v) pasg))
  :hints (("Goal" :in-theory (enable int-div-names-match))))

(defruled int-div-names-match-of-bits-and-bit
  (implies (and (int-div-names-match zs (lookup-equal-list zs asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name z) pasg))
                       (lookup-equal z asg))
                (consp (omap::assoc (int-div-sym-name z) pasg)))
           (int-div-names-match (append zs (list z))
                                (lookup-equal-list (append zs (list z)) asg)
                                pasg))
  :hints (("Goal"
           :in-theory (enable int-div-names-match-of-append-when-pieces
                              int-div-names-match-of-singleton
                              lookup-equal-list-of-append
                              lookup-equal-list
                              len-of-lookup-equal-list))))

(define int-div-lt-pfcs-list ((xs symbol-listp)
                              (ys symbol-listp)
                              (zs symbol-listp)
                              (z symbolp)
                              (p primep))
  :returns (constrs pfcs::constraint-listp)
  (append (int-div-bool-pfcs-list zs)
          (list (int-div-bool-pfcs z))
          (list (int-div-lt-pfcs xs ys zs z p))))

(defruled int-div-lt-iff
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg)
                (int-div-names-match ys (lookup-equal-list ys asg) pasg)
                (int-div-names-match zs (lookup-equal-list zs asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name z) pasg))
                       (lookup-equal z asg))
                (consp (omap::assoc (int-div-sym-name z) pasg)))
           (equal (pfcs::constraint-list-satp
                   (int-div-lt-pfcs-list xs ys zs z p)
                   defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-lt-gadget xs ys zs z p) asg p)))
  :do-not-induct t
  :use ((:instance int-div-pow2-expr-eval
                   (xs (append zs (list z)))
                   (i 0)))
  :enable (int-div-lt-pfcs-list
           int-div-lt-pfcs
           int-div-lt-sum-expr
           unsigned-small-lt-gadget
           unsigned-small-lt-vector
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           r1cs::dot-product-of-append
           pfield::add
           pfield::mul
           pfcs::constraint-satp-of-equal
           pfcs::constraint-equal-satp
           pfcs::constraint-list-satp-of-cons
           pfcs::constraint-list-satp-of-nil
           pfcs-constraint-list-satp-of-append
           pfcs::eval-expr
           int-div-pow2-expr-eval
           int-div-neg-pow2-expr-eval
           int-div-bool-list-iff
           int-div-bool-one-iff
           int-div-sym-name
           int-div-names-match-of-bits-and-bit
           symbol-listp-of-append-of-symbol
           nfix
           len
           append))

(define int-div-zero-pfcs ((d symbolp) (u symbolp) (p primep))
  :returns (constr pfcs::constraintp)
  (pfcs::make-constraint-equal
   :left (pfcs::make-expression-mul
          :arg1 (pfcs::make-expression-add
                 :arg1 (pfcs::make-expression-mul
                        :arg1 (pfcs::expression-const (1- (ifix p)))
                        :arg2 (pfcs::expression-var (int-div-sym-name d)))
                 :arg2 (pfcs::expression-var (int-div-sym-name u)))
          :arg2 (pfcs::expression-const 1))
   :right (pfcs::expression-const 1)))

(defruled int-div-neg-of-1-minus-prime
  (implies (and (posp p)
                (integerp x)
                (integerp u))
           (equal (mod (+ u (* (+ -1 p) x)) p)
                  (mod (+ u (pfield::neg x p)) p)))
  :hints (("Goal"
           :in-theory (enable pfield::neg
                              acl2::*-of--1
                              acl2::mod-of-minus-arg1
                              acl2::mod-of-+-of-*-same-arg2-arg1
                              acl2::mod-of-+-of-*-same-arg2-arg2
                              acl2::mod-of-+-of-mod-arg2
                              acl2::commutativity-of-*))))

(defruled int-div-zero-iff
  (implies (and (primep p)
                (symbolp d)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (equal (cdr (omap::assoc (int-div-sym-name d) pasg))
                       (lookup-equal d asg))
                (consp (omap::assoc (int-div-sym-name d) pasg))
                (equal (cdr (omap::assoc (int-div-sym-name u) pasg))
                       (lookup-equal u asg))
                (consp (omap::assoc (int-div-sym-name u) pasg)))
           (equal (pfcs::constraint-satp (int-div-zero-pfcs d u p) defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (zero-unit-gadget d u p) asg p)))
  :do-not-induct t
  :enable (int-div-zero-pfcs
           zero-unit-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul
           pfcs::constraint-satp-of-equal
           pfcs::constraint-equal-satp
           pfcs::eval-expr
           int-div-sym-name
           int-div-neg-of-1-minus-prime
           pfield::neg
           nfix
           ifix))

(define int-unsigned-div-pfcs-body
  ((xs symbol-listp)
   (ys symbol-listp)
   (qs symbol-listp)
   (rs symbol-listp)
   (m symbolp)
   (ds symbol-listp)
   (d symbolp)
   (u symbolp)
   (p primep))
  :returns (constrs pfcs::constraint-listp)
  (append (int-div-bool-pfcs-list qs)
          (int-div-bool-pfcs-list rs)
          (list (int-div-mul-pfcs qs ys m))
          (list (int-div-add-pfcs m rs xs))
          (int-div-lt-pfcs-list rs ys ds d p)
          (list (int-div-zero-pfcs d u p))))

(defruled int-unsigned-div-pfcs-body-iff-r1cs
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u)
                (pfcs::assignmentp pasg)
                (pfcs::assignment-wfp pasg p)
                (int-div-names-match xs (lookup-equal-list xs asg) pasg)
                (int-div-names-match ys (lookup-equal-list ys asg) pasg)
                (int-div-names-match qs (lookup-equal-list qs asg) pasg)
                (int-div-names-match rs (lookup-equal-list rs asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name m) pasg))
                       (lookup-equal m asg))
                (consp (omap::assoc (int-div-sym-name m) pasg))
                (int-div-names-match ds (lookup-equal-list ds asg) pasg)
                (equal (cdr (omap::assoc (int-div-sym-name d) pasg))
                       (lookup-equal d asg))
                (consp (omap::assoc (int-div-sym-name d) pasg))
                (equal (cdr (omap::assoc (int-div-sym-name u) pasg))
                       (lookup-equal u asg))
                (consp (omap::assoc (int-div-sym-name u) pasg)))
           (equal (pfcs::constraint-list-satp
                   (int-unsigned-div-pfcs-body xs ys qs rs m ds d u p)
                   defs pasg p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-div-gadget xs ys qs rs m ds d u p)
                   asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-unsigned-div-pfcs-body
                            unsigned-small-div-gadget
                            pfcs-constraint-list-satp-of-append
                            pfcs::constraint-list-satp-of-cons
                            pfcs::constraint-list-satp-of-nil
                            r1cs::r1cs-constraints-holdp-of-append
                            int-div-bool-list-iff
                            int-div-mul-iff
                            int-div-add-iff
                            int-div-lt-iff
                            int-div-zero-iff)
                           (                            acl2::append-of-cons
                            acl2::associativity-of-append
                            acl2::append-when-not-consp)))))

(define int-div-dec-string ((n natp))
  :returns (s stringp)
  (str::nat-to-dec-string (nfix n)))

(define int-div-indexed-sym ((prefix stringp) (i natp))
  :returns (sym symbolp)
  (intern-in-package-of-symbol
   (concatenate 'string prefix (int-div-dec-string i))
   'int-div-indexed-sym))

(define int-div-indexed-syms ((prefix stringp) (i natp) (n natp))
  :guard (<= i n)
  :returns (syms symbol-listp)
  :measure (nfix (- (nfix n) (nfix i)))
  (if (>= (nfix i) (nfix n))
      nil
    (cons (int-div-indexed-sym prefix i)
          (int-div-indexed-syms prefix (+ 1 (nfix i)) n)))
  ///
  (defret len-of-int-div-indexed-syms
    (implies (<= (nfix i) (nfix n))
             (equal (len syms) (- (nfix n) (nfix i))))
    :hints (("Goal" :in-theory (enable int-div-indexed-syms len)))))

(define int-unsigned-div-wires ((n posp))
  :returns (mv (xs symbol-listp)
               (ys symbol-listp)
               (qs symbol-listp)
               (rs symbol-listp)
               (ds symbol-listp))
  (mv (int-div-indexed-syms "X" 0 n)
      (int-div-indexed-syms "Y" 0 n)
      (int-div-indexed-syms "Q" 0 n)
      (int-div-indexed-syms "R" 0 n)
      (int-div-indexed-syms "S" 0 n)))

(define int-unsigned-div-pfcs-def ((n posp))
  :returns (def pfcs::definitionp)
  (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
    (pfcs::make-definition
     :name (pfcs::name-simple
            (concatenate 'string "INT_UNSIGNED_DIV_" (int-div-dec-string n)))
     :para (append (int-div-names xs)
                   (int-div-names ys)
                   (int-div-names qs)
                   (int-div-names rs)
                   (int-div-names (list 'm))
                   (int-div-names ds)
                   (int-div-names (list 'd 'u)))
     :body (int-unsigned-div-pfcs-body xs ys qs rs 'm ds 'd 'u (base-prime)))))

(defruled int-unsigned-div-pfcs-def-no-free
  (implies (member-equal (nfix n) '(8 16 32 64))
           (set::emptyp (pfcs::definition-free-vars
                         (int-unsigned-div-pfcs-def n))))
  :hints (("Goal"
           :in-theory (enable (:e int-unsigned-div-pfcs-def)
                              (:e pfcs::definition-free-vars)
                              (:e set::emptyp)
                              member-equal nfix))))

(defruled int-div-names-of-append
  (equal (int-div-names (append xs ys))
         (append (int-div-names xs) (int-div-names ys)))
  :hints (("Goal" :in-theory (enable int-div-names append))))

(defruled int-div-symbol-listp-of-append
  (implies (and (symbol-listp x) (symbol-listp y))
           (symbol-listp (append x y)))
  :hints (("Goal" :in-theory (enable symbol-listp append))))

(defruled int-div-symbol-listp-of-div-wires
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u))
           (symbol-listp (append xs ys qs rs (list m) ds (list d u))))
  :hints (("Goal"
           :in-theory (enable int-div-symbol-listp-of-append
                              symbol-listp))))

(defruled int-unsigned-div-pfcs-para-is-names
  (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
    (equal (pfcs::definition->para (int-unsigned-div-pfcs-def n))
           (int-div-names
            (append xs ys qs rs (list 'm) ds (list 'd 'u)))))
  :hints (("Goal"
           :in-theory (enable int-unsigned-div-pfcs-def
                              int-unsigned-div-wires
                              int-div-names-of-append
                              int-div-names))))

(defruled int-unsigned-div-pfcs-body-is
  (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
    (equal (pfcs::definition->body (int-unsigned-div-pfcs-def n))
           (int-unsigned-div-pfcs-body xs ys qs rs 'm ds 'd 'u
                                       (base-prime))))
  :hints (("Goal"
           :in-theory (enable int-unsigned-div-pfcs-def
                              int-unsigned-div-wires))))

(defruled int-unsigned-div-pfcs-def-no-dups
  (implies (member-equal (nfix n) '(8 16 32 64))
           (no-duplicatesp-equal
            (pfcs::definition->para (int-unsigned-div-pfcs-def n))))
  :hints (("Goal"
           :in-theory (enable (:e int-unsigned-div-pfcs-def)
                              (:e pfcs::definition->para)
                              (:e no-duplicatesp-equal)
                              member-equal
                              nfix))))

(defruled int-unsigned-div-names-no-dups
  (implies (member-equal (nfix n) '(8 16 32 64))
           (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
             (no-duplicatesp-equal
              (int-div-names
               (append xs ys qs rs (list 'm) ds (list 'd 'u))))))
  :hints (("Goal"
           :in-theory (enable (:e int-unsigned-div-wires)
                              (:e int-div-names)
                              (:e append)
                              (:e no-duplicatesp-equal)
                              member-equal
                              nfix))))

(defruled int-div-primep-of-base
  (implies (equal p (base-prime))
           (primep p))
  :use primep-of-base-prime)

(defruled int-div-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp asg nil)
  :hints (("Goal" :in-theory (enable r1cs::valuation-binds-allp))))

(defruled int-div-fe-listp-of-lookup-equal-list
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (pfield::fe-listp (lookup-equal-list xs asg) p))
  :hints (("Goal"
           :in-theory (enable lookup-equal-list
                              r1cs::valuation-binds-allp
                              pfield::fe-listp
                              r1cs::fep-of-lookup-equal))))

(defruled int-div-fe-listp-of-div-lookups
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp
                 asg (append xs ys qs rs (list m) ds (list d u))))
           (pfield::fe-listp
            (append (lookup-equal-list xs asg)
                    (lookup-equal-list ys asg)
                    (lookup-equal-list qs asg)
                    (lookup-equal-list rs asg)
                    (lookup-equal-list (list m) asg)
                    (lookup-equal-list ds asg)
                    (lookup-equal-list (list d u) asg))
            p))
  :hints (("Goal"
           :use ((:instance int-div-fe-listp-of-lookup-equal-list
                            (xs (append xs ys qs rs (list m) ds (list d u)))))
           :in-theory (e/d (int-div-symbol-listp-of-div-wires
                            lookup-equal-list-of-append
                            lookup-equal-list
                            r1cs::valuation-binds-allp-of-append
                            r1cs::valuation-binds-allp-of-cons
                            int-div-valuation-binds-allp-of-nil)
                           (acl2::append-of-cons
                            acl2::associativity-of-append
                            acl2::append-when-not-consp)))))

(defruled int-div-nat-listp-of-div-lookups
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp
                 asg (append xs ys qs rs (list m) ds (list d u))))
           (nat-listp
            (append (lookup-equal-list xs asg)
                    (lookup-equal-list ys asg)
                    (lookup-equal-list qs asg)
                    (lookup-equal-list rs asg)
                    (lookup-equal-list (list m) asg)
                    (lookup-equal-list ds asg)
                    (lookup-equal-list (list d u) asg))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance pfield::nat-listp-when-fe-listp
                            (x (append (lookup-equal-list xs asg)
                                       (lookup-equal-list ys asg)
                                       (lookup-equal-list qs asg)
                                       (lookup-equal-list rs asg)
                                       (lookup-equal-list (list m) asg)
                                       (lookup-equal-list ds asg)
                                       (lookup-equal-list (list d u) asg)))
                            (p p)))
           :in-theory (e/d (int-div-fe-listp-of-div-lookups)
                           (acl2::append-of-cons
                            acl2::associativity-of-append
                            acl2::append-when-not-consp
                            (:definition binary-append)
                            acl2::list-fix-when-true-listp
                            pfield::fe-listp-of-append)))))

(defruled int-div-assoc-when-lookup-singleton
  (implies (int-div-names-match (list x)
                                (lookup-equal-list (list x) asg)
                                pasg)
           (and (equal (cdr (omap::assoc (int-div-sym-name x) pasg))
                       (lookup-equal x asg))
                (consp (omap::assoc (int-div-sym-name x) pasg))))
  :hints (("Goal" :in-theory (enable int-div-names-match lookup-equal-list))))

(defruled int-div-assoc-when-lookup-two
  (implies (int-div-names-match (list x y)
                                (lookup-equal-list (list x y) asg)
                                pasg)
           (and (equal (cdr (omap::assoc (int-div-sym-name x) pasg))
                       (lookup-equal x asg))
                (consp (omap::assoc (int-div-sym-name x) pasg))
                (equal (cdr (omap::assoc (int-div-sym-name y) pasg))
                       (lookup-equal y asg))
                (consp (omap::assoc (int-div-sym-name y) pasg))))
  :hints (("Goal" :in-theory (enable int-div-names-match lookup-equal-list))))

(defruled int-div-assoc-when-names-match-singleton
  (implies (int-div-names-match (list x) (list v) pasg)
           (and (equal (cdr (omap::assoc (int-div-sym-name x) pasg)) v)
                (consp (omap::assoc (int-div-sym-name x) pasg))))
  :hints (("Goal" :in-theory (enable int-div-names-match))))

(defruled int-div-assoc-when-names-match-two
  (implies (int-div-names-match (list x y) (list vx vy) pasg)
           (and (equal (cdr (omap::assoc (int-div-sym-name x) pasg)) vx)
                (consp (omap::assoc (int-div-sym-name x) pasg))
                (equal (cdr (omap::assoc (int-div-sym-name y) pasg)) vy)
                (consp (omap::assoc (int-div-sym-name y) pasg))))
  :hints (("Goal" :in-theory (enable int-div-names-match))))

(defruled int-div-definition-satp-iff-body
  (implies (and (primep p)
                (pfcs::definitionp def)
                (equal (pfcs::lookup-definition
                        (pfcs::definition->name def) defs)
                       def)
                (set::emptyp (pfcs::definition-free-vars def))
                (no-duplicatesp-equal (pfcs::definition->para def))
                (pfield::fe-listp vals p)
                (equal (len vals) (len (pfcs::definition->para def))))
           (equal (pfcs::definition-satp
                   (pfcs::definition->name def) defs vals p)
                  (pfcs::constraint-list-satp
                   (pfcs::definition->body def)
                   defs
                   (omap::from-lists (pfcs::definition->para def) vals)
                   p)))
  :hints (("Goal"
           :in-theory (enable pfcs::definition-satp
                              pfcs::constraint-satp-of-relation-when-nofreevars
                              pfcs::constraint-relation-nofreevars-satp
                              pfcs::eval-expr-list-of-expression-var-list-and-omap-from-lists
                              pfcs::assignmentp-of-from-lists
                              pfcs::assignment-wfp-of-from-lists
                              pfield::nat-listp-when-fe-listp
                              pfcs::definition->name
                              pfcs::definition->para
                              pfcs::definition->body))))

(defruled int-unsigned-div-from-lists-iff-r1cs
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp
                 asg (append xs ys qs rs (list m) ds (list d u)))
                (no-duplicatesp-equal
                 (int-div-names
                  (append xs ys qs rs (list m) ds (list d u)))))
           (equal (pfcs::constraint-list-satp
                   (int-unsigned-div-pfcs-body xs ys qs rs m ds d u p)
                   defs
                   (omap::from-lists
                    (int-div-names
                     (append xs ys qs rs (list m) ds (list d u)))
                    (lookup-equal-list
                     (append xs ys qs rs (list m) ds (list d u))
                     asg))
                   p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-div-gadget xs ys qs rs m ds d u p)
                   asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-div-names-match-of-from-lists
                            (xs (append xs ys qs rs (list m) ds (list d u)))
                            (vals (append (lookup-equal-list xs asg)
                                          (lookup-equal-list ys asg)
                                          (lookup-equal-list qs asg)
                                          (lookup-equal-list rs asg)
                                          (lookup-equal-list (list m) asg)
                                          (lookup-equal-list ds asg)
                                          (lookup-equal-list (list d u) asg))))
                 (:instance int-unsigned-div-pfcs-body-iff-r1cs
                            (pasg (omap::from-lists
                                   (int-div-names
                                    (append xs ys qs rs
                                            (list m) ds (list d u)))
                                   (append (lookup-equal-list xs asg)
                                           (lookup-equal-list ys asg)
                                           (lookup-equal-list qs asg)
                                           (lookup-equal-list rs asg)
                                           (lookup-equal-list (list m) asg)
                                           (lookup-equal-list ds asg)
                                           (lookup-equal-list (list d u) asg))))))
           :in-theory (e/d (int-div-names-match-of-append
                            int-div-assoc-when-lookup-singleton
                            int-div-assoc-when-lookup-two
                            int-div-symbol-listp-of-div-wires
                            int-div-fe-listp-of-div-lookups
                            int-div-nat-listp-of-div-lookups
                            lookup-equal-list-of-append
                            len-of-lookup-equal-list
                            len-of-int-div-names
                            len
                            pfcs::assignmentp-of-from-lists
                            pfcs::assignment-wfp-of-from-lists
                            pfield::nat-listp-when-fe-listp
                            r1cs::valuation-binds-allp-of-append
                            r1cs::valuation-binds-allp-of-cons
                            int-div-valuation-binds-allp-of-nil)
                           (acl2::append-of-cons
                            acl2::associativity-of-append
                            acl2::append-when-not-consp
                            (:definition binary-append)
                            (:definition lookup-equal-list)
                            acl2::list-fix-when-true-listp
                            pfield::fe-listp-of-append)))))

(defruled int-unsigned-div-defsat-iff-r1cs
  (implies (and (member-equal (nfix n) '(8 16 32 64))
                (equal p (base-prime))
                (equal (pfcs::lookup-definition
                        (pfcs::definition->name
                         (int-unsigned-div-pfcs-def n))
                        defs)
                       (int-unsigned-div-pfcs-def n))
                (r1cs::r1cs-valuationp asg p)
                (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
                  (r1cs::valuation-binds-allp
                   asg (append xs ys qs rs (list 'm) ds (list 'd 'u)))))
           (b* (((mv xs ys qs rs ds) (int-unsigned-div-wires n)))
             (equal (pfcs::definition-satp
                     (pfcs::definition->name (int-unsigned-div-pfcs-def n))
                     defs
                     (lookup-equal-list
                      (append xs ys qs rs (list 'm) ds (list 'd 'u))
                      asg)
                     p)
                    (r1cs::r1cs-constraints-holdp
                     (unsigned-small-div-gadget xs ys qs rs 'm ds 'd 'u p)
                     asg p))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-div-definition-satp-iff-body
                            int-unsigned-div-from-lists-iff-r1cs
                            int-unsigned-div-pfcs-def-no-free
                            int-unsigned-div-pfcs-def-no-dups
                            int-unsigned-div-names-no-dups
                            int-unsigned-div-pfcs-para-is-names
                            int-unsigned-div-pfcs-body-is
                            int-div-primep-of-base
                            int-div-fe-listp-of-lookup-equal-list
                            int-div-symbol-listp-of-div-wires
                            len-of-lookup-equal-list
                            len-of-int-div-names)
                           ((:e int-unsigned-div-pfcs-def)
                            (:e int-unsigned-div-wires)
                            (:e int-unsigned-div-pfcs-body)
                            (:e unsigned-small-div-gadget)
                            (:e int-div-indexed-syms)
                            (:definition lookup-equal-list)
                            (:definition binary-append)
                            (:definition member-equal)
                            acl2::append-of-cons
                            acl2::associativity-of-append
                            acl2::append-when-not-consp
                            acl2::member-of-cons
                            acl2::member-when-atom
                            member-equal
                            nfix
                            r1cs::valuation-binds-allp-of-append
                            r1cs::valuation-binds-allp-of-cons)))))
