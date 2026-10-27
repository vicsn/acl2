; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Linear combinations and field multiplication, as snarkVM synthesizes them.
;
; A snarkVM Field is a LinearCombination: a constant plus terms
; (variable, coefficient).  Addition and multiplication by a constant build a
; new linear combination and emit no constraint; AddAssign merges terms by
; variable and drops a term whose coefficient becomes zero, and Mul<F> drops
; terms whose coefficient becomes zero (circuit/environment/src/helpers/
; linear_combination.rs).  A Field is constant iff it has no terms.  Field
; multiplication (circuit/types/field/src/mul.rs) scales when either side is
; constant and otherwise witnesses a new variable w with the constraint
; (a) * (b) = (w).
;
; Here a linear combination is (const . terms), terms an alist from variables
; to coefficients.  hpos-lc-sv is the R1CS sparse vector of it; its value
; under an assignment is r1cs::dot-product of that vector.
;
; The synthesis functions take a supply vs of fresh variable names and an
; assignment asg, and return the output, the constraints, the remaining
; supply, and asg extended with the witness values snarkVM computes.  The
; constraints and outputs do not depend on asg.  Soundness theorems hold for
; every assignment satisfying the constraints; completeness theorems show
; that the extended asg satisfies them.

(in-package "ALEOVM")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/pow" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Linear combinations.

(defund hpos-pv (v)
  (declare (xargs :verify-guards nil))
  (if (symbolp v) v 1))

(defund hpos-terms-sv (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms)
      nil
    (cons (list (ifix (cdr (car terms)))
                (hpos-pv (car (car terms))))
          (hpos-terms-sv (cdr terms)))))

(defund hpos-lc-sv (lc)
  (declare (xargs :verify-guards nil))
  (cons (list (ifix (car lc)) 1)
        (hpos-terms-sv (cdr lc))))

(defrule hpos-sparse-vectorp-of-hpos-terms-sv
  (r1cs::sparse-vectorp (hpos-terms-sv terms))
  :enable (hpos-terms-sv hpos-pv))

(defrule hpos-sparse-vectorp-of-hpos-lc-sv
  (r1cs::sparse-vectorp (hpos-lc-sv lc))
  :enable hpos-lc-sv)

(defund hpos-lc-eval (lc asg p)
  (declare (xargs :verify-guards nil))
  (r1cs::dot-product (hpos-lc-sv lc) asg p))

(defund hpos-lc-eval-list (lcs asg p)
  (declare (xargs :verify-guards nil))
  (if (atom lcs)
      nil
    (cons (hpos-lc-eval (car lcs) asg p)
          (hpos-lc-eval-list (cdr lcs) asg p))))

(defrule hpos-len-of-hpos-lc-eval-list
  (equal (len (hpos-lc-eval-list lcs asg p)) (len lcs))
  :enable hpos-lc-eval-list)

(defund hpos-terms-eval (terms asg p)
  (declare (xargs :verify-guards nil))
  (r1cs::dot-product (hpos-terms-sv terms) asg p))

(defund hpos-var-val (v asg)
  (declare (xargs :verify-guards nil))
  (if (equal (hpos-pv v) 1) 1 (lookup-equal (hpos-pv v) asg)))

(defrule hpos-fep-of-hpos-lc-eval
  (implies (posp p) (pfield::fep (hpos-lc-eval lc asg p) p))
  :enable hpos-lc-eval)

(defrule hpos-fep-of-hpos-terms-eval
  (implies (posp p) (pfield::fep (hpos-terms-eval terms asg p) p))
  :enable hpos-terms-eval)

(defrule hpos-lc-eval-decomp
  (implies (posp p)
           (equal (hpos-lc-eval lc asg p)
                  (pfield::add (mod (ifix (car lc)) p)
                               (hpos-terms-eval (cdr lc) asg p)
                               p)))
  :enable (hpos-lc-eval hpos-lc-sv hpos-terms-eval r1cs::dot-product))

(defruled hpos-terms-eval-of-cons
  (implies (posp p)
           (equal (hpos-terms-eval (cons term terms) asg p)
                  (pfield::add (pfield::mul (mod (ifix (cdr term)) p)
                                            (hpos-var-val (car term) asg)
                                            p)
                               (hpos-terms-eval terms asg p)
                               p)))
  :enable (hpos-terms-eval hpos-terms-sv hpos-var-val r1cs::dot-product
           hpos-pv))

(defruled hpos-terms-eval-when-consp
  (implies (and (posp p) (consp terms))
           (equal (hpos-terms-eval terms asg p)
                  (pfield::add (pfield::mul (mod (ifix (cdr (car terms))) p)
                                            (hpos-var-val (car (car terms)) asg)
                                            p)
                               (hpos-terms-eval (cdr terms) asg p)
                               p)))
  :use (:instance hpos-terms-eval-of-cons (term (car terms)) (terms (cdr terms))))

(defrule hpos-terms-eval-of-atom
  (implies (atom terms)
           (equal (hpos-terms-eval terms asg p) 0))
  :enable (hpos-terms-eval hpos-terms-sv r1cs::dot-product))

(defund hpos-lc-const (c)
  (declare (xargs :verify-guards nil))
  (cons c nil))

(defund hpos-lc-constp (lc)
  (declare (xargs :verify-guards nil))
  (atom (cdr lc)))

(defrule hpos-lc-eval-of-hpos-lc-const
  (implies (posp p)
           (equal (hpos-lc-eval (hpos-lc-const c) asg p)
                  (mod (ifix c) p)))
  :enable hpos-lc-const)

(defrule hpos-lc-eval-when-hpos-lc-constp
  (implies (and (posp p) (hpos-lc-constp lc))
           (equal (hpos-lc-eval lc asg p)
                  (mod (ifix (car lc)) p)))
  :enable hpos-lc-constp)

(defund hpos-lc-var (v)
  (declare (xargs :verify-guards nil))
  (cons 0 (list (cons v 1))))

(defrule hpos-lc-eval-of-hpos-lc-var
  (implies (and (posp p) (symbolp v))
           (equal (hpos-lc-eval (hpos-lc-var v) asg p)
                  (mod (ifix (lookup-equal v asg)) p)))
  :enable (hpos-lc-var hpos-terms-eval-of-cons hpos-var-val hpos-pv))

;; Adding one term, merging by variable.

(defund hpos-terms-add-term (v c terms p)
  (declare (xargs :verify-guards nil))
  (cond ((atom terms)
         (if (equal (mod (ifix c) p) 0)
             nil
           (list (cons v (mod (ifix c) p)))))
        ((equal (car (car terms)) v)
         (let ((nc (pfield::add (ifix (cdr (car terms))) (ifix c) p)))
           (if (equal nc 0)
               (cdr terms)
             (cons (cons v nc) (cdr terms)))))
        (t (cons (car terms) (hpos-terms-add-term v c (cdr terms) p)))))

(defrule hpos-terms-eval-of-hpos-terms-add-term
  (implies (posp p)
           (equal (hpos-terms-eval (hpos-terms-add-term v c terms p) asg p)
                  (pfield::add (hpos-terms-eval terms asg p)
                               (pfield::mul (mod (ifix c) p)
                                            (hpos-var-val v asg)
                                            p)
                               p)))
  :induct (hpos-terms-add-term v c terms p)
  :enable (hpos-terms-add-term hpos-terms-eval-of-cons hpos-terms-eval-when-consp)
  :prep-lemmas
  ((defrule hpos-mul-add-zero-lemma
     (implies (and (posp p)
                   (equal (pfield::add a c p) 0))
              (equal (pfield::add (pfield::mul a v p) (pfield::mul c v p) p)
                     0))
     :use (:instance pfield::mul-of-add-arg1 (pfield::y1 a) (pfield::y2 c) (pfield::x v) (pfield::p p))
     :disable pfield::mul-of-add-arg1)))

(defund hpos-terms-add (terms other p)
  (declare (xargs :verify-guards nil))
  (if (atom other)
      terms
    (hpos-terms-add (hpos-terms-add-term (car (car other))
                                         (cdr (car other))
                                         terms p)
                    (cdr other) p)))

(defrule hpos-terms-eval-of-hpos-terms-add
  (implies (posp p)
           (equal (hpos-terms-eval (hpos-terms-add terms other p) asg p)
                  (pfield::add (hpos-terms-eval terms asg p)
                               (hpos-terms-eval other asg p)
                               p)))
  :induct (hpos-terms-add terms other p)
  :enable (hpos-terms-add hpos-terms-eval-of-cons))

(defund hpos-lc-add (a b p)
  (declare (xargs :verify-guards nil))
  (cons (pfield::add (ifix (car a)) (ifix (car b)) p)
        (hpos-terms-add (cdr a) (cdr b) p)))

(defrule hpos-lc-eval-of-hpos-lc-add
  (implies (posp p)
           (equal (hpos-lc-eval (hpos-lc-add a b p) asg p)
                  (pfield::add (hpos-lc-eval a asg p)
                               (hpos-lc-eval b asg p)
                               p)))
  :enable hpos-lc-add)

;; Multiplication by a constant.

(defund hpos-terms-scale (terms k p)
  (declare (xargs :verify-guards nil))
  (if (atom terms)
      nil
    (let ((nc (pfield::mul (ifix (cdr (car terms))) (ifix k) p)))
      (if (equal nc 0)
          (hpos-terms-scale (cdr terms) k p)
        (cons (cons (car (car terms)) nc)
              (hpos-terms-scale (cdr terms) k p))))))

(defrule hpos-terms-eval-of-hpos-terms-scale
  (implies (posp p)
           (equal (hpos-terms-eval (hpos-terms-scale terms k p) asg p)
                  (pfield::mul (hpos-terms-eval terms asg p)
                               (mod (ifix k) p)
                               p)))
  :induct (hpos-terms-scale terms k p)
  :enable (hpos-terms-scale hpos-terms-eval-of-cons hpos-terms-eval-when-consp)
  :prep-lemmas
  ((defrule hpos-mul-zero-lemma
     (implies (and (posp p)
                   (equal (pfield::mul k a p) 0))
              (equal (pfield::mul k (pfield::mul a v p) p) 0))
     :use (:instance pfield::mul-associative (pfield::x k) (pfield::y a) (pfield::z v) (pfield::p p))
     :disable pfield::mul-associative)))

(defund hpos-lc-scale (a k p)
  (declare (xargs :verify-guards nil))
  (cons (pfield::mul (ifix (car a)) (ifix k) p)
        (hpos-terms-scale (cdr a) k p)))

(defrule hpos-lc-eval-of-hpos-lc-scale
  (implies (posp p)
           (equal (hpos-lc-eval (hpos-lc-scale a k p) asg p)
                  (pfield::mul (hpos-lc-eval a asg p)
                               (mod (ifix k) p)
                               p)))
  :enable hpos-lc-scale)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bound variables and assignment extension.

(defund hpos-sv-boundp (sv asg)
  (declare (xargs :verify-guards nil))
  (if (atom sv)
      t
    (and (or (equal (cadr (car sv)) 1)
             (r1cs::valuation-bindsp asg (cadr (car sv))))
         (hpos-sv-boundp (cdr sv) asg))))

(defund hpos-lc-boundp (lc asg)
  (declare (xargs :verify-guards nil))
  (hpos-sv-boundp (hpos-lc-sv lc) asg))

(defund hpos-lc-list-boundp (lcs asg)
  (declare (xargs :verify-guards nil))
  (if (atom lcs)
      t
    (and (hpos-lc-boundp (car lcs) asg)
         (hpos-lc-list-boundp (cdr lcs) asg))))

(defund hpos-cs-boundp (cs asg)
  (declare (xargs :verify-guards nil))
  (if (atom cs)
      t
    (and (hpos-sv-boundp (r1cs::r1cs-constraint->a (car cs)) asg)
         (hpos-sv-boundp (r1cs::r1cs-constraint->b (car cs)) asg)
         (hpos-sv-boundp (r1cs::r1cs-constraint->c (car cs)) asg)
         (hpos-cs-boundp (cdr cs) asg))))

(defrule hpos-cs-boundp-of-append
  (equal (hpos-cs-boundp (append x y) asg)
         (and (hpos-cs-boundp x asg) (hpos-cs-boundp y asg)))
  :enable hpos-cs-boundp)

; new extends old: old is a tail of new.
(defund hpos-ext-p (old new)
  (declare (xargs :verify-guards nil))
  (if (equal old new)
      t
    (and (consp new)
         (hpos-ext-p old (cdr new)))))

(defrule hpos-ext-p-reflexive
  (hpos-ext-p x x)
  :enable hpos-ext-p)

(defrule hpos-ext-p-of-acons
  (implies (hpos-ext-p old new)
           (hpos-ext-p old (cons pair new)))
  :enable hpos-ext-p)

(defrule hpos-ext-p-transitive
  (implies (and (hpos-ext-p a b) (hpos-ext-p b c))
           (hpos-ext-p a c))
  :induct (hpos-ext-p b c)
  :enable hpos-ext-p)

(defrule hpos-ext-p-member-strip-cars
  (implies (and (hpos-ext-p old new)
                (member-equal v (strip-cars old)))
           (member-equal v (strip-cars new)))
  :induct (hpos-ext-p old new)
  :enable hpos-ext-p)

(defrule hpos-valuation-bindsp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (r1cs::valuation-bindsp old v))
           (r1cs::valuation-bindsp new v))
  :enable r1cs::valuation-bindsp)

(defrule hpos-lookup-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (member-equal v (strip-cars old)))
           (equal (lookup-equal v new)
                  (lookup-equal v old)))
  :induct (hpos-ext-p old new)
  :enable (hpos-ext-p lookup-equal))

(defrule hpos-sv-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-sv-boundp sv old))
           (hpos-sv-boundp sv new))
  :enable hpos-sv-boundp)

(defrule hpos-lc-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-lc-boundp lc old))
           (hpos-lc-boundp lc new))
  :enable hpos-lc-boundp)

(defrule hpos-lc-list-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-lc-list-boundp lcs old))
           (hpos-lc-list-boundp lcs new))
  :enable hpos-lc-list-boundp)

(defrule hpos-cs-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-cs-boundp cs old))
           (hpos-cs-boundp cs new))
  :enable hpos-cs-boundp)

(defrule hpos-dot-product-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (hpos-sv-boundp sv old))
           (equal (r1cs::dot-product sv new p)
                  (r1cs::dot-product sv old p)))
  :enable (hpos-sv-boundp r1cs::dot-product r1cs::valuation-bindsp))

(defrule hpos-lc-eval-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (hpos-lc-boundp lc old))
           (equal (hpos-lc-eval lc new p)
                  (hpos-lc-eval lc old p)))
  :enable (hpos-lc-eval hpos-lc-boundp)
  :disable hpos-lc-eval-decomp)

(defrule hpos-lc-eval-list-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (hpos-lc-list-boundp lcs old))
           (equal (hpos-lc-eval-list lcs new p)
                  (hpos-lc-eval-list lcs old p)))
  :enable (hpos-lc-eval-list hpos-lc-list-boundp))

(defrule hpos-holdp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (hpos-cs-boundp cs old))
           (equal (r1cs::r1cs-constraints-holdp cs new p)
                  (r1cs::r1cs-constraints-holdp cs old p)))
  :enable (hpos-cs-boundp r1cs::r1cs-constraint-holdsp))

;; Bound variables of linear combination operations.

(defund hpos-terms-boundp (terms asg)
  (declare (xargs :verify-guards nil))
  (if (atom terms)
      t
    (and (or (equal (hpos-pv (car (car terms))) 1)
             (r1cs::valuation-bindsp asg (hpos-pv (car (car terms)))))
         (hpos-terms-boundp (cdr terms) asg))))

(defrule hpos-sv-boundp-of-hpos-terms-sv
  (equal (hpos-sv-boundp (hpos-terms-sv terms) asg)
         (hpos-terms-boundp terms asg))
  :enable (hpos-sv-boundp hpos-terms-sv hpos-terms-boundp))

(defruled hpos-lc-boundp-alt
  (equal (hpos-lc-boundp lc asg)
         (hpos-terms-boundp (cdr lc) asg))
  :enable (hpos-lc-boundp hpos-lc-sv hpos-sv-boundp))

(defrule hpos-terms-boundp-of-hpos-terms-add-term
  (implies (and (hpos-terms-boundp terms asg)
                (or (equal (hpos-pv v) 1)
                    (r1cs::valuation-bindsp asg (hpos-pv v))))
           (hpos-terms-boundp (hpos-terms-add-term v c terms p) asg))
  :enable (hpos-terms-add-term hpos-terms-boundp))

(defrule hpos-terms-boundp-of-hpos-terms-add
  (implies (and (hpos-terms-boundp terms asg)
                (hpos-terms-boundp other asg))
           (hpos-terms-boundp (hpos-terms-add terms other p) asg))
  :induct (hpos-terms-add terms other p)
  :enable (hpos-terms-add hpos-terms-boundp))

(defrule hpos-terms-boundp-of-hpos-terms-scale
  (implies (hpos-terms-boundp terms asg)
           (hpos-terms-boundp (hpos-terms-scale terms k p) asg))
  :enable (hpos-terms-scale hpos-terms-boundp))

(defrule hpos-lc-boundp-of-hpos-lc-add
  (implies (and (hpos-lc-boundp a asg) (hpos-lc-boundp b asg))
           (hpos-lc-boundp (hpos-lc-add a b p) asg))
  :enable (hpos-lc-add hpos-lc-boundp-alt))

(defrule hpos-lc-boundp-of-hpos-lc-scale
  (implies (hpos-lc-boundp a asg)
           (hpos-lc-boundp (hpos-lc-scale a k p) asg))
  :enable (hpos-lc-scale hpos-lc-boundp-alt))

(defrule hpos-lc-boundp-of-hpos-lc-const
  (hpos-lc-boundp (hpos-lc-const c) asg)
  :enable (hpos-lc-const hpos-terms-boundp hpos-lc-boundp-alt))

(defrule hpos-lc-boundp-when-hpos-lc-constp
  (implies (hpos-lc-constp lc)
           (hpos-lc-boundp lc asg))
  :enable (hpos-lc-constp hpos-terms-boundp hpos-lc-boundp-alt))

(defrule hpos-lc-boundp-of-hpos-lc-var
  (implies (and (symbolp w) (r1cs::valuation-bindsp asg w))
           (hpos-lc-boundp (hpos-lc-var w) asg))
  :enable (hpos-lc-var hpos-terms-boundp hpos-pv hpos-lc-boundp-alt))

(defrule hpos-lc-boundp-of-cons-asg
  (implies (hpos-lc-boundp lc asg)
           (hpos-lc-boundp lc (cons pair asg)))
  :use (:instance hpos-lc-boundp-when-ext-p (old asg) (new (cons pair asg))))

(defrule hpos-lc-eval-of-cons-asg
  (implies (and (hpos-lc-boundp lc asg)
                (no-duplicatesp-equal (strip-cars asg))
                (not (member-equal w (strip-cars asg))))
           (equal (hpos-lc-eval lc (cons (cons w v) asg) p)
                  (hpos-lc-eval lc asg p)))
  :use (:instance hpos-lc-eval-when-ext-p (old asg) (new (cons (cons w v) asg))))

(defrule hpos-sv-boundp-of-hpos-lc-sv
  (equal (hpos-sv-boundp (hpos-lc-sv lc) asg)
         (hpos-lc-boundp lc asg))
  :enable hpos-lc-boundp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fresh-variable supply and the completeness invariant.

(defund hpos-supply-okp (vs asg)
  (declare (xargs :verify-guards nil))
  (and (symbol-listp vs)
       (no-duplicatesp-equal vs)
       (not (intersectp-equal vs (strip-cars asg)))))

; asg2, vs2 and cs come from asg, vs by synthesis with witness generation.
(defund hpos-wit-okp (asg vs asg2 vs2 cs p)
  (declare (xargs :verify-guards nil))
  (and (r1cs::r1cs-valuationp asg2 p)
       (hpos-ext-p asg asg2)
       (hpos-ext-p vs2 vs)
       (hpos-supply-okp vs2 asg2)
       (r1cs::r1cs-constraints-holdp cs asg2 p)
       (hpos-cs-boundp cs asg2)))

(defrule hpos-wit-okp-nil
  (implies (and (r1cs::r1cs-valuationp asg p)
                (hpos-supply-okp vs asg))
           (hpos-wit-okp asg vs asg vs nil p))
  :enable (hpos-wit-okp hpos-cs-boundp))

(defrule hpos-wit-okp-append
  (implies (and (hpos-wit-okp asg vs asg1 vs1 cs1 p)
                (hpos-wit-okp asg1 vs1 asg2 vs2 cs2 p))
           (hpos-wit-okp asg vs asg2 vs2 (append cs1 cs2) p))
  :enable hpos-wit-okp
  :use (:instance hpos-holdp-when-ext-p (old asg1) (new asg2) (cs cs1)))

(defrule hpos-wit-okp-forward
  (implies (hpos-wit-okp asg vs asg2 vs2 cs p)
           (and (r1cs::r1cs-valuationp asg2 p)
                (hpos-ext-p asg asg2)
                (hpos-supply-okp vs2 asg2)))
  :rule-classes :forward-chaining
  :enable hpos-wit-okp)

(defrule hpos-no-duplicatesp-strip-cars-when-valuationp
  (implies (r1cs::r1cs-valuationp asg p)
           (no-duplicatesp-equal (strip-cars asg)))
  :enable r1cs::r1cs-valuationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field::mul (MulAssign): returns (mv out cs vs asg).

(defund hpos-mul (a b vs asg p)
  (declare (xargs :verify-guards nil))
  (cond ((hpos-lc-constp b) (mv (hpos-lc-scale a (car b) p) nil vs asg))
        ((hpos-lc-constp a) (mv (hpos-lc-scale b (car a) p) nil vs asg))
        (t (let* ((w (car vs))
                  (out (hpos-lc-var w)))
             (mv out
                 (list (r1cs::make-r1cs-constraint :a (hpos-lc-sv a)
                                                   :b (hpos-lc-sv b)
                                                   :c (hpos-lc-sv out)))
                 (cdr vs)
                 (acons w (pfield::mul (hpos-lc-eval a asg p)
                                       (hpos-lc-eval b asg p)
                                       p)
                        asg))))))

(defrule hpos-mul-sound
  (b* (((mv out cs & &) (hpos-mul a b vs asg p)))
    (implies (and (posp p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval out asgx p)
                    (pfield::mul (hpos-lc-eval a asgx p)
                                 (hpos-lc-eval b asgx p)
                                 p))))
  :enable (hpos-mul r1cs::r1cs-constraint-holdsp)
  :disable hpos-lc-eval-decomp
  :prep-lemmas
  ((defrule hpos-lc-eval-of-car-when-constp
     (implies (and (posp p) (hpos-lc-constp lc))
              (equal (mod (ifix (car lc)) p)
                     (hpos-lc-eval lc asg p))))
   (defrule hpos-eval-is-dot
     (equal (r1cs::dot-product (hpos-lc-sv lc) asg p)
            (hpos-lc-eval lc asg p))
     :enable hpos-lc-eval)))

(defrule hpos-mul-vs-len
  (b* (((mv & & vs2 &) (hpos-mul a b vs asg p)))
    (and (<= (- (len vs) 1) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable hpos-mul)

(defrule hpos-mul-complete
  (b* (((mv out cs vs2 asg2) (hpos-mul a b vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (consp vs)
                  (hpos-lc-boundp a asg)
                  (hpos-lc-boundp b asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-boundp out asg2))))
  :enable (hpos-mul hpos-wit-okp hpos-supply-okp hpos-cs-boundp
           r1cs::r1cs-constraint-holdsp r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable hpos-lc-eval-decomp
  :prep-lemmas
  ((defrule hpos-eval-is-dot-2
     (equal (r1cs::dot-product (hpos-lc-sv lc) asg p)
            (hpos-lc-eval lc asg p))
     :enable hpos-lc-eval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field::pow with a constant exponent whose big-endian bits are BITS
;; (circuit/types/field/src/pow.rs): output = 1; for each bit,
;; output = output.square(), then output *= self if the bit is set.

(defund hpos-bits-val (e bits)
  (declare (xargs :verify-guards nil))
  (if (atom bits)
      (nfix e)
    (hpos-bits-val (+ (nfix e) (nfix e) (if (equal (car bits) 1) 1 0))
                   (cdr bits))))

(defrule hpos-natp-of-hpos-bits-val
  (natp (hpos-bits-val e bits))
  :rule-classes :type-prescription
  :enable hpos-bits-val)

(defund hpos-pow-fold (x acc bits p)
  (declare (xargs :verify-guards nil))
  (if (atom bits)
      acc
    (let* ((sq (pfield::mul acc acc p))
           (acc (if (equal (car bits) 1) (pfield::mul sq x p) sq)))
      (hpos-pow-fold x acc (cdr bits) p))))

(defrule hpos-pow-fold-is-pow
  (implies (and (dm::primep p) (pfield::fep x p) (natp e))
           (equal (hpos-pow-fold x (pfield::pow x e p) bits p)
                  (pfield::pow x (hpos-bits-val e bits) p)))
  :induct (hpos-bits-val e bits)
  :enable (hpos-pow-fold hpos-bits-val)
  :disable (pfield::pow-of-+ pfield::pow-of-+-same-arg1-arg1)
  :prep-lemmas
  ((defrule hpos-pow-double
     (implies (and (dm::primep p) (natp e) (pfield::fep x p))
              (equal (pfield::mul (pfield::pow x e p) (pfield::pow x e p) p)
                     (pfield::pow x (+ e e) p)))
     :use (:instance pfield::pow-of-+ (pfield::a x) (pfield::b e) (pfield::c e) (pfield::p p))
     :disable pfield::pow-of-+)
   (defrule hpos-pow-double-plus-1
     (implies (and (dm::primep p) (natp e) (pfield::fep x p))
              (equal (pfield::mul (pfield::pow x (+ e e) p) x p)
                     (pfield::pow x (+ 1 e e) p)))
     :use (:instance pfield::pow-of-+ (pfield::a x) (pfield::b (+ e e)) (pfield::c 1) (pfield::p p))
     :disable pfield::pow-of-+)))

(defrule hpos-pow-fold-from-1
  (implies (and (dm::primep p) (pfield::fep x p))
           (equal (hpos-pow-fold x 1 bits p)
                  (pfield::pow x (hpos-bits-val 0 bits) p)))
  :use (:instance hpos-pow-fold-is-pow (e 0))
  :disable hpos-pow-fold-is-pow)

(defund hpos-c-pow (x out bits vs asg p)
  (declare (xargs :verify-guards nil))
  (if (atom bits)
      (mv out nil vs asg)
    (b* (((mv sq cs1 vs asg) (hpos-mul out out vs asg p))
         ((mv o2 cs2 vs asg) (if (equal (car bits) 1)
                                 (hpos-mul sq x vs asg p)
                               (mv sq nil vs asg)))
         ((mv o3 cs3 vs asg) (hpos-c-pow x o2 (cdr bits) vs asg p)))
      (mv o3 (append cs1 cs2 cs3) vs asg))))

(defrule hpos-c-pow-sound
  (b* (((mv o cs & &) (hpos-c-pow x out bits vs asg p)))
    (implies (and (posp p)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval o asgx p)
                    (hpos-pow-fold (hpos-lc-eval x asgx p)
                                   (hpos-lc-eval out asgx p)
                                   bits p))))
  :induct (hpos-c-pow x out bits vs asg p)
  :enable (hpos-c-pow hpos-pow-fold)
  :disable hpos-lc-eval-decomp)

(defrule hpos-c-pow-vs-len
  (b* (((mv & & vs2 &) (hpos-c-pow x out bits vs asg p)))
    (and (<= (- (len vs) (* 2 (len bits))) (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :induct (hpos-c-pow x out bits vs asg p)
  :enable hpos-c-pow)

(defrule hpos-c-pow-complete
  (b* (((mv o cs vs2 asg2) (hpos-c-pow x out bits vs asg p)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (* 2 (len bits)) (len vs))
                  (hpos-lc-boundp x asg)
                  (hpos-lc-boundp out asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-boundp o asg2))))
  :induct (hpos-c-pow x out bits vs asg p)
  :enable hpos-c-pow
  :hints (("Subgoal *1/2"
           :use ((:instance hpos-mul-vs-len (a out) (b out))
                 (:instance hpos-mul-vs-len
                            (a (mv-nth 0 (hpos-mul out out vs asg p)))
                            (b x)
                            (vs (mv-nth 2 (hpos-mul out out vs asg p)))
                            (asg (mv-nth 3 (hpos-mul out out vs asg p))))
                 (:instance hpos-mul-complete (a out) (b out))
                 (:instance hpos-mul-complete
                            (a (mv-nth 0 (hpos-mul out out vs asg p)))
                            (b x)
                            (vs (mv-nth 2 (hpos-mul out out vs asg p)))
                            (asg (mv-nth 3 (hpos-mul out out vs asg p))))))))
