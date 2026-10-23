; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Substituting a linear combination for a variable in R1CS constraints.
;
; Gadgets in other books take their field inputs as variables, while
; snarkVM passes a linear combination (e.g. a Poseidon output) straight
; into the constraints of the callee.  hpos-cs-subst rewrites the callee's
; constraints in that way, and the satisfaction of the result is the
; satisfaction of the original under an assignment binding the variable to
; the value of the linear combination.

(in-package "ALEOVM")

(include-book "hpos-lc")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp)))

(defund hpos-sv-scale (c sv)
  (declare (xargs :verify-guards nil))
  (if (endp sv)
      nil
    (cons (list (* (ifix c) (ifix (first (first sv)))) (second (first sv)))
          (hpos-sv-scale c (rest sv)))))

(defund hpos-sv-subst (sv x lc)
  (declare (xargs :verify-guards nil))
  (cond ((endp sv) nil)
        ((equal (second (first sv)) x)
         (append (hpos-sv-scale (first (first sv)) (hpos-lc-sv lc))
                 (hpos-sv-subst (rest sv) x lc)))
        (t (cons (first sv) (hpos-sv-subst (rest sv) x lc)))))

(defrule hpos-dot-product-of-hpos-sv-scale
  (implies (and (posp p) (r1cs::sparse-vectorp sv))
           (equal (r1cs::dot-product (hpos-sv-scale c sv) asg p)
                  (pfield::mul (ifix c) (r1cs::dot-product sv asg p) p)))
  :induct (hpos-sv-scale c sv)
  :enable (hpos-sv-scale r1cs::dot-product r1cs::sparse-vectorp
           r1cs::sparse-vector-elementp pfield::mul pfield::add))

(defrulel hpos-lookup-equal-of-cons
  (equal (lookup-equal k (cons (cons k2 v) a))
         (if (equal k k2) v (lookup-equal k a)))
  :enable lookup-equal)

(defrule hpos-dot-product-of-hpos-sv-subst
  (implies (and (posp p)
                (symbolp x)
                (r1cs::sparse-vectorp sv))
           (equal (r1cs::dot-product (hpos-sv-subst sv x lc) asg p)
                  (r1cs::dot-product sv (acons x (hpos-lc-eval lc asg p) asg) p)))
  :induct (hpos-sv-subst sv x lc)
  :enable (hpos-sv-subst r1cs::dot-product r1cs::sparse-vectorp
           r1cs::sparse-vector-elementp hpos-lc-eval))

(defund hpos-c-subst (c x lc)
  (declare (xargs :verify-guards nil))
  (r1cs::make-r1cs-constraint
   :a (hpos-sv-subst (r1cs::r1cs-constraint->a c) x lc)
   :b (hpos-sv-subst (r1cs::r1cs-constraint->b c) x lc)
   :c (hpos-sv-subst (r1cs::r1cs-constraint->c c) x lc)))

(defund hpos-cs-subst (cs x lc)
  (declare (xargs :verify-guards nil))
  (if (endp cs)
      nil
    (cons (hpos-c-subst (car cs) x lc)
          (hpos-cs-subst (cdr cs) x lc))))

(defrule hpos-holdsp-of-hpos-c-subst
  (implies (and (posp p)
                (symbolp x)
                (r1cs::r1cs-constraintp c))
           (equal (r1cs::r1cs-constraint-holdsp (hpos-c-subst c x lc) asg p)
                  (r1cs::r1cs-constraint-holdsp
                   c (acons x (hpos-lc-eval lc asg p) asg) p)))
  :enable (hpos-c-subst r1cs::r1cs-constraint-holdsp r1cs::r1cs-constraintp))

(defrule hpos-holdp-of-hpos-cs-subst
  (implies (and (posp p)
                (symbolp x)
                (r1cs::r1cs-constraint-listp cs))
           (equal (r1cs::r1cs-constraints-holdp (hpos-cs-subst cs x lc) asg p)
                  (r1cs::r1cs-constraints-holdp
                   cs (acons x (hpos-lc-eval lc asg p) asg) p)))
  :induct (hpos-cs-subst cs x lc)
  :enable (hpos-cs-subst r1cs::r1cs-constraints-holdp))
