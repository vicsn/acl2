; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::add of two variable points, with witness generation, for
; Poseidon::hash_to_group.
;
; The constraints are crv-group-add-gadget (crv-curve.lisp).  A point is a
; cons of two variables (x . y).  The next 6 fresh variables are the
; products u, v0, v1, v01 and the output coordinates x3, y3, in snarkVM's
; allocation order; the witness is the canonical one of
; crv-group-add-gadget-complete (crv-add-complete.lisp).

(in-package "ALEOVM")

(include-book "hpos-ell2")
(include-book "crv-add-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund hpos-gadd-vals (p1 p2)
  (declare (xargs :verify-guards nil))
  (b* ((p primes::*bls12-377-scalar-field-prime*)
       (x1 (ecurve::point-finite->x p1))
       (y1 (ecurve::point-finite->y p1))
       (x2 (ecurve::point-finite->x p2))
       (y2 (ecurve::point-finite->y p2))
       (v0 (pfield::mul x1 y2 p))
       (v1 (pfield::mul x2 y1 p))
       (s (group-add-funspec p1 p2)))
    (list (pfield::mul (pfield::add x1 y1 p) (pfield::add x2 y2 p) p)
          v0
          v1
          (pfield::mul v0 v1 p)
          (pfield::fep-fix (ecurve::point-finite->x s) p)
          (pfield::fep-fix (ecurve::point-finite->y s) p))))

(defund hpos-gadd-cs (a b vs)
  (declare (xargs :verify-guards nil))
  (crv-group-add-gadget (car a) (cdr a) (car b) (cdr b)
                        (nth 0 vs) (nth 1 vs) (nth 2 vs) (nth 3 vs)
                        (nth 4 vs) (nth 5 vs)
                        primes::*bls12-377-scalar-field-prime*))

(defund hpos-c-gadd (a b vs asg)
  (declare (xargs :verify-guards nil))
  (mv (cons (nth 4 vs) (nth 5 vs))
      (hpos-gadd-cs a b vs)
      (nthcdr 6 vs)
      (append (pairlis$ (take 6 vs)
                        (hpos-gadd-vals (hpos-pt-eval a asg) (hpos-pt-eval b asg)))
              asg)))

(defund hpos-gadd-sound-hyps (a b vs asgx)
  (declare (xargs :verify-guards nil))
  (and (symbol-listp (take 6 vs))
       (<= 6 (len vs))
       (r1cs::r1cs-valuationp asgx primes::*bls12-377-scalar-field-prime*)
       (r1cs::valuation-binds-allp asgx (take 6 vs))
       (hpos-pt-boundp a asgx)
       (hpos-pt-boundp b asgx)
       (ecurve::edwards-bls12-pointp (hpos-pt-eval a asgx))
       (ecurve::edwards-bls12-pointp (hpos-pt-eval b asgx))))

;; The six wires, by position.

(defrulel hpos-take-6-open
  (implies (<= 6 (len vs))
           (equal (take 6 vs)
                  (list (nth 0 vs) (nth 1 vs) (nth 2 vs)
                        (nth 3 vs) (nth 4 vs) (nth 5 vs))))
  :expand ((take 6 vs) (take 5 (cdr vs)) (take 4 (cddr vs)) (take 3 (cdddr vs))
           (take 2 (cddddr vs)) (take 1 (cdr (cddddr vs))))
  :enable nth)

(defrulel hpos-nfix-of-lookup-when-valuationp
  (implies (and (r1cs::r1cs-valuationp a p)
                (r1cs::valuation-bindsp a v))
           (equal (nfix (lookup-equal v a)) (lookup-equal v a)))
  :use (:instance r1cs::fep-of-lookup-equal (r1cs::valuation a) (r1cs::var v) (r1cs::prime p))
  :enable pfield::fep)

(defrulel hpos-pt-coords
  (implies (and (r1cs::r1cs-valuationp a p)
                (hpos-pt-boundp pt a))
           (and (equal (ecurve::point-finite->x (hpos-pt-eval pt a))
                       (lookup-equal (car pt) a))
                (equal (ecurve::point-finite->y (hpos-pt-eval pt a))
                       (lookup-equal (cdr pt) a))))
  :enable (hpos-pt-eval hpos-pt-boundp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(defrule hpos-c-gadd-sound
  (b* (((mv pt cs & &) (hpos-c-gadd a b vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-gadd-sound-hyps a b vs asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-pt-eval pt asgx)
                    (group-add-funspec (hpos-pt-eval a asgx)
                                       (hpos-pt-eval b asgx)))))
  :do-not-induct t
  :enable (hpos-c-gadd hpos-gadd-cs hpos-gadd-sound-hyps r1cs::valuation-binds-allp)
  :disable (group-add-funspec)
  :use ((:instance hpos-pt-eval (pt (cons (nth 4 vs) (nth 5 vs))) (asg asgx))
        (:instance hpos-pt-boundp (pt a) (asg asgx))
        (:instance hpos-pt-boundp (pt b) (asg asgx))
        (:instance crv-group-add-gadget-sound
                   (x1 (car a)) (y1 (cdr a)) (x2 (car b)) (y2 (cdr b))
                   (u (nth 0 vs)) (v0 (nth 1 vs)) (v1 (nth 2 vs)) (v01 (nth 3 vs))
                   (x3 (nth 4 vs)) (y3 (nth 5 vs))
                   (p (base-prime)) (asg asgx)
                   (p1 (hpos-pt-eval a asgx)) (p2 (hpos-pt-eval b asgx)))
        (:instance primep-of-base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defrulel hpos-point-finite-of-coords
  (implies (ecurve::edwards-bls12-pointp s)
           (equal (ecurve::point-finite (ecurve::point-finite->x s)
                                        (ecurve::point-finite->y s))
                  s))
  :enable ecurve::edwards-bls12-pointp)

(defruled hpos-pt-eval-when-coords
  (implies (and (ecurve::edwards-bls12-pointp s)
                (equal (lookup-equal x a) (ecurve::point-finite->x s))
                (equal (lookup-equal y a) (ecurve::point-finite->y s)))
           (equal (hpos-pt-eval (cons x y) a) s))
  :enable hpos-pt-eval)

(defrulel hpos-fep-coords
  (implies (ecurve::edwards-bls12-pointp s)
           (and (pfield::fep (ecurve::point-finite->x s)
                             primes::*bls12-377-scalar-field-prime*)
                (pfield::fep (ecurve::point-finite->y s)
                             primes::*bls12-377-scalar-field-prime*)))
  :use ((:instance crv-fep-of-edwards-bls12-coords (p (base-prime)) (pt s))
        primep-of-base-prime))

(defrulel hpos-gadd-vals-facts
  (and (equal (len (hpos-gadd-vals p1 p2)) 6)
       (true-listp (hpos-gadd-vals p1 p2))
       (pfield::fe-listp (hpos-gadd-vals p1 p2) primes::*bls12-377-scalar-field-prime*))
  :enable hpos-gadd-vals
  :disable group-add-funspec)

(defrulel hpos-gadd-supply
  (implies (and (hpos-supply-okp vs asg)
                (<= 6 (len vs)))
           (and (symbol-listp (take 6 vs))
                (no-duplicatesp-equal (take 6 vs))
                (not (intersectp-equal (take 6 vs) (strip-cars asg)))
                (hpos-ext-p (nthcdr 6 vs) vs)
                (not (intersectp-equal (nthcdr 6 vs) (take 6 vs)))
                (hpos-supply-okp (nthcdr 6 vs) asg)))
  :enable hpos-supply-okp
  :disable (hpos-take-6-open take))

(defrulel hpos-gadd-asg-facts
  (b* (((mv & & vs2 asg2) (hpos-c-gadd a b vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= 6 (len vs)))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (hpos-ext-p vs2 vs)
                  (hpos-supply-okp vs2 asg2)
                  (equal (lookup-equal-list (take 6 vs) asg2)
                         (hpos-gadd-vals (hpos-pt-eval a asg) (hpos-pt-eval b asg)))
                  (r1cs::valuation-binds-allp asg2 (take 6 vs)))))
  :do-not-induct t
  :enable hpos-c-gadd
  :disable (hpos-take-6-open take hpos-lookup-equal-list-of-take hpos-gadd-supply)
  :use hpos-gadd-supply)

(defrulel hpos-gadd-lookups
  (implies (and (<= 6 (len vs))
                (equal (lookup-equal-list (take 6 vs) a) vals))
           (and (equal (lookup-equal (nth 0 vs) a) (nth 0 vals))
                (equal (lookup-equal (nth 1 vs) a) (nth 1 vals))
                (equal (lookup-equal (nth 2 vs) a) (nth 2 vals))
                (equal (lookup-equal (nth 3 vs) a) (nth 3 vals))
                (equal (lookup-equal (nth 4 vs) a) (nth 4 vals))
                (equal (lookup-equal (nth 5 vs) a) (nth 5 vals))))
  :rule-classes nil
  :enable lookup-equal-list
  :disable nth)

(defrulel hpos-gadd-binds
  (implies (and (<= 6 (len vs))
                (r1cs::valuation-binds-allp a (take 6 vs)))
           (and (r1cs::valuation-bindsp a (nth 0 vs))
                (r1cs::valuation-bindsp a (nth 1 vs))
                (r1cs::valuation-bindsp a (nth 2 vs))
                (r1cs::valuation-bindsp a (nth 3 vs))
                (r1cs::valuation-bindsp a (nth 4 vs))
                (r1cs::valuation-bindsp a (nth 5 vs))))
  :rule-classes nil
  :enable r1cs::valuation-binds-allp
  :disable nth)

(defrulel hpos-gadd-syms
  (implies (and (<= 6 (len vs))
                (symbol-listp (take 6 vs)))
           (and (symbolp (nth 0 vs)) (symbolp (nth 1 vs)) (symbolp (nth 2 vs))
                (symbolp (nth 3 vs)) (symbolp (nth 4 vs)) (symbolp (nth 5 vs))))
  :rule-classes nil
  :disable nth)

(defrulel hpos-gadd-in-lookups
  (implies (and (r1cs::r1cs-valuationp a2 p)
                (hpos-ext-p asg a2)
                (hpos-pt-boundp pt asg))
           (and (equal (lookup-equal (car pt) a2) (lookup-equal (car pt) asg))
                (equal (lookup-equal (cdr pt) a2) (lookup-equal (cdr pt) asg))
                (r1cs::valuation-bindsp a2 (car pt))
                (r1cs::valuation-bindsp a2 (cdr pt))
                (equal (hpos-pt-eval pt a2) (hpos-pt-eval pt asg))))
  :rule-classes nil
  :enable (hpos-pt-boundp hpos-pt-eval)
  :use ((:instance hpos-lookup-when-ext-p (old asg) (new a2) (v (car pt)))
        (:instance hpos-lookup-when-ext-p (old asg) (new a2) (v (cdr pt)))))

(defrulel hpos-cs-boundp-of-crv-group-add-gadget
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                (symbolp x3) (symbolp y3)
                (r1cs::valuation-bindsp a x1) (r1cs::valuation-bindsp a y1)
                (r1cs::valuation-bindsp a x2) (r1cs::valuation-bindsp a y2)
                (r1cs::valuation-bindsp a u) (r1cs::valuation-bindsp a v0)
                (r1cs::valuation-bindsp a v1) (r1cs::valuation-bindsp a v01)
                (r1cs::valuation-bindsp a x3) (r1cs::valuation-bindsp a y3))
           (hpos-cs-boundp (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3
                                                 primes::*bls12-377-scalar-field-prime*)
                           a))
  :enable (crv-group-add-gadget hpos-cs-boundp hpos-sv-boundp))

(defrulel hpos-gadd-holds-vars
  (b* ((p primes::*bls12-377-scalar-field-prime*))
    (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                  (symbolp u) (symbolp v0) (symbolp v1) (symbolp v01)
                  (symbolp x3) (symbolp y3)
                  (r1cs::r1cs-valuationp a p)
                  (r1cs::valuation-bindsp a x1) (r1cs::valuation-bindsp a y1)
                  (r1cs::valuation-bindsp a x2) (r1cs::valuation-bindsp a y2)
                  (r1cs::valuation-bindsp a u) (r1cs::valuation-bindsp a v0)
                  (r1cs::valuation-bindsp a v1) (r1cs::valuation-bindsp a v01)
                  (r1cs::valuation-bindsp a x3) (r1cs::valuation-bindsp a y3)
                  (ecurve::edwards-bls12-pointp p1)
                  (ecurve::edwards-bls12-pointp p2)
                  (equal (lookup-equal x1 a) (ecurve::point-finite->x p1))
                  (equal (lookup-equal y1 a) (ecurve::point-finite->y p1))
                  (equal (lookup-equal x2 a) (ecurve::point-finite->x p2))
                  (equal (lookup-equal y2 a) (ecurve::point-finite->y p2))
                  (equal (lookup-equal-list (list u v0 v1 v01 x3 y3) a)
                         (hpos-gadd-vals p1 p2)))
             (r1cs::r1cs-constraints-holdp
              (crv-group-add-gadget x1 y1 x2 y2 u v0 v1 v01 x3 y3 p) a p)))
  :do-not-induct t
  :in-theory (union-theories '(hpos-gadd-vals lookup-equal-list car-cons cdr-cons
                               acl2::cons-equal hpos-base-prime-value pfield::fep-fix-when-fep
                               (:e lookup-equal-list))
                             (theory 'minimal-theory))
  :use ((:instance hpos-fep-coords (s (group-add-funspec p1 p2)))
        edwards-bls12-pointp-of-group-add-funspec
        (:instance crv-group-add-gadget-complete (p (base-prime)) (asg a))))

(defrulel hpos-c-gadd-cs
  (equal (mv-nth 1 (hpos-c-gadd a b vs asg)) (hpos-gadd-cs a b vs))
  :enable hpos-c-gadd)

(defrulel hpos-gadd-holds
  (b* (((mv & cs & asg2) (hpos-c-gadd a b vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= 6 (len vs))
                  (hpos-pt-boundp a asg)
                  (hpos-pt-boundp b asg)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval a asg))
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval b asg)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (hpos-cs-boundp cs asg2))))
  :do-not-induct t
  :in-theory '(hpos-gadd-cs hpos-c-gadd-cs)
  :use (hpos-take-6-open
        hpos-gadd-asg-facts
        hpos-gadd-supply
        (:instance hpos-pt-boundp (pt a) (asg asg))
        (:instance hpos-pt-boundp (pt b) (asg asg))
        (:instance hpos-pt-coords (pt a) (a asg) (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-pt-coords (pt b) (a asg) (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-gadd-binds (a (mv-nth 3 (hpos-c-gadd a b vs asg))))
        hpos-gadd-syms
        (:instance hpos-gadd-in-lookups (pt a) (a2 (mv-nth 3 (hpos-c-gadd a b vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-gadd-in-lookups (pt b) (a2 (mv-nth 3 (hpos-c-gadd a b vs asg)))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-cs-boundp-of-crv-group-add-gadget
                   (x1 (car a)) (y1 (cdr a)) (x2 (car b)) (y2 (cdr b))
                   (u (nth 0 vs)) (v0 (nth 1 vs)) (v1 (nth 2 vs)) (v01 (nth 3 vs))
                   (x3 (nth 4 vs)) (y3 (nth 5 vs))
                   (a (mv-nth 3 (hpos-c-gadd a b vs asg))))
        (:instance hpos-gadd-holds-vars
                   (x1 (car a)) (y1 (cdr a)) (x2 (car b)) (y2 (cdr b))
                   (u (nth 0 vs)) (v0 (nth 1 vs)) (v1 (nth 2 vs)) (v01 (nth 3 vs))
                   (x3 (nth 4 vs)) (y3 (nth 5 vs))
                   (a (mv-nth 3 (hpos-c-gadd a b vs asg)))
                   (p1 (hpos-pt-eval a asg)) (p2 (hpos-pt-eval b asg)))))

(defrule hpos-c-gadd-complete
  (b* (((mv pt cs vs2 asg2) (hpos-c-gadd a b vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= 6 (len vs))
                  (hpos-pt-boundp a asg)
                  (hpos-pt-boundp b asg)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval a asg))
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval b asg)))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-pt-boundp pt asg2)
                  (equal (hpos-pt-eval pt asg2)
                         (group-add-funspec (hpos-pt-eval a asg) (hpos-pt-eval b asg))))))
  :do-not-induct t
  :enable (hpos-wit-okp hpos-pt-boundp hpos-pt-eval)
  :disable (group-add-funspec hpos-gadd-asg-facts hpos-gadd-holds nth hpos-take-6-open
            hpos-gadd-supply ecurve::point-finite-of-point-finite->x/y)
  :use (hpos-gadd-asg-facts
        hpos-gadd-holds
        hpos-gadd-supply
        hpos-gadd-syms
        (:instance hpos-gadd-binds (a (mv-nth 3 (hpos-c-gadd a b vs asg))))
        (:instance hpos-gadd-lookups (a (mv-nth 3 (hpos-c-gadd a b vs asg)))
                   (vals (hpos-gadd-vals (hpos-pt-eval a asg) (hpos-pt-eval b asg))))
        (:instance hpos-fep-coords
                   (s (group-add-funspec (hpos-pt-eval a asg) (hpos-pt-eval b asg))))
        (:instance edwards-bls12-pointp-of-group-add-funspec
                   (p1 (hpos-pt-eval a asg)) (p2 (hpos-pt-eval b asg)))
        (:instance hpos-pt-eval-when-coords
                   (x (nth 4 vs)) (y (nth 5 vs)) (a (mv-nth 3 (hpos-c-gadd a b vs asg)))
                   (s (group-add-funspec (hpos-pt-eval a asg) (hpos-pt-eval b asg)))))
  :prep-lemmas
  ((defrule hpos-c-gadd-parts
     (and (equal (mv-nth 0 (hpos-c-gadd a b vs asg)) (cons (nth 4 vs) (nth 5 vs)))
          (equal (mv-nth 2 (hpos-c-gadd a b vs asg)) (nthcdr 6 vs)))
     :enable hpos-c-gadd)
   (defrule hpos-nth-of-gadd-vals
     (and (equal (nth 4 (hpos-gadd-vals p1 p2))
                 (pfield::fep-fix (ecurve::point-finite->x (group-add-funspec p1 p2))
                                  primes::*bls12-377-scalar-field-prime*))
          (equal (nth 5 (hpos-gadd-vals p1 p2))
                 (pfield::fep-fix (ecurve::point-finite->y (group-add-funspec p1 p2))
                                  primes::*bls12-377-scalar-field-prime*)))
     :enable hpos-gadd-vals
     :disable group-add-funspec)))
