; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Canonical witness of hped-elligator2-gadget, for hpos-ell2.lisp.
;
; The constraints are hped-elligator2-gadget (hped-elligator2.lisp) with the
; input linear combination substituted for its input variable
; (hpos-cs-subst).  The next 1041 fresh variables are: a placeholder for the
; substitution (it occurs in no constraint and is never assigned), then the
; 33 named wires of hped-ell2-w, then 251 pairs (square, product) for the
; square-and-multiply of the Legendre power, then the 253 bits of the square
; root and the 252 range-check wires.  The product wire of a pair is unused
; (occurs in no constraint) when its exponent bit is 0; snarkVM allocates no
; variable there.  The witness is the canonical one of
; hped-elligator2-gadget-complete.  U is the public unit wire.

(in-package "ALEOVM")

(include-book "hpos-hash-to-scalar")
(include-book "hped-elligator2")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(set-ignore-ok t)

(defrule hpos-primep-of-edwards-bls12-q
  (primep (ecurve::edwards-bls12-q))
  :use primep-of-base-prime
  :in-theory '(curve-base-prime-is-edwards-bls12-q))

(defrule hpos-edwards-bls12-q-facts
  (and (posp (ecurve::edwards-bls12-q))
       (integerp (ecurve::edwards-bls12-q))
       (< 1 (ecurve::edwards-bls12-q)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (posp (ecurve::edwards-bls12-q))))
  :in-theory '((:e ecurve::edwards-bls12-q) (:e posp) (:e integerp) (:e <)))

(defconst *hpos-ell2-nexp* 251)
(defconst *hpos-ell2-nblock* 1041)

(defrule hpos-len-of-hped-ell2-exp-bits
  (equal (len (hped-ell2-exp-bits)) *hpos-ell2-nexp*)
  :enable ((:e hped-ell2-exp-bits)))

(defrule hpos-bit-listp-of-hped-ell2-exp-bits
  (bit-listp (hped-ell2-exp-bits))
  :enable ((:e hped-ell2-exp-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Power wires.

(defund hpos-pairs (l)
  (declare (xargs :verify-guards nil))
  (if (or (endp l) (endp (cdr l)))
      nil
    (cons (list (car l) (cadr l))
          (hpos-pairs (cddr l)))))

(defund hpos-pw-vals (cs gv av p)
  (declare (xargs :verify-guards nil))
  (if (endp cs)
      nil
    (let ((sv (pfield::mul av av p)))
      (if (equal (car cs) 1)
          (let ((rv (pfield::mul sv gv p)))
            (list* sv rv (hpos-pw-vals (cdr cs) gv rv p)))
        (list* sv 0 (hpos-pw-vals (cdr cs) gv sv p))))))

(defrule hpos-len-of-hpos-pw-vals
  (equal (len (hpos-pw-vals cs gv av p)) (* 2 (len cs)))
  :enable hpos-pw-vals)

(defrule hpos-fe-listp-of-hpos-pw-vals
  (implies (posp p)
           (pfield::fe-listp (hpos-pw-vals cs gv av p) p))
  :enable (hpos-pw-vals pfield::fe-listp))

(defrule hpos-true-listp-of-hpos-pw-vals
  (true-listp (hpos-pw-vals cs gv av p))
  :enable hpos-pw-vals)

(defun hpos-pw-ind (cs pwf acc av gv p)
  (declare (xargs :verify-guards nil))
  (if (endp cs)
      (list pwf acc av gv p)
    (let ((sv (pfield::mul av av p)))
      (if (equal (car cs) 1)
          (hpos-pw-ind (cdr cs) (cddr pwf) (hped-lc-v (cadr pwf))
                       (pfield::mul sv gv p) gv p)
        (hpos-pw-ind (cdr cs) (cddr pwf) (hped-lc-v (car pwf)) sv gv p)))))

(defrule hpos-hped-pw-canonp-of-hpos-pw-vals
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp pwf)
                (r1cs::valuation-binds-allp asg pwf)
                (equal (len pwf) (* 2 (len cs)))
                (equal (lookup-equal-list pwf asg) (hpos-pw-vals cs gv av p))
                (equal (r1cs::dot-product g asg p) gv)
                (equal (r1cs::dot-product acc asg p) av))
           (hped-pw-canonp g cs (hpos-pairs pwf) acc asg p))
  :induct (hpos-pw-ind cs pwf acc av gv p)
  :enable (hpos-pw-vals hpos-pairs lookup-equal-list r1cs::valuation-binds-allp))

(defrule hpos-hped-pw-boundp-of-hpos-pairs
  (implies (and (symbol-listp pwf)
                (r1cs::valuation-binds-allp asg pwf)
                (equal (len pwf) (* 2 (len cs))))
           (hped-pw-boundp cs (hpos-pairs pwf) asg))
  :induct (hpos-pw-ind cs pwf nil nil nil nil)
  :enable (hped-pw-boundp hpos-pairs r1cs::valuation-binds-allp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The 33 named wires: the canonical values, in hped-ell2-w order.

(defund hpos-ell2-wvals (r)
  (declare (xargs :verify-guards nil))
  (hped-ell2-canon-let
   (b* ((pt (ecurve::point-finite xe ye))
        (pt2 (group-double-funspec pt))
        (pt4 (group-mul-by-cofactor-funspec pt))
        (x4 (pfield::fep-fix (ecurve::point-finite->x pt2) p))
        (y4 (pfield::fep-fix (ecurve::point-finite->y pt2) p)))
     (list m1 s tt m2 winv v2 v3 ev x2 x3 rt y ve vex vexy m3 y2 iv xe iu ye
           (pfield::mul xe xe p) (pfield::mul ye ye p) (pfield::mul xe ye p)
           (pfield::mul xe xe p) (pfield::mul ye ye p)
           x4 y4 (pfield::mul x4 y4 p) (pfield::mul x4 x4 p) (pfield::mul y4 y4 p)
           (pfield::fep-fix (ecurve::point-finite->x pt4) p)
           (pfield::fep-fix (ecurve::point-finite->y pt4) p)))))

(defund hpos-ell2-gval (r)
  (declare (xargs :verify-guards nil))
  (hped-ell2-canon-let g))

(defrule hpos-len-of-hpos-ell2-wvals
  (equal (len (hpos-ell2-wvals r)) 33)
  :in-theory (union-theories '(hpos-ell2-wvals len (:e len) car-cons cdr-cons)
                             (theory 'minimal-theory)))

(defrule hpos-true-listp-of-hpos-ell2-wvals
  (true-listp (hpos-ell2-wvals r))
  :in-theory (union-theories '(hpos-ell2-wvals true-listp (:e true-listp) car-cons cdr-cons)
                             (theory 'minimal-theory)))

(defrule hpos-fe-listp-of-hpos-ell2-wvals
  (pfield::fe-listp (hpos-ell2-wvals r) (ecurve::edwards-bls12-q))
  :in-theory (union-theories '(hpos-ell2-wvals pfield::fe-listp (:e pfield::fe-listp) car-cons cdr-cons
                               pfield::fep-of-mul pfield::fep-of-neg pfield::fep-of-add
                               pfield::fep-of-sub pfield::fep-of-inv pfield::fep-of-fep-fix
                               return-type-of-hped-ell2-legendre
                               (:e posp) (:e integerp) (:e <) (:e ecurve::edwards-bls12-q))
                             (theory 'minimal-theory)))

(defruled hpos-ell2-canon-pointp
  (implies (hped-elligator2-encode-validp r)
           (hped-ell2-canon-let
            (ecurve::edwards-bls12-pointp (ecurve::point-finite xe ye))))
  :do-not-induct t
  :use (hped-ell2-validp-forward hped-ell2-canonical-equations)
  :in-theory (theory 'minimal-theory))

(defruledl hpos-lookup-nth
  (implies (< (nfix k) (len w))
           (equal (lookup-equal (nth k w) asg)
                  (nth k (lookup-equal-list w asg))))
  :induct (nth k w)
  :enable (lookup-equal-list nth))

(defund hpos-ell2-wires-okp (w asg r)
  (declare (xargs :verify-guards nil))
  (equal (lookup-equal-list w asg) (hpos-ell2-wvals r)))

(defrulel hpos-lookup-nth-when-hpos-ell2-wires-okp
  (implies (and (hpos-ell2-wires-okp w asg r)
                (< (nfix k) (len w)))
           (equal (lookup-equal (nth k w) asg)
                  (nth k (hpos-ell2-wvals r))))
  :enable hpos-ell2-wires-okp
  :use hpos-lookup-nth)

(defrulel hpos-lookup-car-when-hpos-ell2-wires-okp
  (implies (and (hpos-ell2-wires-okp w asg r)
                (consp w))
           (equal (lookup-equal (car w) asg)
                  (car (hpos-ell2-wvals r))))
  :enable (hpos-ell2-wires-okp lookup-equal-list))

(defrulel hpos-consp-when-len-is-33
  (implies (equal (len w) 33) (consp w)))

(defruled hpos-ell2-wire-facts
  (implies (and (equal (len w) 33)
                (hpos-ell2-wires-okp w asg r)
                (equal (lookup-equal in asg) r)
                (hped-elligator2-encode-validp r))
           (hped-ell2-canon-let
            (and (hped-ell2-wire-vars)
                 (hped-ell2-aux-wires))))
  :do-not-induct t
  :in-theory (union-theories '(hpos-ell2-wvals hpos-lookup-nth-when-hpos-ell2-wires-okp
                               hpos-lookup-car-when-hpos-ell2-wires-okp (:e consp) hpos-consp-when-len-is-33
                               nth (:e nth) car-cons cdr-cons (:e zp) (:e nfix) (:e <) (:e binary-+)
                               (:e unary--) (:e natp)
                               pfield::fep-fix-when-fep curve-base-prime-is-edwards-bls12-q
                               hpos-primep-of-edwards-bls12-q
                               edwards-bls12-pointp-of-group-double-funspec
                               edwards-bls12-pointp-of-group-mul-by-cofactor-funspec)
                             (theory 'minimal-theory))
  :use (hpos-ell2-canon-pointp
        (:instance crv-fep-of-edwards-bls12-coords
                   (p (base-prime))
                   (pt (group-double-funspec
                        (hped-ell2-canon-let (ecurve::point-finite xe ye)))))
        (:instance crv-fep-of-edwards-bls12-coords
                   (p (base-prime))
                   (pt (group-mul-by-cofactor-funspec
                        (hped-ell2-canon-let (ecurve::point-finite xe ye)))))))

(defund hpos-ell2-root (r)
  (declare (xargs :verify-guards nil))
  (nth 10 (hpos-ell2-wvals r)))

(defrulel hpos-symbolp-of-nth-when-symbol-listp
  (implies (symbol-listp l)
           (symbolp (nth k l)))
  :enable nth)

(defrulel hpos-bindsp-of-nth-when-binds-allp
  (implies (and (r1cs::valuation-binds-allp asg l)
                (< (nfix k) (len l)))
           (r1cs::valuation-bindsp asg (nth k l)))
  :enable (nth r1cs::valuation-binds-allp))

(defruled hpos-ell2-g-lc-value
  (implies (and (equal (len w) 33)
                (symbol-listp w)
                (r1cs::r1cs-valuationp asg (ecurve::edwards-bls12-q))
                (r1cs::valuation-binds-allp asg w)
                (hpos-ell2-wires-okp w asg r))
           (equal (r1cs::dot-product (hped-ell2-g-lc w) asg (ecurve::edwards-bls12-q))
                  (hpos-ell2-gval r)))
  :do-not-induct t
  :in-theory (union-theories '(hped-ell2-g-lc hpos-ell2-gval hpos-ell2-wvals
                               hpos-lookup-nth-when-hpos-ell2-wires-okp
                               hpos-symbolp-of-nth-when-symbol-listp
                               hpos-bindsp-of-nth-when-binds-allp
                               hpos-primep-of-edwards-bls12-q
                               hped-dot-of-lc-v hped-dot-of-lc-add hped-dot-of-lc-scale
                               return-type-of-hped-ell2-a return-type-of-hped-ell2-b
                               pfield::fep-of-neg
                               nth (:e nth) car-cons cdr-cons (:e zp) (:e nfix) (:e <)
                               (:e binary-+) (:e unary--) (:e natp) (:e posp)
                               (:e integerp) hpos-edwards-bls12-q-facts)
                             (theory 'minimal-theory)))

(defruled hpos-ell2-gadget-complete-wit
  (implies (and (hped-ell2-gadget-hyps)
                (hpos-ell2-wires-okp w asg (lookup-equal in asg))
                (hped-elligator2-encode-validp (lookup-equal in asg))
                (hped-pw-canonp (hped-ell2-g-lc w) (hped-ell2-exp-bits) pw
                                (hped-ell2-g-lc w) asg (ecurve::edwards-bls12-q))
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (hpos-ell2-root (lookup-equal in asg))))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (field-bits-le (hpos-ell2-root (lookup-equal in asg)))
                        (acl2::nat=>lebits* (1- (ecurve::edwards-bls12-q))))))
           (r1cs::r1cs-constraints-holdp
            (hped-ell2-gadget in w pw bits rs u) asg p))
  :do-not-induct t
  :use ((:instance hpos-ell2-wire-facts (r (lookup-equal in asg)))
        hped-elligator2-gadget-complete)
  :in-theory (union-theories '(hpos-ell2-root hpos-ell2-wvals nth (:e nth) car-cons cdr-cons
                               (:e zp) (:e nfix) (:e <) (:e binary-+) (:e unary--))
                             (theory 'minimal-theory)))

