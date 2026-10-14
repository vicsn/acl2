; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Square-root soundness, completeness, and a sample.
;
; A square has two roots, r and -r.  At most one of them is <= (p-1)/2,
; and exactly one of them is even, because p is odd.  The existing
; field-square-root gadget enforces the square and the lesser-root bound.
; even_square_root enforces the square, the canonical bits, and a zero
; least significant bit.
;
; square_roots_flagged_nondeterministic is not proved equal to the ordered
; funspec.  The separate theorem below is only the unordered relation:
; the second output is the negation of the first, the first squares to x
; when the flag is 0, and both outputs are 0 when the flag is 1.

(in-package "ALEOVM")

(include-book "fb-field-sqrt")
(include-book "fb2-boolean-lte")
(include-book "../r1cs/field-square-root")
(include-book "../r1cs/field-pow-const")
(include-book "../r1cs/boolean-and")
(include-book "../library-extensions/digits")
(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-diff-of-squares
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b))
           (equal (pfield::sub (pfield::mul a a p)
                               (pfield::mul b b p)
                               p)
                  (pfield::mul (pfield::sub a b p)
                               (pfield::add a b p)
                               p)))
  :enable (fieldp
           pfield::mul
           pfield::add
           pfield::sub)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb2-equal-squares-implies-equal-or-neg
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (or (equal a b)
               (equal a (pfield::neg b p))))
  :enable (fb2-diff-of-squares fieldp pfield::neg)
  :disable ((:definition pfield::sub)
            (:definition pfield::add)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance pfield::equal-of-0-and-mul
                  (x (pfield::sub a b (base-prime)))
                  (y (pfield::add a b (base-prime)))
                  (p (base-prime))))

(defruled fb2-lesser-square-root-unique
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (<= a (field-modulus-minus-one-div-two))
                (<= b (field-modulus-minus-one-div-two))
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (equal a b))
  :enable (fb2-equal-squares-implies-equal-or-neg
           field-modulus-minus-one-div-two
           fieldp
           pfield::neg))

(defruled fb2-field-square-root-gadget-sound
  (implies (and (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (field-square-root-gadget x y ys rs p) asg p))
           (equal (lookup-equal y asg)
                  (field-square-root-funspec (lookup-equal x asg))))
  :do-not-induct t
  :enable (fb-field-square-root-gadget-bound
           fb2-lesser-square-root-unique
           field-square-root-funspec
           field-lesser-square-root
           fieldp
           pfield::fep-fix-when-fep
           ecurve::pfield-squarep-suff
           ecurve::pfield-squarep))

(defruled fb2-even-root-unique
  (implies (and (equal p (base-prime))
                (fieldp a)
                (fieldp b)
                (evenp a)
                (evenp b)
                (equal (pfield::mul a a p)
                       (pfield::mul b b p)))
           (equal a b))
  :enable (fb2-equal-squares-implies-equal-or-neg
           fieldp
           pfield::neg
           evenp
           oddp))

(defruled fb2-field-even-square-root-gadget-sound
  (implies (and (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (consp ys)
                (equal (len ys) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-even-square-root-gadget x y ys rs u p) asg p))
           (equal (lookup-equal y asg)
                  (field-even-square-root-funspec (lookup-equal x asg))))
  :do-not-induct t
  :enable (fb-field-even-square-root-gadget
           field-square-gadget-correctness
           field-to-bits-soundness
           fb2-even-root-unique
           field-even-square-root-funspec
           fieldp
           evenp
           ecurve::pfield-even-squarep
           ecurve::pfield-even-squarep-suff
           pfield::fep-fix-when-fep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime 5, 1^2 = 1, and 1 <= (5-1)/2.  Bits (1 0 0).  The bound 2 is
; bits (0 1); the high bit is zero and the fold bit r is 0.

(defconst *fb2-field-square-root-asg*
  '((x . 1) (y . 1) (b0 . 1) (b1 . 0) (b2 . 0) (r . 0)))

(defconst *fb2-field-square-root-prime* 5)

(defrule fb2-field-square-root-sample
  (r1cs::r1cs-constraints-holdp
   (field-square-root-gadget 'x 'y '(b0 b1 b2) '(r)
                             *fb2-field-square-root-prime*)
   *fb2-field-square-root-asg*
   *fb2-field-square-root-prime*)
  :enable (field-square-root-gadget
           field-square-root-rlen
           field-square-root-bound
           field-square-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           bits-lte-const-check-gadget
           bits-lte-const-check-rlen
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-gadget
           zero-gadget-list
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-flagged-roots-unordered
  :short "Unordered reading of @('square_roots_flagged_nondeterministic').
          Not the ordered funspec: either root may be returned first."
  (implies (and (symbolp x)
                (posp e)
                (not (equal e 1))
                (equal e (field-modulus-minus-one-div-two))
                (symbol-listp ss)
                (symbol-listp pow-rs)
                (equal (len ss) (field-pow-const-slen e))
                (equal (len pow-rs) (field-pow-const-rlen e))
                (consp pow-rs)
                (symbolp one-m)
                (symbolp one-r)
                (symbolp square)
                (symbolp root)
                (symbolp zero-m)
                (symbolp zero-r)
                (symbolp err)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg pow-rs)
                (r1cs::valuation-bindsp asg one-m)
                (r1cs::valuation-bindsp asg one-r)
                (r1cs::valuation-bindsp asg square)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg zero-m)
                (r1cs::valuation-bindsp asg zero-r)
                (r1cs::valuation-bindsp asg err)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal root asg))
                (bitp (lookup-equal one-r asg))
                (bitp (lookup-equal zero-r asg))
                (bitp (lookup-equal err asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-square-roots-flagged-gadget
                  x e ss pow-rs one-m one-r square root
                  zero-m zero-r err p)
                 asg p))
           (b* ((x$ (lookup-equal x asg))
                (root$ (lookup-equal root asg))
                (flag$ (lookup-equal err asg))
                (second$ (pfield::neg root$ p)))
             (and (bitp flag$)
                  (if (equal flag$ 1)
                      (and (equal root$ 0)
                           (equal second$ 0))
                    (equal (pfield::mul root$ root$ p) x$)))))
  :do-not-induct t
  :cases ((equal (lookup-equal err asg) 1))
  :enable (fb-field-square-roots-flagged-gadget
           field-is-one-funspec
           field-is-zero-funspec
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           boolean-and-funspec
           fieldp
           bitp)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use ((:instance field-pow-const-soundness
                   (x x) (c e) (ss ss) (rs pow-rs) (p p))
        (:instance field-is-one-gadget-sound
                   (x (car pow-rs)) (m one-m) (r one-r) (p p))
        (:instance field-is-zero-gadget-sound
                   (x x) (m zero-m) (r zero-r) (p p))
        (:instance field-square-gadget-correctness
                   (x root) (r square) (p p))
        (:instance boolean-and-gadget-to-bitand
                   (x zero-r) (y one-r) (z err) (p p))
        (:instance pfield::equal-of-0-and-mul
                   (x (lookup-equal root asg))
                   (y (lookup-equal root asg))
                   (p p))))
