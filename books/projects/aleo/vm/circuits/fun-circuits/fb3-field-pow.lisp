; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness and a PFCS for Field::pow.
;
; The gadget bitifies the exponent and walks those bits with one
; square-and-multiply step per bit.  The witness is the canonical
; exponent bits, the write_bits fold, and the squares, products, and
; results of that walk.  Soundness then says the first result is
; x^e.
;
; The 253-bit loop is not lifted.  The PFCS is one square-and-multiply
; step on a 2-bit exponent, so the exponent is below 4 and the powered
; value is the funspec, not a free variable.

(in-package "ALEOVM")

(include-book "fb-field-pow")
(include-book "fb3-field-write-bits")
(include-book "../r1cs/field-pow-bits")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-pow-spr ((x (pfield::fep x p))
                     (ys bit-listp)
                     (p primep))
  :guard (consp ys)
  :returns (mv (ss true-listp)
               (ps true-listp)
               (rs true-listp))
  :short "Squares, products, and results of one square-and-multiply walk.
          @('ys') is little-endian.  @('(car rs)') is @($x$) to that value."
  (cond ((not (mbt (consp ys))) (mv nil nil nil))
        ((endp (cdr ys))
         (mv nil
             nil
             (list (if1 (car ys) x p))))
        (t (b* (((mv cdr-ss cdr-ps cdr-rs) (fb3-pow-spr x (cdr ys) p))
                (cadr-rs (car cdr-rs))
                (car-ss (pfield::mul cadr-rs cadr-rs p))
                (car-ps (pfield::mul car-ss x p))
                (car-rs (if (= (car ys) 1) car-ps car-ss)))
             (mv (cons car-ss cdr-ss)
                 (cons car-ps cdr-ps)
                 (cons car-rs cdr-rs)))))
  ///
  (defret len-of-fb3-pow-spr-ss
    (implies (consp ys)
             (equal (len ss) (1- (len ys))))
    :hints (("Goal" :in-theory (enable fb3-pow-spr))))
  (defret len-of-fb3-pow-spr-ps
    (implies (consp ys)
             (equal (len ps) (1- (len ys))))
    :hints (("Goal" :in-theory (enable fb3-pow-spr))))
  (defret len-of-fb3-pow-spr-rs
    (equal (len rs) (len ys))
    :hints (("Goal" :in-theory (enable fb3-pow-spr)))))

(define fb3-pow-induct ((ys true-listp)
                        (ss true-listp)
                        (ps true-listp)
                        (rs true-listp))
  (if (or (endp ys) (endp (cdr ys)) (endp rs))
      nil
    (fb3-pow-induct (cdr ys) (cdr ss) (cdr ps) (cdr rs))))

(defruled fb3-pow-aux-satisfies
  (implies (and (symbolp x)
                (symbol-listp ys)
                (symbol-listp ss)
                (symbol-listp ps)
                (symbol-listp rs)
                (consp ys)
                (equal (len ss) (1- (len ys)))
                (equal (len ps) (1- (len ys)))
                (equal (len rs) (len ys))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (pfield::fep (lookup-equal x asg) p)
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal-list ss asg)
                       (mv-nth 0 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list ps asg)
                       (mv-nth 1 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list rs asg)
                       (mv-nth 2 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p))))
           (r1cs::r1cs-constraints-holdp
            (field-pow-bits-gadget-aux x ys ss ps rs p) asg p))
  :hints (("Goal"
           :induct (fb3-pow-induct ys ss ps rs)
           :in-theory (e/d (fb3-pow-induct
                            fb3-pow-spr
                            field-pow-bits-gadget-aux
                            if1-gadget-to-if1
                            if-gadget-to-if
                            field-mul-gadget-correctness
                            field-square-gadget-correctness
                            fb-lookup-equal-list-of-cdr
                            lookup-equal-of-car
                            r1cs::valuation-binds-allp
                            bitp
                            if1)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-pow-bits-holds
  (implies (and (symbolp x)
                (symbol-listp ys)
                (symbol-listp ss)
                (symbol-listp ps)
                (symbol-listp rs)
                (consp ys)
                (equal (len ss) (1- (len ys)))
                (equal (len ps) (1- (len ys)))
                (equal (len rs) (len ys))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (pfield::fep (lookup-equal x asg) p)
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal-list ss asg)
                       (mv-nth 0 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list ps asg)
                       (mv-nth 1 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list rs asg)
                       (mv-nth 2 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p))))
           (r1cs::r1cs-constraints-holdp
            (field-pow-bits-gadget x ys ss ps rs p) asg p))
  :enable (field-pow-bits-gadget
           fb-r1cs-holdp-of-rev)
  :use fb3-pow-aux-satisfies)

(defruled fb3-field-pow-gadget-complete
  (implies (and (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp unitvar)
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (equal (len ys) (integer-length p))
                (symbol-listp zs)
                (equal (len zs) (bits-lt-prime-rlen p))
                (symbol-listp rs)
                (equal (len rs) (len ys))
                (symbol-listp ss)
                (equal (len ss) (1- (len ys)))
                (symbol-listp ps)
                (equal (len ps) (1- (len ys)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg unitvar)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg ps)
                (equal (lookup-equal unitvar asg) 1)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list zs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list ss asg)
                       (mv-nth 0 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list ps asg)
                       (mv-nth 1 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p)))
                (equal (lookup-equal-list rs asg)
                       (mv-nth 2 (fb3-pow-spr (lookup-equal x asg)
                                              (lookup-equal-list ys asg)
                                              p))))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-pow-gadget x y ys zs ss ps rs unitvar p)
                 asg p)
                (equal (car (lookup-equal-list rs asg))
                       (field-pow-funspec (lookup-equal x asg)
                                          (lookup-equal y asg)))))
  :enable (fb-field-pow-gadget
           field-pow-gadget
           fb-field-write-bits-le-gadget
           fb3-pow-bits-holds
           field-bits-le
           fieldp
           pfield::fep-fix-when-fep
           acl2::bit-listp-of-nat=>lebits)
  :use ((:instance fb2-field-write-bits-le-gadget-complete
                   (x y)
                   (bits ys)
                   (rs zs)
                   (u unitvar)
                   (p p)
                   (asg asg))
        fb-field-pow-gadget-sound)
  :disable ((:definition pfield::sub)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule fb3-pow-2-step
  (implies (and (equal p (base-prime))
                (primep p)
                (fieldp x)
                (bitp y0)
                (bitp y1)
                (equal e (+ y0 (* 2 y1)))
                (equal r1 (if (equal y1 1) x 1))
                (equal (pfield::mul r1 r1 p) sq)
                (equal (pfield::mul sq x p) pr)
                (equal z (if (equal y0 1) pr sq)))
           (and (< e 4)
                (equal z (field-pow-funspec x e))))
  :hints (("Goal"
           :cases ((equal y0 0) (equal y0 1))
           :in-theory (e/d (bitp
                            field-pow-funspec
                            fieldp
                            pfield::fep-fix-when-fep
                            pfield::pow-of-+
                            pfield::pow-opener
                            pfield::pow-of-0-arg2
                            pfield::pow-of-1-arg2
                            pfield::pow-of-0-arg1
                            fb3-two-bits-below-4)
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))
          ("Subgoal 1" :cases ((equal y1 0) (equal y1 1)))
          ("Subgoal 2" :cases ((equal y1 0) (equal y1 1))))
  :rule-classes nil)

(defruled fb3-pow-2-below-4
  (implies (and (equal p (base-prime))
                (primep p)
                (fieldp x)
                (bitp y0)
                (bitp y1)
                (equal e (+ y0 (* 2 y1)))
                (equal r1 (if (equal y1 1) x 1))
                (equal (pfield::mul r1 r1 p) sq)
                (equal (pfield::mul sq x p) pr)
                (equal z (if (equal y0 1) pr sq)))
           (< e 4))
  :use fb3-pow-2-step)

(defruled fb3-pow-2-is-funspec
  (implies (and (equal p (base-prime))
                (primep p)
                (fieldp x)
                (bitp y0)
                (bitp y1)
                (equal e (+ y0 (* 2 y1)))
                (equal r1 (if (equal y1 1) x 1))
                (equal (pfield::mul r1 r1 p) sq)
                (equal (pfield::mul sq x p) pr)
                (equal z (if (equal y0 1) pr sq)))
           (equal (field-pow-funspec x e)
                  (if (equal y0 1) pr sq)))
  :use fb3-pow-2-step)

(define fb3-field-pow-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS of one square-and-multiply step, exponent below 4.
          @('z') is @($x^e$), not a free output."
  (pfcs::parse-def
   "field_pow_2(x, e, z, y0, y1, r1, sq, pr) := {
    (1 - y0) * (y0) == (0),
    (1 - y1) * (y1) == (0),
    (e) * (1) == (y0 + 2 * y1),
    (y1) * (x - 1) == (r1 - 1),
    (r1) * (r1) == (sq),
    (sq) * (x) == (pr),
    (y0) * (pr - sq) == (z - sq)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-pow-2-circuit)
            :pred fb3-field-pow-2-pred
            :prime prime)

(defruled fb3-if1-is-if1
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp y1)
                (pfield::fep x p)
                (pfield::fep r1 p))
           (equal (equal (pfield::mul y1
                                      (pfield::sub x (mod 1 p) p)
                                      p)
                         (pfield::sub r1 (mod 1 p) p))
                  (equal r1 (if (equal y1 1) x 1))))
  :hints (("Goal"
           :cases ((equal y1 0) (equal y1 1))
           :use ((:instance pfield::equal-of-0-and-add-of-neg-arg2
                            (x r1)
                            (y 1)
                            (p p))
                 (:instance pfield::equal-of-add-and-add-cancel-4
                            (y x)
                            (x (pfield::neg 1 p))
                            (z r1)
                            (p p)))
           :in-theory (e/d (bitp
                            pfield::sub
                            acl2::mod-of-1-arg1
                            pfield::mul-of-0-arg1
                            pfield::mul-of-1-arg1
                            pfield::equal-of-0-and-add-of-neg-arg2
                            fb3-base-prime-above-16)
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-field-pow-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp e)
                (pfield::fep z prime)
                (pfield::fep y0 prime)
                (pfield::fep y1 prime)
                (pfield::fep r1 prime)
                (pfield::fep sq prime)
                (pfield::fep pr prime))
           (equal (fb3-field-pow-2-pred x e z y0 y1 r1 sq pr prime)
                  (and (bitp y0)
                       (bitp y1)
                       (equal e (+ y0 (* 2 y1)))
                       (equal r1 (if (equal y1 1) x 1))
                       (equal (pfield::mul r1 r1 prime) sq)
                       (equal (pfield::mul sq x prime) pr)
                       (equal z (if (equal y0 1) pr sq))
                       (< e 4)
                       (equal z (field-pow-funspec x e))
                       (equal (list y0 y1)
                              (take 2 (field-bits-le e))))))
  :enable (fb3-field-pow-2-pred
           fb3-bool-check-is-bitp
           fb3-weighted-2
           fb3-if1-is-if1
           fb3-if-is-if
           fb3-pow-2-below-4
           fb3-pow-2-is-funspec
           fb3-bits-match-2)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))
