; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shl, ShlAssign, ShlChecked, ShlWrapped, Shr, ShrAssign, ShrChecked,
; ShrWrapped.
;
; Shl and ShlAssign call shl_checked.  Shr and ShrAssign call shr_checked.
; shr_checked is shr_wrapped plus Boolean::assert_bits_are_zero on the
; exponent bits at and above log2(n).  That excess check is
; int-from-bits-le-gadget.
;
; The shift itself, for widths with 2*n < 252, is a field multiplication
; by a power of two built from the low log2(n) exponent bits, then
; to_lower_bits.  Width 128 uses pow_checked or mul_wrapped and is not
; covered.  Signed shl_checked has an extra sign-extension check.
; Soundness and completeness are not claimed for every width.
;
; Funspec agreement: shl is shl_checked, shr is shr_checked, and
; shr_checked is shr_wrapped when the exponent is below n.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-bits")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shl-checked-bound-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Exponent bits at and above @('log2(n)') must be zero."
  (int-from-bits-le-gadget excess))

(define int-shl-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-bound-gadget excess))

(define int-shl-assign-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-bound-gadget excess))

(define int-shr-checked-bound-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-from-bits-le-gadget excess))

(define int-shr-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-bound-gadget excess))

(define int-shr-assign-unsigned-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-bound-gadget excess))

(defruled int-shr-checked-is-wrapped-when-in-range
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (natp e)
                (< e n))
           (equal (int-shr-checked-spec x e signedp n)
                  (int-shr-wrapped-spec x e signedp n)))
  :hints (("Goal" :in-theory (e/d (int-shr-checked-spec
                                   int-shr-wrapped-spec
                                   acl2::mod-when-<)
                                  (floor mod)))))

(defruled int-shl-checked-errors-when-exponent-wide
  (implies (and (integer-widthp n)
                (natp e)
                (>= e n))
           (equal (int-shl-checked-spec x e signedp n)
                  (spec-error)))
  :enable int-shl-checked-spec)

(defruled int-shr-checked-errors-when-exponent-wide
  (implies (and (integer-widthp n)
                (natp e)
                (>= e n))
           (equal (int-shr-checked-spec x e signedp n)
                  (spec-error)))
  :enable int-shr-checked-spec)

; A left shift by 1 of the value 1, at a width where 2 fits, is the
; field product (1) * (2) = (2).  This is the small-width shift step,
; not the 128-bit pow_checked fallback.

(defconst *int-shl-sample*
  '((x . 1) (two . 2) (z . 2)))

(defruled int-shl-sample-holds
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'x))
          :b (list (list 1 'two))
          :c (list (list 1 'z))))
   *int-shl-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-shl-checked-bound-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shl-checked-bound-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shl-checked-bound-gadget int-from-bits-le-sample-holds))

(defruled int-shr-checked-bound-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shr-checked-bound-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shr-checked-bound-gadget int-from-bits-le-sample-holds))

(defruled int-shl-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shl-assign-unsigned-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shl-assign-unsigned-gadget
           int-shl-checked-bound-sample-holds))

(defruled int-shr-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-shr-assign-unsigned-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-shr-assign-unsigned-gadget
           int-shr-checked-bound-sample-holds))

; The bits at and above log2(n) = (integer-length n)-1 are the excess
; passed to int-from-bits-le-gadget.  Every integer width is a power of
; two, so forcing those bits to 0 forces the exponent below n.  This is
; the exponent check only: it does not perform the shift.

(defruledl int-lebits-below-when-nthcdr-repeat
  (implies (and (bit-listp bits)
                (natp n)
                (equal xs (nthcdr n bits))
                (equal xs (repeat (len xs) 0)))
           (< (lebits=>nat bits) (expt 2 n)))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-lebits-below-pow2-when-excess-zero)
           :in-theory (disable nthcdr repeat
                               acl2::open-small-nthcdr
                               acl2::len-of-nthcdr
                               acl2::repeat-of-nfix))))

(defruled int-exponent-bound-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (bit-listp ebits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n)) ebits))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget excess) asg p))
           (< (lebits=>nat ebits) n))
  :do-not-induct t
  :use ((:instance int-excess-bits-sum-forces-all-zero
                   (p (base-prime)))
        (:instance int-lebits-below-when-nthcdr-repeat
                   (bits ebits)
                   (n (1- (integer-length n)))
                   (xs (nthcdr (1- (integer-length n)) ebits))))
  :enable (int-width-is-power-of-two
           integer-widthp
           posp-when-integer-widthp
           int-bit-listp-of-nthcdr
           int-len-nthcdr-is-len-excess)
  :disable (repeat nthcdr acl2::open-small-nthcdr
                   acl2::len-of-nthcdr acl2::repeat-of-nfix))

(defruled int-shl-checked-bound-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (bit-listp ebits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n)) ebits))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-bound-gadget excess) asg p))
           (< (lebits=>nat ebits) n))
  :enable (int-shl-checked-bound-gadget
           int-exponent-bound-gadget-sound))

(defruled int-shr-checked-bound-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (bit-listp ebits)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n)) ebits))
                (< (len excess) p)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-bound-gadget excess) asg p))
           (< (lebits=>nat ebits) n))
  :enable (int-shr-checked-bound-gadget
           int-exponent-bound-gadget-sound))

; Small-width left shift step: one field product by a power of two.
; For n other than 128, 2*n < 253, so x * 2^e with e < n does not wrap
; in the base field.  This is not pow_checked and not the full shift.

(defruledl int-shl-product-below-double-width
  (implies (and (natp x)
                (natp e)
                (natp n)
                (< x (expt 2 n))
                (< e n))
           (< (* x (expt 2 e)) (expt 2 (* 2 n))))
  :hints (("Goal"
           :use ((:instance acl2::<-of-*-and-*-cancel
                            (x1 x)
                            (x2 (expt 2 n))
                            (y (expt 2 e)))
                 (:instance acl2::*-of-expt-and-expt-same-base
                            (r 2) (i1 n) (i2 e))
                 (:instance acl2::<-of-expt-and-expt-same-base
                            (r 2) (i (+ n e)) (j (* 2 n))))
           :in-theory (disable acl2::<-of-*-and-*-cancel
                               acl2::*-of-expt-and-expt-same-base
                               acl2::<-of-expt-and-expt-same-base))))

(defruledl int-shl-pow2-product-in-field
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (natp x)
                (natp e)
                (< x (expt 2 n))
                (< e n))
           (< (* x (expt 2 e)) p))
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :use ((:instance acl2::<-of-integer-length-arg2
                            (x (base-prime))
                            (n 252))
                 (:instance int-shl-product-below-double-width)
                 (:instance acl2::<-of-expt-and-expt-same-base
                            (r 2) (i (* 2 n)) (j 252)))
           :in-theory (enable integer-widthp
                              integer-length-of-base-prime))))

(defruled int-shl-field-mul-by-pow2
  :short "One constraint @('(x) * (2^e) = (z)') is the integer product, for a width other than 128."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (natp e)
                (< e n)
                (int-valuep x nil n)
                (symbolp xv)
                (symbolp twoe)
                (symbolp zv)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xv)
                (r1cs::valuation-bindsp asg twoe)
                (r1cs::valuation-bindsp asg zv)
                (equal (lookup-equal xv asg) (ifix x))
                (equal (lookup-equal twoe asg) (expt 2 e))
                (r1cs::r1cs-constraints-holdp
                 (list (r1cs::make-r1cs-constraint
                        :a (list (list 1 xv))
                        :b (list (list 1 twoe))
                        :c (list (list 1 zv))))
                 asg p))
           (equal (lookup-equal zv asg)
                  (* (ifix x) (expt 2 e))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-shl-pow2-product-in-field
                           (x (ifix x))
                           (p (base-prime)))
           :in-theory (e/d (r1cs::r1cs-constraints-holdp
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            pfield::mul
                            pfield::add
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<)
                           (mod floor
                            lookup-equal
                            acl2::equal-of-mod-same-arg1)))))

(defruled int-shl-field-mul-in-range-is-checked-spec
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (natp e)
                (< e n)
                (int-valuep x nil n)
                (symbolp xv)
                (symbolp twoe)
                (symbolp zv)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xv)
                (r1cs::valuation-bindsp asg twoe)
                (r1cs::valuation-bindsp asg zv)
                (equal (lookup-equal xv asg) (ifix x))
                (equal (lookup-equal twoe asg) (expt 2 e))
                (int-valuep (lookup-equal zv asg) nil n)
                (r1cs::r1cs-constraints-holdp
                 (list (r1cs::make-r1cs-constraint
                        :a (list (list 1 xv))
                        :b (list (list 1 twoe))
                        :c (list (list 1 zv))))
                 asg p))
           (equal (lookup-equal zv asg)
                  (int-shl-checked-spec x e nil n)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shl-field-mul-by-pow2
           :in-theory (e/d (int-shl-checked-spec
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-shl-field-mul-by-pow2)))))

(defruled int-shl-wrapped-sample-holds
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'x))
          :b (list (list 1 'two))
          :c (list (list 1 'z))))
   *int-shl-sample*
   (base-prime))
  :enable int-shl-sample-holds)

(defruled int-shr-wrapped-sample-holds
  :short "Right shift by 1 of 2 yields 1.  The same assignment satisfies
          @('1 * 2 = 2'), with @('x') the result and @('z') the input."
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'x))
          :b (list (list 1 'two))
          :c (list (list 1 'z))))
   *int-shl-sample*
   (base-prime))
  :enable int-shl-sample-holds)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shl-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_shl_step(x, two, z) := {
    (x) * (two) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-shl-circuit) :pred int-shl-pred :prime prime)

(defruled int-shl-pred-to-shift
  (implies (and (equal prime (base-prime))
                (natp x) (natp z)
                (< (* 2 x) prime)
                (equal two 2))
           (equal (int-shl-pred x two z prime)
                  (equal z (* 2 x))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-shl-pred
                            pfield::mul
                            acl2::mod-when-<)
                           (mod floor)))))
