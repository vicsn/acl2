; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::pow on a variable exponent.
;
; snarkVM walks the big-endian bits of the exponent, squaring and then
; selecting multiply-or-keep with a ternary.  field-pow-gadget bitifies
; the exponent little-endian (field-to-bits-gadget) and runs that
; square-and-multiply from the high bit, which is the same schedule.
; field-pow-soundness already concludes pfield::pow.  The funspec is
; that operation.
;
; Completeness needs every square, product, and range-check witness.
; A PFCS of 253 iterations is not written.  The sample is the gadget at
; the odd prime 5: 3^2 = 4.

(in-package "ALEOVM")

(include-book "../r1cs/field-pow")
(include-book "../fun-specs/primitives-field")
(include-book "../library-extensions/digits")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-pow-gadget ((x symbolp)
                             (y symbolp)
                             (ys symbol-listp)
                             (zs symbol-listp)
                             (ss symbol-listp)
                             (ps symbol-listp)
                             (rs symbol-listp)
                             (unitvar symbolp)
                             (p primep))
  :guard (and (oddp p)
              (equal (len ys) (integer-length p))
              (equal (len zs) (bits-lt-prime-rlen p))
              (equal (len rs) (len ys))
              (equal (len ss) (1- (len ys)))
              (equal (len ps) (1- (len ys))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-pow-gadget x y ys zs ss ps rs unitvar p))

(defruled fb-field-pow-gadget-sound
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
                (r1cs::r1cs-constraints-holdp
                 (fb-field-pow-gadget x y ys zs ss ps rs unitvar p)
                 asg p))
           (equal (car (lookup-equal-list rs asg))
                  (field-pow-funspec (lookup-equal x asg)
                                     (lookup-equal y asg))))
  :do-not-induct t
  :enable (fb-field-pow-gadget field-pow-funspec fieldp)
  :use field-pow-soundness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime 5, base 3, exponent 2 = bits (0 1 0).
; Square-and-multiply witnesses: ss = (4 1), ps = (2 3), rs = (4 3 1).
; Bit-range witnesses for the exponent: zs = (1 0), unit = 1.
; 3^2 = 4.

(defconst *fb-field-pow-prime* 5)

(defconst *fb-field-pow-asg*
  '((x . 3) (y . 2)
    (y0 . 0) (y1 . 1) (y2 . 0)
    (z0 . 1) (z1 . 0)
    (s0 . 4) (s1 . 1)
    (p0 . 2) (p1 . 3)
    (r0 . 4) (r1 . 3) (r2 . 1)
    (u . 1)))

(defrule fb-field-pow-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-pow-gadget 'x 'y '(y0 y1 y2) '(z0 z1)
                        '(s0 s1) '(p0 p1) '(r0 r1 r2) 'u
                        *fb-field-pow-prime*)
   *fb-field-pow-asg*
   *fb-field-pow-prime*)
  :enable (fb-field-pow-gadget
           field-pow-gadget
           field-to-bits-gadget
           field-pow-bits-gadget
           field-pow-bits-gadget-aux
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           bits-lt-prime-gadget
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-unit-gadget
           if-gadget
           if1-gadget
           field-mul-gadget
           field-square-gadget
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
