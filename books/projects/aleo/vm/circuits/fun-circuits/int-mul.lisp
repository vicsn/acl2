; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Mul, MulAssign, MulChecked, MulWrapped, mul_and_check, karatsuba_multiply,
; mul_with_flags.
;
; Mul and MulAssign call mul_checked.
;
; For unsigned widths with 2*n < 252 (8, 16, 32, 64) snarkVM's mul_and_check
; is one field multiplication of the bit-weighted sums, which is
; r1cs/unsigned-small-mul-and-check.  The product witness is boolean-checked
; by Integer::new.  Width 128 uses Karatsuba and is not this constraint.
; Signed mul_checked takes absolute values, calls mul_and_check, then checks
; the sign; that composition is not the unsigned gadget.
;
; mul_wrapped is the Babbage circuit r1cs/unsigned-small-mul-wrapped
; (signed-small-mul-wrapped is the same constraints).  Its soundness
; hypothesis requires the n + n/2 + 1 bit sum to fit in the field, which
; fails for 128.
;
; These theorems are therefore explicitly restricted.  The CSV flags for
; soundness and completeness stay 0.  See bugs-int.txt.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-mul-and-check")
(include-book "../r1cs/unsigned-small-mul-wrapped")
(include-book "../r1cs/boolean-check")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-mul-and-check-gadget ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp)
                                  (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len xs) (len zs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single field product.  Output bits are checked separately."
  (append (boolean-check-gadget-list zs p)
          (unsigned-small-mul-and-check-gadget xs ys zs p)))

(define int-mul-checked-unsigned-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len xs) (len zs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-mul-and-check-gadget xs ys zs p))

(define int-mul-unsigned-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len xs) (len zs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-mul-checked-unsigned-gadget xs ys zs p))

(define int-mul-assign-unsigned-gadget ((xs symbol-listp)
                                        (ys symbol-listp)
                                        (zs symbol-listp)
                                        (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len xs) (len zs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-mul-checked-unsigned-gadget xs ys zs p))

(defruled int-mul-and-check-gadget-to-product
  (implies (and (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mul-and-check-gadget xs ys zs p) asg p)
                  (and (bit-listp (lookup-equal-list zs asg))
                       (equal (mod (* (lebits=>nat (lookup-equal-list xs asg))
                                      (lebits=>nat (lookup-equal-list ys asg)))
                                   p)
                              (mod (lebits=>nat (lookup-equal-list zs asg))
                                   p)))))
  :enable (int-mul-and-check-gadget
           unsigned-small-mul-and-check-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::mul
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           r1cs::r1cs-constraints-holdp-of-append))

(defruledl int-mul-product-below-double-width
  (implies (and (natp x) (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (* x y) (* (expt 2 n) (expt 2 n))))
  :hints (("Goal" :nonlinearp t)))

(defruledl int-mul-small-product-in-field
  (implies (and (integer-widthp n)
                (not (equal n 128))
                (natp x)
                (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (* x y) (base-prime)))
  :do-not-induct t
  :hints (("Goal"
           :use int-mul-product-below-double-width
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :in-theory (enable integer-widthp
                              (:e expt)
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl lebits=>nat-of-int->lebits-when-unsigned
  (implies (and (posp n)
                (int-valuep x nil n))
           (equal (lebits=>nat (int->lebits x n)) x))
  :enable (lebits=>nat-of-int->lebits
           int-valuep
           int-min
           int-max
           acl2::mod-when-<))

(defruledl lebits=>nat-when-lookup-is-int->lebits
  (implies (and (equal (lookup-equal-list xs asg) (int->lebits x n))
                (posp n)
                (int-valuep x nil n))
           (equal (lebits=>nat (lookup-equal-list xs asg)) x))
  :enable lebits=>nat-of-int->lebits-when-unsigned)

(defruledl bit-listp-when-lookup-is-int->lebits
  (implies (equal (lookup-equal-list xs asg) (int->lebits x n))
           (bit-listp (lookup-equal-list xs asg)))
  :enable bit-listp-of-int->lebits-explicit)

(defruled int-mul-checked-unsigned-small-sound
  :short "Unsigned only, and not 128-bit.  Not a full-width theorem."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (not signedp)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-checked-unsigned-gadget xs ys zs p) asg p))
           (and (not (equal (int-mul-checked-spec x y nil n) (spec-error)))
                (equal (lebits=>nat (lookup-equal-list zs asg))
                       (int-mul-checked-spec x y nil n))))
  :do-not-induct t
  :use ((:instance int-mul-and-check-gadget-to-product (p (base-prime)))
        (:instance int-mul-small-product-in-field (n (len xs)))
        (:instance int-width-lt-prime-bits (n (len xs)))
        (:instance lebits=>nat-less-when-len-less
                   (bs (lookup-equal-list zs asg))
                   (p (base-prime))))
  :enable (int-mul-checked-unsigned-gadget
           int-mul-checked-spec
           lebits=>nat-when-lookup-is-int->lebits
           bit-listp-when-lookup-is-int->lebits
           integer-length-of-base-prime
           posp-when-integer-widthp
           acl2::mod-when-<
           int-valuep
           int-min
           int-max)
  :disable (mod floor))

(defruled int-mul-gadget-is-mul-checked
  (equal (int-mul-unsigned-gadget xs ys zs p)
         (int-mul-checked-unsigned-gadget xs ys zs p))
  :enable (int-mul-unsigned-gadget int-mul-checked-unsigned-gadget))

(defruled int-mul-assign-gadget-is-mul-checked
  (equal (int-mul-assign-unsigned-gadget xs ys zs p)
         (int-mul-checked-unsigned-gadget xs ys zs p))
  :enable (int-mul-assign-unsigned-gadget
           int-mul-checked-unsigned-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-mul-wrapped-gadget ((xs symbol-listp)
                                (ys symbol-listp)
                                (lowlow symbolp)
                                (highlow symbolp)
                                (lowhigh symbolp)
                                (zs symbol-listp)
                                (zs-high symbol-listp)
                                (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-high) (1+ (floor (len xs) 2)))
              (< (len (append zs zs-high)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-mul-wrapped-gadget xs ys lowlow highlow lowhigh
                                     zs zs-high p))

(defruled int-mul-wrapped-small-sound
  :short "Not 128-bit.  The carried high half must fit in the field."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (not signedp)
                (evenp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len zs-high) (1+ (floor n 2)))
                (< (len (append zs zs-high)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh
                                         zs zs-high p)
                 asg p))
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (int-mul-wrapped-spec x y nil n)))
  :enable (int-mul-wrapped-gadget
           int-mul-wrapped-spec
           int-wrap
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use unsigned-small-mul-wrapped-gadget-soundness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 2 * 3 = 6 does not fit in 2 bits, so the sample is 1 * 1 = 1.

(defconst *int-mul-and-check-sample*
  '((x0 . 1) (x1 . 0)
    (y0 . 1) (y1 . 0)
    (z0 . 1) (z1 . 0)))

(defruled int-mul-and-check-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-mul-and-check-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-mul-and-check-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-mul-and-check-gadget
                                     unsigned-small-mul-and-check-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     pow2sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-mul-checked-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-mul-checked-unsigned-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-mul-and-check-sample*
   (base-prime))
  :enable (int-mul-checked-unsigned-gadget int-mul-and-check-sample-holds))

(defruled int-mul-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-mul-unsigned-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-mul-and-check-sample*
   (base-prime))
  :enable (int-mul-gadget-is-mul-checked int-mul-checked-sample-holds))

(defruled int-mul-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-mul-assign-unsigned-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-mul-and-check-sample*
   (base-prime))
  :enable (int-mul-assign-gadget-is-mul-checked
           int-mul-checked-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-mul-and-check-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_mul_and_check(x, y, z) := {
    (x) * (y) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-mul-and-check-circuit)
            :pred int-mul-and-check-pred
            :prime prime)

(defruledl int-width-double-below-data-bits
  (implies (and (integer-widthp n)
                (not (equal n 128)))
           (< (* 2 n) 252))
  :enable integer-widthp)

(defruled int-mul-and-check-pred-to-funspec
  :short "Unsigned, product below the field, not the 128-bit Karatsuba case."
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (natp z)
                (< z (expt 2 n))
                (< (* x y) prime))
           (equal (int-mul-and-check-pred x y z prime)
                  (and (not (equal (int-mul-and-check-spec x y nil n)
                                   (spec-error)))
                       (equal z (int-mul-and-check-spec x y nil n)))))
  :enable (int-mul-and-check-pred
           int-mul-and-check-spec
           pfield::mul
           acl2::mod-when-<
           posp-when-integer-widthp
           int-width-double-below-data-bits
           int-spec-field-data-bits
           base-field-size-in-bits
           int-spec-unsigned
           int-wrap
           int-valuep
           int-min
           int-max))

; Karatsuba and mul_with_flags are the 128-bit (and the flag) variants.
; The product field equation above is not their circuit.  Gadgets:

(define int-karatsuba-low-gadget ((x0 symbolp) (y0 symbolp) (z0 symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The @($z_0 = x_0 y_0$) factor inside Karatsuba.  Not the whole
          algorithm, and not claimed sound for the funspec."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x0))
         :b (list (list 1 y0))
         :c (list (list 1 z0)))))

(defconst *int-karatsuba-sample*
  '((x0 . 2) (y0 . 3) (z0 . 6)))

(defruled int-karatsuba-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-karatsuba-low-gadget 'x0 'y0 'z0)
   *int-karatsuba-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-karatsuba-low-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(define int-mul-with-flags-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Small-width flag: the witnessed product differs from the field
          product iff the overflow bit is 1."
  (pfcs::parse-def
   "int_mul_with_flags(x, y, z, flag, w) := {
    (x) * (y) == (pxy),
    (pxy - z) * (w) == (flag),
    (pxy - z) * (1 - flag) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

; pfcs::lift proves its theorem in a fixed theory without fep-of-mul.
; Here the first constraint binds the free pxy to (mul x y prime), so the
; only-if lemma needs that rule.  This is pfcs::lift with it added.

(local
 (defun int-subst-equal (new old tree)
   (declare (xargs :guard t))
   (cond ((equal tree old) new)
         ((atom tree) tree)
         (t (cons (int-subst-equal new old (car tree))
                  (int-subst-equal new old (cdr tree)))))))

(make-event
 (int-subst-equal '((:e no-duplicatesp-equal)
                    (:e pfcs::namep)
                    pfield::fep-of-mul
                    acl2::primep-forward-to-posp)
                  '((:e no-duplicatesp-equal)
                    (:e pfcs::namep))
                  (pfcs::lift-fn (int-mul-with-flags-circuit)
                                 'int-mul-with-flags-pred
                                 'prime
                                 state)))

; pxy is free in the definition, so the lifted predicate quantifies it.
; The small-width flag agrees with int-mul-with-flags-spec only when that
; witness is the field product.  Not claimed for 128-bit Karatsuba.
