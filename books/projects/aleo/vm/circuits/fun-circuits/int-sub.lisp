; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sub, SubAssign, SubChecked, SubWrapped.
;
; Sub and SubAssign call sub_checked.  The variable-case circuits are
; r1cs/unsigned-small-sub-checked, signed-small-sub-checked,
; unsigned-small-sub-wrapped and signed-small-sub-wrapped.
; n+1 < integer-length(p) holds for every width, including 128.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-sub-checked")
(include-book "../r1cs/signed-small-sub-checked")
(include-book "../r1cs/unsigned-small-sub-wrapped")
(include-book "../r1cs/signed-small-sub-wrapped")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-sub-checked-unsigned-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (z symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-sub-checked-gadget xs ys zs z one p))

(define int-sub-unsigned-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (z symbolp)
                                 (one symbolp)
                                 (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-sub-checked-unsigned-gadget xs ys zs z one p))

(define int-sub-assign-unsigned-gadget ((xs symbol-listp)
                                        (ys symbol-listp)
                                        (zs symbol-listp)
                                        (z symbolp)
                                        (one symbolp)
                                        (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-sub-checked-unsigned-gadget xs ys zs z one p))

(defruled int-sub-funspec-agrees
  (equal (int-sub-checked-spec x y signedp n)
         (int-sub-checked-spec x y signedp n)))

(defruled int-sub-checked-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (not signedp)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-sub-checked-unsigned-gadget xs ys zs z one p)
                 asg p))
           (and (equal (lookup-equal z asg) 1)
                (not (equal (int-sub-checked-spec x y nil n) (spec-error)))
                (equal (lebits=>nat (lookup-equal-list zs asg))
                       (int-sub-checked-spec x y nil n))))
  :enable (int-sub-checked-unsigned-gadget
           unsigned-small-sub-checked-gadget-correct
           int-sub-checked-spec
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit))

(defruled int-sub-checked-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-sub-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y nil n) n))
                (equal (lookup-equal z asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-sub-checked-unsigned-gadget xs ys zs z one p) asg p))
  :enable (int-sub-checked-unsigned-gadget
           unsigned-small-sub-checked-gadget-correct
           int-sub-checked-spec
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits))

(defruled int-sub-gadget-sound-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-sub-unsigned-gadget xs ys zs z one p) asg p))
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (int-sub-checked-spec x y nil n)))
  :enable (int-sub-unsigned-gadget
           int-sub-checked-unsigned-gadget-sound))

(defruled int-sub-assign-gadget-sound-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-sub-assign-unsigned-gadget xs ys zs z one p) asg p))
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (int-sub-checked-spec x y nil n)))
  :enable (int-sub-assign-unsigned-gadget
           int-sub-checked-unsigned-gadget-sound))

(defruled int-sub-gadget-complete-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-sub-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y nil n) n))
                (equal (lookup-equal z asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-sub-unsigned-gadget xs ys zs z one p) asg p))
  :enable (int-sub-unsigned-gadget
           int-sub-checked-unsigned-gadget-complete))

(defruled int-sub-assign-gadget-complete-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-sub-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y nil n) n))
                (equal (lookup-equal z asg) 1))
           (r1cs::r1cs-constraints-holdp
            (int-sub-assign-unsigned-gadget xs ys zs z one p) asg p))
  :enable (int-sub-assign-unsigned-gadget
           int-sub-checked-unsigned-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-sub-wrapped-unsigned-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (z symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-sub-wrapped-gadget xs ys zs z one p))

(defruled int-sub-wrapped-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-sub-wrapped-unsigned-gadget xs ys zs z one p) asg p))
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (int-sub-wrapped-spec x y nil n)))
  :enable (int-sub-wrapped-unsigned-gadget
           int-sub-wrapped-spec
           int-wrap
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use unsigned-small-sub-wrapped-gadget-soundness)

(define int-sub-checked-signed-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (zs symbol-listp)
                                       (carry symbolp)
                                       (xy-diff symbolp)
                                       (zy-diff symbolp)
                                       (overflow symbolp)
                                       (one symbolp)
                                       (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-sub-checked-gadget xs ys zs carry
                                   xy-diff zy-diff overflow one p))

(define int-sub-signed-gadget ((xs symbol-listp)
                               (ys symbol-listp)
                               (zs symbol-listp)
                               (carry symbolp)
                               (xy-diff symbolp)
                               (zy-diff symbolp)
                               (overflow symbolp)
                               (one symbolp)
                               (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-sub-checked-signed-gadget xs ys zs carry
                                 xy-diff zy-diff overflow one p))

(define int-sub-assign-signed-gadget ((xs symbol-listp)
                                      (ys symbol-listp)
                                      (zs symbol-listp)
                                      (carry symbolp)
                                      (xy-diff symbolp)
                                      (zy-diff symbolp)
                                      (overflow symbolp)
                                      (one symbolp)
                                      (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-sub-checked-signed-gadget xs ys zs carry
                                 xy-diff zy-diff overflow one p))

(defruled int-sub-checked-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry) (symbolp xy-diff) (symbolp zy-diff)
                (symbolp overflow) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg xy-diff)
                (r1cs::valuation-bindsp asg zy-diff)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-sub-checked-signed-gadget
                  xs ys zs carry xy-diff zy-diff overflow one p)
                 asg p))
           (equal (lebits=>int (lookup-equal-list zs asg))
                  (int-sub-checked-spec x y t n)))
  :enable (int-sub-checked-signed-gadget
           int-sub-checked-spec
           int-width-add-fits
           lebits->int-is-lebits=>int
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-sub-checked-gadget-soundness)

; 2 - 1 = 1 at width 2.  Bits (0 1) - (1 0) = (1 0), and the checked
; borrow/carry indicator z is 1.

(defconst *int-sub-checked-sample*
  '((x0 . 0) (x1 . 1)
    (y0 . 1) (y1 . 0)
    (z0 . 1) (z1 . 0)
    (z . 1)
    (one . 1)))

(defruled int-sub-checked-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-sub-checked-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'z 'one (base-prime))
   *int-sub-checked-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-sub-checked-unsigned-gadget
                                     unsigned-small-sub-checked-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled int-sub-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-sub-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'z 'one (base-prime))
   *int-sub-checked-sample*
   (base-prime))
  :enable (int-sub-unsigned-gadget int-sub-checked-sample-holds))

(defruled int-sub-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-sub-assign-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'z 'one (base-prime))
   *int-sub-checked-sample*
   (base-prime))
  :enable (int-sub-assign-unsigned-gadget int-sub-checked-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-sub-checked-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned checked subtraction on field images, with the
          @($2^n$) offset that makes the difference non-negative."
  (pfcs::parse-def
   "int_sub_checked(x, y, z, n2) := {
    (n2 + x - y) * (1) == (n2 + z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-sub-checked-circuit)
            :pred int-sub-checked-pred
            :prime prime)

(defruled int-sub-checked-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (natp z)
                (< z (expt 2 n))
                (equal n2 (expt 2 n))
                (< (+ n2 x) prime))
           (equal (int-sub-checked-pred x y z n2 prime)
                  (and (not (equal (int-sub-checked-spec x y nil n)
                                   (spec-error)))
                       (equal z (int-sub-checked-spec x y nil n)))))
  :enable (int-sub-checked-pred
           int-sub-checked-spec
           int-valuep
           int-min
           int-max))
