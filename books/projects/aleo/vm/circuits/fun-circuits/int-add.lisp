; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Add, AddAssign, AddChecked, AddWrapped.
;
; Add and AddAssign call add_checked, so they are that gadget.  The funspec
; of all three is int-add-checked-spec.
;
; snarkVM's variable-case circuits are the r1cs gadgets
;   unsigned-small-add-checked / signed-small-add-checked
;   unsigned-small-add-wrapped / signed-small-add-wrapped
; The small-add hypothesis n+1 < integer-length(p) holds for every integer
; width, including 128 (int-width-add-fits).

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-add-checked")
(include-book "../r1cs/signed-small-add-checked")
(include-book "../r1cs/unsigned-small-add-wrapped")
(include-book "../r1cs/signed-small-add-wrapped")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-add-checked-unsigned-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (carry symbolp)
                                         (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-add-checked-gadget xs ys zs carry p))

(define int-add-checked-signed-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (zs symbol-listp)
                                       (carry symbolp)
                                       (xy-diff symbolp)
                                       (zx-diff symbolp)
                                       (overflow symbolp)
                                       (one symbolp)
                                       (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-add-checked-gadget xs ys zs carry
                                   xy-diff zx-diff overflow one p))

; Add and AddAssign are add_checked.

(define int-add-unsigned-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (carry symbolp)
                                 (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-add-checked-unsigned-gadget xs ys zs carry p))

(define int-add-signed-gadget ((xs symbol-listp)
                               (ys symbol-listp)
                               (zs symbol-listp)
                               (carry symbolp)
                               (xy-diff symbolp)
                               (zx-diff symbolp)
                               (overflow symbolp)
                               (one symbolp)
                               (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-add-checked-signed-gadget xs ys zs carry
                                 xy-diff zx-diff overflow one p))

(define int-add-assign-unsigned-gadget ((xs symbol-listp)
                                        (ys symbol-listp)
                                        (zs symbol-listp)
                                        (carry symbolp)
                                        (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-add-checked-unsigned-gadget xs ys zs carry p))

(define int-add-assign-signed-gadget ((xs symbol-listp)
                                      (ys symbol-listp)
                                      (zs symbol-listp)
                                      (carry symbolp)
                                      (xy-diff symbolp)
                                      (zx-diff symbolp)
                                      (overflow symbolp)
                                      (one symbolp)
                                      (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-add-checked-signed-gadget xs ys zs carry
                                 xy-diff zx-diff overflow one p))

(defruled int-add-funspec-agrees
  (equal (int-add-checked-spec x y signedp n)
         (int-add-checked-spec x y signedp n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-add-checked-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (not signedp)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-add-checked-unsigned-gadget xs ys zs carry p)
                 asg p))
           (b* ((spec (int-add-checked-spec x y nil n)))
             (and (not (equal spec (spec-error)))
                  (equal (lookup-equal-list zs asg)
                         (int->lebits spec n)))))
  :enable (int-add-checked-unsigned-gadget
           unsigned-small-add-checked-gadget-correct
           int-add-checked-spec
           int-valuep
           int-min
           int-max
           int-width-add-fits
           lebits=>nat-of-int->lebits
           lebits->int-when-unsigned
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::lebits=>nat-injectivity))

(defruled int-add-checked-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-add-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y nil n) n))
                (equal (lookup-equal carry asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-checked-unsigned-gadget xs ys zs carry p)
            asg p))
  :enable (int-add-checked-unsigned-gadget
           unsigned-small-add-checked-gadget-correct
           int-add-checked-spec
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits))

(defruled int-add-checked-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (symbolp xy-diff)
                (symbolp zx-diff)
                (symbolp overflow)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (signedp)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg xy-diff)
                (r1cs::valuation-bindsp asg zx-diff)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (int-valuep x t n)
                (int-valuep y t n)
                (r1cs::r1cs-constraints-holdp
                 (int-add-checked-signed-gadget
                  xs ys zs carry xy-diff zx-diff overflow one p)
                 asg p))
           (b* ((spec (int-add-checked-spec x y t n)))
             (and (not (equal spec (spec-error)))
                  (equal (lebits=>int (lookup-equal-list zs asg))
                         spec))))
  :enable (int-add-checked-signed-gadget
           int-add-checked-spec
           int-valuep
           int-min
           int-max
           int-width-add-fits
           lebits->int-is-lebits=>int
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-add-checked-gadget-soundness)

(defruled int-add-gadget-sound-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-add-unsigned-gadget xs ys zs carry p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-add-checked-spec x y nil n) n)))
  :enable (int-add-unsigned-gadget
           int-add-checked-unsigned-gadget-sound))

(defruled int-add-assign-gadget-sound-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-add-assign-unsigned-gadget xs ys zs carry p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-add-checked-spec x y nil n) n)))
  :enable (int-add-assign-unsigned-gadget
           int-add-checked-unsigned-gadget-sound))

(defruled int-add-gadget-complete-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-add-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y nil n) n))
                (equal (lookup-equal carry asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-unsigned-gadget xs ys zs carry p) asg p))
  :enable (int-add-unsigned-gadget
           int-add-checked-unsigned-gadget-complete))

(defruled int-add-assign-gadget-complete-unsigned
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal (int-add-checked-spec x y nil n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y nil n) n))
                (equal (lookup-equal carry asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-assign-unsigned-gadget xs ys zs carry p) asg p))
  :enable (int-add-assign-unsigned-gadget
           int-add-checked-unsigned-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-add-wrapped-unsigned-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (carry symbolp)
                                         (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-add-wrapped-gadget xs ys zs carry p))

(define int-add-wrapped-signed-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (zs symbol-listp)
                                       (carry symbolp)
                                       (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (signed-small-add-wrapped-gadget xs ys zs carry p))

(defruled int-add-wrapped-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-add-wrapped-unsigned-gadget xs ys zs carry p) asg p))
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (int-add-wrapped-spec x y nil n)))
  :enable (int-add-wrapped-unsigned-gadget
           int-add-wrapped-spec
           int-wrap
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use unsigned-small-add-wrapped-gadget-soundness)

(defruled int-add-wrapped-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-add-wrapped-signed-gadget xs ys zs carry p) asg p))
           (equal (mod (lebits=>int (lookup-equal-list zs asg))
                       (expt 2 n))
                  (int-spec-unsigned (int-add-wrapped-spec x y t n) n)))
  :enable (int-add-wrapped-signed-gadget
           int-add-wrapped-spec
           int-wrap
           int-spec-unsigned
           int-width-add-fits
           lebits->int-is-lebits=>int
           lebits->int-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use signed-small-add-wrapped-gadget-soundness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 1+1 = 2, bits (1 0) + (1 0) = (0 1), carry 0.

(defconst *int-add-checked-sample*
  '((x0 . 1) (x1 . 0)
    (y0 . 1) (y1 . 0)
    (z0 . 0) (z1 . 1)
    (carry . 0)))

(defruled int-add-checked-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-add-checked-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'carry (base-prime))
   *int-add-checked-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-add-checked-unsigned-gadget
                                     unsigned-small-add-checked-gadget
                                     unsigned-small-add-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     zero-gadget
                                     pow2sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-add-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-add-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'carry (base-prime))
   *int-add-checked-sample*
   (base-prime))
  :enable (int-add-unsigned-gadget int-add-checked-sample-holds))

(defruled int-add-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-add-assign-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'carry (base-prime))
   *int-add-checked-sample*
   (base-prime))
  :enable (int-add-assign-unsigned-gadget int-add-checked-sample-holds))

(defruled int-add-wrapped-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-add-wrapped-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'carry (base-prime))
   *int-add-checked-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-add-wrapped-unsigned-gadget
                                     unsigned-small-add-wrapped-gadget
                                     unsigned-small-add-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     pow2sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-add-checked-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned checked addition on field images: @('(x + y) (1) = (z)').
          This is unsatisfiable when @($x+y$) does not fit in the integer."
  (pfcs::parse-def
   "int_add_checked(x, y, z) := {
    (x + y) * (1) == (z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-add-checked-circuit)
            :pred int-add-checked-pred
            :prime prime)

(defruled int-add-checked-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (natp z)
                (< z (expt 2 n))
                (< (+ x y) prime))
           (equal (int-add-checked-pred x y z prime)
                  (and (not (equal (int-add-checked-spec x y nil n)
                                   (spec-error)))
                       (equal z (int-add-checked-spec x y nil n)))))
  :enable (int-add-checked-pred
           int-add-checked-spec
           int-valuep
           int-min
           int-max))
