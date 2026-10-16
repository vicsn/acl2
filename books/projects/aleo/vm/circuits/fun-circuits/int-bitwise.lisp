; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BitAnd, BitOr, BitXor and the *_assign wrappers.
;
; snarkVM zips the little-endian bits and applies the boolean gadget.
; Boolean not does not appear.  The assign methods store the same bits.
; The r1cs/ integer-and, integer-or and integer-xor gadgets are those
; constraints, for every width, signed or unsigned.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/integer-and")
(include-book "../r1cs/integer-or")
(include-book "../r1cs/integer-xor")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-bitand-gadget ((xs symbol-listp)
                           (ys symbol-listp)
                           (zs symbol-listp))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (integer-and-gadget xs ys zs))

(define int-bitor-gadget ((xs symbol-listp)
                          (ys symbol-listp)
                          (zs symbol-listp)
                          (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (integer-or-gadget xs ys zs p))

(define int-bitxor-gadget ((xs symbol-listp)
                           (ys symbol-listp)
                           (zs symbol-listp)
                           (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (integer-xor-gadget xs ys zs p))

; BitAndAssign / BitOrAssign / BitXorAssign are the same circuits and the
; same funspecs (the result is written back into self).

(define int-bitand-assign-gadget ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-bitand-gadget xs ys zs))

(define int-bitor-assign-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-bitor-gadget xs ys zs p))

(define int-bitxor-assign-gadget ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp)
                                  (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-bitxor-gadget xs ys zs p))

(defruled int-bitand-assign-gadget-is-bitand
  (equal (int-bitand-assign-gadget xs ys zs)
         (int-bitand-gadget xs ys zs))
  :enable (int-bitand-assign-gadget int-bitand-gadget))

(defruled int-bitor-assign-gadget-is-bitor
  (equal (int-bitor-assign-gadget xs ys zs p)
         (int-bitor-gadget xs ys zs p))
  :enable (int-bitor-assign-gadget int-bitor-gadget))

(defruled int-bitxor-assign-gadget-is-bitxor
  (equal (int-bitxor-assign-gadget xs ys zs p)
         (int-bitxor-gadget xs ys zs p))
  :enable (int-bitxor-assign-gadget int-bitxor-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-bit-listp-when-equal-int->lebits
  (implies (equal bits (int->lebits x n))
           (bit-listp bits))
  :enable bit-listp-of-int->lebits-explicit)

(defruled int-bitand-gadget-to-bits
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (int-bitand-gadget xs ys zs) asg p)
                             (equal zs$ (bitand-list xs$ ys$))))))
  :enable (int-bitand-gadget integer-and-to-bitand-list))

(defruled int-bitand-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitand-gadget xs ys zs) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitand-spec x y signedp n) n)))
  :enable (int-bitand-gadget-to-bits
           int->lebits-of-int-bitand-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitand-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitand-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitand-gadget xs ys zs) asg p))
  :enable (int-bitand-gadget-to-bits
           int->lebits-of-int-bitand-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitand-assign-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitand-assign-gadget xs ys zs) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitand-spec x y signedp n) n)))
  :enable (int-bitand-assign-gadget-is-bitand
           int-bitand-gadget-sound))

(defruled int-bitand-assign-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitand-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitand-assign-gadget xs ys zs) asg p))
  :enable (int-bitand-assign-gadget-is-bitand
           int-bitand-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-bitor-gadget-to-bits
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (int-bitor-gadget xs ys zs p) asg p)
                             (equal zs$ (bitor-list xs$ ys$))))))
  :enable (int-bitor-gadget integer-or-to-bitor-list))

(defruled int-bitor-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitor-gadget xs ys zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitor-spec x y signedp n) n)))
  :enable (int-bitor-gadget-to-bits
           int->lebits-of-int-bitor-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitor-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitor-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitor-gadget xs ys zs p) asg p))
  :enable (int-bitor-gadget-to-bits
           int->lebits-of-int-bitor-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitor-assign-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitor-assign-gadget xs ys zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitor-spec x y signedp n) n)))
  :enable (int-bitor-assign-gadget-is-bitor
           int-bitor-gadget-sound))

(defruled int-bitor-assign-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitor-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitor-assign-gadget xs ys zs p) asg p))
  :enable (int-bitor-assign-gadget-is-bitor
           int-bitor-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-bitxor-gadget-to-bits
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (int-bitxor-gadget xs ys zs p) asg p)
                             (equal zs$ (bitxor-list xs$ ys$))))))
  :enable (int-bitxor-gadget integer-xor-to-bitxor-list))

(defruled int-bitxor-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitxor-gadget xs ys zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitxor-spec x y signedp n) n)))
  :enable (int-bitxor-gadget-to-bits
           int->lebits-of-int-bitxor-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitxor-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitxor-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitxor-gadget xs ys zs p) asg p))
  :enable (int-bitxor-gadget-to-bits
           int->lebits-of-int-bitxor-spec
           bit-listp-of-int->lebits-explicit
           int-bit-listp-when-equal-int->lebits))

(defruled int-bitxor-assign-gadget-sound
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-bitxor-assign-gadget xs ys zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-bitxor-spec x y signedp n) n)))
  :enable (int-bitxor-assign-gadget-is-bitxor
           int-bitxor-gadget-sound))

(defruled int-bitxor-assign-gadget-complete
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal n (len xs))
                (posp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-bitxor-spec x y signedp n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-bitxor-assign-gadget xs ys zs p) asg p))
  :enable (int-bitxor-assign-gadget-is-bitxor
           int-bitxor-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *int-bitand-sample*
  '((x0 . 1) (y0 . 1) (z0 . 1)
    (x1 . 0) (y1 . 1) (z1 . 0)))

(defruled int-bitand-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitand-gadget '(x0 x1) '(y0 y1) '(z0 z1))
   *int-bitand-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-bitand-gadget
                                     integer-and-gadget
                                     boolean-and-gadget-list
                                     boolean-and-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defconst *int-bitor-sample*
  '((x0 . 1) (y0 . 0) (z0 . 1)
    (x1 . 0) (y1 . 0) (z1 . 0)))

(defruled int-bitor-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitor-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-bitor-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-bitor-gadget
                                     integer-or-gadget
                                     boolean-or-gadget-list
                                     boolean-or-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defconst *int-bitxor-sample*
  '((x0 . 1) (y0 . 0) (z0 . 1)
    (x1 . 1) (y1 . 1) (z1 . 0)))

(defruled int-bitxor-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitxor-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-bitxor-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-bitxor-gadget
                                     integer-xor-gadget
                                     boolean-xor-gadget-list
                                     boolean-xor-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

; The assign samples are the same constraints.

(defruled int-bitand-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitand-assign-gadget '(x0 x1) '(y0 y1) '(z0 z1))
   *int-bitand-sample*
   (base-prime))
  :enable (int-bitand-assign-gadget-is-bitand int-bitand-sample-holds))

(defruled int-bitor-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitor-assign-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-bitor-sample*
   (base-prime))
  :enable (int-bitor-assign-gadget-is-bitor int-bitor-sample-holds))

(defruled int-bitxor-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-bitxor-assign-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-bitxor-sample*
   (base-prime))
  :enable (int-bitxor-assign-gadget-is-bitxor int-bitxor-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-bitand-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_bitand(x0, y0, z0, x1, y1, z1) := {
    (x0) * (y0) == (z0),
    (x1) * (y1) == (z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-bitand-circuit) :pred int-bitand-pred :prime prime)

(define int-bitor-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_bitor(x0, y0, z0, x1, y1, z1) := {
    (1 - x0) * (1 - y0) == (1 - z0),
    (1 - x1) * (1 - y1) == (1 - z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-bitor-circuit) :pred int-bitor-pred :prime prime)

(define int-bitxor-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_bitxor(x0, y0, z0, x1, y1, z1) := {
    (2 * x0) * (y0) == (x0 + y0 - z0),
    (2 * x1) * (y1) == (x1 + y1 - z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-bitxor-circuit) :pred int-bitxor-pred :prime prime)

(defruled int-bitand-pred-to-funspec
  :short "Width-2 instance of the same per-bit constraints as the gadget.
          Width 2 is not an @('integer-widthp'), but it is the same
          boolean-and constraint the gadget emits at every width."
  (implies (and (equal prime (base-prime))
                (bitp x0) (bitp y0) (bitp z0)
                (bitp x1) (bitp y1) (bitp z1)
                (int-valuep x signedp 2)
                (int-valuep y signedp 2)
                (equal (int->lebits x 2) (list x0 x1))
                (equal (int->lebits y 2) (list y0 y1)))
           (equal (int-bitand-pred x0 y0 z0 x1 y1 z1 prime)
                  (equal (list z0 z1)
                         (bitand-list (list x0 x1) (list y0 y1)))))
  :enable (int-bitand-pred
           bitand-list
           bitand
           pfield::mul-of-1-arg1
           pfield::mul-of-1-arg2
           pfield::mul-of-0-arg1
           pfield::mul-of-0-arg2))

(defruled int-bitor-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp x0) (bitp y0) (bitp z0)
                (bitp x1) (bitp y1) (bitp z1))
           (equal (int-bitor-pred x0 y0 z0 x1 y1 z1 prime)
                  (and (equal z0 (bitor x0 y0))
                       (equal z1 (bitor x1 y1)))))
  :enable (int-bitor-pred bitor))

(defruled int-bitxor-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp x0) (bitp y0) (bitp z0)
                (bitp x1) (bitp y1) (bitp z1))
           (equal (int-bitxor-pred x0 y0 z0 x1 y1 z1 prime)
                  (and (equal z0 (bitxor x0 y0))
                       (equal z1 (bitxor x1 y1)))))
  :enable (int-bitxor-pred bitxor))
