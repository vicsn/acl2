; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SubWrapped::sub_wrapped for both signednesses and every width.
;
; In variable mode snarkVM computes the field element
; self.to_field() + (!other).to_field() + 1, which is 2^n + X - Y for the
; unsigned readings X, Y of the input bits, and takes its low n+1 bits,
; dropping the carry.  to_field reads the bits as unsigned whatever the
; signedness, so the constraints are unsigned-small-sub-wrapped-gadget for
; signed and unsigned types alike.  The output integer is read with
; lebits->int at the type's signedness.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-sub-wrapped")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-sub-wrapped-gadget ((xs symbol-listp)
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
  :short "Variable-mode @('sub_wrapped'), either signedness."
  (unsigned-small-sub-wrapped-gadget xs ys zs z one p))

(defruledl int-divshift-mod-diff-of-mods
  (implies (and (integerp x) (integerp y) (posp m))
           (equal (mod (- (mod x m) (mod y m)) m)
                  (mod (- x y) m))))

(defruledl int-divshift-lebits->int-when-nat-is-mod
  (implies (and (posp n)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (lebits->int bits signedp)
                  (int-wrap v signedp n)))
  :enable (lebits->int int-wrap))

(defruledl int-divshift-bits-from-mod
  (implies (and (natp n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable int->lebits)

(defruled int-divshift-sub-wrapped-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sub-wrapped-gadget xs ys zs z one p) asg p))
           (and (bit-listp (lookup-equal-list zs asg))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lebits->int (lookup-equal-list zs asg) signedp)
                       (int-sub-wrapped-spec x y signedp n))))
  :do-not-induct t
  :use (unsigned-small-sub-wrapped-gadget-soundness
        (:instance int-divshift-mod-diff-of-mods (m (expt 2 n)))
        (:instance int-divshift-lebits->int-when-nat-is-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y)))
        (:instance int-valuep-of-lebits->int
                   (bits (lookup-equal-list zs asg)))
        (:instance lebits->int-of-int->lebits
                   (x (int-sub-wrapped-spec x y signedp n)))
        (:instance int-divshift-bits-from-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y))))
  :enable (int-divshift-sub-wrapped-gadget
           int-sub-wrapped-spec
           int->lebits-of-int-wrap
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp
           len-of-lookup-equal-list
           int-valuep))

(defruledl int-divshift-int->lebits-of-offset
  (implies (and (posp n) (integerp x) (integerp y))
           (equal (int->lebits (+ (expt 2 n)
                                  (mod x (expt 2 n))
                                  (- (mod y (expt 2 n))))
                               n)
                  (int->lebits (- x y) n)))
  :enable int->lebits)

(defruledl int-divshift-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

(defruledl int-divshift-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruledl int-divshift-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

(defruledl int-divshift-sub-wrapped-offset-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (natp a) (natp b)
                (< a (expt 2 n)) (< b (expt 2 n))
                (equal (lookup-equal-list xs asg) (int->lebits a n))
                (equal (lookup-equal-list ys asg) (int->lebits b n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) a (- b)) n))
                (equal (lookup-equal z asg) (if (< a b) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-wrapped-gadget xs ys zs z one p) asg p))
  :do-not-induct t
  :use ((:instance unsigned-small-sub-gadget-correct
                   (zs (append zs (list z))))
        (:instance int-unsigned-lt-offset (x a) (y b)))
  :enable (unsigned-small-sub-wrapped-gadget
           int-divshift-valuation-binds-allp-of-nil
           int-divshift-lookup-equal-list-of-nil
           int-divshift-lebits=>nat-of-nil
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           bit-listp-of-append-of-bit
           symbol-listp-of-append-of-symbol
           len-of-append-of-singleton
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits))

(defruledl int-divshift-int->lebits-of-mod
  (implies (posp n)
           (equal (int->lebits (mod x (expt 2 n)) n)
                  (int->lebits x n)))
  :enable int->lebits)

(defruled int-divshift-sub-wrapped-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lookup-equal z asg)
                       (if (< (mod x (expt 2 n)) (mod y (expt 2 n))) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-sub-wrapped-gadget xs ys zs z one p) asg p))
  :do-not-induct t
  :use ((:instance int-divshift-sub-wrapped-offset-holds
                   (a (mod x (expt 2 n)))
                   (b (mod y (expt 2 n))))
        (:instance int-divshift-int->lebits-of-offset)
        (:instance int-divshift-int->lebits-of-mod)
        (:instance int-divshift-int->lebits-of-mod (x y)))
  :enable (int-divshift-sub-wrapped-gadget
           int-sub-wrapped-spec
           int->lebits-of-int-wrap
           posp-when-integer-widthp
           int-valuep))
