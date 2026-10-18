; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SubWrapped::sub_wrapped with one constant operand, both signednesses,
; every width.
;
; Constant minuend: unsigned-small-sub-wrapped-const-var-gadget
; (r1cs/unsigned-small-sub-wrapped-const-var).
;
; Constant subtrahend C: self.to_field() is the little-endian combination
; of the variable bits, (!other).to_field() + 1 folds into the single
; constant 2^n - C, and to_lower_bits_le(n+1) boolean-checks n+1 result
; bits and equates their weighted sum with that combination.  That is
; int-divshift-sub-wrapped-var-const-gadget below.
;
; Constant/constant emits no constraint (the result is a constant).

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-sub-wrapped-const-var")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-c-mod-diff-of-mods
  (implies (and (integerp x) (integerp y) (posp m))
           (equal (mod (- (mod x m) (mod y m)) m)
                  (mod (- x y) m))))

(defruledl int-divshift-c-lebits->int-when-nat-is-mod
  (implies (and (posp n)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (lebits->int bits signedp)
                  (int-wrap v signedp n)))
  :enable (lebits->int int-wrap))

(defruledl int-divshift-c-bits-from-mod
  (implies (and (natp n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable int->lebits)

(defruledl int-divshift-c-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

(defruledl int-divshift-c-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruledl int-divshift-c-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

(defruledl int-divshift-c-int->lebits-of-mod
  (implies (posp n)
           (equal (int->lebits (mod x (expt 2 n)) n)
                  (int->lebits x n)))
  :enable int->lebits)

(defruledl int-divshift-c-int->lebits-of-offset
  (implies (and (posp n) (integerp x) (integerp y))
           (equal (int->lebits (+ (expt 2 n)
                                  (mod x (expt 2 n))
                                  (- (mod y (expt 2 n))))
                               n)
                  (int->lebits (- x y) n)))
  :enable int->lebits)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Constant minuend.

(defruledl int-divshift-c-consp-of-int->lebits
  (implies (posp n)
           (consp (int->lebits x n)))
  :use len-of-int->lebits
  :disable len-of-int->lebits)

(defruled int-divshift-sub-wrapped-const-var-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits x n) ys zs z one p)
                 asg p))
           (and (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lebits->int (lookup-equal-list zs asg) signedp)
                       (int-sub-wrapped-spec x y signedp n))))
  :do-not-induct t
  :use ((:instance unsigned-small-sub-wrapped-const-var-gadget-soundness
                   (cs (int->lebits x n)))
        (:instance int-divshift-c-mod-diff-of-mods (m (expt 2 n)))
        (:instance int-divshift-c-lebits->int-when-nat-is-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y)))
        (:instance int-divshift-c-bits-from-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y))))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           int-divshift-c-consp-of-int->lebits
           integer-widthp
           integer-length-of-base-prime
           lebits=>nat-of-int->lebits
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp
           len-of-lookup-equal-list
           int-valuep))

(defruledl int-divshift-sub-wrapped-const-var-offset-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (natp a) (natp b)
                (< a (expt 2 n)) (< b (expt 2 n))
                (equal (lookup-equal-list ys asg) (int->lebits b n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) a (- b)) n))
                (equal (lookup-equal z asg) (if (< a b) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits a n) ys zs z one p)
            asg p))
  :do-not-induct t
  :use ((:instance unsigned-small-sub-const-var-gadget-correct
                   (cs (int->lebits a n))
                   (zs (append zs (list z))))
        (:instance int-unsigned-lt-offset (x a) (y b)))
  :enable (unsigned-small-sub-wrapped-const-var-gadget
           int-divshift-c-consp-of-int->lebits
           int-divshift-c-valuation-binds-allp-of-nil
           int-divshift-c-lookup-equal-list-of-nil
           int-divshift-c-lebits=>nat-of-nil
           integer-widthp
           integer-length-of-base-prime
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

(defruled int-divshift-sub-wrapped-const-var-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp ys) (symbol-listp zs)
                (symbolp z) (symbolp one)
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lookup-equal z asg)
                       (if (< (mod x (expt 2 n)) (mod y (expt 2 n))) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits x n) ys zs z one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-sub-wrapped-const-var-offset-holds
                   (a (mod x (expt 2 n)))
                   (b (mod y (expt 2 n))))
        (:instance int-divshift-c-int->lebits-of-offset)
        (:instance int-divshift-c-int->lebits-of-mod)
        (:instance int-divshift-c-int->lebits-of-mod (x y)))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           posp-when-integer-widthp
           int-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Constant subtrahend.

(define int-divshift-sub-wrapped-var-const-gadget ((xs symbol-listp)
                                                   (cs bit-listp)
                                                   (zs symbol-listp)
                                                   (z symbolp)
                                                   (p primep))
  :guard (and (equal (len cs) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard
                    :hints (("Goal"
                             :in-theory
                             (enable symbol-listp-of-append-of-symbol))))
  (append (boolean-check-gadget-list (append zs (list z)) p)
          (list (r1cs::make-r1cs-constraint
                 :a (append (pow2sum-vector xs 0)
                            (list (list (- (expt 2 (len xs))
                                           (lebits=>nat cs))
                                        1)))
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append zs (list z)) 0)))))

(defruledl int-divshift-var-const-correct
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (bit-listp cs)
                (symbol-listp zs) (symbolp z)
                (integer-widthp n)
                (equal (len xs) n)
                (equal (len cs) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-sub-wrapped-var-const-gadget xs cs zs z p)
                   asg p)
                  (and (bit-listp (lookup-equal-list zs asg))
                       (bitp (lookup-equal z asg))
                       (equal (+ (lebits=>nat (lookup-equal-list zs asg))
                                 (* (lookup-equal z asg) (expt 2 n)))
                              (+ (lebits=>nat (lookup-equal-list xs asg))
                                 (expt 2 n)
                                 (- (lebits=>nat cs)))))))
  :do-not-induct t
  :use ((:instance int-width-add-fits)
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list xs asg)))
        (:instance acl2::lebits=>nat-upper-bound (digits cs))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list zs asg))))
  :enable (int-divshift-sub-wrapped-var-const-gadget
           int-divshift-c-valuation-binds-allp-of-nil
           int-divshift-c-lookup-equal-list-of-nil
           int-divshift-c-lebits=>nat-of-nil
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraints-holdp-of-append
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product-of-append
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::add
           pfield::mul
           acl2::mod-when-<
           integer-widthp
           integer-length-of-base-prime
           posp-when-integer-widthp
           bit-listp-of-append-of-bit
           symbol-listp-of-append-of-symbol
           len-of-append-of-singleton
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           len-of-lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons))

(defruledl int-divshift-mod-congruence
  (implies (equal a b) (equal (mod a m) (mod b m))))

(defthm int-divshift-low-from-carry
  (implies (and (natp lo) (bitp c) (posp m) (< lo m)
                (integerp x) (integerp y)
                (equal (+ lo (* c m)) (+ (mod x m) m (- (mod y m)))))
           (equal (mod (- x y) m) lo))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable bitp)
           :use ((:instance acl2::mod-when-< (x lo) (y m))
                 (:instance int-divshift-mod-congruence
                            (a (+ lo (* c m)))
                            (b (+ (mod x m) m (- (mod y m)))))
                 (:instance int-divshift-c-mod-diff-of-mods)))))

(defruledl int-divshift-lebits-of-lookup
  (implies (and (equal (lookup-equal-list xs asg) (int->lebits x n))
                (natp n)
                (integerp x))
           (equal (lebits=>nat (lookup-equal-list xs asg))
                  (mod x (expt 2 n))))
  :enable lebits=>nat-of-int->lebits)

(defruled int-divshift-sub-wrapped-var-const-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp xs) (symbol-listp zs) (symbolp z)
                (integer-widthp n)
                (equal (len xs) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sub-wrapped-var-const-gadget
                  xs (int->lebits y n) zs z p)
                 asg p))
           (and (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lebits->int (lookup-equal-list zs asg) signedp)
                       (int-sub-wrapped-spec x y signedp n))))
  :do-not-induct t
  :use ((:instance int-divshift-var-const-correct (cs (int->lebits y n)))
        (:instance int-divshift-lebits-of-lookup)
        (:instance int-divshift-low-from-carry
                   (lo (lebits=>nat (lookup-equal-list zs asg)))
                   (c (lookup-equal z asg))
                   (m (expt 2 n)))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list zs asg)))
        (:instance int-divshift-c-mod-diff-of-mods (m (expt 2 n)))
        (:instance int-divshift-c-lebits->int-when-nat-is-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y)))
        (:instance int-divshift-c-bits-from-mod
                   (bits (lookup-equal-list zs asg))
                   (v (- x y))))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           lebits=>nat-of-int->lebits
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp
           len-of-lookup-equal-list
           int-valuep))

(defruledl int-divshift-var-const-offset-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp zs) (symbolp z)
                (integer-widthp n)
                (equal (len xs) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (natp a) (natp b)
                (< a (expt 2 n)) (< b (expt 2 n))
                (equal (lookup-equal-list xs asg) (int->lebits a n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) a (- b)) n))
                (equal (lookup-equal z asg) (if (< a b) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-sub-wrapped-var-const-gadget
             xs (int->lebits b n) zs z p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-var-const-correct (cs (int->lebits b n)))
        (:instance int-unsigned-lt-offset (x a) (y b)))
  :enable (lebits=>nat-of-int->lebits
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp
           acl2::mod-when-<))

(defruled int-divshift-sub-wrapped-var-const-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (booleanp signedp)
                (symbol-listp xs) (symbol-listp zs) (symbolp z)
                (integer-widthp n)
                (equal (len xs) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-wrapped-spec x y signedp n) n))
                (equal (lookup-equal z asg)
                       (if (< (mod x (expt 2 n)) (mod y (expt 2 n))) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-sub-wrapped-var-const-gadget
             xs (int->lebits y n) zs z p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-var-const-offset-holds
                   (a (mod x (expt 2 n)))
                   (b (mod y (expt 2 n))))
        (:instance int-divshift-c-int->lebits-of-offset)
        (:instance int-divshift-c-int->lebits-of-mod)
        (:instance int-divshift-c-int->lebits-of-mod (x y)))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           posp-when-integer-widthp
           int-valuep))
