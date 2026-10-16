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
(local (include-book "../library-extensions/bit-lists"))
(include-book "../r1cs/unsigned-small-sub-checked")
(include-book "../r1cs/signed-small-sub-checked")
(include-book "../r1cs/unsigned-small-sub-wrapped")
(include-book "../r1cs/signed-small-sub-wrapped")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(deflabel int-sub-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (current-theory 'int-sub-before-mod)))

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
  :do-not-induct t
  :use unsigned-small-sub-checked-gadget-correct
  :enable (int-sub-checked-unsigned-gadget
           int-sub-checked-spec
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::mod-when-<))

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
  :do-not-induct t
  :use unsigned-small-sub-checked-gadget-correct
  :enable (int-sub-checked-unsigned-gadget
           int-sub-checked-spec
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::mod-when-<))

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
  :do-not-induct t
  :use (:instance int-sub-checked-unsigned-gadget-sound (signedp nil))
  :enable int-sub-unsigned-gadget)

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
  :do-not-induct t
  :use (:instance int-sub-checked-unsigned-gadget-sound (signedp nil))
  :enable int-sub-assign-unsigned-gadget)

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
  :do-not-induct t
  :use int-sub-checked-unsigned-gadget-complete
  :enable int-sub-unsigned-gadget)

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
  :do-not-induct t
  :use int-sub-checked-unsigned-gadget-complete
  :enable int-sub-assign-unsigned-gadget)

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
  :do-not-induct t
  :enable (int-sub-wrapped-unsigned-gadget
           int-sub-wrapped-spec
           int-wrap
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           int-valuep
           int-min
           int-max
           acl2::mod-when-<)
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

(defruledl int-lebits=>int-of-signed-int->lebits
  (implies (and (posp n)
                (int-valuep x t n))
           (equal (lebits=>int (int->lebits x n))
                  (ifix x)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance lebits->int-of-int->lebits (signedp t))
                 (:instance lebits->int-is-lebits=>int
                            (bits (int->lebits x n))))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit)
                           (lebits=>int lebits->int)))))

(defruledl int-lebits=>int-in-signed-range
  (implies (and (bit-listp bits)
                (posp n)
                (equal (len bits) n))
           (and (<= (- (expt 2 (1- n))) (lebits=>int bits))
                (< (lebits=>int bits) (expt 2 (1- n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-valuep-of-lebits->int (signedp t))
                 (:instance lebits->int-is-lebits=>int (bits bits)))
           :in-theory (e/d (int-valuep int-min int-max)
                           (lebits=>int lebits->int
                            int-valuep-of-lebits->int)))))

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
           integer-widthp
           integer-length-of-base-prime
           posp-when-integer-widthp
           lebits->int-is-lebits=>int
           lebits->int-of-int->lebits
           lebits->int
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           int-valuep-of-lebits->int
           not-spec-error-when-integerp
           int-lebits=>int-of-signed-int->lebits
           int-lebits=>int-in-signed-range
           len-of-lookup-equal-list
           int-valuep
           int-min
           int-max)
  :do-not-induct t
  :use ((:instance signed-small-sub-checked-gadget-soundness
                   (xy-diff-sign xy-diff)
                   (zy-diff-sign zy-diff)
                   (over/under-flow overflow))
        (:instance int-lebits=>int-in-signed-range
                   (bits (lookup-equal-list zs asg))
                   (n (len zs)))))

(defruledl int-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

(defruledl int-consp-ys-and-zs
  (implies (and (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs)))
           (and (consp ys)
                (consp zs))))

(defruledl int-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruledl int-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

(defruledl int-msb-xor-constraint-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal z asg)
                       (bitxor (car (last (lookup-equal-list xs asg)))
                               (car (last (lookup-equal-list ys asg))))))
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last xs))
                                (car (last ys))
                                z
                                p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs)))
                   (y (car (last ys))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars ys)
                   (var (car (last ys))))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance member-equal-of-car-of-last (xs xs))
        (:instance member-equal-of-car-of-last (xs ys)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last)
  :disable bitp)

; Completeness.  The circuit forces the overflow bit to 0.  Whenever the
; funspec is not spec-error that bit is 0: signs differ only when the
; difference does not have the subtrahend's sign.  Width 128 is included
; because n+1 < 253.

(defruled int-sub-checked-signed-gadget-complete
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
                (not (equal (int-sub-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-sub-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zy-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-sub-checked-spec x y t n) n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-sub-checked-signed-gadget
             xs ys zs carry xy-diff zy-diff overflow one p)
            asg p))
  :do-not-induct t
  :use ((:instance unsigned-small-sub-gadget-correct
                   (zs (append zs (list carry))))
        int-consp-ys-and-zs
        (:instance int-msb-xor-constraint-holds
                   (xs xs)
                   (ys ys)
                   (z xy-diff))
        (:instance int-msb-xor-constraint-holds
                   (xs zs)
                   (ys ys)
                   (z zy-diff))
        (:instance int-sub-signed-overflow-bitxor-is-zero
                   (n (len xs)))
        (:instance int-sub-carry-on-lebits
                   (n (len xs))))
  :enable (int-sub-checked-signed-gadget
           signed-small-sub-checked-gadget
           unsigned-small-sub-wrapped-gadget
           unsigned-small-sub-gadget-correct
           int-consp-ys-and-zs
           boolean-and-notright-gadget-to-booland-boolnot
           zero-gadget-to-equal-0
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           lookup-equal-of-car
           lookup-equal-list-of-last
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           member-equal-of-car-of-last
           symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           symbol-listp-of-append-of-symbol
           bit-listp-of-append-of-bit
           len-of-append-of-singleton
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           int-sub-carry-on-lebits
           int-lookup-equal-list-of-nil
           int-lebits=>nat-of-nil
           int-sub-checked-spec-when-not-error
           int-sub-signed-overflow-bitxor-is-zero
           int-sub-checked-spec
           int-valuep
           int-min
           int-max
           int-valuation-binds-allp-of-nil
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-sub-gadget-complete-signed
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
                (not (equal (int-sub-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-sub-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zy-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-sub-checked-spec x y t n) n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-sub-signed-gadget
             xs ys zs carry xy-diff zy-diff overflow one p)
            asg p))
  :enable (int-sub-signed-gadget
           int-sub-checked-signed-gadget-complete))

(defruled int-sub-assign-gadget-complete-signed
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
                (not (equal (int-sub-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-sub-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-sub-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zy-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-sub-checked-spec x y t n) n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-sub-assign-signed-gadget
             xs ys zs carry xy-diff zy-diff overflow one p)
            asg p))
  :enable (int-sub-assign-signed-gadget
           int-sub-checked-signed-gadget-complete))

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
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-sub-checked-pred
                            int-sub-checked-spec
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            pfield::add
                            pfield::mul
                            pfield::neg
                            pfield::sub
                            acl2::mod-when-<)
                           (mod floor)))))
