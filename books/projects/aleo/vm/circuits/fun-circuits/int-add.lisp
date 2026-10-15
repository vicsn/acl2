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
(local (include-book "../library-extensions/bit-lists"))
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

(defthm int-add-funspec-agrees
  (equal (int-add-checked-spec x y signedp n)
         (int-add-checked-spec x y signedp n))
  :rule-classes nil)

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
  :do-not-induct t
  :use ((:instance unsigned-small-add-checked-gadget-correct (z carry))
        (:instance acl2::lebits=>nat-injectivity
                   (digits1 (lookup-equal-list zs asg))
                   (digits2 (int->lebits (int-add-checked-spec x y nil n)
                                         n))))
  :enable (int-add-checked-unsigned-gadget
           acl2::bit-list-fix-when-bit-listp
           int-add-checked-spec
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
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
  :do-not-induct t
  :use (:instance unsigned-small-add-checked-gadget-correct (z carry))
  :enable (int-add-checked-unsigned-gadget
           int-add-checked-spec
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits))

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
                (equal signedp t)
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
           len-of-lookup-equal-list)
  :do-not-induct t
  :use ((:instance signed-small-add-checked-gadget-soundness
                   (xy-diff-sign xy-diff)
                   (zx-diff-sign zx-diff)
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

; boolean-xor-gadget-to-bitxor does not fire on (car (last zs)) unless
; that symbol is known to be bound and boolean.  This packages the
; membership, binding, and bitp facts for one sign-bit xor.

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
; funspec is not spec-error, that bit really is 0 (the operands' signs
; agree only when the sum has the same sign), and the carry of the
; unsigned reading witnesses the wrapped sum.  n+1 < 253 for every width,
; including 128.

(defruled int-add-checked-signed-gadget-complete
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
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal (int-add-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-add-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zx-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-add-checked-spec x y t n)
                                           n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-checked-signed-gadget
             xs ys zs carry xy-diff zx-diff overflow one p)
            asg p))
  :do-not-induct t
  :use ((:instance unsigned-small-add-gadget-correct
                   (zs (append zs (list carry))))
        int-consp-ys-and-zs
        (:instance int-msb-xor-constraint-holds
                   (xs xs)
                   (ys ys)
                   (z xy-diff))
        (:instance int-msb-xor-constraint-holds
                   (xs zs)
                   (ys xs)
                   (z zx-diff))
        (:instance int-add-signed-overflow-bitxor-is-zero
                   (n (len xs))))
  :enable (int-add-checked-signed-gadget
           signed-small-add-checked-gadget
           unsigned-small-add-wrapped-gadget
           unsigned-small-add-gadget-correct
           int-consp-ys-and-zs
           boolean-and-notleft-gadget-to-booland-boolnot
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
           int-add-carry-on-lebits
           int-add-checked-spec-when-not-error
           int-add-signed-overflow-bitxor-is-zero
           int-add-checked-spec
           int-valuep
           int-min
           int-max
           int-valuation-binds-allp-of-nil
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

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
  :do-not-induct t
  :use (:instance int-add-checked-unsigned-gadget-sound (signedp nil))
  :enable int-add-unsigned-gadget)

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
  :do-not-induct t
  :use (:instance int-add-checked-unsigned-gadget-sound (signedp nil))
  :enable int-add-assign-unsigned-gadget)

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
  :do-not-induct t
  :use int-add-checked-unsigned-gadget-complete
  :enable int-add-unsigned-gadget)

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
  :do-not-induct t
  :use int-add-checked-unsigned-gadget-complete
  :enable int-add-assign-unsigned-gadget)

(defruled int-add-gadget-complete-signed
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry) (symbolp xy-diff) (symbolp zx-diff)
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
                (r1cs::valuation-bindsp asg zx-diff)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal (int-add-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-add-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zx-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-add-checked-spec x y t n) n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-signed-gadget
             xs ys zs carry xy-diff zx-diff overflow one p)
            asg p))
  :enable (int-add-signed-gadget
           int-add-checked-signed-gadget-complete))

(defruled int-add-assign-gadget-complete-signed
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp carry) (symbolp xy-diff) (symbolp zx-diff)
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
                (r1cs::valuation-bindsp asg zx-diff)
                (r1cs::valuation-bindsp asg overflow)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal (int-add-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-checked-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-add-carry x y n))
                (equal (lookup-equal xy-diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal zx-diff asg)
                       (bitxor (car (last (int->lebits
                                           (int-add-checked-spec x y t n) n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal overflow asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-add-assign-signed-gadget
             xs ys zs carry xy-diff zx-diff overflow one p)
            asg p))
  :enable (int-add-assign-signed-gadget
           int-add-checked-signed-gadget-complete))

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
  :do-not-induct t
  :enable (int-add-wrapped-unsigned-gadget
           int-add-wrapped-spec
           int-wrap
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use (:instance unsigned-small-add-wrapped-gadget-soundness
                  (z carry)))

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
           int-lebits=>int-of-signed-int->lebits
           bit-listp-of-int->lebits-explicit
           integer-widthp
           integer-length-of-base-prime)
  :do-not-induct t
  :use (:instance signed-small-add-wrapped-gadget-soundness
                  (z carry)))

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
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-add-checked-pred
                            int-add-checked-spec
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            pfield::add
                            pfield::mul
                            acl2::mod-when-<)
                           (mod floor)))))
