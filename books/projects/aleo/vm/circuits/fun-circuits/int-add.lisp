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

(deflabel int-add-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (in-theory (current-theory 'int-add-before-mod)))

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
           acl2::mod-when-<
           acl2::pos-fix-when-posp
           lebits=>nat-of-int->lebits
           lebits->int-when-unsigned
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::lebits=>nat-injectivity))

(local (in-theory (current-theory 'int-add-before-mod)))

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
           acl2::mod-when-<
           acl2::pos-fix-when-posp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits))

(local (in-theory (disable acl2::mod-when-<)))

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
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           acl2::mod-when-<
           acl2::pos-fix-when-posp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use (:instance unsigned-small-add-wrapped-gadget-soundness
                  (z carry)))

(local (in-theory (disable acl2::mod-when-<)))

(deflabel int-add-before-ifix)
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (in-theory (current-theory 'int-add-before-ifix)))

(local (defthm int-mod-plus-minus-modulus
         (implies (and (integerp a)
                       (posp m))
                  (equal (mod (+ (- m) a) m)
                         (mod a m)))
         :rule-classes nil
         :hints (("Goal"
                  :in-theory (enable acl2::mod-of-minus-arg1
                                     acl2::equal-of-mod-of-+-and-mod-cancel
                                     acl2::mod-when-integerp-of-quotient
                                     acl2::mod-of-+-of-*-same-arg2-arg1
                                     acl2::mod-of-+-of-*-same-arg2-arg2)))))

(defruledl int-spec-unsigned-of-signed-wrap-sum
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n))
           (equal (int-spec-unsigned (int-add-wrapped-spec x y t n) n)
                  (mod (+ (ifix x) (ifix y)) (expt 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-mod-plus-minus-modulus
                           (a (mod (+ (ifix x) (ifix y)) (expt 2 n)))
                           (m (expt 2 n)))
           :in-theory (enable int-add-wrapped-spec
                              int-wrap
                              int-spec-unsigned
                              int-valuep
                              int-min
                              int-max
                              integer-widthp
                              posp-when-integer-widthp
                              acl2::pos-fix-when-posp
                              acl2::ifix-when-integerp
                              acl2::mod-when-<
                              acl2::mod-of-mod-same-arg2
                              acl2::integerp-of-mod
                              acl2::integerp-of-mod-type)
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)))))

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
           int-spec-unsigned-of-signed-wrap-sum
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           int-lebits=>int-of-signed-int->lebits
           bit-listp-of-int->lebits-explicit
           acl2::ifix-when-integerp)
  :do-not-induct t
  :use (:instance signed-small-add-wrapped-gadget-soundness
                  (z carry)))

(local (in-theory (disable int-spec-unsigned-of-signed-wrap-sum
                           int-lebits=>int-of-signed-int->lebits
                           acl2::ifix-when-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness.  The wrapped-add gadget is unsigned-small-add on n+1
; bits.  The canonical carry is int-add-carry: it is the unique bit that
; makes the weighted sum of the result bits and the carry equal the sum
; of the unsigned readings.  The same witness serves both signednesses,
; because wrapped addition is arithmetic on the bit patterns.  Every
; integer width, including 128, satisfies n+1 < 253.

(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(defruledl int-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

(defruledl lebits=>nat-of-bits-and-carry
  (implies (and (bit-listp bits)
                (bitp c))
           (equal (lebits=>nat (append bits (list c)))
                  (+ (lebits=>nat bits)
                     (* c (expt 2 (len bits))))))
  :enable (acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           int-lebits=>nat-of-nil
           acl2::bfix-when-bitp))

(defruled int-add-wrapped-carry-equation
  :short "The canonical carry is forced by the wrapped sum's bits:
          @('N(x) + N(y) = N(wrap(x+y)) + carry * 2^n')."
  (implies (and (posp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (+ (lebits=>nat (int->lebits x n))
                     (lebits=>nat (int->lebits y n)))
                  (+ (lebits=>nat
                      (int->lebits (int-add-wrapped-spec x y signedp n) n))
                     (* (int-add-carry x y n) (expt 2 n)))))
  :enable (int-add-wrapped-spec
           int->lebits-of-int-wrap
           lebits=>nat-of-int->lebits)
  :hints (("Goal" :use (:instance int-add-carry-equation))))

(defruledl int-valuation-binds-allp-of-nil-wrapped
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

(defruledl int-lookup-equal-list-of-nil-wrapped
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruled int-add-wrapped-unsigned-gadget-complete
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
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-wrapped-spec x y nil n) n))
                (equal (lookup-equal carry asg) (int-add-carry x y n)))
           (r1cs::r1cs-constraints-holdp
            (int-add-wrapped-unsigned-gadget xs ys zs carry p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-add-wrapped-carry-equation
                           (signedp nil))))
  :enable (int-add-wrapped-unsigned-gadget
           unsigned-small-add-wrapped-gadget
           unsigned-small-add-gadget-correct
           int-add-wrapped-carry-equation
           lebits=>nat-of-bits-and-carry
           int-valuation-binds-allp-of-nil-wrapped
           int-lookup-equal-list-of-nil-wrapped
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           symbol-listp-of-append-of-symbol
           bit-listp-of-append-of-bit
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           len-of-append-of-singleton
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-add-wrapped-signed-gadget-complete
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
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-add-wrapped-spec x y t n) n))
                (equal (lookup-equal carry asg) (int-add-carry x y n)))
           (r1cs::r1cs-constraints-holdp
            (int-add-wrapped-signed-gadget xs ys zs carry p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-add-wrapped-carry-equation
                           (signedp t))))
  :enable (int-add-wrapped-signed-gadget
           signed-small-add-wrapped-gadget
           unsigned-small-add-wrapped-gadget
           unsigned-small-add-gadget-correct
           int-add-wrapped-carry-equation
           lebits=>nat-of-bits-and-carry
           int-valuation-binds-allp-of-nil-wrapped
           int-lookup-equal-list-of-nil-wrapped
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           symbol-listp-of-append-of-symbol
           bit-listp-of-append-of-bit
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           len-of-append-of-singleton
           integer-widthp
           integer-length-of-base-prime
           int-width-add-fits
           posp-when-integer-widthp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

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
  :hints (("Goal"
           :use int-add-checked-sample-holds
           :in-theory (enable int-add-unsigned-gadget))))

(defruled int-add-assign-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-add-assign-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'carry (base-prime))
   *int-add-checked-sample*
   (base-prime))
  :hints (("Goal"
           :use int-add-checked-sample-holds
           :in-theory (enable int-add-assign-unsigned-gadget))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrapped addition as a PFCS.  One constraint forces the carry:
; N(x) + N(y) = N(wrap(x+y)) + carry * 2^n.  That equation, for both
; signednesses and every integer width including 128, is int-add-wrapped-spec.

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (in-theory (current-theory 'int-add-before-ifix)))
(local (in-theory (enable acl2::expt-when-not-integerp-arg1-cheap
                           acl2::<-of-0-and-expt
                           acl2::integerp-of-expt-when-natp
                           acl2::integerp-of-mod
                           acl2::integerp-of-mod-type
                           acl2::ifix-when-integerp
                           acl2::ifix-when-not-integerp-unlimited
                           acl2::ifix-of-+-when-integerp-arg1
                           acl2::pos-fix-when-posp
                           acl2::mod-when-<
                           acl2::mod-when-<-of-0
                           acl2::fold-consts-in-+)))

(define int-add-wrapped-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Wrapped addition on unsigned readings:
          @('N(x) + N(y) = N(wrap(x+y)) + carry * 2^n')."
  (pfcs::parse-def
   "int_add_wrapped(x, y, z, carry, n2) := {
    (carry) * (n2) == (x + y - z)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-add-wrapped-circuit)
            :pred int-add-wrapped-pred
            :prime prime)

(defruledl int-spec-unsigned-of-wrapped-sum
  (implies (and (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int-spec-unsigned
                   (int-add-wrapped-spec x y signedp n)
                   n)
                  (mod (+ (ifix x) (ifix y)) (expt 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((not signedp)
                   (< (mod (+ (ifix x) (ifix y)) (expt 2 n))
                      (expt 2 (1- n)))
                   (equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (int-spec-unsigned
                            int-add-wrapped-spec
                            int-wrap
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            acl2::ifix-when-integerp
                            acl2::ifix-of-+-when-integerp-arg1
                            acl2::pos-fix-when-posp
                            acl2::integerp-of-mod
                            acl2::integerp-of-mod-type
                            acl2::mod-of-mod-same-arg2
                            acl2::mod-of-mod-when-multiple-safe
                            acl2::mod-of-+-of-constant
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0
                            acl2::mod-of-+-of-*-same-arg1-arg2
                            acl2::mod-of-+-of-*-same-arg2-arg1)
                           (mod floor)))))

(local
 (defthm int-carry-split-unique
  (implies (and (natp z)
                (natp z0)
                (bitp c)
                (bitp c0)
                (posp m)
                (< z m)
                (< z0 m)
                (equal (+ z (* c m))
                       (+ z0 (* c0 m))))
           (and (equal z z0)
                (equal c c0)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable bitp)
           :cases ((equal c 0) (equal c 1)
                   (equal c0 0) (equal c0 1))))))

(defruledl int-base-prime-posp
  (implies (equal prime (base-prime))
           (posp prime))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (enable base-prime
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl int-expt-width-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n))
           (< (expt 2 n) prime))
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp
                              base-prime
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl int-expt-two-widths-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n))
           (< (expt 2 (+ 1 n)) prime))
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp
                              base-prime
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl int-add-readings-sum-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp x)
                (< x (expt 2 n))
                (natp y)
                (< y (expt 2 n)))
           (< (+ x y) prime))
  :hints (("Goal"
           :use int-expt-two-widths-below-prime
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp natp))))

(defruledl int-small-nat-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp z)
                (< z (expt 2 n)))
           (< z prime))
  :hints (("Goal"
           :use int-expt-width-below-prime
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp natp))))

(defruledl int-add-carry-limb-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (bitp carry)
                (equal n2 (expt 2 n)))
           (and (< (* carry n2) prime)
                (<= 0 (* carry n2))))
  :hints (("Goal"
           :use int-expt-width-below-prime
           :cases ((equal carry 0)
                   (equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable bitp integer-widthp))))

(defruledl int-add-diff-in-open-range
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp x) (< x (expt 2 n))
                (natp y) (< y (expt 2 n))
                (natp z) (< z (expt 2 n)))
           (and (< (- (+ x y) z) prime)
                (< (- prime) (- (+ x y) z))))
  :hints (("Goal"
           :use int-expt-two-widths-below-prime
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp natp))))

(defruledl int-mod-when-inside
  (implies (and (integerp a)
                (integerp p)
                (< 0 p)
                (< (- p) a)
                (< a p))
           (equal (mod a p)
                  (if (< a 0) (+ a p) a)))
  :hints (("Goal"
           :cases ((< a 0))
           :in-theory (e/d (acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defruledl int-add-wrapped-mod-iff
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp x) (< x (expt 2 n))
                (natp y) (< y (expt 2 n))
                (natp z) (< z (expt 2 n))
                (bitp carry)
                (equal n2 (expt 2 n)))
           (equal (equal (mod (* carry n2) prime)
                         (mod (+ x y (- z)) prime))
                  (equal (+ x y)
                         (+ z (* carry n2)))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128)
                   (equal carry 0)
                   (< (+ x y) z))
           :in-theory (e/d (int-mod-when-inside
                            bitp
                            integer-widthp
                            base-prime
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))


(defruledl int-add-wrapped-pred-is-sum
  (implies (and (equal prime (base-prime))
                (integer-widthp n)
                (natp x)
                (< x (expt 2 n))
                (natp y)
                (< y (expt 2 n))
                (natp z)
                (< z (expt 2 n))
                (bitp carry)
                (equal n2 (expt 2 n)))
           (equal (int-add-wrapped-pred x y z carry n2 prime)
                  (equal (+ x y)
                         (+ z (* carry n2)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-add-wrapped-mod-iff)
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (int-add-wrapped-pred
                            integer-widthp
                            base-prime
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            pfield::add
                            pfield::mul
                            pfield::neg
                            pfield::sub
                            bitp
                            acl2::ifix-when-integerp
                            acl2::pos-fix-when-posp
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0
                            acl2::mod-of-+-same-arg1
                            acl2::mod-of-+-same-arg2
                            int-add-carry-limb-below-prime
                            int-small-nat-below-prime
                            int-base-prime-posp
                            int-mod-when-inside)
                           (mod floor
                            int-add-wrapped-mod-iff
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants
                            (:elim acl2::floor-mod-elim-rule))))))

(defruledl int-spec-unsigned-below
  (implies (integer-widthp n)
           (< (int-spec-unsigned x n) (expt 2 n)))
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (e/d (int-spec-unsigned
                            integer-widthp
                            acl2::ifix-when-integerp
                            acl2::<-of-mod-same-arg2)
                           (mod floor)))))

(defruledl int-nfix-of-width
  (implies (integer-widthp n)
           (equal (nfix n) n))
  :enable integer-widthp)

(defruledl int-spec-unsigned-is-mod
  (implies (integer-widthp n)
           (equal (int-spec-unsigned x n)
                  (mod (ifix x) (expt 2 n))))
  :enable (int-spec-unsigned int-nfix-of-width))

(defruledl int-add-wrapped-readings-equation
  (implies (and (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (+ (int-spec-unsigned x n)
                     (int-spec-unsigned y n))
                  (+ (int-spec-unsigned
                      (int-add-wrapped-spec x y signedp n)
                      n)
                     (* (int-add-carry x y n)
                        (expt 2 n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-add-carry-equation)
                 (:instance int-spec-unsigned-of-wrapped-sum))
           :in-theory (e/d (integer-widthp
                            posp-when-integer-widthp
                            acl2::ifix-when-integerp
                            int-spec-unsigned-is-mod
                            int-spec-unsigned-of-wrapped-sum)
                           (mod floor
                            int-spec-unsigned
                            int-add-carry
                            int-add-wrapped-spec)))))

(defruledl int-add-wrapped-sum-iff-spec
  (implies (and (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (natp z)
                (< z (expt 2 n))
                (bitp carry)
                (equal n2 (expt 2 n)))
           (equal (equal (+ (int-spec-unsigned x n)
                            (int-spec-unsigned y n))
                         (+ z (* carry n2)))
                  (and (equal z
                              (int-spec-unsigned
                               (int-add-wrapped-spec x y signedp n)
                               n))
                       (equal carry (int-add-carry x y n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-add-wrapped-readings-equation)
                 (:instance int-carry-split-unique
                            (m (expt 2 n))
                            (z0 (int-spec-unsigned
                                 (int-add-wrapped-spec x y signedp n)
                                 n))
                            (c0 (int-add-carry x y n))
                            (c carry))
                 (:instance int-spec-unsigned-below
                            (x (int-add-wrapped-spec x y signedp n))))
           :in-theory (e/d (integer-widthp
                            posp-when-integer-widthp
                            bitp
                            (:t int-add-carry)
                            (:t expt))
                           (int-add-carry
                            int-add-wrapped-spec
                            int-spec-unsigned
                            mod floor)))))

(defruled int-add-wrapped-pred-to-funspec
  :short "The wrapped-add carry equation is int-add-wrapped-spec for
          both signednesses and every integer width, including 128."
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n)
                (natp z)
                (< z (expt 2 n))
                (bitp carry)
                (equal n2 (expt 2 n)))
           (equal (int-add-wrapped-pred
                   (int-spec-unsigned x n)
                   (int-spec-unsigned y n)
                   z carry n2 prime)
                  (and (equal z
                              (int-spec-unsigned
                               (int-add-wrapped-spec x y signedp n)
                               n))
                       (equal carry (int-add-carry x y n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-add-wrapped-pred-is-sum
                            (x (int-spec-unsigned x n))
                            (y (int-spec-unsigned y n)))
                 (:instance int-add-wrapped-sum-iff-spec))
           :in-theory (e/d (int-spec-unsigned-below)
                           (int-add-wrapped-pred
                            int-add-wrapped-pred-is-sum
                            int-add-wrapped-sum-iff-spec
                            bitp
                            int-spec-unsigned
                            int-add-wrapped-spec
                            int-add-carry
                            mod floor)))))
