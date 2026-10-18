; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness of unsigned 128-bit unsigned_division_via_witness
; (unsigned-medium-div-gadget): the canonical quotient and remainder
; witnesses, the four 64-bit partial products of mul_checked with zero
; carries, the add_checked sum with zero carry, and the comparison witness
; satisfy the constraints.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-compare")
(include-book "../r1cs/unsigned-medium-div")

(local (include-book "../library-extensions/r1cses"))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-m-lebits=>nat-of-repeat-0
  (equal (lebits=>nat (repeat k 0)) 0)
  :induct (repeat k 0)
  :enable (repeat acl2::lebits=>nat-of-cons))

(defruledl int-divshift-m-bit-listp-of-repeat-0
  (bit-listp (repeat k 0))
  :induct (repeat k 0)
  :enable repeat)

(defruledl int-divshift-m-bit-listp-of-take
  (implies (and (bit-listp x) (<= (nfix k) (len x)))
           (bit-listp (take k x)))
  :induct (take k x)
  :enable (take bit-listp))

(defruledl int-divshift-m-bit-listp-of-nthcdr
  (implies (bit-listp x)
           (bit-listp (nthcdr k x)))
  :induct (nthcdr k x)
  :enable (nthcdr bit-listp))

(defruledl int-divshift-m-binds-of-take
  (implies (and (r1cs::valuation-binds-allp asg x)
                (<= (nfix k) (len x)))
           (r1cs::valuation-binds-allp asg (take k x)))
  :induct (take k x)
  :enable (take r1cs::valuation-binds-allp))

(defruledl int-divshift-m-binds-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg x)
           (r1cs::valuation-binds-allp asg (nthcdr k x)))
  :induct (nthcdr k x)
  :enable (nthcdr r1cs::valuation-binds-allp))

(defruled int-divshift-medium-mul-checked-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbolp low-low) (symbolp high-low)
                (symbolp low-high) (symbolp high-high)
                (symbol-listp zs) (symbol-listp zs-carry-low)
                (symbol-listp zs-carry-high)
                (equal (len xs) 128)
                (equal (len ys) 128)
                (equal (len zs) 128)
                (equal (len zs-carry-low) 65)
                (equal (len zs-carry-high) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-carry-low)
                (r1cs::valuation-binds-allp asg zs-carry-high)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (bit-listp (lookup-equal-list zs asg))
                (equal (lookup-equal low-low asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list xs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-low asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list xs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal low-high asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list xs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-high asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list xs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-high asg) 0)
                (equal (lebits=>nat (lookup-equal-list zs asg))
                       (* (lebits=>nat (lookup-equal-list xs asg))
                          (lebits=>nat (lookup-equal-list ys asg))))
                (equal (lookup-equal-list zs-carry-low asg) (repeat 65 0))
                (equal (lookup-equal-list zs-carry-high asg) (repeat 128 0)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-medium-mul-checked-gadget
             xs ys low-low high-low low-high high-high
             zs zs-carry-low zs-carry-high p)
            asg p))
  :do-not-induct t
  :use ((:instance babbage-mul-lebits-correct
                   (x-bits (lookup-equal-list xs asg))
                   (y-bits (lookup-equal-list ys asg))
                   (n 64))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list zs asg))))
  :enable (unsigned-medium-mul-checked-gadget
           unsigned-medium-mul-carry-gadget
           babbage-mul-lebits
           r1cs::r1cs-constraints-holdp-of-append
           bits-mul-field-gadget-to-equal-of-mul
           boolean-check-gadget-list-to-bit-listp
           zero-gadget-list-to-all-equal-0
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           lookup-equal-list-of-append
           lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           acl2::lebits=>nat-of-append
           int-divshift-m-lebits=>nat-of-repeat-0
           int-divshift-m-bit-listp-of-repeat-0
           int-divshift-m-bit-listp-of-take
           int-divshift-m-bit-listp-of-nthcdr
           int-divshift-m-binds-of-take
           int-divshift-m-binds-of-nthcdr
           pfield::add
           pfield::mul
           acl2::mod-when-<
           integer-length-of-base-prime))

(defruledl int-divshift-medium-div-holds-from-values
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp low-low) (symbolp high-low)
                (symbolp low-high) (symbolp high-high)
                (symbol-listp ms) (symbol-listp ms-carry-low)
                (symbol-listp ms-carry-high) (symbol-listp ls)
                (symbolp l) (symbol-listp ds) (symbolp d) (symbolp one)
                (equal (len xs) 128)
                (equal (len ys) 128)
                (equal (len qs) 128)
                (equal (len rs) 128)
                (equal (len ms) 128)
                (equal (len ms-carry-low) 65)
                (equal (len ms-carry-high) 128)
                (equal (len ls) 128)
                (equal (len ds) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg ms)
                (r1cs::valuation-binds-allp asg ms-carry-low)
                (r1cs::valuation-binds-allp asg ms-carry-high)
                (r1cs::valuation-binds-allp asg ls)
                (r1cs::valuation-bindsp asg l)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal d asg) 0)
                (equal (lookup-equal l asg) 0)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (bit-listp (lookup-equal-list qs asg))
                (bit-listp (lookup-equal-list rs asg))
                (bit-listp (lookup-equal-list ms asg))
                (bit-listp (lookup-equal-list ls asg))
                (equal (lookup-equal low-low asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-low asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal low-high asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-high asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-high asg) 0)
                (equal (lebits=>nat (lookup-equal-list ms asg))
                       (* (lebits=>nat (lookup-equal-list qs asg))
                          (lebits=>nat (lookup-equal-list ys asg))))
                (equal (lookup-equal-list ms-carry-low asg) (repeat 65 0))
                (equal (lookup-equal-list ms-carry-high asg) (repeat 128 0))
                (equal (lebits=>nat (lookup-equal-list ls asg))
                       (+ (lebits=>nat (lookup-equal-list ms asg))
                          (lebits=>nat (lookup-equal-list rs asg))))
                (equal (lebits=>nat (lookup-equal-list xs asg))
                       (lebits=>nat (lookup-equal-list ls asg)))
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-lt-gadget rs ys ds d p) asg p))
           (r1cs::r1cs-constraints-holdp
            (unsigned-medium-div-gadget
             xs ys qs rs low-low high-low low-high high-high
             ms ms-carry-low ms-carry-high ls l ds d one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-medium-mul-checked-complete
                   (xs qs) (zs ms)
                   (zs-carry-low ms-carry-low)
                   (zs-carry-high ms-carry-high)))
  :enable (unsigned-medium-div-gadget
           r1cs::r1cs-constraints-holdp-of-append
           boolean-check-gadget-list-to-bit-listp
           unsigned-small-add-checked-gadget-correct
           zero-unit-gadget-to-equal-0
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::mul
           integer-length-of-base-prime))

(defruledl int-divshift-m-lebits=>nat-of-int->lebits-unsigned
  (implies (and (posp n)
                (natp x)
                (< x (expt 2 n)))
           (equal (lebits=>nat (int->lebits x n)) x))
  :enable (lebits=>nat-of-int->lebits acl2::mod-when-<))

(defruledl int-divshift-m-euclid-nat
  (implies (and (natp x)
                (posp y))
           (and (natp (truncate x y))
                (natp (rem x y))
                (< (rem x y) y)
                (<= (* (truncate x y) y) x)
                (equal (+ (* (truncate x y) y) (rem x y)) x)))
  :enable (acl2::truncate-becomes-floor-gen acl2::rem-becomes-mod mod))

(defruledl int-divshift-m-small-lt-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp ys) (symbol-listp rs) (symbol-listp ds)
                (symbolp d)
                (equal (len rs) 128)
                (equal (len ys) 128)
                (equal (len ds) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (natp r) (natp y)
                (< r y) (< y (expt 2 128))
                (equal (lookup-equal-list rs asg) (int->lebits r 128))
                (equal (lookup-equal-list ys asg) (int->lebits y 128))
                (equal (lookup-equal-list ds asg)
                       (int->lebits (+ (expt 2 128) r (- y)) 128))
                (equal (lookup-equal d asg) 0))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-lt-gadget rs ys ds d p) asg p))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-gadget-complete
                  (xs rs) (zs ds) (z d) (x r) (n 128))
  :enable (int-is-less-than-unsigned-gadget
           integer-widthp int-valuep int-min int-max))

(defruledl int-divshift-m-hh-zero
  (implies (and (equal (len qb) 128)
                (equal (len yb) 128)
                (< (* (lebits=>nat qb) (lebits=>nat yb)) (expt 2 128)))
           (equal (* (lebits=>nat (nthcdr 64 qb))
                     (lebits=>nat (nthcdr 64 yb)))
                  0))
  :do-not-induct t
  :use (:instance babbage-mul-lebits-correct
                  (x-bits qb) (y-bits yb) (n 64))
  :enable babbage-mul-lebits
  :disable babbage-mul-lebits-correct)

(defruled int-divshift-unsigned-division-128-complete
  :short "The canonical snarkVM witnesses satisfy the unsigned 128-bit
          division gadget."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp low-low) (symbolp high-low)
                (symbolp low-high) (symbolp high-high)
                (symbol-listp ms) (symbol-listp ms-carry-low)
                (symbol-listp ms-carry-high) (symbol-listp ls)
                (symbolp l) (symbol-listp ds) (symbolp d) (symbolp one)
                (equal (len xs) 128)
                (equal (len ys) 128)
                (equal (len qs) 128)
                (equal (len rs) 128)
                (equal (len ms) 128)
                (equal (len ms-carry-low) 65)
                (equal (len ms-carry-high) 128)
                (equal (len ls) 128)
                (equal (len ds) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg ms)
                (r1cs::valuation-binds-allp asg ms-carry-low)
                (r1cs::valuation-binds-allp asg ms-carry-high)
                (r1cs::valuation-binds-allp asg ls)
                (r1cs::valuation-bindsp asg l)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x nil 128)
                (int-valuep y nil 128)
                (not (equal y 0))
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list ys asg) (int->lebits y 128))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate x y) 128))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem x y) 128))
                (equal (lookup-equal low-low asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-low asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal low-high asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal high-high asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal-list ms asg)
                       (int->lebits (* (truncate x y) y) 128))
                (equal (lookup-equal-list ms-carry-low asg) (repeat 65 0))
                (equal (lookup-equal-list ms-carry-high asg) (repeat 128 0))
                (equal (lookup-equal-list ls asg) (int->lebits x 128))
                (equal (lookup-equal l asg) 0)
                (equal (lookup-equal-list ds asg)
                       (int->lebits (+ (expt 2 128) (rem x y) (- y)) 128))
                (equal (lookup-equal d asg) 0))
           (r1cs::r1cs-constraints-holdp
            (unsigned-medium-div-gadget
             xs ys qs rs low-low high-low low-high high-high
             ms ms-carry-low ms-carry-high ls l ds d one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-m-euclid-nat)
        (:instance int-divshift-m-hh-zero
                   (qb (lookup-equal-list qs asg))
                   (yb (lookup-equal-list ys asg)))
        (:instance int-divshift-m-small-lt-holds (r (rem x y)))
        (:instance int-divshift-medium-div-holds-from-values)
        (:instance int-divshift-m-lebits=>nat-of-int->lebits-unsigned
                   (n 128))
        (:instance int-divshift-m-lebits=>nat-of-int->lebits-unsigned
                   (n 128) (x y))
        (:instance int-divshift-m-lebits=>nat-of-int->lebits-unsigned
                   (n 128) (x (truncate x y)))
        (:instance int-divshift-m-lebits=>nat-of-int->lebits-unsigned
                   (n 128) (x (rem x y)))
        (:instance int-divshift-m-lebits=>nat-of-int->lebits-unsigned
                   (n 128) (x (* (truncate x y) y))))
  :enable (bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           int-valuep int-min int-max)
  :disable (truncate rem floor mod))
