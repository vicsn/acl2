; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unsigned unsigned_division_via_witness at every width.
;
; Widths 8, 16, 32, 64 (2n < data bits) emit unsigned-small-div-gadget;
; soundness is int-unsigned-division-small-sound in int-div.lisp.  Width
; 128 emits unsigned-medium-div-gadget (mul_checked, add_checked, then
; the Euclidean equality and remainder < divisor).  This book proves the
; 128-bit soundness against the same wrapped funspecs, and completeness of
; the small gadget for the canonical snarkVM witnesses.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-div")
(include-book "int-compare")
(include-book "../r1cs/unsigned-medium-div")

(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-lebits=>nat-of-int->lebits-unsigned
  (implies (and (posp n)
                (int-valuep x nil n))
           (equal (lebits=>nat (int->lebits x n)) x))
  :enable (lebits=>nat-of-int->lebits
           int-valuep
           int-min
           int-max
           acl2::mod-when-<))

(defruledl int-divshift-wrapped-div-rem-unsigned
  (implies (and (posp n)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal y 0)))
           (and (equal (int-div-wrapped-spec x y nil n) (truncate x y))
                (equal (int-rem-wrapped-spec x y nil n) (rem x y))))
  :enable (int-div-wrapped-spec
           int-rem-wrapped-spec
           int-wrap
           int-valuep
           int-min
           int-max
           acl2::mod-when-<))

(defruled int-divshift-unsigned-division-128-sound
  :short "Unsigned 128-bit @('unsigned_division_via_witness') soundness."
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
                (equal (lookup-equal-list xs asg) (int->lebits x 128))
                (equal (lookup-equal-list ys asg) (int->lebits y 128))
                (r1cs::r1cs-constraints-holdp
                 (unsigned-medium-div-gadget
                  xs ys qs rs low-low high-low low-high high-high
                  ms ms-carry-low ms-carry-high ls l ds d one p)
                 asg p))
           (and (not (equal y 0))
                (bit-listp (lookup-equal-list qs asg))
                (bit-listp (lookup-equal-list rs asg))
                (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-wrapped-spec x y nil 128))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-wrapped-spec x y nil 128))))
  :do-not-induct t
  :use (unsigned-medium-div-gadget-euclidian
        unsigned-medium-div-opt-gadget-soundness
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned
                   (n 128))
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned
                   (n 128) (x y))
        (:instance int-divshift-wrapped-div-rem-unsigned (n 128)))
  :enable (integer-length-of-base-prime
           bit-listp-of-int->lebits-explicit
)
  :disable (truncate rem floor mod evenp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-integer-length-below
  (implies (and (natp m)
                (natp n)
                (< m (expt 2 n)))
           (<= (integer-length m) n))
  :use (:instance acl2::integer-length-monotonic
                  (x m) (y (+ -1 (expt 2 n)))))

(defruledl int-divshift-euclid-nat
  (implies (and (natp x)
                (posp y))
           (and (natp (truncate x y))
                (natp (rem x y))
                (< (rem x y) y)
                (<= (* (truncate x y) y) x)
                (equal (+ (* (truncate x y) y) (rem x y)) x)))
  :enable (acl2::truncate-becomes-floor-gen acl2::rem-becomes-mod mod))

(defruledl int-divshift-small-div-holds-from-values
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ys) n)
                (equal (len qs) n)
                (equal (len rs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal d asg) 0)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (bit-listp (lookup-equal-list qs asg))
                (bit-listp (lookup-equal-list rs asg))
                (equal (lookup-equal m asg)
                       (* (lebits=>nat (lookup-equal-list qs asg))
                          (lebits=>nat (lookup-equal-list ys asg))))
                (equal (lebits=>nat (lookup-equal-list xs asg))
                       (+ (lookup-equal m asg)
                          (lebits=>nat (lookup-equal-list rs asg))))
                (<= (integer-length (lookup-equal m asg)) n)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-lt-gadget rs ys ds d p) asg p))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-div-gadget xs ys qs rs m ds d u p)
            asg p))
  :do-not-induct t
  :use (:instance int-width-div-fits)
  :enable (unsigned-small-div-gadget
           r1cs::r1cs-constraints-holdp-of-append
           boolean-check-gadget-list-to-bit-listp
           bits-mul-field-gadget-to-equal-of-mul
           field-bits-add-bits-gadget-to-add
           zero-unit-gadget-to-equal-0
           integer-length-of-base-prime))

(defruledl int-divshift-small-div-lt-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp ys) (symbol-listp rs) (symbol-listp ds)
                (symbolp d)
                (equal n (len rs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len ds) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (int-valuep r nil n)
                (int-valuep y nil n)
                (< r y)
                (equal (lookup-equal-list rs asg) (int->lebits r n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list ds asg)
                       (int->lebits (+ (expt 2 n) r (- y)) n))
                (equal (lookup-equal d asg) 0))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-lt-gadget rs ys ds d p) asg p))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-gadget-complete
                  (xs rs) (zs ds) (z d) (x r))
  :enable int-is-less-than-unsigned-gadget)

(defruledl int-divshift-int-valuep-unsigned
  (implies (and (posp n) (natp v) (< v (expt 2 n)))
           (int-valuep v nil n))
  :enable (int-valuep int-min int-max))

(defruledl int-divshift-unsigned-below
  (implies (and (posp n) (int-valuep x nil n))
           (and (natp x) (< x (expt 2 n))))
  :enable (int-valuep int-min int-max))

(defruled int-divshift-unsigned-small-div-gadget-complete
  :short "The canonical snarkVM witnesses satisfy the unsigned small
          division gadget (widths 8, 16, 32, 64)."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ys) n)
                (equal (len qs) n)
                (equal (len rs) n)
                (equal (len ds) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal y 0))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate x y) n))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem x y) n))
                (equal (lookup-equal m asg) (* (truncate x y) y))
                (equal (lookup-equal-list ds asg)
                       (int->lebits (+ (expt 2 n) (rem x y) (- y)) n))
                (equal (lookup-equal d asg) 0))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-div-gadget xs ys qs rs m ds d u p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-euclid-nat)
        (:instance int-divshift-unsigned-below)
        (:instance int-divshift-unsigned-below (x y))
        (:instance int-divshift-int-valuep-unsigned (v (truncate x y)))
        (:instance int-divshift-int-valuep-unsigned (v (rem x y)))
        (:instance int-divshift-integer-length-below
                   (m (* (truncate x y) y)))
        (:instance int-divshift-small-div-lt-holds (r (rem x y)))
        (:instance int-divshift-small-div-holds-from-values)
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned)
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned (x y))
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned
                   (x (truncate x y)))
        (:instance int-divshift-lebits=>nat-of-int->lebits-unsigned
                   (x (rem x y))))
  :enable (bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp)
  :disable (truncate rem floor mod))
