; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness and PFCS for Field::square_root and Field::even_square_root.
;
; The canonical witness is the lesser root, respectively the even root.
; square_root checks the root's bits against (p - 1)/2.  That constant
; has 252 bits, so the 253rd bit is forced to 0 and the low 252 bits
; use the boolean lte fold.  even_square_root reuses the write_bits
; witness and adds a zero LSB.
;
; The PFCSs are the same shapes at 3 bits.  square_root then accepts
; only a root <= 2; even_square_root only an even root <= 4.  Neither
; claims that every square's canonical root fits in 3 bits.  The
; ordered funspec of square_roots_flagged_nondeterministic is not used.

(in-package "ALEOVM")

(include-book "fb3-field-write-bits")
(include-book "fb2-field-sqrt")
(include-book "../r1cs/bits-lte-const-check")
(include-book "../r1cs/field-square")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../library-extensions/bit-lists")
(include-book "std/lists/last" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/append" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-square-root-bound-facts
  (implies (equal p (base-prime))
           (and (equal (field-square-root-bound p)
                       (field-modulus-minus-one-div-two))
                (equal (integer-length (field-square-root-bound p)) 252)
                (evenp (field-square-root-bound p))
                (< (field-square-root-bound p) (expt 2 252))
                (< 4 (field-square-root-bound p))
                (posp (field-square-root-bound p))))
  :hints (("Goal"
           :in-theory (enable field-square-root-bound
                              field-modulus-minus-one-div-two
                              base-prime
                              evenp
                              (:e ecurve::edwards-bls12-q)
                              (:e integer-length)
                              (:e floor)
                              (:e evenp)
                              (:e expt)
                              (:e posp)))))

(defruled fb3-square-root-bound-bits
  (implies (equal p (base-prime))
           (and (equal (len (nat=>lebits* (field-square-root-bound p))) 252)
                (member-equal 0 (nat=>lebits* (field-square-root-bound p)))
                (equal (car (last (nat=>lebits* (field-square-root-bound p))))
                       1)))
  :hints (("Goal"
           :use ((:instance nat=>lebits*-msb-is-1
                            (n (field-square-root-bound (base-prime))))
                 (:instance len-of-nat=>lebits*-is-integer-length
                            (n (field-square-root-bound (base-prime)))))
           :expand ((acl2::nat=>lendian*
                     2 (field-square-root-bound (base-prime))))
           :in-theory (e/d (nat=>lebits*
                            member-equal
                            evenp
                            fb3-square-root-bound-facts)
                           (acl2::nat=>lendian*
                            nat=>lebits*-msb-is-1
                            len-of-nat=>lebits*-is-integer-length)))))

(defruled fb3-neg-of-upper-half
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (pfield::fep r p)
                (< (field-modulus-minus-one-div-two) r))
           (<= (pfield::neg r p) (field-modulus-minus-one-div-two)))
  :enable (pfield::neg
           pfield::fep
           field-modulus-minus-one-div-two
           oddp
           acl2::mod-of-minus-arg1
           acl2::mod-when-<
           fb3-square-root-bound-facts)
  :disable (pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            (:definition pfield::sub)))

(defruled fb3-lesser-root-in-range
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (fieldp x)
                (ecurve::pfield-squarep x p))
           (and (fieldp (field-lesser-square-root x))
                (<= (field-lesser-square-root x)
                    (field-square-root-bound p))
                (equal (pfield::mul (field-lesser-square-root x)
                                    (field-lesser-square-root x)
                                    p)
                       x)))
  :enable (field-lesser-square-root
           field-square-root-bound
           field-modulus-minus-one-div-two
           fb3-square-root-bound-facts
           fb3-neg-of-upper-half
           fieldp
           pfield::fep-fix-when-fep
           pfield::mul-of-neg-arg1
           pfield::mul-of-neg-arg2
           pfield::neg-of-neg)
  :disable ((:definition pfield::sub))
  :use (:instance ecurve::pfield-squarep-necc
                  (x x)
                  (p (base-prime))))

(defruled fb3-last-is-list-of-car
  (implies (consp x)
           (equal (last x) (list (car (last x)))))
  :hints (("Goal" :in-theory (enable last))))

(defruled fb3-nthcdr-of-len-minus-1
  (implies (and (consp x) (true-listp x))
           (equal (nthcdr (1- (len x)) x)
                  (last x)))
  :hints (("Goal" :in-theory (enable nthcdr last len))))

(defruled fb3-msb-of-small-nat=>lebits
  (implies (and (natp n)
                (< n (expt 2 252)))
           (equal (car (last (acl2::nat=>lebits 253 n))) 0))
  :hints (("Goal"
           :use ((:instance lebits=>nat-lower-bound-when-msb-is-1
                            (bits (acl2::nat=>lebits 253 n)))
                 (:instance acl2::lebits=>nat-of-nat=>lebits
                            (width 253)
                            (nat n))
                 (:instance bitp-of-car-of-last-when-bit-listp
                            (bits (acl2::nat=>lebits 253 n))))
           :in-theory (e/d (acl2::len-of-nat=>lebits
                            acl2::bit-listp-of-nat=>lebits
                            bitp)
                           (lebits=>nat-lower-bound-when-msb-is-1
                            acl2::lebits=>nat-of-nat=>lebits
                            bitp-of-car-of-last-when-bit-listp)))))

(defruled fb3-high-bit-of-small
  (implies (and (natp n)
                (< n (expt 2 252)))
           (equal (nthcdr 252 (acl2::nat=>lebits 253 n))
                  '(0)))
  :enable (fb3-msb-of-small-nat=>lebits
           fb3-last-is-list-of-car
           fb3-nthcdr-of-len-minus-1
           acl2::len-of-nat=>lebits
           acl2::bit-listp-of-nat=>lebits))

(defruled fb3-low-252-value
  (implies (and (natp n)
                (< n (expt 2 252)))
           (equal (lebits=>nat (take 252 (acl2::nat=>lebits 253 n)))
                  n))
  :enable (fb3-high-bit-of-small
           acl2::lebits=>nat-of-nat=>lebits
           acl2::lebits=>nat-of-append
           acl2::len-of-nat=>lebits
           append-of-take-and-nthcdr
           lebits=>nat))

(defruled fb3-sqrt-comparison-bit
  (implies (and (equal p (base-prime))
                (natp y)
                (<= y (field-square-root-bound p)))
           (equal (boolean-is-less-than-or-equal-constant-funspec
                   (take 252 (acl2::nat=>lebits 253 y))
                   (nat=>lebits* (field-square-root-bound p)))
                  1))
  :enable (boolean-is-less-than-or-equal-constant-funspec
           fb3-low-252-value
           fb3-square-root-bound-facts
           fb3-square-root-bound-bits
           acl2::lebits=>nat-of-nat=>lebits*
           acl2::len-of-take
           acl2::len-of-nat=>lebits))

(defruled fb3-field-square-root-square-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbolp y)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-square-root-funspec
                               (lookup-equal x asg))))
                (equal (lookup-equal y asg)
                       (field-square-root-funspec
                        (lookup-equal x asg))))
           (r1cs::r1cs-constraints-holdp
            (field-square-gadget y x) asg p))
  :enable (field-square-gadget-correctness
           field-square-root-funspec
           fb3-lesser-root-in-range
           fieldp))

(defruled fb3-field-square-root-bits-hold
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp y)
                (symbol-listp ys)
                (equal (len ys) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg))))
           (and (r1cs::r1cs-constraints-holdp
                 (boolean-check-gadget-list ys p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (pow2sum-gadget y ys) asg p)))
  :enable (boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           field-bits-le
           fb-integer-length-of-base-prime
           fb-base-prime-below-2-253
           pfield::fep-fix-when-fep
           fieldp
           acl2::lebits=>nat-of-nat=>lebits
           acl2::bit-listp-of-nat=>lebits
           acl2::mod-when-<))

(defruled fb3-symbol-listp-of-take
  (implies (symbol-listp xs)
           (symbol-listp (take n xs)))
  :hints (("Goal" :in-theory (enable take symbol-listp))))

(defruled fb3-bit-listp-of-take
  (implies (and (bit-listp xs)
                (<= (nfix n) (len xs)))
           (bit-listp (take n xs)))
  :hints (("Goal" :in-theory (enable take bit-listp))))

(defruled fb3-field-square-root-range-holds
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal y asg))
                (<= (lookup-equal y asg) (field-square-root-bound p))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (take 252 (lookup-equal-list ys asg))
                        (nat=>lebits* (field-square-root-bound p)))))
           (r1cs::r1cs-constraints-holdp
            (bits-lte-const-check-gadget
             ys (nat=>lebits* (field-square-root-bound p)) rs p)
            asg p))
  :hints (("Goal"
           :use (:instance fb-boolean-assert-lte-const-gadget-complete
                           (xs (take 252 ys))
                           (cs (nat=>lebits*
                                (field-square-root-bound (base-prime))))
                           (rs rs)
                           (p p)
                           (asg asg))
           :in-theory (e/d (bits-lte-const-check-gadget
                            bits-lte-const-check-rlen
                            field-square-root-rlen
                            fb-boolean-assert-lte-const-gadget
                            zero-gadget-list-to-all-equal-0
                            fb3-square-root-bound-bits
                            fb3-square-root-bound-facts
                            fb3-sqrt-comparison-bit
                            fb3-high-bit-of-small
                            fb3-symbol-listp-of-take
                            fb3-bit-listp-of-take
                            fb-symbol-listp-of-nthcdr
                            fb-valuation-binds-allp-of-nthcdr
                            r1cs::valuation-binds-allp-of-take
                            lookup-equal-list-of-take
                            lookup-equal-list-of-nthcdr
                            field-bits-le
                            fieldp
                            pfield::fep-fix-when-fep
                            fb-integer-length-of-base-prime
                            base-field-size-in-bits
                            acl2::len-of-take
                            len-of-nthcdr
                            acl2::bit-listp-of-nat=>lebits
                            repeat
                            fb-base-prime-below-2-253)
                           ((:definition pfield::sub))))))

(defruled fb3-field-square-root-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-square-root-funspec
                               (lookup-equal x asg))))
                (equal (lookup-equal y asg)
                       (field-square-root-funspec (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (take 252 (lookup-equal-list ys asg))
                        (nat=>lebits* (field-square-root-bound p)))))
           (r1cs::r1cs-constraints-holdp
            (field-square-root-gadget x y ys rs p) asg p))
  :enable (field-square-root-gadget
           fb3-field-square-root-square-holds
           fb3-field-square-root-bits-hold
           fb3-lesser-root-in-range
           field-square-root-funspec
           fieldp)
  :use (:instance fb3-field-square-root-range-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-even-root-square-and-even
  (implies (and (equal p (base-prime))
                (fieldp x)
                (ecurve::pfield-even-squarep x p))
           (and (fieldp (field-even-square-root-funspec x))
                (evenp (field-even-square-root-funspec x))
                (equal (pfield::mul (field-even-square-root-funspec x)
                                    (field-even-square-root-funspec x)
                                    p)
                       x)))
  :enable (field-even-square-root-funspec
           fieldp
           pfield::fep-fix-when-fep
           evenp)
  :use (:instance ecurve::pfield-even-squarep-necc
                  (x x)
                  (p (base-prime))))

(defruled fb3-car-of-nat=>lebits-is-mod2
  (implies (and (posp width)
                (natp n)
                (< n (expt 2 width)))
           (equal (car (acl2::nat=>lebits width n))
                  (mod n 2)))
  :hints (("Goal"
           :use ((:instance acl2::lebits=>nat-of-nat=>lebits
                            (width width)
                            (nat n))
                 (:instance acl2::lebits=>nat-of-cons
                            (lodigit (car (acl2::nat=>lebits width n)))
                            (hidigits (cdr (acl2::nat=>lebits width n)))))
           :in-theory (e/d (acl2::bit-listp-of-nat=>lebits
                            acl2::len-of-nat=>lebits
                            bitp
                            acl2::bfix
                            acl2::mod-when-<)
                           (acl2::lebits=>nat-of-nat=>lebits
                            acl2::lebits=>nat-of-cons
                            acl2::nat=>lebits
                            acl2::nat=>lendian*)))))

(defruled fb3-even-lsb-is-zero
  (implies (and (equal p (base-prime))
                (fieldp y)
                (evenp y))
           (equal (car (field-bits-le y)) 0))
  :enable (field-bits-le
           fieldp
           pfield::fep-fix-when-fep
           fb-base-prime-below-2-253
           base-field-size-in-bits
           fb3-car-of-nat=>lebits-is-mod2
           evenp))

(defruled fb3-lsb-zero-constraint-holds
  (implies (and (primep p)
                (symbol-listp ys)
                (consp ys)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg (car ys))
                (equal (lookup-equal (car ys) asg) 0))
           (r1cs::r1cs-constraints-holdp
            (list (r1cs::make-r1cs-constraint
                   :a (list (list 1 1)
                            (list (1- p) (car ys)))
                   :b (list (list 1 1))
                   :c (list (list 1 1))))
            asg p))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defruled fb3-field-even-square-root-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (symbolp u)
                (consp ys)
                (equal (len ys) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal u asg) 1)
                (not (reserrp (field-even-square-root-funspec
                               (lookup-equal x asg))))
                (equal (lookup-equal y asg)
                       (field-even-square-root-funspec
                        (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (fb-field-even-square-root-gadget x y ys rs u p) asg p))
  :enable (fb-field-even-square-root-gadget
           fb-field-write-bits-le-gadget
           field-square-gadget-correctness
           fb3-even-root-square-and-even
           fb3-even-lsb-is-zero
           fb3-lsb-zero-constraint-holds
           field-even-square-root-funspec
           field-bits-le
           car-of-lookup-equal-list
           fieldp)
  :use (:instance fb2-field-write-bits-le-gadget-complete
                  (x y)
                  (bits ys)
                  (rs rs)
                  (u u)
                  (p p)
                  (asg asg))
  :disable ((:definition pfield::sub)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-mul1-equals-arg
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep b p))
           (equal (equal (pfield::mul b (mod 1 p) p) (mod 0 p))
                  (equal b 0)))
  :enable (acl2::mod-of-1-arg1
           acl2::mod-of-0-arg1
           pfield::mul-of-1-arg2
           fb3-base-prime-above-16))

(defruled fb3-lsb-equation-is-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp b))
           (equal (equal (pfield::mul (pfield::sub (mod 1 p) b p)
                                      (mod 1 p)
                                      p)
                         (mod 1 p))
                  (equal b 0)))
  :enable (acl2::mod-of-1-arg1
           pfield::mul-of-1-arg2
           fb3-sub1-iff-zero
           fb3-base-prime-above-16
           bitp))

(define fb3-field-square-root-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for @('Field::square_root').
          The bound bits of 2 are @('(0 1)'), so the high bit is zero
          and the fold bit @('r') is zero."
  (pfcs::parse-def
   "field_square_root_3(x, y, b0, b1, b2, r) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (1 - b2) * (b2) == (0),
    (y) * (y) == (x),
    (y) * (1) == (b0 + 2 * b1 + 4 * b2),
    (b2) * (1) == (0),
    (b1) * (b0) == (r),
    (r) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-square-root-3-circuit)
            :pred fb3-field-square-root-3-pred
            :prime prime)

(defruled fb3-three-bits-at-most-2
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b2 0)
                (equal r (bitand b1 b0))
                (equal r 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2))))
           (<= y 2))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (enable bitp bitand))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))))

(defruled fb3-take-3-of-field-bits-le
  (implies (and (equal p (base-prime))
                (fieldp y)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal y (+ b0 (* 2 b1) (* 4 b2))))
           (equal (list b0 b1 b2)
                  (take 3 (field-bits-le y))))
  :enable (field-write-bits-le-funspec)
  :use (:instance fb3-bits-match-write-bits-le (x y)))

(defruled fb3-not-reserrp-when-fieldp
  (implies (fieldp y)
           (not (reserrp y)))
  :enable (fieldp pfield::fep reserrp))

(defruled fb3-square-root-3-is-funspec
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (fieldp x)
                (fieldp y)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal (pfield::mul y y p) x)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal b2 0)
                (equal r (bitand b1 b0))
                (equal r 0))
           (equal (field-square-root-funspec x) y))
  :enable (field-square-root-funspec
           field-lesser-square-root
           fb3-lesser-root-in-range
           fb3-three-bits-at-most-2
           fb3-square-root-bound-facts
           fb2-lesser-square-root-unique
           fieldp
           pfield::fep-fix-when-fep)
  :use (:instance ecurve::pfield-squarep-suff
                  (r y)
                  (x x)
                  (p (base-prime))))

(defruled fb3-square-root-3-not-error
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (fieldp x)
                (fieldp y)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal (pfield::mul y y p) x)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal b2 0)
                (equal r (bitand b1 b0))
                (equal r 0))
           (not (reserrp (field-square-root-funspec x))))
  :enable (fb3-square-root-3-is-funspec
           fb3-not-reserrp-when-fieldp))

(defrule fb3-field-square-root-3-pred-sound
  (implies (and (equal prime (base-prime))
                (primep prime)
                (oddp prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep r prime)
                (fb3-field-square-root-3-pred x y b0 b1 b2 r prime))
           (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal (pfield::mul y y prime) x)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal b2 0)
                (equal r (bitand b1 b0))
                (equal r 0)
                (not (reserrp (field-square-root-funspec x)))
                (equal y (field-square-root-funspec x))
                (<= y 2)
                (equal (list b0 b1 b2)
                       (take 3 (field-bits-le y)))))
  :rule-classes nil
  :enable (fb3-field-square-root-3-pred
           fb3-bool-check-is-bitp
           fb3-weighted-3
           fb3-mul1-equals-arg
           fb3-mul-is-bitand
           fb3-three-bits-at-most-2
           fb3-take-3-of-field-bits-le
           fb3-square-root-3-is-funspec
           fb3-square-root-3-not-error)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))

(defruled fb3-field-square-root-3-pred-complete
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep r prime)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal (pfield::mul y y prime) x)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal b2 0)
                (equal r (bitand b1 b0))
                (equal r 0)
                (not (reserrp (field-square-root-funspec x)))
                (equal y (field-square-root-funspec x))
                (<= y 2)
                (equal (list b0 b1 b2)
                       (take 3 (field-bits-le y))))
           (fb3-field-square-root-3-pred x y b0 b1 b2 r prime))
  :enable (fb3-field-square-root-3-pred
           fb3-bool-check-is-bitp
           fb3-weighted-3
           fb3-mul1-equals-arg
           fb3-mul-is-bitand
           bitp)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb3-field-square-root-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (oddp prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep r prime))
           (equal (fb3-field-square-root-3-pred x y b0 b1 b2 r prime)
                  (and (bitp b0)
                       (bitp b1)
                       (bitp b2)
                       (equal (pfield::mul y y prime) x)
                       (equal y (+ b0 (* 2 b1) (* 4 b2)))
                       (equal b2 0)
                       (equal r (bitand b1 b0))
                       (equal r 0)
                       (not (reserrp (field-square-root-funspec x)))
                       (equal y (field-square-root-funspec x))
                       (<= y 2)
                       (equal (list b0 b1 b2)
                              (take 3 (field-bits-le y))))))
  :use (fb3-field-square-root-3-pred-sound
        fb3-field-square-root-3-pred-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-field-even-square-root-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for @('Field::even_square_root').
          The write_bits range check plus a zero LSB."
  (pfcs::parse-def
   "field_even_square_root_3(x, y, b0, b1, b2, z0, z1, u) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (1 - b2) * (b2) == (0),
    (1 - b0) * (1) == (1),
    (u) * (1) == (1),
    (u - z1) * (1) == (1),
    (y) * (1) == (b0 + 2 * b1 + 4 * b2),
    (1 - b1) * (1 - b0) == (1 - z0),
    (b2) * (z0) == (z1),
    (y) * (y) == (x)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-even-square-root-3-circuit)
            :pred fb3-field-even-square-root-3-pred
            :prime prime)

(defruled fb3-even-three-bits-at-most-4
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2))))
           (and (evenp y)
                (<= y 4)))
  :hints (("Goal"
           :cases ((equal b1 0) (equal b1 1))
           :in-theory (enable bitp bitor bitand evenp))
          ("Subgoal 1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2" :cases ((equal b2 0) (equal b2 1)))))

(defruled fb3-even-three-bits-even
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2))))
           (evenp y))
  :use fb3-even-three-bits-at-most-4)

(defruled fb3-even-three-bits-bound
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2))))
           (<= y 4))
  :use fb3-even-three-bits-at-most-4)

(defruled fb3-even-root-3-is-funspec
  (implies (and (equal p (base-prime))
                (primep p)
                (fieldp x)
                (fieldp y)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal (pfield::mul y y p) x))
           (equal (field-even-square-root-funspec x) y))
  :enable (fb3-even-three-bits-at-most-4
           field-even-square-root-funspec
           fb3-even-root-square-and-even
           fb2-even-root-unique
           fieldp
           evenp)
  :use (:instance ecurve::pfield-even-squarep-suff
                  (r y)
                  (x x)
                  (p (base-prime))))

(defruled fb3-even-root-3-not-error
  (implies (and (equal p (base-prime))
                (primep p)
                (fieldp x)
                (fieldp y)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal (pfield::mul y y p) x))
           (not (reserrp (field-even-square-root-funspec x))))
  :enable fb3-not-reserrp-when-fieldp
  :use fb3-even-root-3-is-funspec)

(defrule fb3-field-even-square-root-3-pred-sound
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (fb3-field-even-square-root-3-pred
                 x y b0 b1 b2 z0 z1 u prime))
           (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal u 1)
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal (pfield::mul y y prime) x)
                (evenp y)
                (<= y 4)
                (equal y (field-even-square-root-funspec x))
                (not (reserrp (field-even-square-root-funspec x)))
                (equal (list b0 b1 b2)
                       (take 3 (field-bits-le y)))))
  :rule-classes nil
  :enable (fb3-field-even-square-root-3-pred
           fb3-bool-check-is-bitp
           fb3-lsb-equation-is-zero
           fb3-unit-is-one
           fb3-zero-unit-is-zero
           fb3-weighted-3
           fb3-or-is-bitor
           fb3-mul-is-bitand
           fb3-even-three-bits-even
           fb3-even-three-bits-bound
           fb3-even-root-3-is-funspec
           fb3-even-root-3-not-error
           fb3-take-3-of-field-bits-le)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))

(defruled fb3-field-even-square-root-3-pred-complete
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal b0 0)
                (equal u 1)
                (equal z1 0)
                (equal y (+ b0 (* 2 b1) (* 4 b2)))
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal (pfield::mul y y prime) x)
                (evenp y)
                (<= y 4)
                (equal y (field-even-square-root-funspec x))
                (not (reserrp (field-even-square-root-funspec x)))
                (equal (list b0 b1 b2)
                       (take 3 (field-bits-le y))))
           (fb3-field-even-square-root-3-pred
            x y b0 b1 b2 z0 z1 u prime))
  :enable (fb3-field-even-square-root-3-pred
           fb3-bool-check-is-bitp
           fb3-lsb-equation-is-zero
           fb3-unit-is-one
           fb3-zero-unit-is-zero
           fb3-weighted-3
           fb3-or-is-bitor
           fb3-mul-is-bitand
           bitp)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb3-field-even-square-root-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime))
           (equal (fb3-field-even-square-root-3-pred
                   x y b0 b1 b2 z0 z1 u prime)
                  (and (bitp b0)
                       (bitp b1)
                       (bitp b2)
                       (equal b0 0)
                       (equal u 1)
                       (equal z1 0)
                       (equal y (+ b0 (* 2 b1) (* 4 b2)))
                       (equal z0 (bitor b1 b0))
                       (equal z1 (bitand b2 z0))
                       (equal (pfield::mul y y prime) x)
                       (evenp y)
                       (<= y 4)
                       (equal y (field-even-square-root-funspec x))
                       (not (reserrp (field-even-square-root-funspec x)))
                       (equal (list b0 b1 b2)
                              (take 3 (field-bits-le y))))))
  :use (fb3-field-even-square-root-3-pred-sound
        fb3-field-even-square-root-3-pred-complete))
