; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shl, ShlAssign, ShlChecked, ShlWrapped, Shr, ShrAssign, ShrChecked,
; ShrWrapped, for the field shift snarkVM emits when 2*n is below the
; data-bit width of the base field (every integer width other than 128).
;
; Each low exponent bit i emits one select.  Constant multiplication by
; 2^(2^i) is free, and Field::ternary is one constraint
;   (bit) * ((2^(2^i) - 1) * cur) = (next - cur)
; The first cur is the little-endian (left shift) or bit-reversed
; (unsigned right shift) linear combination of the value bits.  Later
; curs are the previous witness.  Field::to_lower_bits_le then boolean-
; checks the 2*n result bits and weighs them.
;
; Unsigned shl_checked also zeros the exponent bits at and above log2(n)
; and the high n result bits.  Unsigned shr_checked zeros only the
; exponent bits.  shl_wrapped uses the same shift for both signednesses,
; because x and its bit pattern agree modulo 2^n.  Signed shl_checked
; sign-extends, signed shr_wrapped adds a sign mask, and width 128 uses
; pow_checked or division.  Those circuits are not this gadget.
;
; The value bits and the exponent bits are not boolean-checked here
; (Integer::new checked them).  A satisfying assignment therefore does
; not by itself prove bit-listp of those inputs, so R1CS-SOUND is not
; claimed.  R1CS-COMPLETE is the witness for every funspec input that
; returns a value, and unsatisfiability when the exponent is out of
; range.  The high-zero check is the circuit's rejection of a product
; that does not fit in n bits; that unsatisfiability is not proved.

(in-package "ALEOVM")

(include-book "int-shift")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")

(include-book "std/lists/last" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/typed-lists/symbol-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shift-pow ((i natp))
  :returns (pow natp :rule-classes :type-prescription)
  (expt 2 (expt 2 (nfix i))))

(define int-shift-scale ((i natp))
  :returns (scale natp :rule-classes :type-prescription)
  (1- (int-shift-pow i))
  ///
  (defruled int-shift-scale-alt
    (equal (int-shift-scale i)
           (1- (expt 2 (expt 2 (nfix i)))))
    :enable (int-shift-scale int-shift-pow)))

(define int-shift-after ((cur natp) (bit bitp) (i natp))
  :returns (next natp :rule-classes :type-prescription)
  (if (equal bit 1)
      (* (nfix cur) (int-shift-pow i))
    (nfix cur))
  ///
  (defruled int-shift-after-as-sum
    (implies (and (natp cur) (bitp bit) (natp i))
             (equal (int-shift-after cur bit i)
                    (+ cur (* bit (int-shift-scale i) cur))))
    :enable (int-shift-after int-shift-scale int-shift-pow bitp)))

(define int-shift-run ((cur natp) (bits bit-listp) (i natp))
  :returns (v natp :rule-classes :type-prescription)
  (if (endp bits)
      (nfix cur)
    (int-shift-run (int-shift-after cur (car bits) i)
                   (cdr bits)
                   (+ 1 (nfix i))))
  ///
  (defruled int-shift-run-of-atom
    (implies (atom bits)
             (equal (int-shift-run cur bits i)
                    (nfix cur)))
    :enable int-shift-run))

(define int-shift-witness-values ((cur natp) (bits bit-listp) (i natp))
  :returns (vals nat-listp)
  (if (endp bits)
      nil
    (b* ((next (int-shift-after cur (car bits) i)))
      (cons next
            (int-shift-witness-values next (cdr bits) (+ 1 (nfix i))))))
  ///
  (defret len-of-int-shift-witness-values
    (equal (len vals) (len bits))
    :hints (("Goal" :in-theory (enable int-shift-witness-values))))
  (defret consp-of-int-shift-witness-values
    (equal (consp vals) (consp bits))
    :hints (("Goal" :in-theory (enable int-shift-witness-values)))))

(defruled int-shift-after-as-mul
  (implies (and (natp cur) (bitp bit) (natp i))
           (equal (int-shift-after cur bit i)
                  (* cur (expt 2 (* bit (expt 2 i))))))
  :enable (int-shift-after int-shift-pow bitp))

(defruled int-shift-run-value
  (implies (and (natp cur) (bit-listp bits) (natp i))
           (equal (int-shift-run cur bits i)
                  (* cur (expt 2 (* (lebits=>nat bits) (expt 2 i))))))
  :hints (("Goal"
           :induct (int-shift-run cur bits i)
           :in-theory (e/d (int-shift-run
                            int-shift-after-as-mul
                            acl2::lebits=>nat-of-cons
                            bit-listp
                            acl2::expt-of-+)
                           (acl2::lebits=>nat)))))

(local
 (defun int-below-expt-ind (k)
   (if (zp k) t (int-below-expt-ind (1- k)))))

(defruledl int-below-expt-plus
  (implies (and (natp cur)
                (natp a)
                (natp k)
                (< cur (expt 2 a)))
           (< cur (expt 2 (+ a k))))
  :hints (("Goal"
           :induct (int-below-expt-ind k)
           :in-theory (enable expt))))

(defruledl int-double-power
  (implies (natp i)
           (equal (+ (expt 2 i) (expt 2 i))
                  (expt 2 (+ 1 i))))
  :enable acl2::expt-of-+-of-1-arg2)

(defruledl int-shift-below-wider-power
  (implies (and (natp cur)
                (natp width)
                (natp i)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< cur (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :use (:instance int-below-expt-plus
                  (a (+ width (expt 2 i)))
                  (k (expt 2 i)))
  :enable int-double-power
  :disable (int-below-expt-plus expt acl2::expt-of-+-of-1-arg2))

(defruledl int-shift-after-bound
  (implies (and (natp width)
                (natp cur)
                (natp i)
                (bitp bit)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< (int-shift-after cur bit i)
              (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal bit 1))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            bitp
                            int-shift-below-wider-power)
                           (acl2::*-of-expt-and-expt-same-base)))
          ("Subgoal 1"
           :use (:instance acl2::<-of-*-and-*-cancel
                           (x1 cur)
                           (x2 (expt 2 (+ width (expt 2 i))))
                           (y (expt 2 (expt 2 i))))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            acl2::*-of-expt-and-expt-same-base
                            int-double-power)
                           (acl2::<-of-*-and-*-cancel)))))

(defruledl int-shift-run-bound
  (implies (and (natp width)
                (natp cur)
                (natp i)
                (bit-listp bits)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< (int-shift-run cur bits i)
              (expt 2 (+ width (expt 2 (+ i (len bits)))))))
  :hints (("Goal"
           :induct (int-shift-run cur bits i)
           :in-theory (e/d (int-shift-run
                            int-shift-after-bound
                            bit-listp)
                           (int-shift-after int-shift-pow)))))

(defruled int-shift-below-prime
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (natp v)
                (< v (expt 2 (* 2 n))))
           (< v p))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :in-theory (enable integer-widthp
                              integer-length-of-base-prime
                              (:e expt)
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defruledl int-shift-pow-small
  (implies (and (integer-widthp n)
                (not (equal n 128))
                (natp i)
                (< i (1- (integer-length n))))
           (< (expt 2 (expt 2 i))
              (expt 2 (* 2 n))))
  :do-not-induct t
  :enable ((:e expt) (:e integer-length) integer-widthp)
  :hints (("Goal"
           :cases ((and (equal n 8) (equal i 0))
                   (and (equal n 8) (equal i 1))
                   (and (equal n 8) (equal i 2))
                   (and (equal n 16) (equal i 0))
                   (and (equal n 16) (equal i 1))
                   (and (equal n 16) (equal i 2))
                   (and (equal n 16) (equal i 3))
                   (and (equal n 32) (equal i 0))
                   (and (equal n 32) (equal i 1))
                   (and (equal n 32) (equal i 2))
                   (and (equal n 32) (equal i 3))
                   (and (equal n 32) (equal i 4))
                   (and (equal n 64) (equal i 0))
                   (and (equal n 64) (equal i 1))
                   (and (equal n 64) (equal i 2))
                   (and (equal n 64) (equal i 3))
                   (and (equal n 64) (equal i 4))
                   (and (equal n 64) (equal i 5))))))

(defruledl int-twice
  (equal (* 2 n) (+ n n)))

(defruledl int-span-is-double
  (implies (and (natp n) (natp e))
           (equal (+ (+ n e) (- n e))
                  (* 2 n)))
  :hints (("Goal" :in-theory (enable acl2::+-of-+-of---same int-twice))))

(defruledl int-nat-below-sum-power
  (implies (and (natp x)
                (natp n)
                (natp e)
                (<= e n)
                (< x (expt 2 (+ n e))))
           (< x (expt 2 (* 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-below-expt-plus
                            (cur x)
                            (a (+ n e))
                            (k (- n e)))
                 int-span-is-double)
           :in-theory (e/d (acl2::+-of-+-of---same)
                           (int-below-expt-plus
                            int-span-is-double
                            int-twice
                            expt)))))

(defruledl int-shift-cur-below-step
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (< cur (expt 2 n)))
           (< cur (expt 2 (+ n (expt 2 i)))))
  :do-not-induct t
  :use (:instance int-below-expt-plus
                  (a n)
                  (k (expt 2 i)))
  :disable (int-below-expt-plus expt))

(defruledl int-shift-run-below-span
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (bit-listp bits)
                (< cur (expt 2 n)))
           (< (int-shift-run cur bits i)
              (expt 2 (+ n (expt 2 (+ i (len bits)))))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-shift-run-bound (width n))
           :in-theory (e/d (int-shift-cur-below-step)
                           (int-shift-run
                            int-shift-run-bound
                            int-below-expt-plus)))))

(defruledl int-shift-span-le-width
  (implies (and (integer-widthp n)
                (natp i)
                (natp m)
                (<= (+ i m) (1- (integer-length n))))
           (<= (expt 2 (+ i m)) n))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal (+ i m) (1- (integer-length n))))
           :in-theory (enable int-width-is-power-of-two
                              acl2::expt-monotone-strong
                              integer-widthp
                              posp-when-integer-widthp))))

(defruledl int-shift-run-below-double
  (implies (and (integer-widthp n)
                (natp cur)
                (natp i)
                (bit-listp bits)
                (<= (+ i (len bits)) (1- (integer-length n)))
                (< cur (expt 2 n)))
           (< (int-shift-run cur bits i)
              (expt 2 (* 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-nat-below-sum-power
                           (x (int-shift-run cur bits i))
                           (e (expt 2 (+ i (len bits)))))
           :in-theory (e/d (int-shift-run-below-span
                            int-shift-span-le-width
                            posp-when-integer-widthp)
                           (int-shift-run
                            int-nat-below-sum-power)))))

(defruled int-shift-running-below-prime
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (natp cur)
                (natp i)
                (bit-listp bits)
                (< i (1- (integer-length n)))
                (<= (+ i (len bits)) (1- (integer-length n)))
                (< cur (expt 2 n)))
           (< (int-shift-run cur bits i) p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-shift-below-prime
                           (v (int-shift-run cur bits i)))
           :in-theory (e/d (int-shift-run-below-double)
                           (int-shift-run
                            int-shift-below-prime)))))

(defruledl int-shift-product-below-next-span
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (< cur (expt 2 (+ n (expt 2 i)))))
           (< (* cur (expt 2 (expt 2 i)))
              (expt 2 (+ n (expt 2 (+ 1 i))))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance acl2::<-of-*-and-*-cancel
                            (x1 cur)
                            (x2 (expt 2 (+ n (expt 2 i))))
                            (y (expt 2 (expt 2 i))))
                 (:instance acl2::*-of-expt-and-expt-same-base
                            (r 2)
                            (i1 (+ n (expt 2 i)))
                            (i2 (expt 2 i)))
                 (:instance int-double-power))
           :in-theory (disable acl2::<-of-*-and-*-cancel
                               acl2::*-of-expt-and-expt-same-base
                               int-double-power
                               expt))))

(defruled int-shift-cur-times-pow-below-prime
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (natp cur)
                (natp i)
                (< i (1- (integer-length n)))
                (< cur (expt 2 (+ n (expt 2 i)))))
           (and (< (int-shift-pow i) p)
                (< (* cur (int-shift-pow i)) p)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-shift-product-below-next-span)
                 (:instance int-shift-span-le-width
                            (i (+ 1 i))
                            (m 0))
                 (:instance int-nat-below-sum-power
                            (x (* cur (expt 2 (expt 2 i))))
                            (e (expt 2 (+ 1 i))))
                 (:instance int-shift-below-prime
                            (v (* cur (int-shift-pow i))))
                 (:instance int-shift-pow-small)
                 (:instance int-shift-below-prime
                            (v (int-shift-pow i))))
           :in-theory (e/d (int-shift-pow
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-shift-product-below-next-span
                            int-shift-span-le-width
                            int-nat-below-sum-power
                            int-shift-below-prime
                            int-shift-pow-small
                            expt)))))

(defruled int-shift-witness-last-is-run
  (implies (consp bits)
           (equal (car (last (int-shift-witness-values cur bits i)))
                  (int-shift-run cur bits i)))
  :hints (("Goal"
           :induct (int-shift-witness-values cur bits i)
           :in-theory (enable int-shift-witness-values
                              int-shift-run
                              last))))

(defruled int-shl-wrapped-is-wrap-of-pattern
  (implies (and (integer-widthp n)
                (booleanp signedp)
                (int-valuep x signedp n)
                (natp e))
           (equal (int-shl-wrapped-spec x e signedp n)
                  (int-wrap (* (int-spec-unsigned x n)
                               (expt 2 (mod e n)))
                            signedp n)))
  :do-not-induct t
  :enable (int-shl-wrapped-spec
           int-wrap
           int-spec-unsigned
           int-valuep
           integer-widthp
           posp-when-integer-widthp
           nfix
           lnfix))

(defruled lebits->int-is-int-wrap
  (implies (and (bit-listp bits)
                (posp n)
                (booleanp signedp)
                (equal (len bits) n))
           (equal (lebits->int bits signedp)
                  (int-wrap (lebits=>nat bits) signedp n)))
  :do-not-induct t
  :enable (lebits->int
           int-wrap
           acl2::lebits=>nat-upper-bound
           acl2::mod-when-<)
  :disable (acl2::lebits=>nat mod floor))

(defruled int-lebits-take-is-mod
  (implies (and (bit-listp bits)
                (natp n)
                (<= n (len bits)))
           (equal (lebits=>nat (take n bits))
                  (mod (lebits=>nat bits) (expt 2 n))))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-of-append
                   (lodigits (take n bits))
                   (hidigits (nthcdr n bits)))
        (:instance acl2::append-of-take-and-nthcdr
                   (x bits)
                   (n n))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (take n bits))))
  :enable (acl2::mod-when-<
           acl2::len-of-take
           acl2::take-of-too-many)
  :disable (acl2::lebits=>nat-upper-bound
            acl2::lebits=>nat
            mod floor take nthcdr))

(defruled int-low-bits-are-wrap
  (implies (and (bit-listp bits)
                (posp n)
                (booleanp signedp)
                (equal (len bits) (* 2 n)))
           (equal (lebits->int (take n bits) signedp)
                  (int-wrap (lebits=>nat bits) signedp n)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (lebits->int-is-int-wrap
                            int-lebits-take-is-mod
                            int-wrap
                            posp
                            acl2::mod-of-mod-same-arg2
                            acl2::ifix-when-integerp
                            acl2::integerp-of-mod)
                           (lebits->int
                            acl2::lebits=>nat
                            take)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-floor-of-double
  (implies (and (natp a) (posp e))
           (equal (floor (* 2 a) (expt 2 e))
                  (floor a (expt 2 (+ -1 e)))))
  :hints (("Goal"
           :cases ((equal e 1))
           :in-theory (enable acl2::floor-of-*-of-expt-and-expt
                              acl2::floor-of-*-same))))

(defruled int-floor-lebits-nthcdr
  (implies (and (bit-listp bits) (natp e))
           (equal (floor (lebits=>nat bits) (expt 2 e))
                  (lebits=>nat (nthcdr e bits))))
  :hints (("Goal"
           :induct (nthcdr e bits)
           :in-theory (e/d (nthcdr
                            acl2::lebits=>nat-of-cons
                            bit-listp
                            bitp
                            int-floor-of-double
                            acl2::floor-of-+-1-and-*-2-and-expt)
                           (acl2::lebits=>nat)))))

(defruledl int-rev-split
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (rev bits)
                  (append (rev (nthcdr e bits))
                          (rev (take e bits)))))
  :hints (("Goal"
           :induct (nthcdr e bits)
           :in-theory (enable rev nthcdr take bit-listp))))

(defruledl int-lebits-rev-cons
  (implies (bitp a)
           (equal (lebits=>nat (rev (cons a bs)))
                  (+ (lebits=>nat (rev bs))
                     (* a (expt 2 (len bs))))))
  :do-not-induct t
  :enable (acl2::rev-of-cons
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           bitp)
  :disable (acl2::lebits=>nat rev))

(defruledl int-bit-listp-of-rev-for-shift
  (implies (bit-listp xs)
           (bit-listp (rev xs)))
  :hints (("Goal" :in-theory (enable bit-listp rev))))

(defruledl int-len-cdr-of-nthcdr
  (implies (and (consp xs)
                (natp k)
                (< k (len xs)))
           (equal (len (cdr (nthcdr k xs)))
                  (- (len (cdr xs)) k)))
  :hints (("Goal" :in-theory (enable nthcdr len))))

(defruledl int-shr-rev-value-split
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (lebits=>nat (rev bits))
                  (+ (lebits=>nat (rev (nthcdr e bits)))
                     (* (lebits=>nat (rev (take e bits)))
                        (expt 2 (len (nthcdr e bits)))))))
  :hints (("Goal"
           :induct (nthcdr e bits)
           :in-theory (e/d (nthcdr
                            take
                            bit-listp
                            int-lebits-rev-cons
                            acl2::rev-of-cons
                            acl2::lebits=>nat-of-cons
                            acl2::lebits=>nat-of-append
                            acl2::len-of-rev
                            acl2::len-of-nthcdr)
                           (acl2::lebits=>nat
                            rev
                            acl2::rev-of-append)))
          ("Subgoal *1/2"
           :use ((:instance int-lebits-rev-cons
                            (a (car bits))
                            (bs (cdr bits)))
                 (:instance int-len-cdr-of-nthcdr
                            (xs bits)
                            (k (1- e))))
           :in-theory (e/d (nthcdr
                            take
                            len
                            bit-listp
                            int-lebits-rev-cons
                            acl2::rev-of-cons
                            acl2::lebits=>nat-of-cons
                            acl2::lebits=>nat-of-append
                            acl2::len-of-rev
                            acl2::len-of-nthcdr
                            acl2::*-of-expt-and-expt-same-base)
                           (acl2::lebits=>nat
                            rev
                            acl2::rev-of-append
                            acl2::expt-of-+
                            int-len-cdr-of-nthcdr)))))

(defruledl int-shr-rev-value-split-rw
  (implies (and (syntaxp (or (atom bits)
                             (not (eq (car bits) 'take))))
                (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (lebits=>nat (rev bits))
                  (+ (lebits=>nat (rev (nthcdr e bits)))
                     (* (lebits=>nat (rev (take e bits)))
                        (expt 2 (len (nthcdr e bits)))))))
  :hints (("Goal" :use int-shr-rev-value-split)))

(defruledl int-shr-low-product-below
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (< (* (lebits=>nat (rev (nthcdr e bits)))
                 (expt 2 e))
              (expt 2 (len bits))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance acl2::lebits=>nat-upper-bound
                            (digits (rev (nthcdr e bits))))
                 (:instance acl2::<-of-*-and-*-cancel
                            (x1 (lebits=>nat (rev (nthcdr e bits))))
                            (x2 (expt 2 (len (nthcdr e bits))))
                            (y (expt 2 e)))
                 (:instance acl2::*-of-expt-and-expt-same-base
                            (r 2)
                            (i1 (len (nthcdr e bits)))
                            (i2 e)))
           :in-theory (e/d (acl2::len-of-rev
                            acl2::len-of-nthcdr
                            int-bit-listp-of-rev-for-shift
                            int-bit-listp-of-nthcdr)
                           (acl2::lebits=>nat
                            acl2::lebits=>nat-upper-bound
                            acl2::<-of-*-and-*-cancel
                            acl2::*-of-expt-and-expt-same-base
                            rev nthcdr)))))

(defruledl int-group-three
  (equal (* a b c)
         (* b (* a c))))

(defruledl int-shr-high-multiple
  (implies (and (integerp e) (integerp n))
           (equal (* (expt 2 e) hi (expt 2 (+ (- e) n)))
                  (* hi (expt 2 n))))
  :hints (("Goal"
           :use (:instance acl2::*-of-expt-and-expt-same-base
                           (r 2)
                           (i1 e)
                           (i2 (+ (- e) n)))
           :in-theory (e/d (int-group-three
                            acl2::+-of-+-of---same)
                           (acl2::*-of-expt-and-expt-same-base
                            acl2::expt-of-+)))))

(defruledl int-shr-mod-reduced
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (mod (* (lebits=>nat (rev bits)) (expt 2 e))
                       (expt 2 (len bits)))
                  (* (lebits=>nat (rev (nthcdr e bits)))
                     (expt 2 e))))
  :do-not-induct t
  :hints (("Goal"
           :use int-shr-low-product-below
           :in-theory (e/d (int-shr-rev-value-split-rw
                            int-shr-high-multiple
                            acl2::mod-of-+-of-*-same-arg1-arg1
                            acl2::mod-of-+-of-*-same-arg1-arg2
                            acl2::mod-of-+-of-*-same-arg2-arg1
                            acl2::mod-of-+-of-*-same-arg2-arg2
                            acl2::mod-of-*-lemma
                            acl2::mod-of-*-lemma-alt
                            acl2::mod-when-<
                            acl2::len-of-nthcdr
                            acl2::distributivity)
                           (acl2::lebits=>nat
                            rev take nthcdr
                            acl2::rev-of-append
                            acl2::expt-of-+
                            mod floor)))))

(defruledl int-shr-low-rev-value
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (lebits=>nat
                   (rev (append (nthcdr e bits)
                                (repeat e 0))))
                  (* (lebits=>nat (rev (nthcdr e bits)))
                     (expt 2 e))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance acl2::rev-of-append
                           (x (nthcdr e bits))
                           (y (repeat e 0)))
           :in-theory (e/d (acl2::rev-of-repeat
                            acl2::lebits=>nat-of-append
                            lebits=>nat-of-repeat-0
                            acl2::len-of-repeat)
                           (acl2::lebits=>nat
                            acl2::rev-of-append
                            acl2::equal-of-append-repeat
                            rev nthcdr repeat)))))

(defruled int-shr-mod-is-rev-floor-bits
  (implies (and (bit-listp bits)
                (natp e)
                (<= e (len bits)))
           (equal (mod (* (lebits=>nat (rev bits)) (expt 2 e))
                       (expt 2 (len bits)))
                  (lebits=>nat
                   (rev (append (nthcdr e bits)
                                (repeat e 0))))))
  :do-not-induct t
  :hints (("Goal"
           :use int-shr-mod-reduced
           :in-theory (e/d (int-shr-low-rev-value)
                           (acl2::lebits=>nat
                            rev
                            acl2::rev-of-append
                            acl2::rev-of-repeat
                            int-shr-mod-reduced)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm symbol-listp-of-nthcdr-for-shift
   (implies (symbol-listp xs)
            (symbol-listp (nthcdr n xs)))
   :hints (("Goal" :in-theory (enable symbol-listp nthcdr)))))

(defruledl int-lebits-of-nil
  (equal (lebits=>nat nil) 0)
  :hints (("Goal" :in-theory (enable acl2::lebits=>nat))))

(defruledl int-rev-of-atom
  (implies (atom x)
           (equal (rev x) nil))
  :hints (("Goal" :in-theory (enable rev))))

(define int-be-weighted ((vals true-listp) (w natp))
  :returns (sum natp :rule-classes :type-prescription)
  :measure (len vals)
  (if (endp vals)
      0
    (+ (* (nfix (car vals)) (expt 2 (nfix w)))
       (int-be-weighted (cdr vals) (nfix (1- (nfix w)))))))

(define int-be-pow2sum-vector ((xs symbol-listp) (w natp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  :measure (len xs)
  (if (endp xs)
      nil
    (cons (list (expt 2 (nfix w)) (car xs))
          (int-be-pow2sum-vector (cdr xs) (nfix (1- (nfix w))))))
  ///
  (defret consp-of-int-be-pow2sum-vector
    (equal (consp vec) (consp xs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-shift-scale-cur-below
  (implies (and (natp cur)
                (not (equal 0 cur))
                (natp i)
                (rationalp p)
                (< (* (expt 2 (expt 2 i)) cur) p))
           (< (* (+ -1 (expt 2 (expt 2 i))) cur) p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance acl2::<-of-*-and-*-cancel
                           (x1 (+ -1 (expt 2 (expt 2 i))))
                           (x2 (expt 2 (expt 2 i)))
                           (y cur))
           :in-theory (disable acl2::<-of-*-and-*-cancel))))

(local
 (defthm int-shift-mod-diff-core
  (implies (and (natp cur)
                (natp next)
                (natp scale)
                (integerp p)
                (< 1 p)
                (< cur p)
                (< next p)
                (< (* scale cur) p)
                (< (+ cur (* scale cur)) p)
                (equal (mod (* scale cur) p)
                       (mod (+ (- cur) next) p)))
           (equal next (+ cur (* scale cur))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< next cur))
           :in-theory (enable acl2::mod-when-<
                              acl2::mod-when-<-of-0)))))

(local
 (defthm int-shift-mod-diff-is-sum
  (implies (and (natp cur)
                (not (equal 0 cur))
                (natp next)
                (integerp pow)
                (< 1 pow)
                (integerp p)
                (< 1 p)
                (< cur p)
                (< next p)
                (< (* pow cur) p)
                (equal (mod (* (+ -1 pow) cur) p)
                       (mod (+ (- cur) next) p)))
           (equal next (+ cur (* (+ -1 pow) cur))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance acl2::<-of-*-and-*-cancel
                            (x1 (+ -1 pow))
                            (x2 pow)
                            (y cur))
                 (:instance int-shift-mod-diff-core
                            (scale (+ -1 pow))))
           :in-theory (disable acl2::<-of-*-and-*-cancel)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(define int-shift-var-step-gadget ((bit symbolp)
                                   (cur symbolp)
                                   (next symbolp)
                                   (i natp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "One select after the first: @('bit * ((2^(2^i)-1) * cur) = next - cur')."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 bit))
         :b (list (list (int-shift-scale i) cur))
         :c (list (list 1 next)
                  (list (- p 1) cur)))))

(define int-shift-var-chain ((prev symbolp)
                             (ebits symbol-listp)
                             (nexts symbol-listp)
                             (i natp)
                             (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp ebits) (endp nexts))
      nil
    (append (int-shift-var-step-gadget (car ebits) prev (car nexts) i p)
            (int-shift-var-chain (car nexts)
                                 (cdr ebits)
                                 (cdr nexts)
                                 (+ 1 (nfix i))
                                 p))))

(define int-shift-lc-step-gadget ((bit symbolp)
                                  (xs symbol-listp)
                                  (next symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "First left-shift select.  @('cur') is the little-endian value."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 bit))
         :b (pow2sum-vector xs 0)
         :c (append (list (list 1 next))
                    (pow2sum-neg-prime-vector xs 0 p)))))

(define int-shift-be-step-gadget ((bit symbolp)
                                  (xs symbol-listp)
                                  (next symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "First unsigned right-shift select.  @('cur') is the bit-reversal."
  (b* ((vec (int-be-pow2sum-vector xs (nfix (1- (len xs))))))
    (list (r1cs::make-r1cs-constraint
           :a (list (list 1 bit))
           :b vec
           :c (append (list (list 1 next))
                      (vector-neg-prime vec p))))))

(define int-shl-chain-gadget ((xs symbol-listp)
                              (ebits symbol-listp)
                              (nexts symbol-listp)
                              (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (endp ebits)
      nil
    (append (int-shift-lc-step-gadget (car ebits) xs (car nexts) p)
            (int-shift-var-chain (car nexts)
                                 (cdr ebits)
                                 (cdr nexts)
                                 1
                                 p))))

(define int-shr-chain-gadget ((xs symbol-listp)
                              (ebits symbol-listp)
                              (nexts symbol-listp)
                              (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (endp ebits)
      nil
    (append (int-shift-be-step-gadget (car ebits) xs (car nexts) p)
            (int-shift-var-chain (car nexts)
                                 (cdr ebits)
                                 (cdr nexts)
                                 1
                                 p))))

(define int-shift-lower-gadget ((final symbolp)
                                (zs symbol-listp)
                                (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('Field::to_lower_bits_le') of the shift witness."
  (append (boolean-check-gadget-list zs p)
          (pow2sum-gadget final zs)))

(define int-shl-wrapped-gadget ((xs symbol-listp)
                                (ebits symbol-listp)
                                (nexts symbol-listp)
                                (zs symbol-listp)
                                (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Unsigned or signed @('shl_wrapped') for a width other than 128."
  (append (int-shl-chain-gadget xs ebits nexts p)
          (int-shift-lower-gadget (car (last nexts)) zs p)))

(define int-shr-wrapped-gadget ((xs symbol-listp)
                                (ebits symbol-listp)
                                (nexts symbol-listp)
                                (zs symbol-listp)
                                (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Unsigned @('shr_wrapped') for a width other than 128."
  (append (int-shr-chain-gadget xs ebits nexts p)
          (int-shift-lower-gadget (car (last nexts)) zs p)))

(define int-shl-checked-shift-gadget ((xs symbol-listp)
                                      (ebits symbol-listp)
                                      (excess symbol-listp)
                                      (nexts symbol-listp)
                                      (zs symbol-listp)
                                      (high symbol-listp)
                                      (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Unsigned @('shl_checked'): exponent bound, the wrapped shift,
          and zero high result bits.  @('high') is @('(nthcdr n zs)')."
  (append (int-shl-checked-bound-gadget excess)
          (int-shl-wrapped-gadget xs ebits nexts zs p)
          (int-from-bits-le-gadget high)))

(define int-shr-checked-shift-gadget ((xs symbol-listp)
                                      (ebits symbol-listp)
                                      (excess symbol-listp)
                                      (nexts symbol-listp)
                                      (zs symbol-listp)
                                      (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Unsigned @('shr_checked'): exponent bound plus unsigned wrapped shift."
  (append (int-shr-checked-bound-gadget excess)
          (int-shr-wrapped-gadget xs ebits nexts zs p)))

(define int-shl-shift-gadget ((xs symbol-listp)
                              (ebits symbol-listp)
                              (excess symbol-listp)
                              (nexts symbol-listp)
                              (zs symbol-listp)
                              (high symbol-listp)
                              (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-shift-gadget xs ebits excess nexts zs high p))

(define int-shl-assign-shift-gadget ((xs symbol-listp)
                                     (ebits symbol-listp)
                                     (excess symbol-listp)
                                     (nexts symbol-listp)
                                     (zs symbol-listp)
                                     (high symbol-listp)
                                     (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shl-checked-shift-gadget xs ebits excess nexts zs high p))

(define int-shr-shift-gadget ((xs symbol-listp)
                              (ebits symbol-listp)
                              (excess symbol-listp)
                              (nexts symbol-listp)
                              (zs symbol-listp)
                              (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-shift-gadget xs ebits excess nexts zs p))

(define int-shr-assign-shift-gadget ((xs symbol-listp)
                                     (ebits symbol-listp)
                                     (excess symbol-listp)
                                     (nexts symbol-listp)
                                     (zs symbol-listp)
                                     (p primep))
  :guard (consp nexts)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-shr-checked-shift-gadget xs ebits excess nexts zs p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-shift-var-step-to-after
  (implies (and (symbolp bit)
                (symbolp cur)
                (symbolp next)
                (natp i)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg next)
                (bitp (lookup-equal bit asg))
                (< (int-shift-pow i) p)
                (< (* (lookup-equal cur asg) (int-shift-pow i)) p))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-shift-var-step-gadget bit cur next i p) asg p)
                  (equal (lookup-equal next asg)
                         (int-shift-after (lookup-equal cur asg)
                                          (lookup-equal bit asg)
                                          i))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance pfield::equal-of-add-of-neg-simple
                           (x 0)
                           (y (lookup-equal next asg))
                           (z (lookup-equal cur asg))
                           (p p))
           :in-theory (e/d (int-shift-var-step-gadget
                            int-shift-after-as-sum
                            int-shift-scale
                            int-shift-pow
                            r1cs::r1cs-constraints-holdp
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            pfield::mul
                            pfield::add
                            pfield::neg
                            acl2::mod-when-<
                            bitp)
                           (mod floor lookup-equal
                                acl2::equal-of-mod-same-arg1
                                pfield::equal-of-add-of-neg-simple)))
          ("Subgoal 4"
           :use (:instance acl2::mod-when-<
                           (x (* (+ -1 (expt 2 (expt 2 i)))
                                 (lookup-equal cur asg)))
                           (y p))
           :in-theory (e/d (int-shift-pow
                            acl2::<-of-*-and-*-cancel
                            acl2::*-of-0)
                           (acl2::mod-when-<
                            lookup-equal
                            mod)))
          ("Subgoal 4''"
           :use (:instance int-shift-scale-cur-below
                           (cur (lookup-equal cur asg))
                           (i i)
                           (p p)))
          ("Subgoal 2"
           :use (:instance int-shift-mod-diff-is-sum
                           (cur (lookup-equal cur asg))
                           (next (lookup-equal next asg))
                           (pow (expt 2 (expt 2 i)))
                           (p p)))))

(defruled int-shift-lc-step-to-after
  (implies (and (symbolp bit)
                (symbol-listp xs)
                (symbolp next)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg next)
                (bitp (lookup-equal bit asg))
                (bit-listp (lookup-equal-list xs asg))
                (< (* 2 (lebits=>nat (lookup-equal-list xs asg))) p))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-shift-lc-step-gadget bit xs next p) asg p)
                  (equal (lookup-equal next asg)
                         (int-shift-after
                          (lebits=>nat (lookup-equal-list xs asg))
                          (lookup-equal bit asg)
                          0))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-shift-lc-step-gadget
                            int-shift-after-as-sum
                            int-shift-scale
                            int-shift-pow
                            pow2sum-vector-to-mod-of-lebits=>nat
                            pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
                            r1cs::r1cs-constraints-holdp
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            r1cs::dot-product-of-append
                            pfield::mul
                            pfield::add
                            pfield::neg
                            acl2::mod-when-<
                            bitp)
                           (mod floor lookup-equal
                                acl2::equal-of-mod-same-arg1
                                pow2sum-vector
                                pow2sum-neg-prime-vector)))
          ("Subgoal 6"
           :use (:instance int-shift-mod-diff-core
                           (cur (lebits=>nat (lookup-equal-list xs asg)))
                           (next (lookup-equal next asg))
                           (scale 0)
                           (p p)))
          ("Subgoal 2"
           :use (:instance int-shift-mod-diff-is-sum
                           (cur (lebits=>nat (lookup-equal-list xs asg)))
                           (next (lookup-equal next asg))
                           (pow 2)
                           (p p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-shift-step-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The doubling select snarkVM emits for exponent bit 0 once
          @('cur') is a single wire: @('(bit) * (cur) = (next - cur)').
          Later bits use the same shape with constant coefficient
          @('2^(2^i) - 1'), which is @('int-shift-var-step-gadget')."
  (pfcs::parse-def
   "int_shift_step(bit, cur, next) := {
    (bit) * (cur) == (next - cur)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-shift-step-circuit)
            :pred int-shift-step-pred
            :prime prime)

(defruled int-shift-step-pred-to-after
  :short "PFCS-SPEC of the doubling select."
  (implies (and (equal prime (base-prime))
                (bitp bit)
                (natp cur)
                (natp next)
                (< next prime)
                (< (* 2 cur) prime))
           (equal (int-shift-step-pred bit cur next prime)
                  (equal next (int-shift-after cur bit 0))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance pfield::equal-of-add-of-neg-simple
                           (x 0)
                           (y next)
                           (z cur)
                           (p prime))
           :in-theory (e/d (int-shift-step-pred
                            int-shift-after-as-sum
                            int-shift-scale
                            int-shift-pow
                            pfield::mul
                            pfield::add
                            pfield::neg
                            acl2::mod-when-<
                            bitp)
                           (mod floor
                                pfield::equal-of-add-of-neg-simple)))
          ("Subgoal 2"
           :use (:instance int-shift-mod-diff-is-sum
                           (cur cur)
                           (next next)
                           (pow 2)
                           (p (base-prime))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-exponent-high-bits-nonzero
  (implies (and (natp e)
                (natp m)
                (natp k)
                (<= k m)
                (< e (expt 2 m))
                (<= (expt 2 k) e))
           (not (equal (nthcdr k (int->lebits e m))
                       (repeat (len (nthcdr k (int->lebits e m))) 0))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-lebits-below-pow2-when-excess-zero
                            (bits (int->lebits e m))
                            (n k))
                 (:instance lebits=>nat-of-int->lebits
                            (x e)
                            (n m)))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            acl2::mod-when-<
                            acl2::ifix-when-integerp)
                           (int-lebits-below-pow2-when-excess-zero
                            lebits=>nat-of-int->lebits
                            int->lebits
                            nthcdr
                            repeat
                            mod)))))

(defruled int-shl-checked-bound-gadget-unsat
  :short "R1CS-COMPLETE, exponent out of range, of the zero check
          @('shl_checked') emits for a width other than 128, both
          signednesses.  @('m') is the exponent magnitude, 8, 16, or 32.
          The high bits are the wires @('assert_bits_are_zero') sees.
          A constant shift halts in the host before this check."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-bound-gadget excess)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-from-bits-le-gadget-iff-all-zero
                            (p p)
                            (asg asg)
                            (excess excess))
                 (:instance int-exponent-high-bits-nonzero
                            (k (1- (integer-length n))))
                 (:instance int-len-nthcdr-is-len-excess
                            (n (1- (integer-length n)))
                            (bits (int->lebits e m)))
                 (:instance int-width-is-power-of-two))
           :in-theory (e/d (int-shl-checked-bound-gadget
                            int-bit-listp-of-nthcdr
                            bit-listp-of-int->lebits-explicit
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-from-bits-le-gadget-iff-all-zero
                            int-exponent-high-bits-nonzero
                            int-len-nthcdr-is-len-excess
                            int-width-is-power-of-two
                            nthcdr
                            repeat
                            int->lebits
                            lookup-equal-list)))))

(defruled int-shr-checked-bound-gadget-unsat
  :short "R1CS-COMPLETE, exponent out of range, of the zero check
          @('shr_checked') emits for every integer width, both
          signednesses.  The hypotheses are the same as
          @('int-shl-checked-bound-gadget-unsat'), except width 128
          is included: @('shr_checked') emits this check before the
          wrapped shift, including the division circuit at width 128."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-bound-gadget excess)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-from-bits-le-gadget-iff-all-zero
                            (p p)
                            (asg asg)
                            (excess excess))
                 (:instance int-exponent-high-bits-nonzero
                            (k (1- (integer-length n))))
                 (:instance int-len-nthcdr-is-len-excess
                            (n (1- (integer-length n)))
                            (bits (int->lebits e m)))
                 (:instance int-width-is-power-of-two))
           :in-theory (e/d (int-shr-checked-bound-gadget
                            int-bit-listp-of-nthcdr
                            bit-listp-of-int->lebits-explicit
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-from-bits-le-gadget-iff-all-zero
                            int-exponent-high-bits-nonzero
                            int-len-nthcdr-is-len-excess
                            int-width-is-power-of-two
                            nthcdr
                            repeat
                            int->lebits
                            lookup-equal-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-shift-lower-when-bits
  (implies (and (symbolp final)
                (symbol-listp zs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg final)
                (r1cs::valuation-binds-allp asg zs)
                (bit-listp (lookup-equal-list zs asg))
                (equal (lookup-equal final asg)
                       (lebits=>nat (lookup-equal-list zs asg)))
                (< (lebits=>nat (lookup-equal-list zs asg)) p))
           (r1cs::r1cs-constraints-holdp
            (int-shift-lower-gadget final zs p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-shift-lower-gadget
                            boolean-check-gadget-list-to-bit-listp
                            pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
                            r1cs::r1cs-constraints-holdp-of-append
                            acl2::mod-when-<)
                           (boolean-check-gadget-list
                            pow2sum-gadget
                            mod
                            floor
                            lookup-equal)))))

(defruled int-shift-var-chain-when-witness
  :short "The canonical select witnesses satisfy the tail of the shift."
  (implies (and (symbolp prev)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal (len nexts) (len ebits))
                (natp i)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (natp (lookup-equal prev asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< i (1- (integer-length n)))
                (<= (+ i (len ebits)) (1- (integer-length n)))
                (< (lookup-equal prev asg)
                   (expt 2 (+ n (expt 2 i))))
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (lookup-equal prev asg)
                        (lookup-equal-list ebits asg)
                        i)))
           (r1cs::r1cs-constraints-holdp
            (int-shift-var-chain prev ebits nexts i p)
            asg p))
  :hints (("Goal"
           :induct (int-shift-var-chain prev ebits nexts i p)
           :in-theory (e/d (int-shift-var-chain
                            int-shift-witness-values
                            int-shift-var-step-to-after
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul
                            pfield::neg)))
          ("Subgoal *1/2"
           :use ((:instance int-shift-after-bound
                            (width n)
                            (cur (lookup-equal prev asg))
                            (bit (lookup-equal (car ebits) asg))
                            (i i))
                 (:instance int-shift-cur-times-pow-below-prime
                            (cur (lookup-equal prev asg))
                            (p (base-prime))
                            (i i))
                 (:instance int-shift-var-step-to-after
                            (bit (car ebits))
                            (cur prev)
                            (next (car nexts))
                            (i i)
                            (p (base-prime))
                            (asg asg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-shl-wrapped-bits-are-spec
  :short "The low @('n') bits of @('N(x) * 2^(e mod n)') are @('shl_wrapped')."
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (booleanp signedp)
                (int-valuep x signedp n)
                (natp e))
           (equal (lebits->int
                   (take n
                         (int->lebits (* (int-spec-unsigned x n)
                                         (expt 2 (mod e n)))
                                      (* 2 n)))
                   signedp)
                  (int-shl-wrapped-spec x e signedp n)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-low-bits-are-wrap
                            (bits (int->lebits
                                   (* (int-spec-unsigned x n)
                                      (expt 2 (mod e n)))
                                   (* 2 n)))
                            (n n)
                            (signedp signedp))
                 (:instance int-shl-wrapped-is-wrap-of-pattern)
                 (:instance int-shift-run-below-double
                            (cur (int-spec-unsigned x n))
                            (i 0)
                            (bits (int->lebits (mod e n)
                                               (1- (integer-length n)))))
                 (:instance int-shift-run-value
                            (cur (int-spec-unsigned x n))
                            (i 0)
                            (bits (int->lebits (mod e n)
                                               (1- (integer-length n))))))
           :in-theory (e/d (lebits=>nat-of-int->lebits
                            len-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            int-spec-unsigned
                            int-width-is-power-of-two
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<
                            acl2::<-of-mod-same-arg2
                            acl2::ifix-when-integerp
                            nfix
                            lnfix)
                           (int-low-bits-are-wrap
                            int-shl-wrapped-is-wrap-of-pattern
                            int-shift-run-below-double
                            int-shift-run-value
                            int->lebits
                            mod
                            floor
                            take)))))

(defruled int-shl-chain-when-witness
  :short "Canonical witnesses satisfy the variable-mode left-shift selects."
  (implies (and (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (equal (len xs) n)
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< (lebits=>nat (lookup-equal-list xs asg))
                   (expt 2 n))
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (lebits=>nat (lookup-equal-list xs asg))
                        (lookup-equal-list ebits asg)
                        0)))
           (r1cs::r1cs-constraints-holdp
            (int-shl-chain-gadget xs ebits nexts p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :use ((:instance int-shift-lc-step-to-after
                            (bit (car ebits))
                            (next (car nexts))
                            (p (base-prime)))
                 (:instance int-shift-var-chain-when-witness
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1)
                            (p (base-prime)))
                 (:instance int-shift-cur-below-step
                            (cur (lebits=>nat (lookup-equal-list xs asg)))
                            (i 0))
                 (:instance int-shift-after-bound
                            (width n)
                            (cur (lebits=>nat (lookup-equal-list xs asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-shift-cur-times-pow-below-prime
                            (cur (lebits=>nat (lookup-equal-list xs asg)))
                            (i 0)
                            (p (base-prime))))
           :in-theory (e/d (int-shl-chain-gadget
                            int-shift-witness-values
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp
                            integer-widthp
                            posp-when-integer-widthp)
                           (int-shift-lc-step-to-after
                            int-shift-var-chain-when-witness
                            int-shift-cur-below-step
                            int-shift-after-bound
                            int-shift-cur-times-pow-below-prime
                            mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul)))))

(defruled int-shl-wrapped-gadget-complete
  :short "R1CS-COMPLETE of variable-mode @('shl_wrapped'), both
          signednesses, every integer width other than 128.  A constant
          exponent emits no select.  @('zs') is the @('2n')-bit
          little-endian image of @('N(x)*2^(e mod n)'), and the low
          @('n') bits are the funspec."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (booleanp signedp)
                (int-valuep x signedp n)
                (natp e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (symbol-listp zs)
                (equal (len xs) n)
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits))
                (equal (len zs) (* 2 n))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (r1cs::valuation-bindsp asg (car (last nexts)))
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ebits asg)
                       (int->lebits (mod e n)
                                    (1- (integer-length n))))
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (int-spec-unsigned x n)
                        (lookup-equal-list ebits asg)
                        0))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (* (int-spec-unsigned x n)
                                       (expt 2 (mod e n)))
                                    (* 2 n))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-shl-wrapped-gadget xs ebits nexts zs p)
                 asg p)
                (equal (lebits->int
                        (take n (lookup-equal-list zs asg))
                        signedp)
                       (int-shl-wrapped-spec x e signedp n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-shl-chain-when-witness)
                 (:instance int-shift-lower-when-bits
                            (final (car (last nexts)))
                            (p (base-prime)))
                 (:instance int-shl-wrapped-bits-are-spec)
                 (:instance int-shift-witness-last-is-run
                            (cur (int-spec-unsigned x n))
                            (bits (lookup-equal-list ebits asg))
                            (i 0))
                 (:instance int-shift-run-value
                            (cur (int-spec-unsigned x n))
                            (bits (lookup-equal-list ebits asg))
                            (i 0))
                 (:instance lebits=>nat-of-int->lebits
                            (x x)
                            (n n))
                 (:instance lebits=>nat-of-int->lebits
                            (x (mod e n))
                            (n (1- (integer-length n))))
                 (:instance lebits=>nat-of-int->lebits
                            (x (* (int-spec-unsigned x n)
                                  (expt 2 (mod e n))))
                            (n (* 2 n)))
                 (:instance int-shift-below-prime
                            (v (* (int-spec-unsigned x n)
                                  (expt 2 (mod e n))))
                            (p (base-prime)))
                 (:instance int-shift-run-below-double
                            (cur (int-spec-unsigned x n))
                            (i 0)
                            (bits (lookup-equal-list ebits asg)))
                 (:instance car-of-lookup-equal-list
                            (keys (last nexts))
                            (alist asg)))
           :in-theory (e/d (int-shl-wrapped-gadget
                            int-spec-unsigned
                            int-width-is-power-of-two
                            last-of-lookup-equal-list
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<
                            acl2::ifix-when-integerp
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int-shl-chain-when-witness
                            int-shift-lower-when-bits
                            int-shl-wrapped-bits-are-spec
                            int-shift-witness-last-is-run
                            int-shift-run-value
                            lebits=>nat-of-int->lebits
                            int-shift-below-prime
                            int->lebits
                            mod
                            floor
                            lookup-equal
                            lookup-equal-list-of-last
                            car-of-lookup-equal-list
                            take)))))

(defruled int-shl-checked-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shl_checked')
          unsatisfiable, width other than 128.  @('shl') and
          @('shl_assign') emit this circuit.  The high exponent bits
          are not all zero.  Signed @('shl_checked') sign-extends and
          is not this gadget."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (symbol-listp high)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-shift-gadget
                  xs ebits excess nexts zs high p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shl-checked-bound-gadget-unsat
           :in-theory (e/d (int-shl-checked-shift-gadget
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int-shl-checked-bound-gadget-unsat)))))

(defruled int-shl-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shl') unsatisfiable,
          width other than 128.  @('shl') emits @('shl_checked')."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (symbol-listp high)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shl-shift-gadget xs ebits excess nexts zs high p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shl-checked-shift-gadget-unsat-wide
           :in-theory (e/d (int-shl-shift-gadget)
                           (int-shl-checked-shift-gadget-unsat-wide)))))

(defruled int-shl-assign-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shl_assign')
          unsatisfiable, width other than 128.  @('shl_assign') emits
          @('shl_checked')."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (symbol-listp high)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shl-assign-shift-gadget
                  xs ebits excess nexts zs high p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shl-checked-shift-gadget-unsat-wide
           :in-theory (e/d (int-shl-assign-shift-gadget)
                           (int-shl-checked-shift-gadget-unsat-wide)))))

(defruled int-shr-checked-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shr_checked')
          unsatisfiable, width other than 128.  @('shr') and
          @('shr_assign') emit this circuit.  Signed right shift adds
          a sign mask and is not this gadget.  Width 128 divides."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-shift-gadget
                  xs ebits excess nexts zs p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shr-checked-bound-gadget-unsat
           :in-theory (e/d (int-shr-checked-shift-gadget
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int-shr-checked-bound-gadget-unsat)))))

(defruled int-shr-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shr') unsatisfiable,
          width other than 128."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shr-shift-gadget xs ebits excess nexts zs p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shr-checked-shift-gadget-unsat-wide
           :in-theory (e/d (int-shr-shift-gadget)
                           (int-shr-checked-shift-gadget-unsat-wide)))))

(defruled int-shr-assign-shift-gadget-unsat-wide
  :short "Exponent out of range makes unsigned @('shr_assign')
          unsatisfiable, width other than 128."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (<= n e)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (not (r1cs::r1cs-constraints-holdp
                 (int-shr-assign-shift-gadget xs ebits excess nexts zs p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use int-shr-checked-shift-gadget-unsat-wide
           :in-theory (e/d (int-shr-assign-shift-gadget)
                           (int-shr-checked-shift-gadget-unsat-wide)))))

(local
 (defthm int-bit-listp-of-repeat-0
   (bit-listp (repeat n 0))
   :hints (("Goal" :in-theory (enable repeat bit-listp)))))

(defruledl int-shl-checked-excess-lookup-zero
  (implies (and (integer-widthp n)
                (member-equal m '(8 16 32))
                (natp e)
                (< e n)
                (< e (expt 2 m))
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (equal (lookup-equal-list excess asg)
                  (repeat (len excess) 0)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal m 8) (equal m 16) (equal m 32))
           :use ((:instance int-excess-zero-when-lebits-below
                            (bits (int->lebits e m))
                            (n (1- (integer-length n))))
                 (:instance int-len-nthcdr-is-len-excess
                            (n (1- (integer-length n)))
                            (bits (int->lebits e m))))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            len-of-int->lebits
                            lebits=>nat-of-int->lebits
                            int-width-is-power-of-two
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<
                            acl2::ifix-when-integerp)
                           (int-excess-zero-when-lebits-below
                            int-len-nthcdr-is-len-excess
                            int->lebits
                            nthcdr
                            repeat
                            mod)))))

(defruledl int-shl-checked-high-lookup-zero
  (implies (and (integer-widthp n)
                (int-valuep z nil n)
                (equal (lookup-equal-list zs asg)
                       (int->lebits z (* 2 n)))
                (equal (lookup-equal-list high asg)
                       (nthcdr n (lookup-equal-list zs asg))))
           (equal (lookup-equal-list high asg)
                  (repeat (len high) 0)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32)
                   (equal n 64) (equal n 128))
           :use ((:instance int-excess-zero-when-lebits-below
                            (bits (lookup-equal-list zs asg))
                            (n n))
                 (:instance int-len-nthcdr-is-len-excess
                            (excess high)
                            (n n)
                            (bits (lookup-equal-list zs asg))))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            len-of-int->lebits
                            lebits=>nat-of-int->lebits
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<
                            acl2::ifix-when-integerp)
                           (int-excess-zero-when-lebits-below
                            int-len-nthcdr-is-len-excess
                            int->lebits
                            nthcdr
                            repeat
                            mod)))))

(defruledl int-shl-checked-excess-holds
  (implies (and (primep p)
                (integer-widthp n)
                (member-equal m '(8 16 32))
                (natp e)
                (< e n)
                (< e (expt 2 m))
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (< (len excess) p)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m))))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget excess)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-excess-zero-implies-constraint (p p))
           :in-theory (e/d (int-shl-checked-excess-lookup-zero
                            int-bit-listp-of-repeat-0
                            int-bit-listp-of-nthcdr
                            bit-listp-of-int->lebits-explicit)
                           (int-excess-zero-implies-constraint
                            int->lebits
                            nthcdr
                            repeat
                            lookup-equal-list)))))

(defruledl int-shl-checked-high-holds
  (implies (and (primep p)
                (integer-widthp n)
                (int-valuep z nil n)
                (symbol-listp high)
                (symbol-listp zs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg high)
                (< (len high) p)
                (equal (lookup-equal-list zs asg)
                       (int->lebits z (* 2 n)))
                (equal (lookup-equal-list high asg)
                       (nthcdr n (lookup-equal-list zs asg))))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget high)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-excess-zero-implies-constraint
                           (excess high)
                           (p p))
           :in-theory (e/d (int-shl-checked-high-lookup-zero
                            int-bit-listp-of-repeat-0
                            int-bit-listp-of-nthcdr
                            bit-listp-of-int->lebits-explicit)
                           (int-excess-zero-implies-constraint
                            int->lebits
                            nthcdr
                            repeat
                            lookup-equal-list)))))

(local
 (defthm int-shl-checked-spec-when-fits
   (implies (and (integer-widthp n)
                 (not signedp)
                 (int-valuep x nil n)
                 (natp e)
                 (< e n)
                 (int-valuep (* x (expt 2 e)) nil n))
            (equal (int-shl-checked-spec x e nil n)
                   (int-shl-wrapped-spec x e nil n)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (int-shl-checked-spec
                             int-shl-wrapped-spec
                             int-wrap
                             int-valuep
                             int-min
                             int-max
                             integer-widthp
                             posp-when-integer-widthp
                             lnfix
                             nfix
                             acl2::mod-when-<
                             acl2::ifix-when-integerp)
                           (mod))))))

(defruled int-shl-checked-shift-gadget-complete
  :short "R1CS-COMPLETE, success half, of unsigned @('shl_checked')
          for a width other than 128.  The exponent is below the
          width and @($x \\cdot 2^e$) fits in the unsigned range.
          @('shl') and @('shl_assign') emit this circuit.  Signed
          @('shl_checked') sign-extends and is not this gadget.
          A product that does not fit is a separate @('spec-error')
          and is not proved unsatisfiable here."
  (implies (and (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (not signedp)
                (int-valuep x nil n)
                (natp e)
                (< e n)
                (member-equal m '(8 16 32))
                (< e (expt 2 m))
                (int-valuep (* x (expt 2 e)) nil n)
                (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp excess)
                (symbol-listp nexts)
                (symbol-listp zs)
                (symbol-listp high)
                (equal (len xs) n)
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits))
                (equal (len zs) (* 2 n))
                (consp nexts)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg excess)
                (r1cs::valuation-binds-allp asg nexts)
                (r1cs::valuation-bindsp asg (car (last nexts)))
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg high)
                (< (len excess) p)
                (< (len high) p)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ebits asg)
                       (int->lebits e (1- (integer-length n))))
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n))
                               (int->lebits e m)))
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (int-spec-unsigned x n)
                        (lookup-equal-list ebits asg)
                        0))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (* x (expt 2 e)) (* 2 n)))
                (equal (lookup-equal-list high asg)
                       (nthcdr n (lookup-equal-list zs asg))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-shift-gadget
                  xs ebits excess nexts zs high p)
                 asg p)
                (equal (lebits->int
                        (take n (lookup-equal-list zs asg))
                        nil)
                       (int-shl-checked-spec x e nil n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-shl-wrapped-gadget-complete
                            (signedp nil))
                 (:instance int-shl-checked-excess-holds)
                 (:instance int-shl-checked-high-holds
                            (z (* x (expt 2 e))))
                 (:instance int-shl-checked-spec-when-fits))
           :in-theory (e/d (int-shl-checked-shift-gadget
                            int-shl-checked-bound-gadget
                            int-spec-unsigned
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            nfix
                            acl2::mod-when-<
                            acl2::ifix-when-integerp
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int-shl-wrapped-gadget-complete
                            int-shl-checked-excess-holds
                            int-shl-checked-high-holds
                            int-shl-wrapped-gadget
                            int-from-bits-le-gadget
                            int-shl-checked-spec
                            int-shl-wrapped-spec
                            int-wrap
                            int->lebits
                            nthcdr
                            repeat
                            mod
                            floor
                            lookup-equal)))))
