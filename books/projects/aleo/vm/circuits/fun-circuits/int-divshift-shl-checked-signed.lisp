; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode signed shl_checked (and shl, shl_assign, which emit the same
; circuit) for widths 8, 16, 32 and 64, where 3n is below the field data
; size.  snarkVM (circuit/types/integers/src/shl_checked.rs) asserts the
; exponent bits at and above log2(n) are zero, sign-extends the value bits
; to 2n bits, runs the same select chain as the unsigned case starting
; from Field::from_bits_le of the 2n bits, takes to_lower_bits_le(3n) of
; the final select, and asserts (E::assert_eq, i.e. (bit) (1) = (msb)) that
; bits n..2n-1 equal bit n-1.  The result integer is the low n bits.
;
; The sign-extended linear combination names the msb wire n+1 times; snarkVM
; merges the repeated terms, which has the same dot product.

(in-package "ALEOVM")

(include-book "int-divshift-shlc-signed-bits")
(include-book "int-divshift-shl-checked-sound")
(include-book "../r1cs/equal")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-sext-wires ((xs symbol-listp))
  :short "The value wires followed by @('n') copies of the msb wire."
  (append xs (repeat (len xs) (car (last xs)))))

(define int-divshift-msb-eq-gadget ((bits symbol-listp) (msb symbolp))
  :short "@('E::assert_eq(bit, msb)') for each bit."
  (if (endp bits)
      nil
    (append (equal-gadget (car bits) msb)
            (int-divshift-msb-eq-gadget (cdr bits) msb))))

(define int-divshift-shl-checked-signed-gadget ((xs symbol-listp)
                                                (ebits symbol-listp)
                                                (excess symbol-listp)
                                                (nexts symbol-listp)
                                                (zs symbol-listp)
                                                (p primep))
  :verify-guards nil
  :short "Signed @('shl_checked') for widths 8 to 64."
  (b* ((n (len xs)))
    (append (int-shl-checked-bound-gadget excess)
            (int-shl-chain-gadget (int-divshift-sext-wires xs) ebits nexts p)
            (int-shift-lower-gadget (car (last nexts)) zs p)
            (int-divshift-msb-eq-gadget (take n (nthcdr n zs))
                                        (nth (1- n) zs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-msb-eq-gadget-iff
  (implies (and (symbol-listp bits)
                (symbolp msb)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-bindsp asg msb))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-msb-eq-gadget bits msb) asg p)
                  (equal (lookup-equal-list bits asg)
                         (repeat (len bits) (lookup-equal msb asg)))))
  :induct (len bits)
  :enable (int-divshift-msb-eq-gadget
           equal-gadget-to-equal
           r1cs::r1cs-constraints-holdp-of-append
           r1cs::valuation-binds-allp
           lookup-equal-list
           repeat))

(defruled int-divshift-sext-wire-facts
  (implies (and (symbol-listp xs)
                (consp xs)
                (r1cs::valuation-binds-allp asg xs)
                (integer-widthp n)
                (equal (len xs) n)
                (integerp x)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n)))
           (and (symbol-listp (int-divshift-sext-wires xs))
                (r1cs::valuation-binds-allp asg (int-divshift-sext-wires xs))
                (equal (lookup-equal-list (int-divshift-sext-wires xs) asg)
                       (int->lebits x (* 2 n)))
                (bit-listp (lookup-equal-list (int-divshift-sext-wires xs)
                                              asg))
                (equal (lebits=>nat (lookup-equal-list
                                     (int-divshift-sext-wires xs) asg))
                       (mod x (expt 2 (* 2 n))))))
  :do-not-induct t
  :use ((:instance int-divshift-slc-sext-bits (y x))
        (:instance msb-wire)
        (:instance lebits=>nat-of-int->lebits (x x) (n (* 2 n))))
  :in-theory (e/d (int-divshift-sext-wires
                   lookup-equal-list-of-append
                   lookup-equal-list-of-repeat
                   r1cs::valuation-binds-allp-of-append
                   binds-allp-of-repeat
                   symbol-listp-of-repeat
                   bit-listp-of-int->lebits-explicit
                   posp-when-integer-widthp
                   acl2::ifix-when-integerp)
                  (int-divshift-slc-sext-bits msb-wire
                   lebits=>nat-of-int->lebits int->lebits))
  :prep-lemmas
  ((defruled msb-wire
     (implies (and (symbol-listp xs)
                   (consp xs)
                   (r1cs::valuation-binds-allp asg xs))
              (and (symbolp (car (last xs)))
                   (r1cs::valuation-bindsp asg (car (last xs)))
                   (equal (lookup-equal (car (last xs)) asg)
                          (car (last (lookup-equal-list xs asg))))))
     :induct (len xs)
     :enable (last lookup-equal-list r1cs::valuation-binds-allp symbol-listp))
   (defruled binds-allp-of-repeat
     (implies (r1cs::valuation-bindsp asg a)
              (r1cs::valuation-binds-allp asg (repeat k a)))
     :enable (repeat r1cs::valuation-binds-allp))
   (defruled symbol-listp-of-repeat
     (implies (symbolp a) (symbol-listp (repeat k a)))
     :enable repeat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun int-divshift-sc-expt-ind (k)
   (if (zp k) t (int-divshift-sc-expt-ind (1- k)))))

(defruledl int-divshift-sc-below-expt-plus
  (implies (and (natp cur)
                (natp a)
                (natp k)
                (< cur (expt 2 a)))
           (< cur (expt 2 (+ a k))))
  :hints (("Goal"
           :induct (int-divshift-sc-expt-ind k)
           :in-theory (enable expt))))

(defruledl int-divshift-sc-double-power
  (implies (natp i)
           (equal (+ (expt 2 i) (expt 2 i))
                  (expt 2 (+ 1 i))))
  :enable acl2::expt-of-+-of-1-arg2)

(defruledl int-divshift-sc-below-wider-power
  (implies (and (natp cur)
                (natp width)
                (natp i)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< cur (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :use (:instance int-divshift-sc-below-expt-plus
                  (a (+ width (expt 2 i)))
                  (k (expt 2 i)))
  :enable int-divshift-sc-double-power
  :disable (int-divshift-sc-below-expt-plus expt acl2::expt-of-+-of-1-arg2))

(defruledl int-divshift-sc-after-bound
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
                            int-divshift-sc-below-wider-power)
                           (acl2::*-of-expt-and-expt-same-base)))
          ("Subgoal 1"
           :use (:instance acl2::<-of-*-and-*-cancel
                           (x1 cur)
                           (x2 (expt 2 (+ width (expt 2 i))))
                           (y (expt 2 (expt 2 i))))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            acl2::*-of-expt-and-expt-same-base
                            int-divshift-sc-double-power)
                           (acl2::<-of-*-and-*-cancel)))))

(defruledl int-divshift-sc-cur-below-step
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (< cur (expt 2 n)))
           (< cur (expt 2 (+ n (expt 2 i)))))
  :do-not-induct t
  :use (:instance int-divshift-sc-below-expt-plus
                  (a n)
                  (k (expt 2 i)))
  :disable (int-divshift-sc-below-expt-plus expt))

(defruledl int-divshift-sc-atom-when-len-0
  (implies (equal (len x) 0)
           (not (consp x))))

(defruledl int-divshift-sc-pow-below
  (implies (and (natp w)
                (natp i)
                (natp k)
                (< (expt 2 (+ w (expt 2 (+ i k)))) p))
           (< (expt 2 (expt 2 i)) p))
  :do-not-induct t
  :use ((:instance acl2::expt-monotone-strong (r 2) (i i) (j (+ i k)))
        (:instance acl2::expt-monotone-strong
                   (r 2) (i (expt 2 i)) (j (+ w (expt 2 (+ i k))))))
  :cases ((equal k 0) (equal (+ w (expt 2 (+ i k))) (expt 2 i)))
  :in-theory (disable acl2::expt-monotone-strong
                      acl2::<-of-expt-and-expt-same-base))

(defruledl int-divshift-sc-wide-mono
  (implies (and (natp w)
                (natp i)
                (natp k)
                (<= 1 k))
           (<= (expt 2 (+ w (expt 2 (+ 1 i))))
               (expt 2 (+ w (expt 2 (+ i k))))))
  :do-not-induct t
  :use ((:instance acl2::expt-monotone-strong (r 2) (i (+ 1 i)) (j (+ i k)))
        (:instance acl2::expt-monotone-strong
                   (r 2)
                   (i (+ w (expt 2 (+ 1 i))))
                   (j (+ w (expt 2 (+ i k))))))
  :cases ((equal k 1))
  :in-theory (disable acl2::expt-monotone-strong
                      acl2::<-of-expt-and-expt-same-base))

(defruledl int-divshift-sc-step-bounds
  (implies (and (natp w)
                (natp cur)
                (natp i)
                (natp k)
                (<= 1 k)
                (< cur (expt 2 (+ w (expt 2 i))))
                (< (expt 2 (+ w (expt 2 (+ i k)))) p))
           (and (< (int-shift-pow i) p)
                (< (* cur (int-shift-pow i)) p)))
  :do-not-induct t
  :use ((:instance int-divshift-sc-after-bound (width w) (bit 1))
        (:instance acl2::expt-monotone-weak-copy
                   (a (expt 2 (+ 1 i))) (b (expt 2 (+ i k))))
        (:instance acl2::expt-monotone-weak-copy
                   (a (+ 1 i)) (b (+ i k)))
        (:instance acl2::expt-monotone-weak-copy
                   (a (+ w (expt 2 (+ 1 i)))) (b (+ w (expt 2 (+ i k)))))
        (:instance acl2::expt-monotone-weak-copy
                   (a (expt 2 i)) (b (+ w (expt 2 (+ 1 i)))))
        (:instance acl2::expt-monotone-weak-copy
                   (a i) (b (+ 1 i)))
        (:instance int-divshift-sc-pow-below)
        (:instance int-divshift-sc-wide-mono))
  :in-theory (e/d (int-shift-after int-shift-pow)
                  (int-divshift-sc-after-bound acl2::expt-monotone-weak-copy
                   acl2::<-of-expt-and-expt-same-base))
  :prep-lemmas
  ((defruled acl2::expt-monotone-weak-copy
     (implies (and (natp a) (natp b) (<= a b))
              (<= (expt 2 a) (expt 2 b)))
     :use (:instance acl2::expt-monotone-strong (r 2) (i a) (j b))
     :cases ((equal a b)))))

(defruled int-divshift-gvar-chain-sound
  :short "The tail selects force the canonical witnesses for any starting
          width @('w'), given that the final span is below the prime."
  (implies (and (symbolp prev)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal (len nexts) (len ebits))
                (natp i)
                (natp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (natp (lookup-equal prev asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< (lookup-equal prev asg) (expt 2 (+ w (expt 2 i))))
                (< (expt 2 (+ w (expt 2 (+ i (len ebits))))) p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-var-chain prev ebits nexts i p)
                 asg p))
           (equal (lookup-equal-list nexts asg)
                  (int-shift-witness-values
                   (lookup-equal prev asg)
                   (lookup-equal-list ebits asg)
                   i)))
  :hints (("Goal"
           :induct (int-shift-var-chain prev ebits nexts i p)
           :in-theory (e/d (int-shift-var-chain
                            int-divshift-sc-atom-when-len-0
                            int-shift-witness-values
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
           :use ((:instance int-divshift-sc-after-bound
                            (width w)
                            (cur (lookup-equal prev asg))
                            (bit (lookup-equal (car ebits) asg))
                            (i i))
                 (:instance int-divshift-sc-step-bounds
                            (cur (lookup-equal prev asg))
                            (k (len ebits)))
                 (:instance int-shift-var-step-to-after
                            (bit (car ebits))
                            (cur prev)
                            (next (car nexts))
                            (i i))))))

(defruled int-divshift-gvar-chain-complete
  (implies (and (symbolp prev)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal (len nexts) (len ebits))
                (natp i)
                (natp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (natp (lookup-equal prev asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< (lookup-equal prev asg) (expt 2 (+ w (expt 2 i))))
                (< (expt 2 (+ w (expt 2 (+ i (len ebits))))) p)
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
                            int-divshift-sc-atom-when-len-0
                            int-shift-witness-values
                            lookup-equal-of-car
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (mod
                            floor
                            lookup-equal
                            lookup-equal-list
                            car-of-lookup-equal-list
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul
                            pfield::neg)))
          ("Subgoal *1/2"
           :use ((:instance int-divshift-sc-after-bound
                            (width w)
                            (cur (lookup-equal prev asg))
                            (bit (lookup-equal (car ebits) asg))
                            (i i))
                 (:instance int-divshift-sc-step-bounds
                            (cur (lookup-equal prev asg))
                            (k (len ebits)))
                 (:instance int-shift-var-step-to-after
                            (bit (car ebits))
                            (cur prev)
                            (next (car nexts))
                            (i i))))))
