; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND and R1CS-COMPLETE of variable-mode signed shl_checked (and shl,
; shl_assign) for widths 8, 16, 32 and 64.  The select chain starts from
; the 2n-bit sign extension S = x mod 2^(2n), its final select is
; V = S * 2^e < 2^(3n), and to_lower_bits_le(3n) gives the bits of V.  The
; assert_eq constraints make bits n..2n-1 of V equal to bit n-1, which with
; e < n pins the signed value of the low n bits to x * 2^e.

(in-package "ALEOVM")

(include-book "int-divshift-shl-checked-signed")

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

(set-prover-step-limit 20000000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-wc-first-bounds
  (implies (and (natp w)
                (natp s)
                (natp k)
                (<= 1 k)
                (< s (expt 2 w))
                (< (expt 2 (+ w (expt 2 k))) p))
           (and (< (* 2 s) p)
                (< s (expt 2 (+ w 1)))))
  :do-not-induct t
  :use ((:instance acl2::expt-monotone-strong (r 2) (i 0) (j k))
        (:instance acl2::expt-monotone-strong
                   (r 2) (i (+ w 1)) (j (+ w (expt 2 k)))))
  :cases ((equal (expt 2 k) 1))
  :enable acl2::expt-of-+
  :disable (acl2::expt-monotone-strong
            acl2::<-of-expt-and-expt-same-base))

(defruled int-divshift-wide-chain-sound
  :short "The left-shift selects starting from any bit vector of width
          @('w') force the canonical witnesses, given that the final span
          is below the prime."
  (implies (and (symbol-listp ys)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (consp ebits)
                (equal (len nexts) (len ebits))
                (natp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (bit-listp (lookup-equal-list ys asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< (lebits=>nat (lookup-equal-list ys asg)) (expt 2 w))
                (< (expt 2 (+ w (expt 2 (len ebits)))) p)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-chain-gadget ys ebits nexts p)
                 asg p))
           (equal (lookup-equal-list nexts asg)
                  (int-shift-witness-values
                   (lebits=>nat (lookup-equal-list ys asg))
                   (lookup-equal-list ebits asg)
                   0)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-wc-first-bounds
                            (s (lebits=>nat (lookup-equal-list ys asg)))
                            (k (len ebits)))
                 (:instance int-shift-lc-step-to-after
                            (bit (car ebits))
                            (xs ys)
                            (next (car nexts)))
                 (:instance int-divshift-gvar-chain-sound
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1))
                 (:instance int-divshift-sc-after-bound
                            (width w)
                            (cur (lebits=>nat (lookup-equal-list ys asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i 0)))
           :in-theory (e/d (int-shl-chain-gadget
                            int-shift-witness-values
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (int-shift-lc-step-to-after
                            int-divshift-gvar-chain-sound
                            int-divshift-wc-first-bounds
                            int-divshift-sc-after-bound
                            mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul)))))

(defruled int-divshift-wide-chain-complete
  (implies (and (symbol-listp ys)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (consp ebits)
                (equal (len nexts) (len ebits))
                (natp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (bit-listp (lookup-equal-list ys asg))
                (bit-listp (lookup-equal-list ebits asg))
                (< (lebits=>nat (lookup-equal-list ys asg)) (expt 2 w))
                (< (expt 2 (+ w (expt 2 (len ebits)))) p)
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (lebits=>nat (lookup-equal-list ys asg))
                        (lookup-equal-list ebits asg)
                        0)))
           (r1cs::r1cs-constraints-holdp
            (int-shl-chain-gadget ys ebits nexts p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-wc-first-bounds
                            (s (lebits=>nat (lookup-equal-list ys asg)))
                            (k (len ebits)))
                 (:instance int-shift-lc-step-to-after
                            (bit (car ebits))
                            (xs ys)
                            (next (car nexts)))
                 (:instance int-divshift-gvar-chain-complete
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1))
                 (:instance int-divshift-sc-after-bound
                            (width w)
                            (cur (lebits=>nat (lookup-equal-list ys asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i 0)))
           :in-theory (e/d (int-shl-chain-gadget
                            int-shift-witness-values
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (int-shift-lc-step-to-after
                            int-divshift-gvar-chain-complete
                            int-divshift-wc-first-bounds
                            int-divshift-sc-after-bound
                            mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-wl-bits-from-nat
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable (int->lebits acl2::mod-when-<))

(defruled int-divshift-wide-lower-sound
  :short "@('Field::to_lower_bits_le(k)') of a value below @('2^k'), with
          @('2^k') below the prime, forces the canonical bits."
  (implies (and (symbolp final)
                (symbol-listp zs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg final)
                (r1cs::valuation-binds-allp asg zs)
                (natp v)
                (< (expt 2 (len zs)) p)
                (equal (lookup-equal final asg) v)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget final zs p)
                 asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits v (len zs))))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list zs asg)))
        (:instance int-divshift-wl-bits-from-nat
                   (bits (lookup-equal-list zs asg))
                   (n (len zs))))
  :in-theory (e/d (int-shift-lower-gadget
                   boolean-check-gadget-list-to-bit-listp
                   pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
                   r1cs::r1cs-constraints-holdp-of-append
                   len-of-lookup-equal-list
                   acl2::mod-when-<)
                  (boolean-check-gadget-list
                   pow2sum-gadget
                   mod
                   floor
                   lookup-equal)))

(defruled int-divshift-wide-lower-complete
  (implies (and (symbolp final)
                (symbol-listp zs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg final)
                (r1cs::valuation-binds-allp asg zs)
                (natp v)
                (< v (expt 2 (len zs)))
                (< (expt 2 (len zs)) p)
                (equal (lookup-equal final asg) v)
                (equal (lookup-equal-list zs asg)
                       (int->lebits v (len zs))))
           (r1cs::r1cs-constraints-holdp
            (int-shift-lower-gadget final zs p)
            asg p))
  :do-not-induct t
  :use ((:instance lebits=>nat-of-int->lebits (x v) (n (len zs))))
  :in-theory (e/d (int-shift-lower-gadget
                   boolean-check-gadget-list-to-bit-listp
                   pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp-of-int->lebits-explicit
                   acl2::mod-when-<
                   acl2::ifix-when-integerp)
                  (boolean-check-gadget-list
                   pow2sum-gadget
                   lebits=>nat-of-int->lebits
                   int->lebits
                   mod
                   floor
                   lookup-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-sl-take-binds
  (implies (and (r1cs::valuation-binds-allp asg keys)
                (<= (nfix k) (len keys)))
           (r1cs::valuation-binds-allp asg (take k keys)))
  :induct (take k keys)
  :enable (take r1cs::valuation-binds-allp))

(defruled int-divshift-sl-nthcdr-binds
  (implies (r1cs::valuation-binds-allp asg keys)
           (r1cs::valuation-binds-allp asg (nthcdr k keys)))
  :induct (nthcdr k keys)
  :enable (nthcdr r1cs::valuation-binds-allp))

(defruled int-divshift-sl-take-symbols
  (implies (and (symbol-listp keys)
                (<= (nfix k) (len keys)))
           (symbol-listp (take k keys)))
  :induct (take k keys)
  :enable take)

(defruled int-divshift-sl-nthcdr-symbols
  (implies (symbol-listp keys)
           (symbol-listp (nthcdr k keys)))
  :induct (nthcdr k keys)
  :enable nthcdr)

(defruled int-divshift-sl-nth-facts
  (implies (and (symbol-listp keys)
                (r1cs::valuation-binds-allp asg keys)
                (natp k)
                (< k (len keys)))
           (and (symbolp (nth k keys))
                (r1cs::valuation-bindsp asg (nth k keys))
                (equal (lookup-equal (nth k keys) asg)
                       (nth k (lookup-equal-list keys asg)))))
  :induct (nth k keys)
  :enable (nth lookup-equal-list r1cs::valuation-binds-allp))

(defruled int-divshift-sl-take-lookup
  (implies (<= (nfix k) (len keys))
           (equal (lookup-equal-list (take k keys) asg)
                  (take k (lookup-equal-list keys asg))))
  :induct (take k keys)
  :enable (take lookup-equal-list))

(local
 (defun int-divshift-sl-ind (k l)
   (if (zp k) (list k l) (int-divshift-sl-ind (1- k) (cdr l)))))

(defruledl int-divshift-sl-take-nthcdr-gen
  (implies (and (natp k) (natp a))
           (equal (take a (nthcdr k l))
                  (nthcdr k (take (+ k a) l))))
  :induct (int-divshift-sl-ind k l)
  :enable (nthcdr take))

(defruledl int-divshift-sl-take-nthcdr
  (implies (and (natp n) (<= (* 2 n) (len l)))
           (equal (take n (nthcdr n l))
                  (nthcdr n (take (* 2 n) l))))
  :do-not-induct t
  :use ((:instance int-divshift-sl-take-nthcdr-gen (k n) (a n))
        (:instance two-n (x n)))
  :in-theory nil
  :prep-lemmas
  ((defruled two-n
     (equal (+ x x) (* 2 x)))))

(defruledl int-divshift-sl-nth-is-last-of-take
  (implies (and (posp n) (<= n (len l)))
           (equal (nth (1- n) l)
                  (car (last (take n l)))))
  :induct (int-divshift-sl-ind n l)
  :enable (nth take last))

(defruled int-divshift-sl-high-of-bits
  :short "The wires checked by @('assert_eq') read bits @('n..2n-1') and
          bit @('n-1') of the @('3n') lower bits of @('V')."
  (implies (and (posp n) (integerp v))
           (and (equal (take n (nthcdr n (int->lebits v (* 3 n))))
                       (nthcdr n (int->lebits v (* 2 n))))
                (equal (nth (1- n) (int->lebits v (* 3 n)))
                       (car (last (int->lebits v n))))
                (equal (take n (int->lebits v (* 3 n)))
                       (int->lebits v n))))
  :do-not-induct t
  :use ((:instance int-divshift-sl-take-nthcdr (l (int->lebits v (* 3 n))))
        (:instance int-divshift-sl-nth-is-last-of-take
                   (l (int->lebits v (* 3 n))))
        (:instance int-divshift-take-of-int->lebits (k (* 2 n)) (w (* 3 n)))
        (:instance int-divshift-take-of-int->lebits (k n) (w (* 3 n))))
  :in-theory (e/d (len-of-int->lebits)
                  (int-divshift-take-of-int->lebits int->lebits take nthcdr
                   nth)))

(defruled int-divshift-sl-prime-bound
  (implies (and (integer-widthp n) (not (equal n 128)))
           (and (< (expt 2 (+ (* 2 n) n)) (base-prime))
                (< (expt 2 (* 3 n)) (base-prime))
                (< 0 (1- (integer-length n)))))
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
  :enable (integer-widthp (:e expt) (:e base-prime) (:e integer-length)
           (:e ecurve::edwards-bls12-q)))

(defruled int-divshift-sl-v-bound
  (implies (and (natp n)
                (natp e)
                (< e n)
                (natp s)
                (< s (expt 2 (* 2 n))))
           (< (* s (expt 2 e)) (expt 2 (* 3 n))))
  :do-not-induct t
  :use ((:instance acl2::<-of-*-and-*-cancel
                   (x1 s) (x2 (expt 2 (* 2 n))) (y (expt 2 e)))
        (:instance acl2::expt-monotone-strong
                   (r 2) (i (+ (* 2 n) e)) (j (* 3 n))))
  :enable acl2::expt-of-+
  :disable (acl2::<-of-*-and-*-cancel acl2::expt-monotone-strong
            acl2::<-of-expt-and-expt-same-base))

(defruled int-divshift-sl-mod-shift
  (implies (and (integerp x) (natp e) (posp m))
           (equal (mod (* (mod x m) (expt 2 e)) m)
                  (mod (* x (expt 2 e)) m)))
  :use (:instance acl2::mod-of-*-of-mod
                  (acl2::x (expt 2 e)) (acl2::x1 x) (acl2::z m))
  :disable acl2::mod-of-*-of-mod)

(defruledl int-divshift-sl-nonlinear
  (implies (and (integerp x) (natp a) (natp h)
                (<= x h) (<= (- h) x) (<= a h))
           (and (<= (* x a) (* h h))
                (<= (- (* h h)) (* x a))))
  :hints (("Goal" :nonlinearp t)))

(defruled int-divshift-sl-product-small
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (natp e)
                (< e n))
           (and (integerp (* x (expt 2 e)))
                (<= (* 4 (* x (expt 2 e))) (expt 2 (* 2 n)))
                (<= (- (expt 2 (* 2 n))) (* 4 (* x (expt 2 e))))))
  :do-not-induct t
  :use ((:instance int-divshift-sl-nonlinear
                   (a (expt 2 e)) (h (expt 2 (1- n))))
        (:instance acl2::expt-monotone-strong
                   (r 2) (i e) (j (1- n)))
        (:instance sq (a n))
        (:instance acl2::expt-of-+ (r 2) (i1 1) (i2 (+ -1 n))))
  :cases ((equal e (1- n)))
  :enable (int-valuep int-min int-max posp-when-integer-widthp)
  :disable (int-divshift-sl-nonlinear acl2::expt-monotone-strong
            acl2::expt-of-+ acl2::<-of-expt-and-expt-same-base)
  :prep-lemmas
  ((defruled sq
     (implies (natp a)
              (equal (* (expt 2 a) (expt 2 a)) (expt 2 (* 2 a))))
     :use (:instance acl2::expt-of-+ (r 2) (i1 a) (i2 a))
     :disable acl2::expt-of-+)))

(defruled int-divshift-sl-spec
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (natp e)
                (< e n)
                (int-valuep (* x (expt 2 e)) t n))
           (equal (int-shl-checked-spec x e t n) (* x (expt 2 e))))
  :enable (int-shl-checked-spec int-valuep acl2::ifix-when-integerp))

(defruled int-divshift-sl-sext-excess-holds
  (implies (and (primep p)
                (equal p (base-prime))
                (integer-widthp n)
                (member-equal m '(8 16 32))
                (natp e)
                (< e n)
                (< e (expt 2 m))
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n)) (int->lebits e m))))
           (r1cs::r1cs-constraints-holdp
            (int-shl-checked-bound-gadget excess) asg p))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-shlc-excess-len
                   (k (1- (integer-length n))))
        (:instance int-excess-zero-when-lebits-below
                   (bits (int->lebits e m))
                   (n (1- (integer-length n))))
        (:instance int-excess-zero-implies-constraint)
        (:instance len-of-lookup-equal-list (keys excess) (alist asg)))
  :enable (int-shl-checked-bound-gadget int-bit-listp-of-nthcdr)
  :disable (int-excess-zero-when-lebits-below
            int-excess-zero-implies-constraint
            len-of-lookup-equal-list
            int->lebits nthcdr repeat
            acl2::len-of-nthcdr acl2::repeat-of-nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sslc-base-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (integer-widthp n)
        (not (equal n 128))
        (integerp x)
        (int-valuep x t n)
        (member-equal m '(8 16 32))
        (natp e)
        (< e (expt 2 m))
        (<= (1- (integer-length n)) m)
        (symbol-listp xs)
        (symbol-listp ebits)
        (symbol-listp excess)
        (symbol-listp nexts)
        (symbol-listp zs)
        (equal (len xs) n)
        (equal (len ebits) (1- (integer-length n)))
        (equal (len nexts) (len ebits))
        (equal (len zs) (* 3 n))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ebits)
        (r1cs::valuation-binds-allp asg excess)
        (r1cs::valuation-binds-allp asg nexts)
        (r1cs::valuation-bindsp asg (car (last nexts)))
        (r1cs::valuation-binds-allp asg zs)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ebits asg)
               (take (1- (integer-length n)) (int->lebits e m)))
        (equal (lookup-equal-list excess asg)
               (nthcdr (1- (integer-length n)) (int->lebits e m)))))

(defmacro int-divshift-sslc-sound-hyps ()
  '(and (int-divshift-sslc-base-hyps)
        (r1cs::r1cs-constraints-holdp
         (int-divshift-shl-checked-signed-gadget xs ebits excess nexts zs p)
         asg p)))

(defrulel int-divshift-sslc-holds
  (implies (int-divshift-sslc-sound-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-bound-gadget excess) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-chain-gadget (int-divshift-sext-wires xs)
                                       ebits nexts p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last nexts)) zs p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-msb-eq-gadget (take n (nthcdr n zs))
                                             (nth (1- n) zs))
                 asg p)))
  :rule-classes nil
  :in-theory (union-theories '(int-divshift-shl-checked-signed-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defrulel int-divshift-sslc-bound
  (implies (int-divshift-sslc-sound-hyps)
           (< e n))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-holds)
        (:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-shlc-excess-len
                   (k (1- (integer-length n))))
        (:instance int-shl-checked-bound-gadget-sound
                   (ebits (int->lebits e m))))
  :in-theory (theory 'minimal-theory))

(defruled int-divshift-sslc-consp-bits
  (implies (posp k)
           (consp (int->lebits v k)))
  :use (:instance len-of-int->lebits (x v) (n k))
  :disable (len-of-int->lebits int->lebits))

(defruled int-divshift-sslc-consp-when-len
  (implies (< 0 (len x)) (consp x)))

(defruled int-divshift-sslc-final-value
  (implies (and (integer-widthp n)
                (natp e)
                (< e n)
                (natp s)
                (symbol-listp nexts)
                (consp nexts)
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        s (int->lebits (mod e n) (1- (integer-length n))) 0)))
           (equal (lookup-equal (car (last nexts)) asg)
                  (* s (expt 2 e))))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-consp-bits
                   (v (mod e n)) (k (1- (integer-length n))))
        (:instance int-shift-witness-last-is-run
                   (cur s)
                   (bits (int->lebits (mod e n) (1- (integer-length n))))
                   (i 0))
        (:instance int-shift-run-value
                   (cur s)
                   (bits (int->lebits (mod e n) (1- (integer-length n))))
                   (i 0))
        (:instance lebits=>nat-of-int->lebits
                   (x (mod e n)) (n (1- (integer-length n))))
        (:instance car-of-lookup-equal-list (keys (last nexts)) (alist asg))
        (:instance last-of-lookup-equal-list (keys nexts) (alist asg)))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit
                   len-of-int->lebits
                   acl2::mod-when-<
                   acl2::ifix-when-integerp
                   posp-when-integer-widthp)
                  (int-shift-witness-last-is-run
                   int-divshift-sl-prime-bound
                   int-divshift-sslc-consp-bits
                   int-shift-run-value
                   lebits=>nat-of-int->lebits
                   car-of-lookup-equal-list
                   last-of-lookup-equal-list
                   lookup-equal-list-of-last
                   int->lebits
                   mod
                   lookup-equal)))

(defruled int-divshift-sslc-sext-small
  (implies (and (integer-widthp n) (integerp x))
           (and (natp (mod x (expt 2 (* 2 n))))
                (< (mod x (expt 2 (* 2 n))) (expt 2 (* 2 n)))))
  :enable posp-when-integer-widthp)

(defrulel int-divshift-sslc-nexts
  (implies (int-divshift-sslc-sound-hyps)
           (equal (lookup-equal-list nexts asg)
                  (int-shift-witness-values
                   (mod x (expt 2 (* 2 n)))
                   (int->lebits (mod e n) (1- (integer-length n)))
                   0)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-holds)
        (:instance int-divshift-sslc-bound)
        (:instance int-divshift-shlc-low-bits)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sext-wire-facts)
        (:instance bit-listp-of-int->lebits-explicit
                   (x (mod e n)) (n (1- (integer-length n))))
        (:instance int-divshift-wide-chain-sound
                   (ys (int-divshift-sext-wires xs))
                   (w (* 2 n))))
  :in-theory (e/d (int-divshift-sslc-consp-when-len)
                  (int-divshift-sslc-sext-small
                   int-divshift-sext-wire-facts
                   int-divshift-wide-chain-sound
                   int-divshift-sl-prime-bound
                   int-divshift-shlc-low-bits
                   int-divshift-shlc-width-facts
                   bit-listp-of-int->lebits-explicit
                   int->lebits
                   mod
                   take
                   nthcdr)))

(defrulel int-divshift-sslc-v
  (implies (int-divshift-sslc-sound-hyps)
           (equal (lookup-equal (car (last nexts)) asg)
                  (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-nexts)
        (:instance int-divshift-sslc-bound)
        (:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sslc-final-value
                   (s (mod x (expt 2 (* 2 n))))))
  :in-theory (e/d (int-divshift-sslc-consp-when-len)
                  (int-divshift-sslc-final-value
                   int-divshift-sslc-sext-small
                   int-divshift-sl-prime-bound
                   int->lebits mod lookup-equal)))

(defrulel int-divshift-sslc-zs
  (implies (int-divshift-sslc-sound-hyps)
           (equal (lookup-equal-list zs asg)
                  (int->lebits (* (mod x (expt 2 (* 2 n))) (expt 2 e))
                               (* 3 n))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-holds)
        (:instance int-divshift-sslc-v)
        (:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-wide-lower-sound
                   (final (car (last nexts)))
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e)))))
  :in-theory (e/d ()
                  (int-divshift-wide-lower-sound
                   int-divshift-sslc-sext-small
                   int-divshift-sl-prime-bound
                   int->lebits mod lookup-equal)))

(defrulel int-divshift-sslc-msb
  (implies (int-divshift-sslc-sound-hyps)
           (b* ((v (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
             (equal (nthcdr n (int->lebits v (* 2 n)))
                    (repeat n (car (last (int->lebits v n)))))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-holds)
        (:instance int-divshift-sslc-zs)
        (:instance int-divshift-sl-high-of-bits
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
        (:instance int-divshift-msb-eq-gadget-iff
                   (bits (take n (nthcdr n zs)))
                   (msb (nth (1- n) zs)))
        (:instance int-divshift-sl-take-binds (keys (nthcdr n zs)) (k n))
        (:instance int-divshift-sl-nthcdr-binds (keys zs) (k n))
        (:instance int-divshift-sl-take-symbols (keys (nthcdr n zs)) (k n))
        (:instance int-divshift-sl-nthcdr-symbols (keys zs) (k n))
        (:instance int-divshift-sl-nth-facts (keys zs) (k (1- n)))
        (:instance int-divshift-sl-take-lookup (keys (nthcdr n zs)) (k n))
        (:instance lookup-equal-list-of-nthcdr
                   (i n) (keys zs) (alist asg)))
  :in-theory (e/d (posp-when-integer-widthp)
                  (int-divshift-sl-high-of-bits
                   int-divshift-msb-eq-gadget-iff
                   int-divshift-sl-take-binds
                   int-divshift-sl-nthcdr-binds
                   int-divshift-sl-take-symbols
                   int-divshift-sl-nthcdr-symbols
                   int-divshift-sl-nth-facts
                   int-divshift-sl-take-lookup
                   lookup-equal-list-of-nthcdr
                   int->lebits mod lookup-equal take nthcdr nth repeat)))

(defruled int-divshift-shl-checked-signed-gadget-sound
  :short "R1CS-SOUND of variable-mode signed @('shl_checked'), @('shl')
          and @('shl_assign') for widths 8 to 64.  A satisfying assignment
          forces the exponent below @('n'), the product @('x * 2^e') into
          the signed range, and the low @('n') result bits to decode to the
          funspec value."
  (implies (int-divshift-sslc-sound-hyps)
           (and (< e n)
                (int-valuep (* x (expt 2 e)) t n)
                (equal (int-shl-checked-spec x e t n) (* x (expt 2 e)))
                (equal (lebits->int (take n (lookup-equal-list zs asg)) t)
                       (int-shl-checked-spec x e t n))))
  :do-not-induct t
  :use ((:instance int-divshift-sslc-bound)
        (:instance int-divshift-sslc-zs)
        (:instance int-divshift-sslc-msb)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sl-high-of-bits
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
        (:instance int-divshift-sl-mod-shift (m (expt 2 (* 2 n))))
        (:instance int-divshift-sl-product-small)
        (:instance int-divshift-slc-check-sound
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e)))
                   (y (* x (expt 2 e))))
        (:instance int-divshift-sl-spec))
  :in-theory (e/d (posp-when-integer-widthp)
                  (int-divshift-sslc-sext-small
                   int-divshift-sl-high-of-bits
                   int-divshift-sl-mod-shift
                   int-divshift-sl-product-small
                   int-divshift-slc-check-sound
                   int-divshift-sl-spec
                   int-shl-checked-spec
                   int-valuep
                   int->lebits lebits->int mod take nthcdr repeat)))
