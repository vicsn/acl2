; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness of the variable-exponent field shift (fun-circuits/
; int-shift-pfcs.lisp) for every width other than 128.  Each select
; constraint is an equivalence with int-shift-after once the exponent bit
; is a bit and the running value is in range, so an induction over the
; exponent bits forces every select witness to be the canonical one.
; Field::to_lower_bits_le then forces the 2n result bits to be the bits of
; the final select, which is below 2^(2n) and hence below the prime.

(in-package "ALEOVM")

(include-book "int-shift-pfcs")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun int-divshift-expt-ind (k)
   (if (zp k) t (int-divshift-expt-ind (1- k)))))

(defruledl int-divshift-below-expt-plus
  (implies (and (natp cur)
                (natp a)
                (natp k)
                (< cur (expt 2 a)))
           (< cur (expt 2 (+ a k))))
  :hints (("Goal"
           :induct (int-divshift-expt-ind k)
           :in-theory (enable expt))))

(defruledl int-divshift-double-power
  (implies (natp i)
           (equal (+ (expt 2 i) (expt 2 i))
                  (expt 2 (+ 1 i))))
  :enable acl2::expt-of-+-of-1-arg2)

(defruledl int-divshift-below-wider-power
  (implies (and (natp cur)
                (natp width)
                (natp i)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< cur (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :use (:instance int-divshift-below-expt-plus
                  (a (+ width (expt 2 i)))
                  (k (expt 2 i)))
  :enable int-divshift-double-power
  :disable (int-divshift-below-expt-plus expt acl2::expt-of-+-of-1-arg2))

(defruledl int-divshift-after-bound
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
                            int-divshift-below-wider-power)
                           (acl2::*-of-expt-and-expt-same-base)))
          ("Subgoal 1"
           :use (:instance acl2::<-of-*-and-*-cancel
                           (x1 cur)
                           (x2 (expt 2 (+ width (expt 2 i))))
                           (y (expt 2 (expt 2 i))))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            acl2::*-of-expt-and-expt-same-base
                            int-divshift-double-power)
                           (acl2::<-of-*-and-*-cancel)))))

(defruledl int-divshift-cur-below-step
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (< cur (expt 2 n)))
           (< cur (expt 2 (+ n (expt 2 i)))))
  :do-not-induct t
  :use (:instance int-divshift-below-expt-plus
                  (a n)
                  (k (expt 2 i)))
  :disable (int-divshift-below-expt-plus expt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-atom-when-len-0
  (implies (equal (len x) 0)
           (not (consp x))))

(defruled int-divshift-var-chain-sound
  :short "The tail selects force the canonical witnesses."
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
                (<= (+ i (len ebits)) (1- (integer-length n)))
                (< (lookup-equal prev asg)
                   (expt 2 (+ n (expt 2 i))))
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
                            int-divshift-atom-when-len-0
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
           :use ((:instance int-divshift-after-bound
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

(defruled int-divshift-shl-chain-sound
  :short "The variable-mode left-shift selects force the canonical witnesses."
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
                (r1cs::r1cs-constraints-holdp
                 (int-shl-chain-gadget xs ebits nexts p)
                 asg p))
           (equal (lookup-equal-list nexts asg)
                  (int-shift-witness-values
                   (lebits=>nat (lookup-equal-list xs asg))
                   (lookup-equal-list ebits asg)
                   0)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :use ((:instance int-shift-lc-step-to-after
                            (bit (car ebits))
                            (next (car nexts))
                            (p (base-prime)))
                 (:instance int-divshift-var-chain-sound
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1)
                            (p (base-prime)))
                 (:instance int-divshift-cur-below-step
                            (cur (lebits=>nat (lookup-equal-list xs asg)))
                            (i 0))
                 (:instance int-divshift-after-bound
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
                            int-divshift-var-chain-sound
                            int-divshift-cur-below-step
                            int-divshift-after-bound
                            int-shift-cur-times-pow-below-prime
                            mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul)))))

(defruledl int-divshift-bits-from-nat
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable (int->lebits acl2::mod-when-<))

(defruled int-divshift-shift-lower-sound
  :short "@('Field::to_lower_bits_le') of a value below @('2^(2n)')
          forces the canonical bits."
  (implies (and (symbolp final)
                (symbol-listp zs)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (equal (len zs) (* 2 n))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg final)
                (r1cs::valuation-binds-allp asg zs)
                (natp v)
                (< v (expt 2 (* 2 n)))
                (equal (lookup-equal final asg) v)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget final zs p)
                 asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits v (* 2 n))))
  :do-not-induct t
  :use ((:instance int-shift-below-prime
                   (v (lebits=>nat (lookup-equal-list zs asg))))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list zs asg)))
        (:instance int-divshift-bits-from-nat
                   (bits (lookup-equal-list zs asg))
                   (n (* 2 n))))
  :in-theory (e/d (int-shift-lower-gadget
                   boolean-check-gadget-list-to-bit-listp
                   pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
                   r1cs::r1cs-constraints-holdp-of-append
                   len-of-lookup-equal-list
                   acl2::mod-when-<)
                  (boolean-check-gadget-list
                   pow2sum-gadget
                   int-shift-below-prime
                   mod
                   floor
                   lookup-equal)))

(defruledl int-divshift-shifted-below-double
  (implies (and (integer-widthp n)
                (natp v)
                (< v (expt 2 n))
                (natp s)
                (< s n))
           (< (* v (expt 2 s)) (expt 2 (* 2 n))))
  :do-not-induct t
  :use ((:instance acl2::<-of-*-and-*-cancel
                   (x1 v) (x2 (expt 2 n)) (y (expt 2 s)))
        (:instance acl2::expt-monotone-strong (r 2) (j (* 2 n)) (i (+ n s))))
  :enable (acl2::expt-of-+ posp-when-integer-widthp)
  :disable acl2::<-of-*-and-*-cancel)

(defruled int-divshift-shl-wrapped-gadget-sound
  :short "R1CS-SOUND of variable-mode @('shl_wrapped'), both
          signednesses, every integer width other than 128.  The value
          wires are @('Integer::new') bits of @('x'); the exponent select
          bits are the low @('log2(n)') bits of the exponent, i.e. the
          bits of @('e mod n')."
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
                (r1cs::r1cs-constraints-holdp
                 (int-shl-wrapped-gadget xs ebits nexts zs p)
                 asg p))
           (and (equal (lookup-equal-list zs asg)
                       (int->lebits (* (int-spec-unsigned x n)
                                       (expt 2 (mod e n)))
                                    (* 2 n)))
                (equal (lebits->int
                        (take n (lookup-equal-list zs asg))
                        signedp)
                       (int-shl-wrapped-spec x e signedp n))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-shl-chain-sound)
                 (:instance int-divshift-shift-lower-sound
                            (final (car (last nexts)))
                            (v (* (int-spec-unsigned x n)
                                  (expt 2 (mod e n)))))
                 (:instance int-shl-wrapped-gadget-complete)
                 (:instance int-divshift-shifted-below-double
                            (v (int-spec-unsigned x n))
                            (s (mod e n)))
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
                           (int-divshift-shl-chain-sound
                            int-divshift-shift-lower-sound
                            int-shl-wrapped-gadget-complete
                            int-divshift-shifted-below-double
                            int-shift-witness-last-is-run
                            int-shift-run-value
                            lebits=>nat-of-int->lebits
                            int->lebits
                            mod
                            floor
                            lookup-equal
                            lookup-equal-list-of-last
                            car-of-lookup-equal-list
                            take)))))
