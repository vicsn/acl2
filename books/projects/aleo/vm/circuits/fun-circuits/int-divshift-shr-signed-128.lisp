; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND of variable-mode signed shr_wrapped at width 128 (the path in
; circuit/types/integers/src/shr_wrapped.rs where 2n is not below the field
; data size).  The divisor D = 2^(e mod 128) comes from the square-and-
; multiply power chain and to_lower_bits_le(128).  Then:
;   abs_wrapped(x), unsigned_division_via_witness(|x|, D) -> (q, r),
;   (!q).add_wrapped(1), which is the constant-minus-variable subtraction
;     0 - q (the same linear combination sum 2^i (1 - q_i) + 1),
;   r.to_field().is_equal(0), whose two constraints are those of
;     is_not_equal with the result bit nz (is_equal is 1 - nz),
;   (-q).sub_wrapped(1), with a constant subtrahend,
;   ternary(1 - nz, -q, -q - 1), i.e. the ternary on !nz,
;   ternary(msb(x), rounded, q).
; As in int-is-zero-gadget, the zero operand of is_equal is a list of wires
; whose values are the bits of 0.

(in-package "ALEOVM")

(include-book "int-divshift-shr-unsigned-128")
(include-book "int-divshift-signed-div-128")
(include-book "int-divshift-sshr128-arith")
(include-book "int-equal")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))

(set-prover-step-limit 20000000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund int-divshift-shr-signed-128-gadget
  (xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl mch ls l ds d
      nqs nc zeros nz nw mqs mc rds res one p)
  (declare (xargs :verify-guards nil))
  (append (int-divshift-pow2-gadget rbits sqs ts p)
          (int-shift-lower-gadget (car (last ts)) ys p)
          (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
          (unsigned-medium-div-gadget axs ys qs rs ll hl lh hh
                                      ms mcl mch ls l ds d one p)
          (unsigned-small-sub-wrapped-const-var-gadget
           (int->lebits 0 128) qs nqs nc one p)
          (int-is-not-equal-gadget rs zeros nz nw one p)
          (int-divshift-sub-wrapped-var-const-gadget
           nqs (int->lebits 1 128) mqs mc p)
          (int-divshift-negsel-gadget nz nqs mqs rds one p)
          (integer-ternary-gadget (car (last xs)) rds qs res p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-ss128-qr
  (implies (and (natp a)
                (<= a (expt 2 127))
                (posp dv)
                (< dv (expt 2 128)))
           (and (natp (truncate a dv))
                (<= (truncate a dv) (expt 2 127))
                (natp (rem a dv))
                (int-valuep (rem a dv) nil 128)
                (int-valuep (- (truncate a dv)) t 128)))
  :do-not-induct t
  :use (:instance acl2::floor-bound-hack)
  :enable (int-valuep int-min int-max
           acl2::truncate-becomes-floor acl2::rem-becomes-mod)
  :disable (floor mod truncate rem)
  :prep-lemmas
  ((defruled acl2::floor-bound-hack
     (implies (and (natp a) (posp dv))
              (and (<= 0 (floor a dv))
                   (<= (floor a dv) a)
                   (<= 0 (mod a dv))
                   (< (mod a dv) dv)))
     :use (:instance acl2::floor-upper-bound-copy (x a) (y dv))
     :prep-lemmas
     ((defruled acl2::floor-upper-bound-copy
        (implies (and (natp x) (posp y))
                 (<= (floor x y) x))
        :use (:instance acl2::my-floor-upper-bound (i x) (j y))
        :nonlinearp t)))))

(defruled int-divshift-ss128-values
  (implies (and (int-valuep x t 128)
                (natp e))
           (b* ((a (abs x))
                (dv (expt 2 (mod e 128)))
                (q (truncate a dv))
                (r (rem a dv)))
             (and (integerp x)
                  (natp a)
                  (<= a (expt 2 127))
                  (int-valuep a nil 128)
                  (posp dv)
                  (< dv (expt 2 128))
                  (int-valuep dv nil 128)
                  (natp q)
                  (<= q (expt 2 127))
                  (natp r)
                  (int-valuep r nil 128)
                  (int-valuep (- q) t 128)
                  (int-valuep 1 t 128)
                  (int-valuep 0 nil 128))))
  :do-not-induct t
  :use ((:instance acl2::<-of-expt-and-expt-same-base
                   (r 2) (i (mod e 128)) (j 128))
        (:instance int-divshift-ss128-qr
                   (a (abs x)) (dv (expt 2 (mod e 128))))
        (:instance abs-facts))
  :enable (int-valuep int-min int-max)
  :disable (acl2::<-of-expt-and-expt-same-base int-divshift-ss128-qr
            abs floor mod truncate rem)
  :prep-lemmas
  ((defruled abs-facts
     (implies (int-valuep x t 128)
              (and (natp (abs x))
                   (<= (abs x) (expt 2 127))))
     :enable (int-valuep int-min int-max))))

(defruled int-divshift-ss128-floor-range
  (implies (and (int-valuep x t 128)
                (posp dv))
           (int-valuep (floor x dv) t 128))
  :do-not-induct t
  :cases ((< x 0))
  :use ((:instance acl2::floor-neg-bound-hack)
        (:instance acl2::floor-pos-bound-hack))
  :in-theory (e/d (int-valuep int-min int-max)
                  (floor acl2::<=-of-floor-same-when-negative-integer-2
                   acl2::<=-of-floor-same-when-negative-integer))
  :prep-lemmas
  ((defruled acl2::floor-pos-bound-hack
     (implies (and (integerp x) (<= 0 x) (posp dv))
              (and (<= 0 (floor x dv))
                   (<= (floor x dv) x)))
     :use (:instance acl2::my-floor-upper-bound (i x) (j dv))
     :nonlinearp t)
   (defruled acl2::floor-neg-bound-hack
     (implies (and (integerp x) (< x 0) (posp dv))
              (and (<= x (floor x dv))
                   (< (floor x dv) 0)))
     :use ((:instance acl2::my-floor-lower-bound (i x) (j dv))
           (:instance acl2::my-floor-upper-bound (i x) (j dv)))
     :nonlinearp t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-ss128-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (int-valuep x t 128)
        (natp e)
        (symbol-listp xs) (symbol-listp rbits) (symbol-listp sqs)
        (symbol-listp ts) (symbol-listp ys)
        (symbol-listp axs) (symbol-listp mxs) (symbolp cx)
        (symbol-listp qs) (symbol-listp rs)
        (symbolp ll) (symbolp hl) (symbolp lh) (symbolp hh)
        (symbol-listp ms) (symbol-listp mcl) (symbol-listp mch)
        (symbol-listp ls) (symbolp l) (symbol-listp ds) (symbolp d)
        (symbol-listp nqs) (symbolp nc)
        (symbol-listp zeros) (symbolp nz) (symbolp nw)
        (symbol-listp mqs) (symbolp mc)
        (symbol-listp rds) (symbol-listp res)
        (symbolp one)
        (equal (len xs) 128) (equal (len rbits) 7)
        (equal (len sqs) 6) (equal (len ts) 6) (equal (len ys) 128)
        (equal (len axs) 128) (equal (len mxs) 128)
        (equal (len qs) 128) (equal (len rs) 128) (equal (len ms) 128)
        (equal (len mcl) 65) (equal (len mch) 128) (equal (len ls) 128)
        (equal (len ds) 128)
        (equal (len nqs) 128) (equal (len zeros) 128)
        (equal (len mqs) 128) (equal (len rds) 128) (equal (len res) 128)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rbits)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg ts)
        (r1cs::valuation-bindsp asg (car (last ts)))
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg axs)
        (r1cs::valuation-binds-allp asg mxs)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg qs)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg ll) (r1cs::valuation-bindsp asg hl)
        (r1cs::valuation-bindsp asg lh) (r1cs::valuation-bindsp asg hh)
        (r1cs::valuation-binds-allp asg ms)
        (r1cs::valuation-binds-allp asg mcl)
        (r1cs::valuation-binds-allp asg mch)
        (r1cs::valuation-binds-allp asg ls)
        (r1cs::valuation-bindsp asg l)
        (r1cs::valuation-binds-allp asg ds)
        (r1cs::valuation-bindsp asg d)
        (r1cs::valuation-binds-allp asg nqs)
        (r1cs::valuation-bindsp asg nc)
        (r1cs::valuation-binds-allp asg zeros)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-bindsp asg nw)
        (r1cs::valuation-binds-allp asg mqs)
        (r1cs::valuation-bindsp asg mc)
        (r1cs::valuation-binds-allp asg rds)
        (r1cs::valuation-binds-allp asg res)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))
        (equal (lookup-equal-list rbits asg)
               (rev (int->lebits (mod e 128) 7)))
        (equal (lookup-equal-list zeros asg) (int->lebits 0 128))))

(defmacro int-divshift-ss128-sound-hyps ()
  '(and (int-divshift-ss128-common-hyps)
        (r1cs::r1cs-constraints-holdp
         (int-divshift-shr-signed-128-gadget
          xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl mch ls l ds d
          nqs nc zeros nz nw mqs mc rds res one p)
         asg p)))

(defrulel int-divshift-ss128-holds
  (implies (int-divshift-ss128-sound-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last ts)) ys p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-medium-div-gadget axs ys qs rs ll hl lh hh
                                             ms mcl mch ls l ds d one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 128) qs nqs nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-is-not-equal-gadget rs zeros nz nw one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sub-wrapped-var-const-gadget
                  nqs (int->lebits 1 128) mqs mc p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-negsel-gadget nz nqs mqs rds one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (integer-ternary-gadget (car (last xs)) rds qs res p)
                 asg p)))
  :rule-classes nil
  :in-theory (union-theories '(int-divshift-shr-signed-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defrulel int-divshift-ss128-step-divisor
  (implies (int-divshift-ss128-sound-hyps)
           (and (equal (lookup-equal-list ys asg)
                       (int->lebits (expt 2 (mod e 128)) 128))
                (equal (lookup-equal-list axs asg)
                       (int->lebits (abs x) 128))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-holds)
        (:instance int-divshift-pow2-lower-128-sound)
        (:instance int-divshift-sd128-abs-bits (n 128)))
  :in-theory (union-theories '((:e integer-widthp))
                             (theory 'minimal-theory)))

(defrulel int-divshift-ss128-step-div
  (implies (int-divshift-ss128-sound-hyps)
           (b* ((a (abs x))
                (dv (expt 2 (mod e 128))))
             (and (equal (lookup-equal-list qs asg)
                         (int->lebits (truncate a dv) 128))
                  (equal (lookup-equal-list rs asg)
                         (int->lebits (rem a dv) 128)))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-holds)
        (:instance int-divshift-ss128-step-divisor)
        (:instance int-divshift-ss128-values)
        (:instance int-divshift-sd128-udiv
                   (ays ys) (a (abs x)) (b (expt 2 (mod e 128)))))
  :in-theory (theory 'minimal-theory))

(defrulel int-divshift-ss128-step-neg
  (implies (int-divshift-ss128-sound-hyps)
           (b* ((q (truncate (abs x) (expt 2 (mod e 128))))
                (r (rem (abs x) (expt 2 (mod e 128)))))
             (and (equal (lookup-equal-list nqs asg) (int->lebits (- q) 128))
                  (equal (lookup-equal nz asg) (if (equal r 0) 0 1)))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-holds)
        (:instance int-divshift-ss128-step-div)
        (:instance int-divshift-ss128-values)
        (:instance int-divshift-sd128-neg
                   (vs qs) (nvs nqs) (n 128)
                   (v (truncate (abs x) (expt 2 (mod e 128)))))
        (:instance int-is-not-equal-gadget-sound
                   (xs rs) (ys zeros) (z nz) (w nw) (n 128) (signedp nil)
                   (x (rem (abs x) (expt 2 (mod e 128)))) (y 0)))
  :in-theory (union-theories '((:e integer-widthp) (:e expt) (:e int->lebits)
                               int-is-not-equal-spec int-spec-bool)
                             (theory 'minimal-theory)))

(defrulel int-divshift-ss128-step-round
  (implies (int-divshift-ss128-sound-hyps)
           (b* ((q (truncate (abs x) (expt 2 (mod e 128))))
                (r (rem (abs x) (expt 2 (mod e 128)))))
             (equal (lookup-equal-list rds asg)
                    (int->lebits (if (equal r 0) (- q) (+ -1 (- q))) 128))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-holds)
        (:instance int-divshift-ss128-step-neg)
        (:instance int-divshift-ss128-values)
        (:instance int-divshift-sub-wrapped-var-const-sound
                   (xs nqs) (zs mqs) (z mc) (n 128) (signedp t)
                   (x (- (truncate (abs x) (expt 2 (mod e 128))))) (y 1))
        (:instance int-divshift-negsel-gadget-sound
                   (c nz) (xs nqs) (ys mqs) (zs rds) (n 128)
                   (x (- (truncate (abs x) (expt 2 (mod e 128)))))
                   (y (int-sub-wrapped-spec
                       (- (truncate (abs x) (expt 2 (mod e 128)))) 1 t 128)))
        (:instance int->lebits-of-int-wrap
                   (x (+ -1 (- (truncate (abs x) (expt 2 (mod e 128))))))
                   (signedp t) (n 128)))
  :in-theory (e/d (int-sub-wrapped-spec bitp)
                  (int-divshift-sub-wrapped-var-const-sound
                   int-divshift-negsel-gadget-sound
                   int->lebits-of-int-wrap
                   int-divshift-ss128-values
                   int->lebits int-wrap truncate rem abs lookup-equal
                   lookup-equal-list)))

(defruled int-divshift-shr-signed-128-gadget-sound
  :short "R1CS-SOUND of variable-mode signed @('shr_wrapped') at width
          128: the result bits decode to @('floor(x, 2^(e mod 128))')."
  (implies (int-divshift-ss128-sound-hyps)
           (and (equal (lookup-equal-list res asg)
                       (int->lebits (int-shr-wrapped-spec x e t 128) 128))
                (equal (lebits->int (lookup-equal-list res asg) t)
                       (int-shr-wrapped-spec x e t 128))))
  :do-not-induct t
  :use ((:instance int-divshift-ss128-holds)
        (:instance int-divshift-ss128-step-div)
        (:instance int-divshift-ss128-step-round)
        (:instance int-divshift-ss128-values)
        (:instance int-divshift-sd128-msb-lookup (n 128))
        (:instance int-divshift-sd128-msb-binds (n 128))
        (:instance integer-ternary-gadget-correctness
                   (x (car (last xs))) (ys rds) (zs qs) (ws res))
        (:instance int-divshift-sshr128-floor-cases
                   (d (expt 2 (mod e 128))))
        (:instance int-divshift-ss128-floor-range
                   (dv (expt 2 (mod e 128))))
        (:instance lebits->int-of-int->lebits
                   (x (floor x (expt 2 (mod e 128)))) (signedp t) (n 128)))
  :in-theory (e/d (int-shr-wrapped-spec acl2::ifix-when-integerp)
                  (int-divshift-sd128-msb-lookup
                   int-divshift-sd128-msb-binds
                   integer-ternary-gadget-correctness
                   int-divshift-sshr128-floor-cases
                   int-divshift-ss128-floor-range
                   int-divshift-ss128-values
                   lebits->int-of-int->lebits
                   int->lebits lebits->int floor truncate rem abs mod
                   lookup-equal lookup-equal-list)))
