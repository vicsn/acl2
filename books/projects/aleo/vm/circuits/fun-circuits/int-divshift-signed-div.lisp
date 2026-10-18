; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed DivWrapped::div_wrapped and RemWrapped::rem_wrapped, variable
; operands, widths 8, 16, 32, 64 (snarkVM circuit/types/integers/src/
; div_wrapped.rs and rem_wrapped.rs):
;
;   a = x.abs_wrapped(), b = y.abs_wrapped()       (as unsigned)
;   q, r = unsigned_division_via_witness(a, b)
;   div: same = !(msb x ^ msb y); ternary(same, q, 0.sub_wrapped(q))
;   rem: ternary(!msb x, r, 0.sub_wrapped(r))
;
; Boolean NOT is free (the linear combination 1 - c), so the select is
; the per-bit Boolean ternary constraint (1 - c) * (a - b) = out - b,
; which is integer-ternary-not-gadget with the unit on the one wire.

(in-package "ALEOVM")

(include-book "int-divshift-signed-arith")
(include-book "int-divshift-unsigned-div")
(include-book "int-divshift-sub-wrapped-const")
(include-book "int-abs")
(include-book "../r1cs/integer-ternary")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Negated select.

(define int-divshift-negsel-gadget ((c symbolp)
                                    (xs symbol-listp)
                                    (ys symbol-listp)
                                    (zs symbol-listp)
                                    (one symbolp)
                                    (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Bits of @('if c then y else x'), i.e. the ternary on @('!c')."
  (integer-ternary-not-gadget c xs ys zs one p))

(defruled int-divshift-negsel-gadget-sound
  (implies (and (primep p)
                (symbolp c) (symbolp one)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg one)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal c asg))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-negsel-gadget c xs ys zs one p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (if (equal (lookup-equal c asg) 0) x y) n)))
  :use (:instance integer-ternary-not-gadget-correctness
                  (x c) (ys xs) (zs ys) (ws zs))
  :enable int-divshift-negsel-gadget)

(defruled int-divshift-negsel-gadget-complete
  (implies (and (primep p)
                (symbolp c) (symbolp one)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (equal n (len xs))
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg one)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal c asg))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (if (equal (lookup-equal c asg) 0) x y)
                                    n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-negsel-gadget c xs ys zs one p) asg p))
  :use (:instance integer-ternary-not-gadget-correctness
                  (x c) (ys xs) (zs ys) (ws zs))
  :enable int-divshift-negsel-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers.

(defruledl int-divshift-sd-bits-from-mod
  (implies (and (natp n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable int->lebits)

(defruledl int-divshift-sd-mod-lebits=>int
  (implies (and (bit-listp bits) (equal (len bits) n))
           (equal (mod (lebits=>int bits) (expt 2 n))
                  (lebits=>nat bits)))
  :use (:instance acl2::lebits=>nat-upper-bound (digits bits))
  :enable lebits=>int)

(defruledl int-divshift-sd-abs-valuep
  (implies (and (posp n) (int-valuep x t n))
           (and (natp (abs x))
                (<= (abs x) (expt 2 (1- n)))
                (< (abs x) (expt 2 n))
                (int-valuep (abs x) nil n)
                (equal (mod (abs x) (expt 2 n)) (abs x))))
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruledl int-divshift-sd-valuep-below
  (implies (and (posp n) (natp v) (<= v (expt 2 (1- n))))
           (and (int-valuep v nil n)
                (equal (mod v (expt 2 n)) v)))
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruledl int-divshift-sd-integerp
  (implies (int-valuep x signedp n)
           (integerp x))
  :enable int-valuep)

(defruledl int-divshift-sd-msb-bitp
  (implies (and (posp n) (int-valuep x t n))
           (bitp (car (last (int->lebits x n)))))
  :use int-signed-msb)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Abs step: the absolute value bits are exactly int->lebits of |x|.

(defruled int-divshift-sd-abs-bits
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp axs) (symbol-listp mxs)
                (symbolp cx) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len axs) n)
                (equal (len mxs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg axs)
                (r1cs::valuation-binds-allp asg mxs)
                (r1cs::valuation-bindsp asg cx)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
                 asg p))
           (equal (lookup-equal-list axs asg) (int->lebits (abs x) n)))
  :do-not-induct t
  :use ((:instance signed-small-abs-wrapped-gadget-soundness
                   (ys axs) (minus-xs mxs) (carry cx))
        (:instance lebits->int-is-lebits=>int (bits (int->lebits x n)))
        (:instance lebits->int-of-int->lebits (signedp t))
        (:instance int-divshift-sd-mod-lebits=>int
                   (bits (lookup-equal-list axs asg)))
        (:instance int-divshift-sd-abs-valuep)
        (:instance int-divshift-sd-integerp (signedp t))
        (:instance int-width-add-fits)
        (:instance int-divshift-sd-bits-from-mod
                   (bits (lookup-equal-list axs asg))
                   (v (abs x))))
  :enable (int-abs-wrapped-signed-gadget
           integer-length-of-base-prime
           posp-when-integer-widthp
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits)
  :disable (abs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Unsigned division step.

(defruled int-divshift-sd-udiv
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp axs) (symbol-listp ays)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp one)
                (equal n (len axs))
                (integer-widthp n)
                (not (equal n 128))
                (equal (len ays) n)
                (equal (len qs) n)
                (equal (len rs) n)
                (equal (len ds) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg axs)
                (r1cs::valuation-binds-allp asg ays)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep a nil n)
                (int-valuep b nil n)
                (equal (lookup-equal-list axs asg) (int->lebits a n))
                (equal (lookup-equal-list ays asg) (int->lebits b n))
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-div-gadget axs ays qs rs m ds d one p)
                 asg p))
           (and (not (equal b 0))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate a b) n))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem a b) n))))
  :do-not-induct t
  :use ((:instance unsigned-small-div-gadget-euclidian
                   (xs axs) (ys ays) (u one))
        (:instance int-unsigned-division-small-sound
                   (xs axs) (ys ays) (u one) (x a) (y b) (signedp nil))
        (:instance int-divshift-sd-bits-from-mod
                   (bits (lookup-equal-list qs asg))
                   (v (truncate a b)))
        (:instance int-divshift-sd-bits-from-mod
                   (bits (lookup-equal-list rs asg))
                   (v (rem a b)))
        (:instance lebits=>nat-of-int->lebits (x b))
        (:instance int-width-div-fits))
  :enable (int-unsigned-division-via-witness-gadget
           int-div-wrapped-spec
           int-rem-wrapped-spec
           int-wrap
           int-valuep
           integer-length-of-base-prime
           posp-when-integer-widthp
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits)
  :disable (truncate rem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Negation step: 0.sub_wrapped(v) for 0 <= v <= 2^(n-1).

(defruled int-divshift-sd-neg
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp vs) (symbol-listp nvs)
                (symbolp nc) (symbolp one)
                (integer-widthp n)
                (equal (len vs) n)
                (equal (len nvs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg vs)
                (r1cs::valuation-binds-allp asg nvs)
                (r1cs::valuation-bindsp asg nc)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (natp v)
                (<= v (expt 2 (1- n)))
                (equal (lookup-equal-list vs asg) (int->lebits v n))
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 n) vs nvs nc one p)
                 asg p))
           (equal (lookup-equal-list nvs asg) (int->lebits (- v) n)))
  :do-not-induct t
  :use ((:instance int-divshift-sub-wrapped-const-var-sound
                   (x 0) (y v) (ys vs) (zs nvs) (z nc) (signedp nil))
        (:instance int-divshift-sd-valuep-below)
        (:instance int-divshift-sd-valuep-below (v 0)))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           posp-when-integer-widthp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Signed div_wrapped.

(defund int-divshift-signed-div-wrapped-gadget
  (xs ys axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
          (int-abs-wrapped-signed-gadget ys ays mys cy one p)
          (unsigned-small-div-gadget axs ays qs rs m ds d one p)
          (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
          (unsigned-small-sub-wrapped-const-var-gadget
           (int->lebits 0 (len xs)) qs nqs nc one p)
          (int-divshift-negsel-gadget s qs nqs zs one p)))

(defmacro int-divshift-sd-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
                (primep p)
        (symbol-listp xs) (symbol-listp ys)
        (symbol-listp axs) (symbol-listp mxs) (symbolp cx)
        (symbol-listp ays) (symbol-listp mys) (symbolp cy)
        (symbol-listp qs) (symbol-listp rs) (symbolp m)
        (symbol-listp ds) (symbolp d) (symbolp nc)
        (symbol-listp zs) (symbolp one)
        (equal n (len xs))
        (integer-widthp n)
        (not (equal n 128))
        (equal (len ys) n)
        (equal (len axs) n) (equal (len mxs) n)
        (equal (len ays) n) (equal (len mys) n)
        (equal (len qs) n) (equal (len rs) n) (equal (len ds) n)
        (equal (len zs) n)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg axs)
        (r1cs::valuation-binds-allp asg mxs)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ays)
        (r1cs::valuation-binds-allp asg mys)
        (r1cs::valuation-bindsp asg cy)
        (r1cs::valuation-binds-allp asg qs)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg m)
        (r1cs::valuation-binds-allp asg ds)
        (r1cs::valuation-bindsp asg d)
        (r1cs::valuation-bindsp asg nc)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (int-valuep x t n)
        (int-valuep y t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ys asg) (int->lebits y n))))

(defrulel int-divshift-sd-div-final
  (implies (and (posp n)
                (integerp x) (integerp y) (not (equal y 0))
                (equal sv (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (equal zv (if (equal sv 0)
                              (int->lebits (truncate (abs x) (abs y)) n)
                            (int->lebits (- (truncate (abs x) (abs y))) n))))
           (equal zv (int->lebits (int-div-wrapped-spec x y t n) n)))
  :rule-classes nil
  :use int-divshift-truncate-via-abs
  :enable (int-div-wrapped-spec int->lebits-of-int-wrap bitxor)
  :disable (truncate abs))

(defmacro int-divshift-sd-div-hyps ()
  '(and (int-divshift-sd-common-hyps)
        (symbolp s) (symbol-listp nqs)
        (equal (len nqs) n)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg nqs)
        (r1cs::r1cs-constraints-holdp
         (int-divshift-signed-div-wrapped-gadget
          xs ys axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
         asg p)))

(defruledl int-divshift-sd-consp-when-len
  (implies (posp (len xs)) (consp xs)))

(defruledl int-divshift-sd-natp-when-integer-widthp
  (implies (integer-widthp n) (posp n))
  :enable integer-widthp)

(defruledl int-divshift-sd-div-step-ax
  (implies (int-divshift-sd-div-hyps)
           (equal (lookup-equal-list axs asg) (int->lebits (abs x) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-divshift-sd-abs-bits)
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-div-step-ay
  (implies (int-divshift-sd-div-hyps)
           (equal (lookup-equal-list ays asg) (int->lebits (abs y) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-divshift-sd-abs-bits
                           (xs ys) (axs ays) (mxs mys) (cx cy) (x y))
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-abs-nonzero
  (implies (equal (abs y) 0) (equal (ifix y) 0)))

(defruledl int-divshift-sd-div-step-q
  (implies (int-divshift-sd-div-hyps)
           (and (not (equal y 0))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate (abs x) (abs y)) n))))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-div-step-ax
                 int-divshift-sd-div-step-ay
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-abs-valuep)
                 (:instance int-divshift-sd-abs-valuep (x y))
                 (:instance int-divshift-sd-abs-nonzero)
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-sd-udiv (a (abs x)) (b (abs y))))
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         ifix (:e abs))
                       (theory 'minimal-theory)))))

(defruled lookup-equal-of-car-of-last-is-car-of-last-of-lookup
  (implies (consp xs)
           (equal (lookup-equal (car (last xs)) asg)
                  (car (last (lookup-equal-list xs asg)))))
  :induct (len xs)
  :enable (lookup-equal-list last))

(defruled int-divshift-sd-xor
  (implies (and (primep p)
                (posp n)
                (symbol-listp xs) (symbol-listp ys) (symbolp s)
                (equal (len xs) n) (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg s)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
                 asg p))
           (equal (lookup-equal s asg)
                  (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0))))
  :do-not-induct t
  :use ((:instance int-signed-msb)
        (:instance int-signed-msb (x y))
        (:instance int-divshift-sd-consp-when-len)
        (:instance int-divshift-sd-consp-when-len (xs ys))
        (:instance member-equal-of-car-of-last)
        (:instance member-equal-of-car-of-last (xs ys))
        (:instance lookup-equal-of-car-of-last-is-car-of-last-of-lookup)
        (:instance lookup-equal-of-car-of-last-is-car-of-last-of-lookup
                   (xs ys))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs))) (y (car (last ys))) (z s)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp)
  :disable (boolean-xor-gadget))

(defruledl int-divshift-sd-div-step-s
  (implies (int-divshift-sd-div-hyps)
           (equal (lookup-equal s asg)
                  (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-xor))
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-div-step-nq
  (implies (int-divshift-sd-div-hyps)
           (equal (lookup-equal-list nqs asg)
                  (int->lebits (- (truncate (abs x) (abs y))) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-div-step-q
                 (:instance int-divshift-sd-abs-valuep)
                 (:instance int-divshift-sd-abs-valuep (x y))
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-abs-nonzero)
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-truncate-abs-bounds
                            (a (abs x)) (b (abs y)))
                 (:instance int-divshift-sd-neg
                            (vs qs) (nvs nqs)
                            (v (truncate (abs x) (abs y)))))
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         ifix natp posp (:e abs))
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-div-step-z
  (implies (int-divshift-sd-div-hyps)
           (equal (lookup-equal-list zs asg)
                  (int->lebits (if (equal (lookup-equal s asg) 0)
                                   (truncate (abs x) (abs y))
                                 (- (truncate (abs x) (abs y))))
                               n)))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-div-step-q
                 int-divshift-sd-div-step-s
                 int-divshift-sd-div-step-nq
                 (:instance int-divshift-negsel-gadget-sound
                            (c s) (xs qs) (ys nqs)
                            (x (truncate (abs x) (abs y)))
                            (y (- (truncate (abs x) (abs y))))))
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         bitxor (:e bitp) (:e bitxor))
                       (theory 'minimal-theory)))))

(defruled int-divshift-signed-div-wrapped-gadget-sound
  :short "Signed div_wrapped, widths 8-64: given Integer::new operands,
          the constraints force the output bits to the spec and rule out
          a zero divisor."
  (implies (int-divshift-sd-div-hyps)
           (and (not (equal y 0))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-wrapped-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-div-step-q
                 int-divshift-sd-div-step-s
                 int-divshift-sd-div-step-z
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-integerp (signedp t))
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-sd-div-final
                            (sv (lookup-equal s asg))
                            (zv (lookup-equal-list zs asg))))
           :in-theory (theory 'minimal-theory))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Signed rem_wrapped.

(defund int-divshift-signed-rem-wrapped-gadget
  (xs ys axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
  (declare (xargs :verify-guards nil))
  (append (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
          (int-abs-wrapped-signed-gadget ys ays mys cy one p)
          (unsigned-small-div-gadget axs ays qs rs m ds d one p)
          (unsigned-small-sub-wrapped-const-var-gadget
           (int->lebits 0 (len xs)) rs nrs nc one p)
          (int-divshift-negsel-gadget (car (last xs)) rs nrs zs one p)))

(defmacro int-divshift-sd-rem-hyps ()
  '(and (int-divshift-sd-common-hyps)
        (symbol-listp nrs)
        (equal (len nrs) n)
        (r1cs::valuation-binds-allp asg nrs)
        (r1cs::r1cs-constraints-holdp
         (int-divshift-signed-rem-wrapped-gadget
          xs ys axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
         asg p)))

(defruledl int-divshift-sd-rem-step-ax
  (implies (int-divshift-sd-rem-hyps)
           (equal (lookup-equal-list axs asg) (int->lebits (abs x) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-divshift-sd-abs-bits)
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-rem-step-ay
  (implies (int-divshift-sd-rem-hyps)
           (equal (lookup-equal-list ays asg) (int->lebits (abs y) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-divshift-sd-abs-bits
                           (xs ys) (axs ays) (mxs mys) (cx cy) (x y))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-rem-step-r
  (implies (int-divshift-sd-rem-hyps)
           (and (not (equal y 0))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem (abs x) (abs y)) n))))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-rem-step-ax
                 int-divshift-sd-rem-step-ay
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-abs-valuep)
                 (:instance int-divshift-sd-abs-valuep (x y))
                 (:instance int-divshift-sd-abs-nonzero)
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-sd-udiv (a (abs x)) (b (abs y))))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         ifix (:e abs))
                       (theory 'minimal-theory)))))

(defruledl int-divshift-sd-rem-step-nr
  (implies (int-divshift-sd-rem-hyps)
           (equal (lookup-equal-list nrs asg)
                  (int->lebits (- (rem (abs x) (abs y))) n)))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-rem-step-r
                 (:instance int-divshift-sd-abs-valuep)
                 (:instance int-divshift-sd-abs-valuep (x y))
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-abs-nonzero)
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-rem-abs-bounds
                            (a (abs x)) (b (abs y)))
                 (:instance int-divshift-sd-neg
                            (vs rs) (nvs nrs)
                            (v (rem (abs x) (abs y)))))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         ifix natp posp (:e abs))
                       (theory 'minimal-theory)))))

(defruled int-divshift-sd-msb-lookup
  (implies (and (posp n)
                (equal (len xs) n)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n)))
           (equal (lookup-equal (car (last xs)) asg)
                  (if (< x 0) 1 0)))
  :do-not-induct t
  :use ((:instance int-signed-msb)
        (:instance int-divshift-sd-consp-when-len)
        (:instance lookup-equal-of-car-of-last-is-car-of-last-of-lookup)))

(defruled int-divshift-sd-msb-binds
  (implies (and (posp n)
                (equal (len xs) n)
                (symbol-listp xs)
                (r1cs::valuation-binds-allp asg xs))
           (and (symbolp (car (last xs)))
                (r1cs::valuation-bindsp asg (car (last xs)))))
  :do-not-induct t
  :use ((:instance int-divshift-sd-consp-when-len)
        (:instance member-equal-of-car-of-last)
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg) (vars xs) (var (car (last xs)))))
  :enable (symbolp-of-car-of-last true-listp-when-symbol-listp))

(defruledl int-divshift-sd-rem-step-z
  (implies (int-divshift-sd-rem-hyps)
           (equal (lookup-equal-list zs asg)
                  (int->lebits (if (< x 0)
                                   (- (rem (abs x) (abs y)))
                                 (rem (abs x) (abs y)))
                               n)))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-rem-step-r
                 int-divshift-sd-rem-step-nr
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-sd-msb-lookup)
                 (:instance int-divshift-sd-msb-binds)
                 (:instance int-divshift-negsel-gadget-sound
                            (c (car (last xs))) (xs rs) (ys nrs)
                            (x (rem (abs x) (abs y)))
                            (y (- (rem (abs x) (abs y))))))
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         (:e bitp) posp)
                       (theory 'minimal-theory)))))

(defrulel int-divshift-sd-rem-final
  (implies (and (integerp x) (integerp y) (not (equal y 0))
                (equal zv (int->lebits (if (< x 0)
                                           (- (rem (abs x) (abs y)))
                                         (rem (abs x) (abs y)))
                                       n)))
           (equal zv (int->lebits (int-rem-wrapped-spec x y t n) n)))
  :rule-classes nil
  :use int-divshift-rem-via-abs
  :enable int-rem-wrapped-spec
  :disable (rem abs))

(defruled int-divshift-signed-rem-wrapped-gadget-sound
  :short "Signed rem_wrapped, widths 8-64: given Integer::new operands,
          the constraints force the output bits to the spec and rule out
          a zero divisor."
  (implies (int-divshift-sd-rem-hyps)
           (and (not (equal y 0))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-wrapped-spec x y t n) n))))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-rem-step-r
                 int-divshift-sd-rem-step-z
                 (:instance int-divshift-sd-integerp (signedp t))
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-sd-rem-final
                            (zv (lookup-equal-list zs asg))))
           :in-theory (theory 'minimal-theory))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Completeness: the snarkVM witnesses satisfy both gadgets.

(defruledl int-divshift-sd-abs-wrapped-bits
  (implies (and (posp n) (integerp x))
           (equal (int->lebits (int-abs-wrapped-spec x t n) n)
                  (int->lebits (abs x) n)))
  :enable (int-abs-wrapped-spec int->lebits-of-int-wrap)
  :disable abs)

(defruled int-divshift-sd-abs-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp axs) (symbol-listp mxs)
                (symbolp cx) (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len axs) n)
                (equal (len mxs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg axs)
                (r1cs::valuation-binds-allp asg mxs)
                (r1cs::valuation-bindsp asg cx)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list axs asg) (int->lebits (abs x) n))
                (equal (lookup-equal-list mxs asg) (int->lebits (- x) n))
                (equal (lookup-equal cx asg) (int-sub-carry 0 x n)))
           (r1cs::r1cs-constraints-holdp
            (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-abs-wrapped-signed-gadget-complete
                   (ys axs) (minus-xs mxs) (carry cx))
        (:instance int-divshift-sd-abs-wrapped-bits)
        (:instance int-divshift-sd-integerp (signedp t))
        (:instance int-divshift-sd-natp-when-integer-widthp)
        (:instance int-divshift-sd-consp-when-len))
  :disable ((:e primep) abs int-abs-wrapped-signed-gadget))

(defruled int-divshift-sd-neg-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp vs) (symbol-listp nvs)
                (symbolp nc) (symbolp one)
                (integer-widthp n)
                (equal (len vs) n)
                (equal (len nvs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg vs)
                (r1cs::valuation-binds-allp asg nvs)
                (r1cs::valuation-bindsp asg nc)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (natp v)
                (<= v (expt 2 (1- n)))
                (equal (lookup-equal-list vs asg) (int->lebits v n))
                (equal (lookup-equal-list nvs asg) (int->lebits (- v) n))
                (equal (lookup-equal nc asg) (if (< 0 v) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits 0 n) vs nvs nc one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-sub-wrapped-const-var-complete
                   (x 0) (y v) (ys vs) (zs nvs) (z nc) (signedp nil))
        (:instance int-divshift-sd-valuep-below)
        (:instance int-divshift-sd-valuep-below (v 0))
        (:instance int-divshift-sd-natp-when-integer-widthp))
  :enable (int-sub-wrapped-spec int->lebits-of-int-wrap)
  :disable ((:e primep)))

(defruled int-divshift-sd-xor-complete
  (implies (and (primep p)
                (posp n)
                (symbol-listp xs) (symbol-listp ys) (symbolp s)
                (equal (len xs) n) (equal (len ys) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg s)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal s asg)
                       (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0))))
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-sd-msb-lookup)
        (:instance int-divshift-sd-msb-lookup (xs ys) (x y))
        (:instance int-divshift-sd-msb-binds)
        (:instance int-divshift-sd-msb-binds (xs ys))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs))) (y (car (last ys))) (z s)))
  :disable (boolean-xor-gadget))

(defruled int-divshift-sd-div-sel-complete
  (implies (and (primep p)
                (posp n)
                (symbolp s) (symbolp one)
                (symbol-listp qs) (symbol-listp nqs) (symbol-listp zs)
                (equal (len qs) n) (equal (len nqs) n) (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-bindsp asg one)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg nqs)
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal one asg) 1)
                (integerp x) (integerp y) (not (equal y 0))
                (equal (lookup-equal s asg)
                       (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate (abs x) (abs y)) n))
                (equal (lookup-equal-list nqs asg)
                       (int->lebits (- (truncate (abs x) (abs y))) n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-div-wrapped-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-negsel-gadget s qs nqs zs one p) asg p))
  :do-not-induct t
  :use ((:instance int-divshift-negsel-gadget-complete
                   (c s) (xs qs) (ys nqs)
                   (x (truncate (abs x) (abs y)))
                   (y (- (truncate (abs x) (abs y)))))
        (:instance int-divshift-sd-div-final
                   (sv (lookup-equal s asg))
                   (zv (if (equal (lookup-equal s asg) 0)
                           (int->lebits (truncate (abs x) (abs y)) n)
                         (int->lebits (- (truncate (abs x) (abs y))) n)))))
  :enable bitxor
  :disable (truncate abs int-div-wrapped-spec))

(defruled int-divshift-sd-rem-sel-complete
  (implies (and (primep p)
                (posp n)
                (symbolp one)
                (symbol-listp xs)
                (symbol-listp rs) (symbol-listp nrs) (symbol-listp zs)
                (equal (len xs) n)
                (equal (len rs) n) (equal (len nrs) n) (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg one)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg nrs)
                (r1cs::valuation-binds-allp asg zs)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (integerp y) (not (equal y 0))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem (abs x) (abs y)) n))
                (equal (lookup-equal-list nrs asg)
                       (int->lebits (- (rem (abs x) (abs y))) n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-rem-wrapped-spec x y t n) n)))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-negsel-gadget (car (last xs)) rs nrs zs one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-negsel-gadget-complete
                   (c (car (last xs))) (xs rs) (ys nrs)
                   (x (rem (abs x) (abs y)))
                   (y (- (rem (abs x) (abs y)))))
        (:instance int-divshift-sd-msb-lookup)
        (:instance int-divshift-sd-msb-binds)
        (:instance int-divshift-sd-integerp (signedp t))
        (:instance int-divshift-sd-rem-final
                   (zv (int->lebits (if (< x 0)
                                        (- (rem (abs x) (abs y)))
                                      (rem (abs x) (abs y)))
                                    n))))
  :disable (rem abs int-rem-wrapped-spec))

(defmacro int-divshift-sd-witness-hyps ()
  '(and (not (equal y 0))
        (equal (lookup-equal-list axs asg) (int->lebits (abs x) n))
        (equal (lookup-equal-list mxs asg) (int->lebits (- x) n))
        (equal (lookup-equal cx asg) (int-sub-carry 0 x n))
        (equal (lookup-equal-list ays asg) (int->lebits (abs y) n))
        (equal (lookup-equal-list mys asg) (int->lebits (- y) n))
        (equal (lookup-equal cy asg) (int-sub-carry 0 y n))
        (equal (lookup-equal-list qs asg)
               (int->lebits (truncate (abs x) (abs y)) n))
        (equal (lookup-equal-list rs asg)
               (int->lebits (rem (abs x) (abs y)) n))
        (equal (lookup-equal m asg)
               (* (truncate (abs x) (abs y)) (abs y)))
        (equal (lookup-equal-list ds asg)
               (int->lebits (+ (expt 2 n)
                               (rem (abs x) (abs y))
                               (- (abs y)))
                            n))
        (equal (lookup-equal d asg) 0)))

(defruledl int-divshift-sd-udiv-complete
  (implies (and (int-divshift-sd-common-hyps)
                (int-divshift-sd-witness-hyps))
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-div-gadget axs ays qs rs m ds d one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-sd-abs-valuep)
                 (:instance int-divshift-sd-abs-valuep (x y))
                 (:instance int-divshift-sd-abs-nonzero)
                 (:instance int-divshift-sd-integerp (x y) (signedp t))
                 (:instance int-divshift-sd-natp-when-integer-widthp)
                 (:instance int-divshift-unsigned-small-div-gadget-complete
                            (xs axs) (ys ays) (u one)
                            (x (abs x)) (y (abs y))))
           :in-theory (union-theories '(ifix (:e abs) posp)
                                      (theory 'minimal-theory)))))

(defmacro int-divshift-sd-divc-hyps ()
  '(and (int-divshift-sd-common-hyps)
        (symbolp s) (symbol-listp nqs)
        (equal (len nqs) n)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg nqs)
        (int-divshift-sd-witness-hyps)
        (equal (lookup-equal s asg)
               (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
        (equal (lookup-equal-list nqs asg)
               (int->lebits (- (truncate (abs x) (abs y))) n))
        (equal (lookup-equal nc asg)
               (if (< 0 (truncate (abs x) (abs y))) 0 1))
        (equal (lookup-equal-list zs asg)
               (int->lebits (int-div-wrapped-spec x y t n) n))))

(defmacro int-divshift-sd-remc-hyps ()
  '(and (int-divshift-sd-common-hyps)
        (symbol-listp nrs)
        (equal (len nrs) n)
        (r1cs::valuation-binds-allp asg nrs)
        (int-divshift-sd-witness-hyps)
        (equal (lookup-equal-list nrs asg)
               (int->lebits (- (rem (abs x) (abs y))) n))
        (equal (lookup-equal nc asg)
               (if (< 0 (rem (abs x) (abs y))) 0 1))
        (equal (lookup-equal-list zs asg)
               (int->lebits (int-rem-wrapped-spec x y t n) n))))

(defmacro int-divshift-sd-step (name hyps concl uses &optional extra)
  `(defruledl ,name
     (implies ,hyps ,concl)
     :do-not-induct t
     :hints (("Goal"
              :use ,uses
              :in-theory (union-theories '(ifix natp posp (:e abs) ,@extra)
                                         (theory 'minimal-theory))))))

(int-divshift-sd-step int-divshift-sd-divc-ax (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
  ((:instance int-divshift-sd-abs-complete)))

(int-divshift-sd-step int-divshift-sd-divc-ay (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-abs-wrapped-signed-gadget ys ays mys cy one p) asg p)
  ((:instance int-divshift-sd-abs-complete
              (xs ys) (axs ays) (mxs mys) (cx cy) (x y))))

(int-divshift-sd-step int-divshift-sd-divc-udiv (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (unsigned-small-div-gadget axs ays qs rs m ds d one p) asg p)
  ((:instance int-divshift-sd-udiv-complete)))

(int-divshift-sd-step int-divshift-sd-divc-xor (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (boolean-xor-gadget (car (last xs)) (car (last ys)) s p) asg p)
  ((:instance int-divshift-sd-natp-when-integer-widthp)
   (:instance int-divshift-sd-xor-complete)))

(int-divshift-sd-step int-divshift-sd-divc-neg (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (unsigned-small-sub-wrapped-const-var-gadget
    (int->lebits 0 n) qs nqs nc one p) asg p)
  ((:instance int-divshift-sd-abs-valuep)
   (:instance int-divshift-sd-abs-valuep (x y))
   (:instance int-divshift-sd-abs-nonzero)
   (:instance int-divshift-sd-integerp (x y) (signedp t))
   (:instance int-divshift-sd-natp-when-integer-widthp)
   (:instance int-divshift-truncate-abs-bounds (a (abs x)) (b (abs y)))
   (:instance int-divshift-sd-neg-complete
              (vs qs) (nvs nqs) (v (truncate (abs x) (abs y))))))

(int-divshift-sd-step int-divshift-sd-divc-sel (int-divshift-sd-divc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-divshift-negsel-gadget s qs nqs zs one p) asg p)
  ((:instance int-divshift-sd-integerp (signedp t))
   (:instance int-divshift-sd-integerp (x y) (signedp t))
   (:instance int-divshift-sd-natp-when-integer-widthp)
   (:instance int-divshift-sd-div-sel-complete)))

(defruled int-divshift-signed-div-wrapped-gadget-complete
  :short "Signed div_wrapped, widths 8-64: the snarkVM witnesses
          satisfy the constraints whenever the divisor is nonzero."
  (implies (int-divshift-sd-divc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-div-wrapped-gadget
             xs ys axs mxs cx ays mys cy qs rs m ds d s nqs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-divc-ax
                 int-divshift-sd-divc-ay
                 int-divshift-sd-divc-udiv
                 int-divshift-sd-divc-xor
                 int-divshift-sd-divc-neg
                 int-divshift-sd-divc-sel)
           :in-theory (union-theories
                       '(int-divshift-signed-div-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))

(int-divshift-sd-step int-divshift-sd-remc-ax (int-divshift-sd-remc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
  ((:instance int-divshift-sd-abs-complete)))

(int-divshift-sd-step int-divshift-sd-remc-ay (int-divshift-sd-remc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-abs-wrapped-signed-gadget ys ays mys cy one p) asg p)
  ((:instance int-divshift-sd-abs-complete
              (xs ys) (axs ays) (mxs mys) (cx cy) (x y))))

(int-divshift-sd-step int-divshift-sd-remc-udiv (int-divshift-sd-remc-hyps)
  (r1cs::r1cs-constraints-holdp
   (unsigned-small-div-gadget axs ays qs rs m ds d one p) asg p)
  ((:instance int-divshift-sd-udiv-complete)))

(int-divshift-sd-step int-divshift-sd-remc-neg (int-divshift-sd-remc-hyps)
  (r1cs::r1cs-constraints-holdp
   (unsigned-small-sub-wrapped-const-var-gadget
    (int->lebits 0 n) rs nrs nc one p) asg p)
  ((:instance int-divshift-sd-abs-valuep)
   (:instance int-divshift-sd-abs-valuep (x y))
   (:instance int-divshift-sd-abs-nonzero)
   (:instance int-divshift-sd-integerp (x y) (signedp t))
   (:instance int-divshift-sd-natp-when-integer-widthp)
   (:instance int-divshift-rem-abs-bounds (a (abs x)) (b (abs y)))
   (:instance int-divshift-sd-neg-complete
              (vs rs) (nvs nrs) (v (rem (abs x) (abs y))))))

(int-divshift-sd-step int-divshift-sd-remc-sel (int-divshift-sd-remc-hyps)
  (r1cs::r1cs-constraints-holdp
   (int-divshift-negsel-gadget (car (last xs)) rs nrs zs one p) asg p)
  ((:instance int-divshift-sd-integerp (x y) (signedp t))
   (:instance int-divshift-sd-natp-when-integer-widthp)
   (:instance int-divshift-sd-rem-sel-complete)))

(defruled int-divshift-signed-rem-wrapped-gadget-complete
  :short "Signed rem_wrapped, widths 8-64: the snarkVM witnesses
          satisfy the constraints whenever the divisor is nonzero."
  (implies (int-divshift-sd-remc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-divshift-signed-rem-wrapped-gadget
             xs ys axs mxs cx ays mys cy qs rs m ds d nrs nc zs one p)
            asg p))
  :do-not-induct t
  :hints (("Goal"
           :use (int-divshift-sd-remc-ax
                 int-divshift-sd-remc-ay
                 int-divshift-sd-remc-udiv
                 int-divshift-sd-remc-neg
                 int-divshift-sd-remc-sel)
           :in-theory (union-theories
                       '(int-divshift-signed-rem-wrapped-gadget
                         r1cs::r1cs-constraints-holdp-of-append)
                       (theory 'minimal-theory)))))
