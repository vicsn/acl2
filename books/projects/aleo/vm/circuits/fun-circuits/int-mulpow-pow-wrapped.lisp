; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PowWrapped::pow_wrapped with variable base and variable exponent, every
; width 8 to 128, both signednesses, any exponent width
; (snarkVM circuit/types/integers/src/pow_wrapped.rs):
;
;   result = 1 (constant)
;   for bit in exponent.bits_le.rev():
;     result = result.mul_wrapped(result)
;     result = ternary(bit, result.mul_wrapped(self), result)
;
; The first iteration is constant-folded by snarkVM: 1 * 1 is a constant,
; 1.mul_wrapped(self) has constant x_0 = 1 and x_1 = 0, so z_0 + 2^h z_1 is
; the linear combination of the bits of self and only its
; to_lower_bits_le(n + h + 1) remains (n + h + 1 boolean checks and one
; equality).  The ternary against the constant 1 then becomes !e | p_0 for
; bit 0 and e & p_i for the other bits (Boolean::ternary with a constant
; second operand).  Every later iteration is two Babbage mul_wrapped gadgets
; and an integer ternary.
;
; The two's complement bits do not depend on signedness, so the loop
; invariant is: the result bits are int->lebits of x^v, where v is the value
; of the exponent bits processed so far.

(in-package "ALEOVM")

(include-book "int-mulpow-wrapped")
(include-book "../r1cs/integer-ternary")
(include-book "../r1cs/boolean-or-notleft")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum-vectors")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lookup-equal-list"))
(local (include-book "../library-extensions/r1cses"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-mulpow-pw-valuep-of-mod
  (implies (posp n) (int-valuep (mod (ifix a) (expt 2 n)) nil n))
  :enable (int-valuep int-min int-max))

(defruled int-mulpow-pw-int->lebits-of-mod
  (implies (natp n)
           (equal (int->lebits (mod (ifix a) (expt 2 n)) n)
                  (int->lebits a n)))
  :enable int->lebits)

(defruled int-mulpow-pw-int->lebits-of-wrapped-mod
  (implies (posp n)
           (equal (int->lebits (int-mul-wrapped-spec (mod (ifix a) (expt 2 n))
                                                     (mod (ifix b) (expt 2 n))
                                                     nil n)
                               n)
                  (int->lebits (* (ifix a) (ifix b)) n)))
  :enable (int->lebits int-mul-wrapped-spec int->lebits-of-int-wrap
           int-wrap acl2::mod-of-*-of-mod acl2::mod-of-*-of-mod-2))

(defruled int-mulpow-pw-mul-wrapped-sound-bits
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len zs-high) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (integerp a) (integerp b)
                (equal (lookup-equal-list xs asg) (int->lebits a n))
                (equal (lookup-equal-list ys asg) (int->lebits b n))
                (r1cs::r1cs-constraints-holdp
                 (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh
                                         zs zs-high p)
                 asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits (* a b) n)))
  :do-not-induct t
  :use ((:instance int-mul-wrapped-gadget-sound
                   (x (mod a (expt 2 n))) (y (mod b (expt 2 n)))
                   (signedp nil))
        (:instance int-mulpow-pw-valuep-of-mod)
        (:instance int-mulpow-pw-valuep-of-mod (a b))
        (:instance int-mulpow-pw-int->lebits-of-mod)
        (:instance int-mulpow-pw-int->lebits-of-mod (a b))
        (:instance int-mulpow-pw-int->lebits-of-wrapped-mod))
  :in-theory (e/d (posp-when-integer-widthp) (int->lebits int-mul-wrapped-spec int-valuep)))

(defruled int-mulpow-pw-lo-hi-of-mod
  (implies (and (posp n) (integerp a))
           (and (equal (int-mulpow-lo (mod a (expt 2 n)) n)
                       (int-mulpow-lo a n))
                (equal (int-mulpow-hi (mod a (expt 2 n)) n)
                       (int-mulpow-hi a n))))
  :enable (int-mulpow-lo int-mulpow-hi))

(defruled int-mulpow-pw-sum-of-mod
  (implies (and (posp n) (integerp a) (integerp b))
           (equal (int-mul-wrapped-sum (mod a (expt 2 n))
                                       (mod b (expt 2 n)) n)
                  (int-mul-wrapped-sum a b n)))
  :use (int-mulpow-pw-lo-hi-of-mod (:instance int-mulpow-pw-lo-hi-of-mod (a b)))
  :in-theory (e/d (int-mul-wrapped-sum) (int-mulpow-lo int-mulpow-hi int-mulpow-babbage-sum)))

(defruled int-mulpow-pw-mul-wrapped-complete-bits
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ys)
                (symbolp lowlow) (symbolp highlow) (symbolp lowhigh)
                (symbol-listp zs) (symbol-listp zs-high)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (equal (len zs-high) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high)
                (integerp a) (integerp b)
                (equal (lookup-equal-list xs asg) (int->lebits a n))
                (equal (lookup-equal-list ys asg) (int->lebits b n))
                (equal (lookup-equal lowlow asg)
                       (* (int-mulpow-lo a n) (int-mulpow-lo b n)))
                (equal (lookup-equal highlow asg)
                       (* (int-mulpow-hi a n) (int-mulpow-lo b n)))
                (equal (lookup-equal lowhigh asg)
                       (* (int-mulpow-lo a n) (int-mulpow-hi b n)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (* a b) n))
                (equal (lookup-equal-list zs-high asg)
                       (acl2::nat=>lebits (1+ (floor n 2))
                                          (floor (int-mul-wrapped-sum a b n)
                                                 (expt 2 n)))))
           (r1cs::r1cs-constraints-holdp
            (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh zs zs-high p)
            asg p))
  :do-not-induct t
  :use ((:instance int-mul-wrapped-gadget-complete
                   (x (mod a (expt 2 n))) (y (mod b (expt 2 n)))
                   (signedp nil))
        (:instance int-mulpow-pw-valuep-of-mod)
        (:instance int-mulpow-pw-valuep-of-mod (a b))
        (:instance int-mulpow-pw-int->lebits-of-mod)
        (:instance int-mulpow-pw-int->lebits-of-mod (a b))
        (:instance int-mulpow-pw-int->lebits-of-wrapped-mod)
        (:instance int-mulpow-pw-lo-hi-of-mod)
        (:instance int-mulpow-pw-lo-hi-of-mod (a b))
        (:instance int-mulpow-pw-sum-of-mod))
  :in-theory (e/d (posp-when-integer-widthp)
                  (int->lebits int-mul-wrapped-spec int-valuep
                   int-mulpow-lo int-mulpow-hi int-mul-wrapped-sum)))

(defruled int-mulpow-pw-expt-step
  (implies (and (integerp x) (natp v) (bitp b))
           (equal (expt x (+ (* 2 v) b))
                  (if (equal b 1)
                      (* (* (expt x v) (expt x v)) x)
                    (* (expt x v) (expt x v)))))
  :cases ((equal x 0))
  :use ((:instance acl2::expt-of-+ (r x) (i1 v) (i2 v))
        (:instance acl2::expt-of-+ (r x) (i1 (* 2 v)) (i2 1)))
  :enable bitp)

; A loop iteration record is the list of wires
;   (ll hl lh sqs sqh ll2 hl2 lh2 ms msh rs)
; of the squaring, the multiplication by the base, and the selected result.

(defund int-mulpow-pw-rec-okp (rec n asg)
  (declare (xargs :verify-guards nil))
  (and (true-listp rec)
       (equal (len rec) 11)
       (symbolp (nth 0 rec)) (symbolp (nth 1 rec)) (symbolp (nth 2 rec))
       (symbol-listp (nth 3 rec)) (symbol-listp (nth 4 rec))
       (symbolp (nth 5 rec)) (symbolp (nth 6 rec)) (symbolp (nth 7 rec))
       (symbol-listp (nth 8 rec)) (symbol-listp (nth 9 rec))
       (symbol-listp (nth 10 rec))
       (equal (len (nth 3 rec)) n)
       (equal (len (nth 4 rec)) (1+ (floor n 2)))
       (equal (len (nth 8 rec)) n)
       (equal (len (nth 9 rec)) (1+ (floor n 2)))
       (equal (len (nth 10 rec)) n)
       (r1cs::valuation-bindsp asg (nth 0 rec))
       (r1cs::valuation-bindsp asg (nth 1 rec))
       (r1cs::valuation-bindsp asg (nth 2 rec))
       (r1cs::valuation-binds-allp asg (nth 3 rec))
       (r1cs::valuation-binds-allp asg (nth 4 rec))
       (r1cs::valuation-bindsp asg (nth 5 rec))
       (r1cs::valuation-bindsp asg (nth 6 rec))
       (r1cs::valuation-bindsp asg (nth 7 rec))
       (r1cs::valuation-binds-allp asg (nth 8 rec))
       (r1cs::valuation-binds-allp asg (nth 9 rec))
       (r1cs::valuation-binds-allp asg (nth 10 rec))))

(defund int-mulpow-pw-step-gadget (e xs rs rec p)
  (append (int-mul-wrapped-gadget rs rs (nth 0 rec) (nth 1 rec) (nth 2 rec)
                                  (nth 3 rec) (nth 4 rec) p)
          (int-mul-wrapped-gadget (nth 3 rec) xs (nth 5 rec) (nth 6 rec)
                                  (nth 7 rec) (nth 8 rec) (nth 9 rec) p)
          (integer-ternary-gadget e (nth 8 rec) (nth 3 rec) (nth 10 rec) p)))

(defruled int-mulpow-pw-step-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (bitp (lookup-equal e asg))
                (integerp x) (natp v)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pw-rec-okp rec n asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-step-gadget e xs rs rec p) asg p))
           (equal (lookup-equal-list (nth 10 rec) asg)
                  (int->lebits (expt x (+ (* 2 v) (lookup-equal e asg))) n)))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-mul-wrapped-sound-bits
                   (xs rs) (ys rs)
                   (lowlow (nth 0 rec)) (highlow (nth 1 rec))
                   (lowhigh (nth 2 rec)) (zs (nth 3 rec)) (zs-high (nth 4 rec))
                   (a (expt x v)) (b (expt x v)))
        (:instance int-mulpow-pw-mul-wrapped-sound-bits
                   (xs (nth 3 rec)) (ys xs)
                   (lowlow (nth 5 rec)) (highlow (nth 6 rec))
                   (lowhigh (nth 7 rec)) (zs (nth 8 rec)) (zs-high (nth 9 rec))
                   (a (* (expt x v) (expt x v))) (b x))
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys (nth 8 rec)) (zs (nth 3 rec)) (ws (nth 10 rec)))
        (:instance int-mulpow-pw-expt-step (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-pw-step-gadget
                   int-mulpow-pw-rec-okp
                   r1cs::r1cs-constraints-holdp-of-append
                   bitp)
                  (int->lebits expt)))

(defruled int-mulpow-pw-sum-constraint-iff
  (implies (and (equal p (base-prime))
                (symbol-listp xs) (symbol-listp ws)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ws asg))
                (< (len xs) 253)
                (< (len ws) 253))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::make-r1cs-constraint
                    :a (pow2sum-vector xs 0)
                    :b (list (list 1 1))
                    :c (pow2sum-vector ws 0))
                   asg p)
                  (equal (lebits=>nat (lookup-equal-list xs asg))
                         (lebits=>nat (lookup-equal-list ws asg)))))
  :do-not-induct t
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat (i 0))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat (xs ws) (i 0))
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list xs asg)))
        (:instance lebits=>nat-less-when-len-less
                   (p (base-prime)) (bs (lookup-equal-list ws asg))))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add pfield::mul
           integer-length-of-base-prime
           acl2::mod-when-<))

(defund int-mulpow-pw-and-list (e ps rs)
  (declare (xargs :verify-guards nil))
  (if (endp ps)
      nil
    (append (boolean-and-gadget e (car ps) (car rs))
            (int-mulpow-pw-and-list e (cdr ps) (cdr rs)))))

(defruled int-mulpow-pw-and-list-iff
  (implies (and (symbolp e) (symbol-listp ps) (symbol-listp rs)
                (equal (len rs) (len ps))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (bitp (lookup-equal e asg))
                (bit-listp (lookup-equal-list ps asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-pw-and-list e ps rs) asg p)
                  (equal (lookup-equal-list rs asg)
                         (if (equal (lookup-equal e asg) 1)
                             (lookup-equal-list ps asg)
                           (repeat (len ps) 0)))))
  :induct (int-mulpow-pw-and-list e ps rs)
  :enable (int-mulpow-pw-and-list
           boolean-and-gadget-to-bitand
           bitand
           lookup-equal-list
           repeat))

(defund int-mulpow-pw-first-gadget (e xs ps psh rs one p)
  (declare (xargs :verify-guards nil))
  (append (boolean-check-gadget-list ps p)
          (boolean-check-gadget-list psh p)
          (list (r1cs::make-r1cs-constraint
                 :a (pow2sum-vector xs 0)
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append ps psh) 0)))
          (boolean-or-notleft-gadget e (car ps) (car rs) one p)
          (int-mulpow-pw-and-list e (cdr ps) (cdr rs))))

(defruled int-mulpow-pw-int->lebits-of-1
  (implies (posp n)
           (equal (int->lebits 1 n)
                  (cons 1 (repeat (1- n) 0))))
  :expand ((acl2::nat=>lendian 2 n 1))
  :enable (int->lebits acl2::nat=>lebits acl2::mod-when-<))

(defruled int-mulpow-pw-lebits-bound
  (< (lebits=>nat bs) (expt 2 (len bs)))
  :rule-classes ((:linear :trigger-terms ((lebits=>nat bs))))
  :use (:instance acl2::lendian=>nat-upper-bound (base 2) (digits bs))
  :enable lebits=>nat)

(defruled int-mulpow-pw-first-ps
  (implies (and (posp n) (integerp x)
                (bit-listp a) (bit-listp b)
                (equal (len a) n)
                (equal (mod x (expt 2 n))
                       (+ (lebits=>nat a) (* (expt 2 n) (lebits=>nat b)))))
           (equal (int->lebits x n) a))
  :do-not-induct t
  :cases ((equal (lebits=>nat b) 0))
  :use ((:instance int-mulpow-pw-lebits-bound (bs a))
        (:instance int-mulpow-bits-are-int->lebits (zs a) (y 1)))
  :in-theory (e/d (acl2::mod-when-<) (int->lebits)))

(defrule int-mulpow-pw-first-rs
  (implies (and (bitp e) (bitp q) (bit-listp qs) (bit-listp rs)
                (equal (len rs) (len qs))
                (equal (car rs) (if (or (equal e 0) (equal q 1)) 1 0))
                (consp rs)
                (equal (cdr rs) (if (equal e 1) qs (repeat (len qs) 0))))
           (equal rs (if (equal e 1) (cons q qs) (cons 1 (repeat (len qs) 0)))))
  :rule-classes nil
  :enable bitp
  :cases ((consp rs))
  :expand ((len rs)))

(defruled int-mulpow-pw-holdp-of-singleton
  (equal (r1cs::r1cs-constraints-holdp (list c) asg p)
         (r1cs::r1cs-constraint-holdsp c asg p))
  :enable r1cs::r1cs-constraints-holdp)

(defruled int-mulpow-pw-first-rs-sound
  (implies (and (primep p)
                (symbolp e) (symbolp one)
                (symbol-listp ps) (symbol-listp rs)
                (consp ps) (consp rs)
                (equal (len rs) (len ps))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (bit-listp (lookup-equal-list ps asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget e (car ps) (car rs) one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-and-list e (cdr ps) (cdr rs)) asg p))
           (equal (lookup-equal-list rs asg)
                  (if (equal (lookup-equal e asg) 1)
                      (lookup-equal-list ps asg)
                    (cons 1 (repeat (1- (len ps)) 0)))))
  :do-not-induct t
  :expand ((lookup-equal-list ps asg) (lookup-equal-list rs asg))
  :use ((:instance boolean-or-notleft-gadget-to-boolor-boolnot
                   (x e) (y (car ps)) (z (car rs)))
        (:instance int-mulpow-pw-and-list-iff (ps (cdr ps)) (rs (cdr rs)))
        (:instance int-mulpow-pw-first-rs
                   (e (lookup-equal e asg))
                   (q (lookup-equal (car ps) asg))
                   (qs (lookup-equal-list (cdr ps) asg))
                   (rs (cons (lookup-equal (car rs) asg)
                             (lookup-equal-list (cdr rs) asg)))))
  :enable bitp)

(defruled int-mulpow-pw-first-ps-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp (boolean-check-gadget-list ps p) asg p)
                (r1cs::r1cs-constraints-holdp (boolean-check-gadget-list psh p) asg p)
                (r1cs::r1cs-constraint-holdsp
                 (r1cs::make-r1cs-constraint
                  :a (pow2sum-vector xs 0)
                  :b (list (list 1 1))
                  :c (pow2sum-vector (append ps psh) 0))
                 asg p))
           (equal (lookup-equal-list ps asg) (int->lebits x n)))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance boolean-check-gadget-list-to-bit-listp (xs psh))
        (:instance int-mulpow-pw-sum-constraint-iff (ws (append ps psh)))
        (:instance int-mulpow-width-mul-wrapped-fits)
        (:instance int-mulpow-pw-first-ps
                   (a (lookup-equal-list ps asg))
                   (b (lookup-equal-list psh asg)))
        (:instance lebits=>nat-of-int->lebits))
  :in-theory (e/d (lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   posp-when-integer-widthp)
                  (int->lebits lebits=>nat-of-int->lebits)))

(defruled int-mulpow-pw-first-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-first-gadget e xs ps psh rs one p) asg p))
           (equal (lookup-equal-list rs asg)
                  (int->lebits (expt x (lookup-equal e asg)) n)))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-first-ps-sound)
        (:instance int-mulpow-pw-first-rs-sound)
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pw-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pw-holdp-of-singleton
                   bit-listp-of-int->lebits-explicit
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

(defund int-mulpow-msb-val (bs v)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      v
    (int-mulpow-msb-val (cdr bs) (+ (* 2 v) (car bs)))))

(defruled int-mulpow-msb-val-of-append-singleton
  (equal (int-mulpow-msb-val (append as (list b)) v)
         (+ (* 2 (int-mulpow-msb-val as v)) b))
  :induct (int-mulpow-msb-val as v)
  :enable int-mulpow-msb-val)

(defruled int-mulpow-msb-val-of-rev
  (implies (and (bit-listp bs) (natp v))
           (equal (int-mulpow-msb-val (rev bs) v)
                  (+ (* v (expt 2 (len bs))) (lebits=>nat bs))))
  :induct (len bs)
  :enable (int-mulpow-msb-val int-mulpow-msb-val-of-append-singleton
           rev acl2::expt-of-+ lebits=>nat acl2::lendian=>nat
           acl2::lendian=>nat-of-cons))

(defruled int-mulpow-msb-val-natp
  (implies (and (bit-listp bs) (natp v))
           (natp (int-mulpow-msb-val bs v)))
  :induct (int-mulpow-msb-val bs v)
  :enable int-mulpow-msb-val)

(defruled int-mulpow-pw-rec-okp-out
  (implies (int-mulpow-pw-rec-okp rec n asg)
           (and (symbol-listp (nth 10 rec))
                (equal (len (nth 10 rec)) n)
                (r1cs::valuation-binds-allp asg (nth 10 rec))))
  :enable int-mulpow-pw-rec-okp)

(defund int-mulpow-pw-recs-okp (bs recs n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pw-rec-okp (car recs) n asg)
         (int-mulpow-pw-recs-okp (cdr bs) (cdr recs) n asg))))

(defund int-mulpow-pw-loop-gadget (bs xs rs recs p)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      nil
    (append (int-mulpow-pw-step-gadget (car bs) xs rs (car recs) p)
            (int-mulpow-pw-loop-gadget (cdr bs) xs (nth 10 (car recs))
                                       (cdr recs) p))))

(defund int-mulpow-pw-loop-out (bs rs recs)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      rs
    (int-mulpow-pw-loop-out (cdr bs) (nth 10 (car recs)) (cdr recs))))

(defun int-mulpow-pw-ind (bs rs recs v asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      (list rs recs v asg)
    (int-mulpow-pw-ind (cdr bs) (nth 10 (car recs)) (cdr recs)
                       (+ (* 2 v) (lookup-equal (car bs) asg)) asg)))

(defruled int-mulpow-pw-loop-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp bs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg))
                (integerp x) (natp v)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pw-recs-okp bs recs n asg)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-loop-gadget bs xs rs recs p) asg p))
           (equal (lookup-equal-list (int-mulpow-pw-loop-out bs rs recs) asg)
                  (int->lebits
                   (expt x (int-mulpow-msb-val (lookup-equal-list bs asg) v))
                   n)))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
  :in-theory (e/d (int-mulpow-pw-loop-gadget
                   int-mulpow-pw-loop-out
                   int-mulpow-pw-recs-okp
                   int-mulpow-msb-val
                   int-mulpow-pw-rec-okp-out
                   lookup-equal-list
                   r1cs::r1cs-constraints-holdp-of-append)
                  (int->lebits expt)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pw-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defund int-pow-wrapped-gadget (xs es ps psh r0 recs one p)
  (declare (xargs :verify-guards nil))
  (b* ((bs (rev es)))
    (append (int-mulpow-pw-first-gadget (car bs) xs ps psh r0 one p)
            (int-mulpow-pw-loop-gadget (cdr bs) xs r0 recs p))))

(defund int-pow-wrapped-gadget-out (es r0 recs)
  (declare (xargs :verify-guards nil))
  (int-mulpow-pw-loop-out (cdr (rev es)) r0 recs))

(defruled int-mulpow-pw-bit-listp-of-rev
  (implies (bit-listp bs) (bit-listp (rev bs)))
  :induct (len bs)
  :enable rev)

(defruled int-mulpow-pw-bitp-car
  (implies (and (bit-listp l) (consp l)) (bitp (car l))))

(defruled int-mulpow-pw-exponent-value
  (implies (and (bit-listp bs) (consp bs))
           (equal (int-mulpow-msb-val (cdr (rev bs)) (car (rev bs)))
                  (lebits=>nat bs)))
  :use ((:instance int-mulpow-msb-val-of-rev (v 0))
        (:instance int-mulpow-pw-bit-listp-of-rev)
        (:instance int-mulpow-pw-bitp-car (l (rev bs))))
  :expand ((int-mulpow-msb-val (rev bs) 0))
  :enable (acl2::consp-of-rev bitp))

(defruled int-mulpow-pw-binds-allp-of-rev
  (implies (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (rev l)))
  :induct (len l)
  :enable (rev r1cs::valuation-binds-allp))

(defruled int-mulpow-pw-rev-facts
  (implies (and (symbol-listp es) (consp es)
                (r1cs::valuation-binds-allp asg es)
                (bit-listp (lookup-equal-list es asg)))
           (and (symbol-listp (cdr (rev es)))
                (symbolp (car (rev es)))
                (r1cs::valuation-binds-allp asg (cdr (rev es)))
                (r1cs::valuation-bindsp asg (car (rev es)))
                (bit-listp (lookup-equal-list (cdr (rev es)) asg))
                (bitp (lookup-equal (car (rev es)) asg))))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-binds-allp-of-rev (l es))
        (:instance int-mulpow-pw-bit-listp-of-rev (bs (lookup-equal-list es asg)))
        (:instance acl2::symbol-listp-of-rev (x es))
        (:instance int-mulpow-pw-bitp-car (l (rev (lookup-equal-list es asg)))))
  :expand ((r1cs::valuation-binds-allp asg (rev es)))
  :in-theory (e/d (lookup-equal-list-of-rev acl2::consp-of-rev
                   lookup-equal-list-of-cdr lookup-equal-of-car)
                  (acl2::symbol-listp-of-rev)))

(defruled int-pow-wrapped-gadget-sound
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (symbol-listp r0) (equal (len r0) n)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pw-recs-okp (cdr (rev es)) recs n asg)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (bit-listp (lookup-equal-list es asg))
                (r1cs::r1cs-constraints-holdp
                 (int-pow-wrapped-gadget xs es ps psh r0 recs one p) asg p))
           (equal (lookup-equal-list (int-pow-wrapped-gadget-out es r0 recs) asg)
                  (int->lebits
                   (int-pow-wrapped-spec x (lebits=>nat (lookup-equal-list es asg))
                                         signedp n)
                   n)))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-first-sound
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pw-loop-sound
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg)))
        (:instance int-mulpow-pw-exponent-value
                   (bs (lookup-equal-list es asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-wrapped-gadget
                   int-pow-wrapped-gadget-out
                   int-pow-wrapped-spec
                   int->lebits-of-int-wrap
                   r1cs::r1cs-constraints-holdp-of-append
                   lookup-equal-list-of-rev
                   lookup-equal-list-of-cdr
                   lookup-equal-of-car
                   posp-when-integer-widthp
                   int-valuep)
                  (int->lebits expt int-wrap)))

(defund int-mulpow-pw-rec-honestp (rec x v b n asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (expt x v))
       (sq (* r r))
       (h (floor n 2)))
    (and (equal (lookup-equal (nth 0 rec) asg)
                (* (int-mulpow-lo r n) (int-mulpow-lo r n)))
         (equal (lookup-equal (nth 1 rec) asg)
                (* (int-mulpow-hi r n) (int-mulpow-lo r n)))
         (equal (lookup-equal (nth 2 rec) asg)
                (* (int-mulpow-lo r n) (int-mulpow-hi r n)))
         (equal (lookup-equal-list (nth 3 rec) asg) (int->lebits sq n))
         (equal (lookup-equal-list (nth 4 rec) asg)
                (acl2::nat=>lebits (1+ h) (floor (int-mul-wrapped-sum r r n)
                                                 (expt 2 n))))
         (equal (lookup-equal (nth 5 rec) asg)
                (* (int-mulpow-lo sq n) (int-mulpow-lo x n)))
         (equal (lookup-equal (nth 6 rec) asg)
                (* (int-mulpow-hi sq n) (int-mulpow-lo x n)))
         (equal (lookup-equal (nth 7 rec) asg)
                (* (int-mulpow-lo sq n) (int-mulpow-hi x n)))
         (equal (lookup-equal-list (nth 8 rec) asg) (int->lebits (* sq x) n))
         (equal (lookup-equal-list (nth 9 rec) asg)
                (acl2::nat=>lebits (1+ h) (floor (int-mul-wrapped-sum sq x n)
                                                 (expt 2 n))))
         (equal (lookup-equal-list (nth 10 rec) asg)
                (int->lebits (expt x (+ (* 2 v) b)) n)))))

(defruled int-mulpow-pw-step-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (bitp (lookup-equal e asg))
                (integerp x) (natp v)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pw-rec-okp rec n asg)
                (int-mulpow-pw-rec-honestp rec x v (lookup-equal e asg) n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pw-step-gadget e xs rs rec p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-mul-wrapped-complete-bits
                   (xs rs) (ys rs)
                   (lowlow (nth 0 rec)) (highlow (nth 1 rec))
                   (lowhigh (nth 2 rec)) (zs (nth 3 rec)) (zs-high (nth 4 rec))
                   (a (expt x v)) (b (expt x v)))
        (:instance int-mulpow-pw-mul-wrapped-complete-bits
                   (xs (nth 3 rec)) (ys xs)
                   (lowlow (nth 5 rec)) (highlow (nth 6 rec))
                   (lowhigh (nth 7 rec)) (zs (nth 8 rec)) (zs-high (nth 9 rec))
                   (a (* (expt x v) (expt x v))) (b x))
        (:instance integer-ternary-gadget-correctness
                   (x e) (ys (nth 8 rec)) (zs (nth 3 rec)) (ws (nth 10 rec)))
        (:instance int-mulpow-pw-expt-step (b (lookup-equal e asg))))
  :in-theory (e/d (int-mulpow-pw-step-gadget
                   int-mulpow-pw-rec-okp
                   int-mulpow-pw-rec-honestp
                   r1cs::r1cs-constraints-holdp-of-append
                   bitp)
                  (int->lebits expt int-mulpow-lo int-mulpow-hi
                   int-mul-wrapped-sum)))

(defund int-mulpow-pw-recs-honestp (bs recs x v n asg)
  (declare (xargs :verify-guards nil))
  (if (endp bs)
      t
    (and (int-mulpow-pw-rec-honestp (car recs) x v (lookup-equal (car bs) asg)
                                    n asg)
         (int-mulpow-pw-recs-honestp (cdr bs) (cdr recs) x
                                     (+ (* 2 v) (lookup-equal (car bs) asg))
                                     n asg))))

(defruled int-mulpow-pw-loop-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp rs) (equal (len rs) n)
                (symbol-listp bs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg))
                (integerp x) (natp v)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list rs asg) (int->lebits (expt x v) n))
                (int-mulpow-pw-recs-okp bs recs n asg)
                (int-mulpow-pw-recs-honestp bs recs x v n asg))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pw-loop-gadget bs xs rs recs p) asg p))
  :hints (("Goal" :induct (int-mulpow-pw-ind bs rs recs v asg)
           :in-theory (e/d (int-mulpow-pw-loop-gadget
                            int-mulpow-pw-recs-okp
                            int-mulpow-pw-recs-honestp
                            int-mulpow-pw-rec-okp-out
                            lookup-equal-list
                            r1cs::r1cs-constraints-holdp-of-append)
                           (int->lebits expt)))
          (and (equal (car id) '(0 1))
               '(:use ((:instance int-mulpow-pw-step-complete
                                  (e (car bs)) (rec (car recs)))
                       (:instance int-mulpow-pw-step-sound
                                  (e (car bs)) (rec (car recs))))))))

(defruled int-mulpow-pw-first-rs-complete
  (implies (and (primep p)
                (symbolp e) (symbolp one)
                (symbol-listp ps) (symbol-listp rs)
                (consp ps) (consp rs)
                (equal (len rs) (len ps))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (bit-listp (lookup-equal-list ps asg))
                (equal (lookup-equal-list rs asg)
                       (if (equal (lookup-equal e asg) 1)
                           (lookup-equal-list ps asg)
                         (cons 1 (repeat (1- (len ps)) 0)))))
           (and (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget e (car ps) (car rs) one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-pw-and-list e (cdr ps) (cdr rs)) asg p)))
  :do-not-induct t
  :expand ((lookup-equal-list ps asg) (lookup-equal-list rs asg))
  :use ((:instance boolean-or-notleft-gadget-to-boolor-boolnot
                   (x e) (y (car ps)) (z (car rs)))
        (:instance int-mulpow-pw-and-list-iff (ps (cdr ps)) (rs (cdr rs))))
  :enable bitp)

(defruled int-mulpow-pw-bit-listp-of-repeat-0
  (bit-listp (repeat k 0))
  :enable repeat)

(defruled int-mulpow-pw-lebits=>nat-of-repeat-0
  (equal (lebits=>nat (repeat k 0)) 0)
  :induct (repeat k 0)
  :enable (repeat lebits=>nat acl2::lendian=>nat acl2::lendian=>nat-of-cons))

(defruled int-mulpow-pw-first-ps-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal-list psh asg) (repeat (1+ (floor n 2)) 0)))
           (and (r1cs::r1cs-constraints-holdp (boolean-check-gadget-list ps p) asg p)
                (r1cs::r1cs-constraints-holdp (boolean-check-gadget-list psh p) asg p)
                (r1cs::r1cs-constraint-holdsp
                 (r1cs::make-r1cs-constraint
                  :a (pow2sum-vector xs 0)
                  :b (list (list 1 1))
                  :c (pow2sum-vector (append ps psh) 0))
                 asg p)))
  :do-not-induct t
  :use ((:instance boolean-check-gadget-list-to-bit-listp (xs ps))
        (:instance boolean-check-gadget-list-to-bit-listp (xs psh))
        (:instance int-mulpow-pw-sum-constraint-iff (ws (append ps psh)))
        (:instance int-mulpow-width-mul-wrapped-fits)
        (:instance int-mulpow-pw-bit-listp-of-repeat-0 (k (1+ (floor n 2))))
        (:instance int-mulpow-pw-lebits=>nat-of-repeat-0 (k (1+ (floor n 2)))))
  :in-theory (e/d (lookup-equal-list-of-append
                   acl2::lebits=>nat-of-append
                   bit-listp-of-int->lebits-explicit
                   posp-when-integer-widthp)
                  (int->lebits)))

(defruled int-mulpow-pw-first-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (symbol-listp rs) (equal (len rs) n)
                (symbolp e) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg e)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal e asg))
                (integerp x)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal-list psh asg) (repeat (1+ (floor n 2)) 0))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (expt x (lookup-equal e asg)) n)))
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-pw-first-gadget e xs ps psh rs one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-first-ps-complete)
        (:instance int-mulpow-pw-first-rs-complete)
        (:instance int-mulpow-pw-int->lebits-of-1)
        (:instance posp-when-integer-widthp))
  :in-theory (e/d (int-mulpow-pw-first-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   int-mulpow-pw-holdp-of-singleton
                   bit-listp-of-int->lebits-explicit
                   bitp)
                  (int->lebits r1cs::r1cs-constraints-holdp
                   int-mulpow-pw-int->lebits-of-1)))

(defruled int-pow-wrapped-gadget-complete
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (symbol-listp xs) (equal (len xs) n)
                (symbol-listp es) (consp es)
                (symbol-listp ps) (equal (len ps) n)
                (symbol-listp psh) (equal (len psh) (1+ (floor n 2)))
                (symbol-listp r0) (equal (len r0) n)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg es)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg psh)
                (r1cs::valuation-binds-allp asg r0)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-mulpow-pw-recs-okp (cdr (rev es)) recs n asg)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (bit-listp (lookup-equal-list es asg))
                (equal (lookup-equal-list ps asg) (int->lebits x n))
                (equal (lookup-equal-list psh asg) (repeat (1+ (floor n 2)) 0))
                (equal (lookup-equal-list r0 asg)
                       (int->lebits (expt x (lookup-equal (car (rev es)) asg)) n))
                (int-mulpow-pw-recs-honestp (cdr (rev es)) recs x
                                            (lookup-equal (car (rev es)) asg)
                                            n asg))
           (r1cs::r1cs-constraints-holdp
            (int-pow-wrapped-gadget xs es ps psh r0 recs one p) asg p))
  :do-not-induct t
  :use ((:instance int-mulpow-pw-first-complete
                   (e (car (rev es))) (rs r0))
        (:instance int-mulpow-pw-loop-complete
                   (bs (cdr (rev es))) (rs r0)
                   (v (lookup-equal (car (rev es)) asg)))
        (:instance int-mulpow-pw-rev-facts))
  :in-theory (e/d (int-pow-wrapped-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   posp-when-integer-widthp
                   int-valuep)
                  (int->lebits expt)))
