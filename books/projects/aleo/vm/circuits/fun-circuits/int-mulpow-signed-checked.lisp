; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed MulChecked::mul_checked (also Mul::mul, MulAssign::mul_assign),
; variable operands, every signed width 8 to 128 (snarkVM
; circuit/types/integers/src/mul_checked.rs):
;
;   a = x.abs_wrapped(), b = y.abs_wrapped()          (as unsigned)
;   product = mul_and_check(a, b)
;   same = !(msb x ^ msb y)
;   assert_eq(same & msb product, 0)
;   lower = fold(false, |acc, b| acc | b) over bits 0 .. n-2 of product
;   ok_neg = !msb product | (msb product & !lower)
;   assert_eq(!same & !ok_neg, 0)
;   ternary(same, product, 0.sub_wrapped(product))
;
; NOT is free (the linear combination one - c), so the gadgets used are
; xor, and-notleft, and-notright, or-notleft, a chain of ors, two
; assert_eq constraints (c * 1 = 0), the constant-minus-variable
; subtraction, and the negated select of int-divshift-signed-div.

(in-package "ALEOVM")

(include-book "int-mulpow-checked")
(include-book "int-divshift-sub-wrapped-const")
(include-book "int-abs")
(include-book "../r1cs/integer-ternary")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-and-notleft")
(include-book "../r1cs/boolean-and-notright")
(include-book "../r1cs/boolean-or-notleft")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/butlast" :dir :system))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lookup-equal-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Negated select: bits of if c then y else x.

(define int-mulpow-negsel-gadget ((c symbolp)
                                  (xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp)
                                  (one symbolp)
                                  (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (integer-ternary-not-gadget c xs ys zs one p))

(defruled int-mulpow-negsel-gadget-iff
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
                (equal (lookup-equal-list ys asg) (int->lebits y n)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-negsel-gadget c xs ys zs one p) asg p)
                  (equal (lookup-equal-list zs asg)
                         (int->lebits (if (equal (lookup-equal c asg) 0) x y)
                                      n))))
  :use (:instance integer-ternary-not-gadget-correctness
                  (x c) (ys xs) (zs ys) (ws zs))
  :enable int-mulpow-negsel-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; abs_wrapped and 0.sub_wrapped(v) on the values used here.

(defruledl int-mulpow-bits-from-mod
  (implies (and (natp n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) (mod v (expt 2 n)))
                (integerp v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable int->lebits)

(defruledl int-mulpow-mod-lebits=>int
  (implies (and (bit-listp bits) (equal (len bits) n))
           (equal (mod (lebits=>int bits) (expt 2 n))
                  (lebits=>nat bits)))
  :use (:instance acl2::lebits=>nat-upper-bound (digits bits))
  :enable lebits=>int)

(defruledl int-mulpow-abs-valuep
  (implies (and (posp n) (int-valuep x t n))
           (and (natp (abs x))
                (<= (abs x) (expt 2 (1- n)))
                (< (abs x) (expt 2 n))
                (int-valuep (abs x) nil n)
                (equal (mod (abs x) (expt 2 n)) (abs x))))
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruledl int-mulpow-valuep-below
  (implies (and (posp n) (natp v) (<= v (expt 2 (1- n))))
           (and (int-valuep v nil n)
                (equal (mod v (expt 2 n)) v)))
  :enable (int-valuep int-min int-max)
  :use (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))

(defruledl int-mulpow-integerp-when-valuep
  (implies (int-valuep x signedp n)
           (integerp x))
  :enable int-valuep)

(defruled int-mulpow-abs-bits
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
        (:instance int-mulpow-mod-lebits=>int
                   (bits (lookup-equal-list axs asg)))
        (:instance int-mulpow-abs-valuep)
        (:instance int-mulpow-integerp-when-valuep (signedp t))
        (:instance int-width-add-fits)
        (:instance int-mulpow-bits-from-mod
                   (bits (lookup-equal-list axs asg))
                   (v (abs x))))
  :enable (int-abs-wrapped-signed-gadget
           integer-length-of-base-prime
           posp-when-integer-widthp
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits)
  :disable (abs))

(defruled int-mulpow-neg-bits
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
        (:instance int-mulpow-valuep-below)
        (:instance int-mulpow-valuep-below (v 0)))
  :enable (int-sub-wrapped-spec
           int->lebits-of-int-wrap
           posp-when-integer-widthp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The OR fold: acc | b0 = w0, w0 | b1 = w1, ...

(define int-mulpow-or-fold-gadget ((acc symbolp)
                                   (bits symbol-listp)
                                   (ws symbol-listp)
                                   (p primep))
  :guard (equal (len ws) (len bits))
  :verify-guards nil
  (if (endp bits)
      nil
    (append (boolean-or-gadget acc (car bits) (car ws) p)
            (int-mulpow-or-fold-gadget (car ws) (cdr bits) (cdr ws) p))))

(define int-mulpow-or-scan ((a bitp) (bs bit-listp))
  :verify-guards nil
  (if (endp bs)
      nil
    (cons (bitor a (car bs))
          (int-mulpow-or-scan (bitor a (car bs)) (cdr bs)))))

(defruled int-mulpow-or-fold-iff
  (implies (and (primep p)
                (symbolp acc)
                (symbol-listp bits)
                (symbol-listp ws)
                (equal (len ws) (len bits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg acc)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg ws)
                (bitp (lookup-equal acc asg))
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-or-fold-gadget acc bits ws p) asg p)
                  (equal (lookup-equal-list ws asg)
                         (int-mulpow-or-scan (lookup-equal acc asg)
                                             (lookup-equal-list bits asg)))))
  :induct (int-mulpow-or-fold-gadget acc bits ws p)
  :enable (int-mulpow-or-fold-gadget
           int-mulpow-or-scan
           boolean-or-gadget-to-bitor
           lookup-equal-list)
  :disable bitp)

(defruled int-mulpow-or-scan-last
  (implies (and (bitp a) (bit-listp bs) (consp bs))
           (equal (car (last (int-mulpow-or-scan a bs)))
                  (if (equal (lebits=>nat (cons a bs)) 0) 0 1)))
  :induct (int-mulpow-or-scan a bs)
  :enable (int-mulpow-or-scan bitor acl2::lebits=>nat-of-cons))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; List helpers.

(defruledl int-mulpow-lookup-equal-list-of-butlast
  (equal (lookup-equal-list (butlast l 1) asg)
         (butlast (lookup-equal-list l asg) 1))
  :induct (len l)
  :enable (lookup-equal-list butlast))

(defruledl int-mulpow-lookup-equal-list-of-cdr
  (equal (lookup-equal-list (cdr l) asg)
         (cdr (lookup-equal-list l asg)))
  :enable lookup-equal-list)

(defruledl int-mulpow-binds-allp-of-butlast
  (implies (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (butlast l 1)))
  :induct (len l)
  :enable (r1cs::valuation-binds-allp butlast))

(defruledl int-mulpow-binds-allp-of-cdr
  (implies (r1cs::valuation-binds-allp asg l)
           (r1cs::valuation-binds-allp asg (cdr l)))
  :enable r1cs::valuation-binds-allp)

(defruledl int-mulpow-symbol-listp-of-butlast
  (implies (symbol-listp l)
           (symbol-listp (butlast l 1)))
  :induct (len l)
  :enable butlast)

(defruledl int-mulpow-bindsp-of-car
  (implies (and (r1cs::valuation-binds-allp asg l) (consp l))
           (r1cs::valuation-bindsp asg (car l)))
  :enable r1cs::valuation-binds-allp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Bits of a product below 2^n: the top bit and the value of the others.

(defruledl int-mulpow-split-last
  (implies (and (bit-listp bits) (consp bits))
           (equal (lebits=>nat bits)
                  (+ (lebits=>nat (butlast bits 1))
                     (* (expt 2 (1- (len bits))) (car (last bits))))))
  :do-not-induct t
  :enable (lebits=>nat-of-last
           append-of-butlast-of-1-and-last
           len-of-butlast)
  :disable butlast
  :use ((:instance acl2::lebits=>nat-of-append
                   (lodigits (butlast bits 1))
                   (hidigits (last bits)))
        (:instance len-of-butlast (x bits) (n 1))))

(defruledl int-mulpow-consp-of-int->lebits
  (implies (posp n)
           (consp (int->lebits v n)))
  :use (:instance len-of-int->lebits (x v))
  :disable len-of-int->lebits)

(defrule int-mulpow-top-bit-facts
  :short "For @($0 \\le P < 2^n$), the top bit h and the value lo of
          the lower n-1 bits of @($P$) satisfy @($P = lo + 2^{n-1} h$)."
  (implies (and (posp n)
                (natp v)
                (< v (expt 2 n)))
           (b* ((bits (int->lebits v n))
                (h (car (last bits)))
                (lo (lebits=>nat (butlast bits 1))))
             (and (bitp h)
                  (natp lo)
                  (< lo (expt 2 (1- n)))
                  (equal v (+ lo (* (expt 2 (1- n)) h))))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-mulpow-split-last (bits (int->lebits v n)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (int->lebits v n)))
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (butlast (int->lebits v n) 1))))
  :enable (lebits=>nat-of-int->lebits
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           int-mulpow-consp-of-int->lebits
           len-of-butlast
           acl2::mod-when-<)
  :disable (butlast bitp))

(defrule int-mulpow-top-bit-arith
  (implies (and (posp n)
                (bitp h) (natp lo) (< lo (expt 2 (1- n)))
                (equal v (+ lo (* (expt 2 (1- n)) h))))
           (and (equal (equal h 0) (< v (expt 2 (1- n))))
                (equal (and (equal h 1) (equal lo 0))
                       (equal v (expt 2 (1- n))))))
  :rule-classes nil
  :cases ((equal h 0) (equal h 1))
  :enable bitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The gadget.

(define int-mulpow-assert-zero ((z symbolp))
  (r1cs::make-r1cs-constraint
   :a (list (list 1 z))
   :b (list (list 1 1))
   :c nil))

(defund int-mul-checked-signed-gadget
  (xs ys axs mxs cx ays mys cy z0 z2 m ps carry
   s lws po tt u v nps nc zs one p)
  (declare (xargs :verify-guards nil))
  (b* ((h (car (last ps)))
       (low (butlast ps 1)))
    (append (int-abs-wrapped-signed-gadget xs axs mxs cx one p)
            (int-abs-wrapped-signed-gadget ys ays mys cy one p)
            (int-mul-and-check-any-gadget axs ays z0 z2 m ps carry p)
            (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
            (boolean-and-notleft-gadget s h po one p)
            (list (int-mulpow-assert-zero po))
            (int-mulpow-or-fold-gadget (car low) (cdr low) lws p)
            (boolean-and-notright-gadget h (car (last lws)) tt one p)
            (boolean-or-notleft-gadget h tt u one p)
            (boolean-and-notright-gadget s u v one p)
            (list (int-mulpow-assert-zero v))
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits 0 (len xs)) ps nps nc one p)
            (int-mulpow-negsel-gadget s ps nps zs one p))))

(defund int-mulpow-sc-lens (n ys axs mxs ays mys ps carry lws nps zs)
  (and (equal (len ys) n)
       (equal (len axs) n) (equal (len mxs) n)
       (equal (len ays) n) (equal (len mys) n)
       (equal (len ps) n)
       (equal (len carry) (+ (floor n 2) 1))
       (equal (len lws) (- n 2))
       (equal (len nps) n)
       (equal (len zs) n)))

(defruled int-mulpow-sc-lens-ys
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len ys) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-axs
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len axs) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-mxs
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len mxs) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-ays
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len ays) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-mys
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len mys) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-ps
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len ps) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-carry
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len carry) (+ (floor n 2) 1)))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-lws
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len lws) (- n 2)))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-nps
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len nps) n))
  :enable int-mulpow-sc-lens)

(defruled int-mulpow-sc-lens-zs
  (implies (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
           (equal (len zs) n))
  :enable int-mulpow-sc-lens)

(deftheory int-mulpow-sc-lens-rules
  '(int-mulpow-sc-lens-ys int-mulpow-sc-lens-axs int-mulpow-sc-lens-mxs
    int-mulpow-sc-lens-ays int-mulpow-sc-lens-mys int-mulpow-sc-lens-ps
    int-mulpow-sc-lens-carry int-mulpow-sc-lens-lws int-mulpow-sc-lens-nps
    int-mulpow-sc-lens-zs))

(local (in-theory (enable int-mulpow-sc-lens-rules)))

(defmacro int-mulpow-sc-wire-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (symbol-listp xs) (symbol-listp ys)
        (symbol-listp axs) (symbol-listp mxs) (symbolp cx)
        (symbol-listp ays) (symbol-listp mys) (symbolp cy)
        (symbolp z0) (symbolp z2) (symbolp m)
        (symbol-listp ps) (symbol-listp carry)
        (symbolp s) (symbol-listp lws)
        (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
        (symbol-listp nps) (symbolp nc)
        (symbol-listp zs) (symbolp one)
        (equal n (len xs))
        (integer-widthp n)
        (int-mulpow-sc-lens n ys axs mxs ays mys ps carry lws nps zs)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg axs)
        (r1cs::valuation-binds-allp asg mxs)
        (r1cs::valuation-bindsp asg cx)
        (r1cs::valuation-binds-allp asg ays)
        (r1cs::valuation-binds-allp asg mys)
        (r1cs::valuation-bindsp asg cy)
        (r1cs::valuation-bindsp asg z0)
        (r1cs::valuation-bindsp asg z2)
        (r1cs::valuation-bindsp asg m)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg carry)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg lws)
        (r1cs::valuation-bindsp asg po)
        (r1cs::valuation-bindsp asg tt)
        (r1cs::valuation-bindsp asg u)
        (r1cs::valuation-bindsp asg v)
        (r1cs::valuation-binds-allp asg nps)
        (r1cs::valuation-bindsp asg nc)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (int-valuep x t n)
        (int-valuep y t n)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ys asg) (int->lebits y n))))

(defmacro int-mulpow-sc-hyps ()
  '(and (int-mulpow-sc-wire-hyps)
        (r1cs::r1cs-constraints-holdp
         (int-mul-checked-signed-gadget
          xs ys axs mxs cx ays mys cy z0 z2 m ps carry
          s lws po tt u v nps nc zs one p)
         asg p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers.

(defruledl int-mulpow-sc-width-facts
  (implies (integer-widthp n)
           (and (posp n)
                (<= 8 n)
                (integerp (+ -2 n))
                (posp (+ -2 n))
                (< 1 (+ -1 n))))
  :enable integer-widthp)

(defruledl int-mulpow-sc-product-valuep
  (implies (and (int-valuep a nil n) (int-valuep b nil n)
                (not (equal (int-mul-checked-spec a b nil n) (spec-error))))
           (and (int-valuep (* a b) nil n)
                (equal (int-mul-checked-spec a b nil n) (* a b))))
  :enable (int-mul-checked-spec int-valuep))

(defruledl int-mulpow-sc-valuep-nil
  (implies (and (posp n) (int-valuep v nil n))
           (and (natp v) (< v (expt 2 n))))
  :enable (int-valuep int-min int-max))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Soundness steps.

(defruledl int-mulpow-holdp-of-singleton
  (equal (r1cs::r1cs-constraints-holdp (list c) asg p)
         (r1cs::r1cs-constraint-holdsp c asg p))
  :enable r1cs::r1cs-constraints-holdp)

(defruledl int-mulpow-sc-parts
  (implies (r1cs::r1cs-constraints-holdp
            (int-mul-checked-signed-gadget
             xs ys axs mxs cx ays mys cy z0 z2 m ps carry
             s lws po tt u v nps nc zs one p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget ys ays mys cy one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-any-gadget axs ays z0 z2 m ps carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget s (car (last ps)) po one p)
                 asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero po) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                            (cdr (butlast ps 1)) lws p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget (car (last ps)) (car (last lws))
                                              tt one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget (car (last ps)) tt u one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget s u v one p) asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero v) asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 (len xs)) ps nps nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-negsel-gadget s ps nps zs one p) asg p)))
  :in-theory (union-theories '(int-mul-checked-signed-gadget
                               r1cs::r1cs-constraints-holdp-of-append
                               int-mulpow-holdp-of-singleton)
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-step-ax
  (implies (int-mulpow-sc-hyps)
           (and (equal (lookup-equal-list axs asg) (int->lebits (abs x) n))
                (equal (lookup-equal-list ays asg) (int->lebits (abs y) n))))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        (:instance int-mulpow-abs-bits)
        (:instance int-mulpow-abs-bits
                   (xs ys) (axs ays) (mxs mys) (cx cy) (x y)))
  :in-theory (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory)))

(defruledl int-mulpow-lookup-equal-of-car-of-last
  (implies (consp l)
           (equal (lookup-equal (car (last l)) asg)
                  (car (last (lookup-equal-list l asg)))))
  :induct (len l)
  :enable lookup-equal-list)

(defruledl int-mulpow-sc-step-ps
  (implies (int-mulpow-sc-hyps)
           (and (int-valuep (* (abs x) (abs y)) nil n)
                (equal (lookup-equal-list ps asg)
                       (int->lebits (* (abs x) (abs y)) n))))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        int-mulpow-sc-step-ax
        (:instance int-mulpow-abs-valuep)
        (:instance int-mulpow-abs-valuep (x y))
        (:instance int-mul-and-check-any-gadget-sound
                   (xs axs) (ys ays) (zs ps)
                   (x (abs x)) (y (abs y)) (signedp nil))
        (:instance int-mul-and-check-spec-is-mul-checked-when-unsigned
                   (x (abs x)) (y (abs y)))
        (:instance int-mulpow-sc-product-valuep (a (abs x)) (b (abs y))))
  :in-theory (union-theories '(posp-when-integer-widthp)
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-car-last-facts
  (implies (and (symbol-listp l) (consp l) (r1cs::valuation-binds-allp asg l))
           (and (symbolp (car (last l)))
                (r1cs::valuation-bindsp asg (car (last l)))))
  :induct (len l)
  :enable r1cs::valuation-binds-allp)

(defruledl int-mulpow-consp-when-len
  (implies (and (equal n (len l)) (posp n))
           (consp l)))

(defruledl int-mulpow-sc-step-s
  (implies (int-mulpow-sc-hyps)
           (equal (lookup-equal s asg)
                  (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0))))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        (:instance int-signed-msb)
        (:instance int-signed-msb (x y))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l xs))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l ys))
        (:instance int-mulpow-car-last-facts (l xs))
        (:instance int-mulpow-car-last-facts (l ys))
        (:instance int-mulpow-consp-when-len (l xs))
        (:instance int-mulpow-consp-when-len (l ys))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs))) (y (car (last ys))) (z s)))
  :in-theory (union-theories '(posp-when-integer-widthp (:e bitp))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-bit-listp-of-butlast
  (implies (bit-listp l)
           (bit-listp (butlast l 1)))
  :induct (len l)
  :enable butlast)

(defruledl int-mulpow-bitp-of-car
  (implies (and (bit-listp l) (consp l))
           (bitp (car l))))

(defruledl int-mulpow-len-of-cdr
  (implies (consp l)
           (equal (len (cdr l)) (+ -1 (len l)))))

(defruledl int-mulpow-low-bits-or-iff
  (implies (and (primep p)
                (symbol-listp ps) (symbol-listp lws)
                (natp n) (< 2 n)
                (equal (len ps) n)
                (equal (len lws) (- n 2))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg lws)
                (bit-listp (lookup-equal-list ps asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                              (cdr (butlast ps 1)) lws p)
                   asg p)
                  (equal (lookup-equal-list lws asg)
                         (int-mulpow-or-scan
                          (car (butlast (lookup-equal-list ps asg) 1))
                          (cdr (butlast (lookup-equal-list ps asg) 1))))))
  :do-not-induct t
  :use ((:instance int-mulpow-or-fold-iff
                   (acc (car (butlast ps 1)))
                   (bits (cdr (butlast ps 1)))
                   (ws lws))
        (:instance len-of-butlast (x ps) (n 1))
        (:instance int-mulpow-len-of-cdr (l (butlast ps 1)))
        (:instance int-mulpow-bindsp-of-car (l (butlast ps 1)))
        (:instance lookup-equal-of-car (keys (butlast ps 1)) (alist asg))
        (:instance int-mulpow-bit-listp-of-butlast
                   (l (lookup-equal-list ps asg)))
        (:instance len-of-butlast (x (lookup-equal-list ps asg)) (n 1))
        (:instance int-mulpow-bitp-of-car
                   (l (butlast (lookup-equal-list ps asg) 1))))
  :enable (int-mulpow-lookup-equal-list-of-butlast
           int-mulpow-lookup-equal-list-of-cdr
           int-mulpow-binds-allp-of-butlast
           int-mulpow-binds-allp-of-cdr
           int-mulpow-symbol-listp-of-butlast)
  :disable (butlast int-mulpow-or-fold-gadget int-mulpow-or-scan))

(defruledl int-mulpow-low-bits-or-last
  (implies (and (natp n) (< 2 n)
                (bit-listp bits)
                (equal (len bits) n)
                (equal (len lws) (- n 2))
                (equal (lookup-equal-list lws asg)
                       (int-mulpow-or-scan (car (butlast bits 1))
                                           (cdr (butlast bits 1)))))
           (equal (lookup-equal (car (last lws)) asg)
                  (if (equal (lebits=>nat (butlast bits 1)) 0) 0 1)))
  :do-not-induct t
  :use ((:instance int-mulpow-or-scan-last
                   (a (car (butlast bits 1)))
                   (bs (cdr (butlast bits 1))))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l lws))
        (:instance len-of-butlast (x bits) (n 1))
        (:instance int-mulpow-len-of-cdr (l (butlast bits 1)))
        (:instance int-mulpow-bit-listp-of-butlast (l bits)))
  :disable (butlast int-mulpow-or-scan))

(defruledl int-mulpow-chain-iff
  (implies (and (primep p)
                (symbolp s) (symbolp hw) (symbolp lw) (symbolp po)
                (symbolp tt) (symbolp u) (symbolp v) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-bindsp asg hw)
                (r1cs::valuation-bindsp asg lw)
                (r1cs::valuation-bindsp asg po)
                (r1cs::valuation-bindsp asg tt)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bitp (lookup-equal s asg))
                (bitp (lookup-equal hw asg))
                (bitp (lookup-equal lw asg)))
           (b* ((s$ (lookup-equal s asg))
                (h$ (lookup-equal hw asg))
                (l$ (lookup-equal lw asg))
                (tt$ (if (and (equal h$ 1) (equal l$ 0)) 1 0)))
             (equal (and (r1cs::r1cs-constraints-holdp
                          (boolean-and-notleft-gadget s hw po one p) asg p)
                         (r1cs::r1cs-constraint-holdsp
                          (int-mulpow-assert-zero po) asg p)
                         (r1cs::r1cs-constraints-holdp
                          (boolean-and-notright-gadget hw lw tt one p) asg p)
                         (r1cs::r1cs-constraints-holdp
                          (boolean-or-notleft-gadget hw tt u one p) asg p)
                         (r1cs::r1cs-constraints-holdp
                          (boolean-and-notright-gadget s u v one p) asg p)
                         (r1cs::r1cs-constraint-holdsp
                          (int-mulpow-assert-zero v) asg p))
                    (and (implies (equal s$ 0) (equal h$ 0))
                         (or (equal h$ 0) (equal l$ 0))
                         (equal (lookup-equal po asg) 0)
                         (equal (lookup-equal tt asg) tt$)
                         (equal (lookup-equal u asg) 1)
                         (equal (lookup-equal v asg) 0)))))
  :do-not-induct t
  :use ((:instance boolean-and-notleft-gadget-to-booland-boolnot
                   (x s) (y hw) (z po))
        (:instance int-mulpow-zero-constraint (z po))
        (:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x hw) (y lw) (z tt))
        (:instance boolean-or-notleft-gadget-to-boolor-boolnot
                   (x hw) (y tt) (z u))
        (:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x s) (y u) (z v))
        (:instance int-mulpow-zero-constraint (z v)))
  :enable (int-mulpow-assert-zero bitp))

(defruledl int-mulpow-sc-step-bits
  (implies (int-mulpow-sc-hyps)
           (b* ((pv (* (abs x) (abs y)))
                (bits (int->lebits pv n)))
             (and (natp pv)
                  (< pv (expt 2 n))
                  (bit-listp bits)
                  (equal (len bits) n)
                  (bitp (car (last bits)))
                  (equal (lookup-equal (car (last ps)) asg)
                         (car (last bits))))))
  :do-not-induct t
  :use (int-mulpow-sc-step-ps
        (:instance int-mulpow-sc-valuep-nil (v (* (abs x) (abs y))))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l ps))
        (:instance int-mulpow-consp-when-len (l ps))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (int->lebits (* (abs x) (abs y)) n)))
        (:instance int-mulpow-consp-of-int->lebits (v (* (abs x) (abs y))))
        (:instance len-of-int->lebits (x (* (abs x) (abs y))))
        (:instance bit-listp-of-int->lebits-explicit (x (* (abs x) (abs y)))))
  :in-theory (union-theories '(posp-when-integer-widthp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-step-lws
  (implies (int-mulpow-sc-hyps)
           (equal (lookup-equal (car (last lws)) asg)
                  (if (equal (lebits=>nat
                              (butlast (int->lebits (* (abs x) (abs y)) n) 1))
                             0)
                      0 1)))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        int-mulpow-sc-step-ps
        int-mulpow-sc-step-bits
        int-mulpow-sc-width-facts
        (:instance int-mulpow-low-bits-or-iff)
        (:instance int-mulpow-low-bits-or-last
                   (bits (int->lebits (* (abs x) (abs y)) n))))
  :in-theory (union-theories '(posp-when-integer-widthp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-step-chain
  (implies (int-mulpow-sc-hyps)
           (b* ((bits (int->lebits (* (abs x) (abs y)) n))
                (h (car (last bits)))
                (lo (lebits=>nat (butlast bits 1)))
                (sv (lookup-equal s asg)))
             (and (implies (equal sv 0) (equal h 0))
                  (or (equal h 0) (equal lo 0)))))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        int-mulpow-sc-step-s
        int-mulpow-sc-step-bits
        int-mulpow-sc-step-lws
        (:instance int-mulpow-consp-when-len (l ps))
        (:instance int-mulpow-consp-when-len (l lws) (n (- (len xs) 2)))
        int-mulpow-sc-width-facts
        (:instance int-mulpow-car-last-facts (l ps))
        (:instance int-mulpow-car-last-facts (l lws))
        (:instance int-mulpow-chain-iff
                   (hw (car (last ps))) (lw (car (last lws)))))
  :in-theory (union-theories '(posp-when-integer-widthp
                               bitp bitxor (:e bitp)
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-step-bounds
  (implies (int-mulpow-sc-hyps)
           (b* ((pv (* (abs x) (abs y))))
             (and (<= pv (expt 2 (1- n)))
                  (implies (equal (lookup-equal s asg) 0)
                           (< pv (expt 2 (1- n)))))))
  :do-not-induct t
  :use (int-mulpow-sc-step-bits
        int-mulpow-sc-step-chain
        (:instance int-mulpow-top-bit-facts (v (* (abs x) (abs y))))
        (:instance int-mulpow-top-bit-arith
                   (v (* (abs x) (abs y)))
                   (h (car (last (int->lebits (* (abs x) (abs y)) n))))
                   (lo (lebits=>nat
                        (butlast (int->lebits (* (abs x) (abs y)) n) 1)))))
  :in-theory (union-theories '(posp-when-integer-widthp bitp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-step-zs
  (implies (int-mulpow-sc-hyps)
           (equal (lookup-equal-list zs asg)
                  (int->lebits (if (equal (lookup-equal s asg) 0)
                                   (* (abs x) (abs y))
                                 (- (* (abs x) (abs y))))
                               n)))
  :do-not-induct t
  :use (int-mulpow-sc-parts
        int-mulpow-sc-step-ps
        int-mulpow-sc-step-s
        int-mulpow-sc-step-bits
        int-mulpow-sc-step-bounds
        (:instance len-of-int->lebits (x 0))
        (:instance int-mulpow-neg-bits
                   (vs ps) (nvs nps) (v (* (abs x) (abs y))))
        (:instance int-mulpow-negsel-gadget-iff
                   (c s) (xs ps) (ys nps)
                   (x (* (abs x) (abs y)))
                   (y (- (* (abs x) (abs y))))))
  :in-theory (union-theories '(posp-when-integer-widthp bitp bitxor (:e bitp)
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-final-arith
  (implies (and (integerp x) (integerp y) (posp n)
                (equal sv (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
                (<= (* (abs x) (abs y)) (expt 2 (1- n)))
                (implies (equal sv 0)
                         (< (* (abs x) (abs y)) (expt 2 (1- n)))))
           (and (int-valuep (* x y) t n)
                (equal (if (equal sv 0)
                           (* (abs x) (abs y))
                         (- (* (abs x) (abs y))))
                       (* x y))))
  :cases ((and (< x 0) (< y 0))
          (and (< x 0) (<= 0 y))
          (and (<= 0 x) (< y 0)))
  :hints (("Goal" :in-theory (enable int-valuep int-min int-max bitxor))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defrulel int-mulpow-sc-final-spec
  (implies (and (integerp x) (integerp y) (int-valuep (* x y) t n))
           (and (not (equal (int-mul-checked-spec x y t n) (spec-error)))
                (equal (int-mul-checked-spec x y t n) (* x y))))
  :rule-classes nil
  :enable (int-mul-checked-spec int-valuep spec-error))

(defruled int-mul-checked-signed-gadget-sound
  :short "Signed mul_checked (Mul, MulAssign), every width 8 to 128: given
          Integer::new operands, the constraints imply the product is in
          range and force the output bits to it."
  (implies (int-mulpow-sc-hyps)
           (and (not (equal (int-mul-checked-spec x y t n) (spec-error)))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-mul-checked-spec x y t n) n))))
  :do-not-induct t
  :use (int-mulpow-sc-step-s
        int-mulpow-sc-step-bounds
        int-mulpow-sc-step-zs
        (:instance int-mulpow-integerp-when-valuep (signedp t))
        (:instance int-mulpow-integerp-when-valuep (x y) (signedp t))
        (:instance int-mulpow-sc-final-arith (sv (lookup-equal s asg)))
        (:instance int-mulpow-sc-final-spec))
  :in-theory (union-theories '(posp-when-integer-widthp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Completeness.

(defruledl int-mulpow-sc-unparts
  (implies (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget ys ays mys cy one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-and-check-any-gadget axs ays z0 z2 m ps carry p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget s (car (last ps)) po one p)
                 asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero po) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                            (cdr (butlast ps 1)) lws p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget (car (last ps)) (car (last lws))
                                              tt one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget (car (last ps)) tt u one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget s u v one p) asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero v) asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 (len xs)) ps nps nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mulpow-negsel-gadget s ps nps zs one p) asg p))
           (r1cs::r1cs-constraints-holdp
            (int-mul-checked-signed-gadget
             xs ys axs mxs cx ays mys cy z0 z2 m ps carry
             s lws po tt u v nps nc zs one p)
            asg p))
  :in-theory (union-theories '(int-mul-checked-signed-gadget
                               r1cs::r1cs-constraints-holdp-of-append
                               int-mulpow-holdp-of-singleton)
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-abs-wrapped-bits
  (implies (posp n)
           (equal (int->lebits (int-abs-wrapped-spec x t n) n)
                  (int->lebits (abs (ifix x)) n)))
  :enable (int-abs-wrapped-spec int->lebits-of-int-wrap))

(defruledl int-mulpow-sc-complete-arith
  (implies (and (integerp x) (integerp y) (posp n)
                (int-valuep (* x y) t n))
           (and (<= (* (abs x) (abs y)) (expt 2 (1- n)))
                (implies (equal (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)) 0)
                         (< (* (abs x) (abs y)) (expt 2 (1- n))))
                (equal (if (equal (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)) 0)
                           (* (abs x) (abs y))
                         (- (* (abs x) (abs y))))
                       (* x y))))
  :cases ((and (< x 0) (< y 0))
          (and (< x 0) (<= 0 y))
          (and (<= 0 x) (< y 0)))
  :hints (("Goal" :in-theory (enable int-valuep int-min int-max bitxor))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defruledl int-mulpow-sc-spec-ok
  (implies (and (int-valuep x t n) (int-valuep y t n)
                (not (equal (int-mul-checked-spec x y t n) (spec-error))))
           (int-valuep (* x y) t n))
  :enable (int-mul-checked-spec int-valuep))

(defruledl int-mulpow-sc-nc-value
  (implies (and (natp v) (< v (expt 2 n)) (natp n))
           (equal (if (< (mod 0 (expt 2 n)) (mod v (expt 2 n))) 0 1)
                  (if (equal v 0) 1 0))))

(defruledl int-mulpow-sc-sub-spec
  (implies (and (posp n) (natp v))
           (equal (int->lebits (int-sub-wrapped-spec 0 v nil n) n)
                  (int->lebits (- v) n)))
  :enable (int-sub-wrapped-spec int->lebits-of-int-wrap))

(defmacro int-mulpow-sc-complete-hyps ()
  '(and (int-mulpow-sc-wire-hyps)
        (not (equal (int-mul-checked-spec x y t n) (spec-error)))
        (equal (lookup-equal-list axs asg) (int->lebits (abs x) n))
        (equal (lookup-equal-list mxs asg) (int->lebits (- x) n))
        (equal (lookup-equal cx asg) (int-sub-carry 0 x n))
        (equal (lookup-equal-list ays asg) (int->lebits (abs y) n))
        (equal (lookup-equal-list mys asg) (int->lebits (- y) n))
        (equal (lookup-equal cy asg) (int-sub-carry 0 y n))
        (implies (equal n 128)
                 (and (equal (lookup-equal z0 asg)
                             (* (int-mulpow-lo (abs x) n)
                                (int-mulpow-lo (abs y) n)))
                      (equal (lookup-equal z2 asg)
                             (* (int-mulpow-hi (abs x) n)
                                (int-mulpow-hi (abs y) n)))
                      (equal (lookup-equal m asg)
                             (* (+ (int-mulpow-hi (abs x) n)
                                   (int-mulpow-lo (abs x) n))
                                (+ (int-mulpow-hi (abs y) n)
                                   (int-mulpow-lo (abs y) n))))
                      (equal (lookup-equal-list carry asg)
                             (second (int-karatsuba-multiply-spec
                                      (abs x) (abs y) nil n)))))
        (equal (lookup-equal-list ps asg)
               (int->lebits (* (abs x) (abs y)) n))
        (equal (lookup-equal s asg)
               (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0)))
        (equal (lookup-equal-list lws asg)
               (int-mulpow-or-scan
                (car (butlast (int->lebits (* (abs x) (abs y)) n) 1))
                (cdr (butlast (int->lebits (* (abs x) (abs y)) n) 1))))
        (equal (lookup-equal po asg) 0)
        (equal (lookup-equal tt asg)
               (if (equal (* (abs x) (abs y)) (expt 2 (1- n))) 1 0))
        (equal (lookup-equal u asg) 1)
        (equal (lookup-equal v asg) 0)
        (equal (lookup-equal-list nps asg)
               (int->lebits (- (* (abs x) (abs y))) n))
        (equal (lookup-equal nc asg)
               (if (equal (* (abs x) (abs y)) 0) 1 0))
        (equal (lookup-equal-list zs asg) (int->lebits (* x y) n))))

(defruledl int-mulpow-sc-c-arith
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (not (equal (int-mul-checked-spec x y t n) (spec-error))))
           (b* ((pv (* (abs x) (abs y)))
                (sv (bitxor (if (< x 0) 1 0) (if (< y 0) 1 0))))
             (and (posp n)
                  (integerp x) (integerp y)
                  (int-valuep (* x y) t n)
                  (natp pv)
                  (<= pv (expt 2 (1- n)))
                  (< pv (expt 2 n))
                  (int-valuep pv nil n)
                  (implies (equal sv 0) (< pv (expt 2 (1- n))))
                  (equal (if (equal sv 0) pv (- pv)) (* x y)))))
  :do-not-induct t
  :use ((:instance int-mulpow-integerp-when-valuep (signedp t))
        (:instance int-mulpow-integerp-when-valuep (x y) (signedp t))
        int-mulpow-sc-spec-ok
        int-mulpow-sc-complete-arith
        (:instance int-mulpow-valuep-below (v (* (abs x) (abs y))))
        (:instance acl2::expt-of-+ (acl2::r 2) (acl2::i1 (1- n)) (acl2::i2 1)))
  :enable posp-when-integer-widthp
  :disable (integer-widthp abs bitxor int-valuep))

(defrulel int-mulpow-sc-unsigned-spec
  (implies (and (integerp a) (integerp b) (int-valuep (* a b) nil n))
           (and (not (equal (int-mul-checked-spec a b nil n) (spec-error)))
                (equal (int-mul-checked-spec a b nil n) (* a b))))
  :enable (int-mul-checked-spec int-valuep spec-error))

(defruledl int-mulpow-sc-c-abs
  (implies (int-mulpow-sc-complete-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget ys ays mys cy one p) asg p)))
  :do-not-induct t
  :use (int-mulpow-sc-c-arith
        (:instance int-mulpow-consp-when-len (l xs))
        (:instance int-mulpow-consp-when-len (l ys))
        (:instance int-mulpow-sc-abs-wrapped-bits)
        (:instance int-mulpow-sc-abs-wrapped-bits (x y))
        (:instance int-abs-wrapped-signed-gadget-complete
                   (ys axs) (minus-xs mxs) (carry cx))
        (:instance int-abs-wrapped-signed-gadget-complete
                   (xs ys) (x y) (ys ays) (minus-xs mys) (carry cy)))
  :in-theory (union-theories '(posp-when-integer-widthp ifix
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-c-mul
  (implies (int-mulpow-sc-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mul-and-check-any-gadget axs ays z0 z2 m ps carry p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sc-c-arith
        (:instance int-mulpow-abs-valuep)
        (:instance int-mulpow-abs-valuep (x y))
        (:instance int-mul-and-check-spec-is-mul-checked-when-unsigned
                   (x (abs x)) (y (abs y)))
        (:instance int-mulpow-sc-unsigned-spec (a (abs x)) (b (abs y)))
        (:instance int-mul-and-check-any-gadget-complete
                   (xs axs) (ys ays) (zs ps)
                   (x (abs x)) (y (abs y)) (signedp nil)))
  :in-theory (union-theories '(posp-when-integer-widthp natp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-c-xor
  (implies (int-mulpow-sc-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last xs)) (car (last ys)) s p)
            asg p))
  :do-not-induct t
  :use ((:instance int-signed-msb)
        (:instance int-signed-msb (x y))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l xs))
        (:instance int-mulpow-lookup-equal-of-car-of-last (l ys))
        (:instance int-mulpow-car-last-facts (l xs))
        (:instance int-mulpow-car-last-facts (l ys))
        (:instance int-mulpow-consp-when-len (l xs))
        (:instance int-mulpow-consp-when-len (l ys))
        (:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs))) (y (car (last ys))) (z s)))
  :in-theory (union-theories '(posp-when-integer-widthp (:e bitp))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-bits-generic
  (implies (and (posp n)
                (natp pv)
                (equal (len ps) n)
                (equal (lookup-equal-list ps asg) (int->lebits pv n)))
           (b* ((bits (int->lebits pv n)))
             (and (bit-listp bits)
                  (equal (len bits) n)
                  (bitp (car (last bits)))
                  (bit-listp (lookup-equal-list ps asg))
                  (equal (lookup-equal (car (last ps)) asg)
                         (car (last bits))))))
  :do-not-induct t
  :use ((:instance int-mulpow-lookup-equal-of-car-of-last (l ps))
        (:instance int-mulpow-consp-when-len (l ps))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (int->lebits pv n)))
        (:instance int-mulpow-consp-of-int->lebits (v pv))
        (:instance len-of-int->lebits (x pv))
        (:instance bit-listp-of-int->lebits-explicit (x pv)))
  :disable (bitp int->lebits))

(defruledl int-mulpow-chain-complete-generic
  (implies (and (primep p)
                (symbolp s) (symbolp hw) (symbolp lw) (symbolp po)
                (symbolp tt) (symbolp u) (symbolp v) (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-bindsp asg hw)
                (r1cs::valuation-bindsp asg lw)
                (r1cs::valuation-bindsp asg po)
                (r1cs::valuation-bindsp asg tt)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (posp n)
                (natp pv)
                (<= pv (expt 2 (1- n)))
                (< pv (expt 2 n))
                (bitp (lookup-equal s asg))
                (implies (equal (lookup-equal s asg) 0)
                         (< pv (expt 2 (1- n))))
                (equal (lookup-equal hw asg) (car (last (int->lebits pv n))))
                (equal (lookup-equal lw asg)
                       (if (equal (lebits=>nat (butlast (int->lebits pv n) 1)) 0)
                           0 1))
                (equal (lookup-equal po asg) 0)
                (equal (lookup-equal tt asg)
                       (if (equal pv (expt 2 (1- n))) 1 0))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal v asg) 0))
           (and (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget s hw po one p) asg p)
                (r1cs::r1cs-constraint-holdsp
                 (int-mulpow-assert-zero po) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget hw lw tt one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget hw tt u one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget s u v one p) asg p)
                (r1cs::r1cs-constraint-holdsp
                 (int-mulpow-assert-zero v) asg p)))
  :do-not-induct t
  :use ((:instance int-mulpow-top-bit-facts (v pv))
        (:instance int-mulpow-top-bit-arith
                   (v pv)
                   (h (car (last (int->lebits pv n))))
                   (lo (lebits=>nat (butlast (int->lebits pv n) 1))))
        (:instance int-mulpow-chain-iff))
  :disable (int->lebits butlast bitp
            boolean-and-notleft-gadget boolean-and-notright-gadget
            boolean-or-notleft-gadget int-mulpow-assert-zero))

(defruledl int-mulpow-sc-c-sub
  (implies (int-mulpow-sc-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (unsigned-small-sub-wrapped-const-var-gadget
             (int->lebits 0 (len xs)) ps nps nc one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sc-c-arith
        (:instance int-mulpow-valuep-below (v 0))
        (:instance int-mulpow-sc-sub-spec (v (* (abs x) (abs y))))
        (:instance int-mulpow-sc-nc-value (v (* (abs x) (abs y))))
        (:instance int-divshift-sub-wrapped-const-var-complete
                   (x 0) (y (* (abs x) (abs y))) (ys ps) (zs nps) (z nc)
                   (signedp nil)))
  :in-theory (union-theories '(posp-when-integer-widthp (:e booleanp) (:e natp)
                               (:e expt) (:e unary--) (:e binary-+)
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-sc-c-negsel
  (implies (int-mulpow-sc-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mulpow-negsel-gadget s ps nps zs one p) asg p))
  :do-not-induct t
  :use (int-mulpow-sc-c-arith
        (:instance int-mulpow-negsel-gadget-iff
                   (c s) (xs ps) (ys nps)
                   (x (* (abs x) (abs y)))
                   (y (- (* (abs x) (abs y))))))
  :in-theory (union-theories '(posp-when-integer-widthp bitp bitxor (:e bitp)
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules) (theory 'minimal-theory))))

(defruledl int-mulpow-bitp-of-bitxor-ifs
  (bitp (bitxor (if a 1 0) (if b 1 0)))
  :enable bitxor)

(defruledl int-mulpow-chain-complete-generic2
  (implies (and (primep p)
                (symbol-listp ps) (symbol-listp lws)
                (symbolp s) (symbolp po) (symbolp tt) (symbolp u) (symbolp v)
                (symbolp one)
                (natp n) (< 2 n)
                (equal (len ps) n)
                (equal (len lws) (- n 2))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg lws)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-bindsp asg po)
                (r1cs::valuation-bindsp asg tt)
                (r1cs::valuation-bindsp asg u)
                (r1cs::valuation-bindsp asg v)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (natp pv)
                (<= pv (expt 2 (1- n)))
                (< pv (expt 2 n))
                (bitp (lookup-equal s asg))
                (implies (equal (lookup-equal s asg) 0)
                         (< pv (expt 2 (1- n))))
                (equal (lookup-equal-list ps asg) (int->lebits pv n))
                (equal (lookup-equal-list lws asg)
                       (int-mulpow-or-scan
                        (car (butlast (int->lebits pv n) 1))
                        (cdr (butlast (int->lebits pv n) 1))))
                (equal (lookup-equal po asg) 0)
                (equal (lookup-equal tt asg)
                       (if (equal pv (expt 2 (1- n))) 1 0))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal v asg) 0))
           (and (r1cs::r1cs-constraints-holdp
                 (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                            (cdr (butlast ps 1)) lws p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget s (car (last ps)) po one p)
                 asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero po) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget (car (last ps)) (car (last lws))
                                              tt one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget (car (last ps)) tt u one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget s u v one p) asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero v) asg p)))
  :do-not-induct t
  :use ((:instance int-mulpow-bits-generic)
        (:instance int-mulpow-low-bits-or-iff)
        (:instance int-mulpow-low-bits-or-last (bits (int->lebits pv n)))
        (:instance int-mulpow-consp-when-len (l ps))
        (:instance int-mulpow-consp-when-len (l lws) (n (- n 2)))
        (:instance int-mulpow-car-last-facts (l ps))
        (:instance int-mulpow-car-last-facts (l lws))
        (:instance int-mulpow-chain-complete-generic
                   (hw (car (last ps))) (lw (car (last lws)))))
  :in-theory (union-theories '(posp natp (:e bitp) (:e expt) (:e binary-+)
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (theory 'minimal-theory)))

(defruledl int-mulpow-sc-c-chain
  (implies (int-mulpow-sc-complete-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-mulpow-or-fold-gadget (car (butlast ps 1))
                                            (cdr (butlast ps 1)) lws p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget s (car (last ps)) po one p)
                 asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero po) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget (car (last ps)) (car (last lws))
                                              tt one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-notleft-gadget (car (last ps)) tt u one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget s u v one p) asg p)
                (r1cs::r1cs-constraint-holdsp (int-mulpow-assert-zero v) asg p)))
  :do-not-induct t
  :use (int-mulpow-sc-c-arith
        int-mulpow-sc-width-facts
        (:instance int-mulpow-bitp-of-bitxor-ifs (a (< x 0)) (b (< y 0)))
        (:instance int-mulpow-chain-complete-generic2
                   (pv (* (abs x) (abs y)))))
  :in-theory (union-theories '(posp-when-integer-widthp
                               (:compound-recognizer acl2::natp-compound-recognizer)
                               (:compound-recognizer acl2::posp-compound-recognizer))
                             (union-theories (theory 'int-mulpow-sc-lens-rules)
                                             (theory 'minimal-theory))))

(defruled int-mul-checked-signed-gadget-complete
  :short "Signed mul_checked (Mul, MulAssign), every width 8 to 128: when
          the product is in range, the honest witnesses satisfy the
          constraints.  The Karatsuba witnesses are only read for 128 bits."
  (implies (int-mulpow-sc-complete-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mul-checked-signed-gadget
             xs ys axs mxs cx ays mys cy z0 z2 m ps carry
             s lws po tt u v nps nc zs one p)
            asg p))
  :do-not-induct t
  :use (int-mulpow-sc-unparts
        int-mulpow-sc-c-abs
        int-mulpow-sc-c-mul
        int-mulpow-sc-c-xor
        int-mulpow-sc-c-chain
        int-mulpow-sc-c-sub
        int-mulpow-sc-c-negsel)
  :in-theory (theory 'minimal-theory))
