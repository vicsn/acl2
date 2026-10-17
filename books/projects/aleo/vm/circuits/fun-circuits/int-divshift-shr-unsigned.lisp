; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode unsigned shr_wrapped and shr_checked (and shr, shr_assign)
; for every width other than 128.
;
; The unsigned right shift is a left shift of the bit-reversed value.
; The first select weighs the value bits big-endian, which over the same
; bits is the little-endian weighing of the reversed wires, so the
; constraints are equivalent to int-shl-wrapped-gadget over (rev xs).  The
; left-shift soundness and completeness then give the 2n result bits of
; R * 2^s, with R the reversal of x and s = e mod n, and the low n of them
; reversed are the bits of floor(x / 2^s).

(in-package "ALEOVM")

(include-book "int-divshift-shift-sound")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-dot-be-vector
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::dot-product (int-be-pow2sum-vector xs w) asg p)
                  (mod (int-be-weighted (lookup-equal-list xs asg) w) p)))
  :induct (int-be-pow2sum-vector xs w)
  :enable (int-be-pow2sum-vector
           int-be-weighted
           r1cs::dot-product
           lookup-equal-list
           r1cs::valuation-binds-allp
           pfield::add
           pfield::mul
           bit-listp))

(defruledl int-divshift-be-weighted-rev
  (implies (bit-listp vals)
           (equal (int-be-weighted vals (1- (len vals)))
                  (lebits=>nat (rev vals))))
  :induct (len vals)
  :enable (int-be-weighted
           rev
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           bit-listp))

(defruledl int-divshift-binds-allp-of-rev
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (rev xs)))
  :induct (len xs)
  :enable (rev r1cs::valuation-binds-allp
           r1cs::valuation-binds-allp-of-append))

(defruledl int-divshift-len-pos-when-consp
  (implies (consp x) (< 0 (len x))))

(defruledl int-divshift-dot-be-is-rev
  (implies (and (symbol-listp xs)
                (consp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::dot-product
                   (int-be-pow2sum-vector xs (nfix (1- (len xs)))) asg p)
                  (r1cs::dot-product (pow2sum-vector (rev xs) 0) asg p)))
  :do-not-induct t
  :use ((:instance int-divshift-dot-be-vector (w (nfix (1- (len xs)))))
        (:instance int-divshift-be-weighted-rev
                   (vals (lookup-equal-list xs asg)))
        (:instance pow2sum-vector-to-mod-of-lebits=>nat
                   (xs (rev xs)) (i 0)))
  :enable (lookup-equal-list-of-rev len-of-lookup-equal-list nfix
           int-divshift-binds-allp-of-rev int-divshift-len-pos-when-consp)
  :disable (int-divshift-dot-be-vector int-divshift-be-weighted-rev
            pow2sum-vector-to-mod-of-lebits=>nat))

(defruledl int-divshift-dot-of-cons-single
  (implies (and (syntaxp (not (equal rest ''nil)))
                (posp p))
           (equal (r1cs::dot-product (cons (list 1 v) rest) asg p)
                  (pfield::add (r1cs::dot-product (list (list 1 v)) asg p)
                               (r1cs::dot-product rest asg p)
                               p)))
  :use (:instance r1cs::dot-product-of-append
                  (r1cs::vec1 (list (list 1 v))) (r1cs::vec2 rest)
                  (r1cs::valuation asg) (r1cs::prime p))
  :disable r1cs::dot-product-of-append)

(defruledl int-divshift-be-step-is-lc-step
  (implies (and (symbolp bit)
                (symbol-listp xs)
                (consp xs)
                (symbolp next)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg next)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-shift-be-step-gadget bit xs next p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-shift-lc-step-gadget bit (rev xs) next p) asg p)))
  :do-not-induct t
  :use ((:instance int-divshift-dot-be-is-rev))
  :enable (int-shift-be-step-gadget
           int-shift-lc-step-gadget
           pow2sum-neg-prime-vector
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           int-divshift-dot-of-cons-single
           r1cs::dot-product-of-append
           dot-product-of-vector-neg-prime-to-neg-of-dot-product)
  :disable (int-divshift-dot-be-is-rev
            int-be-pow2sum-vector pow2sum-vector))

(defruled int-divshift-shr-wrapped-is-shl-of-rev
  :short "The unsigned right-shift constraints are the left-shift
          constraints over the reversed value wires."
  (implies (and (symbol-listp xs)
                (consp xs)
                (symbol-listp ebits)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (symbol-listp nexts)
                (consp nexts)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-shr-wrapped-gadget xs ebits nexts zs p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (int-shl-wrapped-gadget (rev xs) ebits nexts zs p)
                   asg p)))
  :do-not-induct t
  :cases ((consp ebits))
  :use ((:instance int-divshift-be-step-is-lc-step
                   (bit (car ebits)) (next (car nexts))))
  :enable (int-shr-wrapped-gadget
           int-shl-wrapped-gadget
           int-shr-chain-gadget
           int-shl-chain-gadget
           r1cs::r1cs-constraints-holdp-of-append
           r1cs::valuation-binds-allp)
  :disable (int-divshift-be-step-is-lc-step
            int-shift-be-step-gadget
            int-shift-lc-step-gadget
            int-shift-var-chain
            int-shift-lower-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-rev-value ((x integerp) (n natp))
  :returns (r natp :rule-classes :type-prescription)
  :short "The unsigned value of the reversed @('n')-bit pattern of @('x')."
  (lebits=>nat (rev (int->lebits x n))))

(defruledl int-divshift-shr-bits-from-nat
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable (int->lebits acl2::mod-when-<))

(defruled int-divshift-rev-value-facts
  (implies (posp n)
           (and (int-valuep (int-divshift-rev-value x n) nil n)
                (equal (int->lebits (int-divshift-rev-value x n) n)
                       (rev (int->lebits x n)))
                (equal (int-spec-unsigned (int-divshift-rev-value x n) n)
                       (int-divshift-rev-value x n))))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound
                   (digits (rev (int->lebits x n))))
        (:instance int-divshift-shr-bits-from-nat
                   (bits (rev (int->lebits x n)))
                   (v (int-divshift-rev-value x n))))
  :enable (int-divshift-rev-value
           int-valuep int-min int-max
           int-spec-unsigned
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           acl2::mod-when-<)
  :disable (int->lebits acl2::lebits=>nat-upper-bound))

(defruledl int-divshift-shr-l-facts
  (implies (and (bit-listp b) (natp s) (<= s (len b)))
           (and (bit-listp (append (nthcdr s b) (repeat s 0)))
                (bit-listp (rev (append (nthcdr s b) (repeat s 0))))
                (equal (len (rev (append (nthcdr s b) (repeat s 0))))
                       (len b))))
  :enable (int-bit-listp-of-nthcdr acl2::bit-listp-of-repeat-0-copy)
  :disable (acl2::rev-of-append nthcdr repeat)
  :prep-lemmas
  ((defrule acl2::bit-listp-of-repeat-0-copy
     (bit-listp (repeat k 0))
     :enable repeat)))

(defruledl int-divshift-shr-take-value
  (implies (and (bit-listp b) (natp n) (equal (len b) n)
                (natp s) (<= s n))
           (equal (lebits=>nat
                   (take n (int->lebits (* (lebits=>nat (rev b)) (expt 2 s))
                                        (* 2 n))))
                  (mod (* (lebits=>nat (rev b)) (expt 2 s)) (expt 2 n))))
  :do-not-induct t
  :use ((:instance int-lebits-take-is-mod
                   (bits (int->lebits (* (lebits=>nat (rev b)) (expt 2 s))
                                      (* 2 n)))
                   (n n))
        (:instance lebits=>nat-of-int->lebits
                   (x (* (lebits=>nat (rev b)) (expt 2 s)))
                   (n (* 2 n)))
        (:instance acl2::mod-of-mod-when-mult-copy
                   (x (* (lebits=>nat (rev b)) (expt 2 s)))
                   (n n)))
  :enable (len-of-int->lebits bit-listp-of-int->lebits-explicit
           acl2::ifix-when-integerp)
  :disable (int->lebits int-lebits-take-is-mod lebits=>nat-of-int->lebits
            take mod)
  :prep-lemmas
  ((defruled acl2::mod-of-mod-when-mult-copy
     (implies (and (integerp x) (natp n))
              (equal (mod (mod x (expt 2 (* 2 n))) (expt 2 n))
                     (mod x (expt 2 n))))
     :use ((:instance acl2::mod-of-mod-when-mult
                      (x x) (y1 (* (expt 2 n) (expt 2 n))) (y2 (expt 2 n)))
           (:instance expt-square-copy (a n)))
     :prep-lemmas
     ((defruled expt-square-copy
        (implies (natp a)
                 (equal (* (expt 2 a) (expt 2 a)) (expt 2 (* 2 a))))
        :use (:instance acl2::expt-of-+ (r 2) (i1 a) (i2 a))
        :disable acl2::expt-of-+)))))

(defruledl int-divshift-shr-take-is-rev-l
  (implies (and (bit-listp b) (natp n) (equal (len b) n)
                (natp s) (<= s n))
           (equal (take n (int->lebits (* (lebits=>nat (rev b)) (expt 2 s))
                                       (* 2 n)))
                  (rev (append (nthcdr s b) (repeat s 0)))))
  :do-not-induct t
  :use ((:instance int-divshift-shr-take-value)
        (:instance int-shr-mod-is-rev-floor-bits (bits b) (e s))
        (:instance int-divshift-shr-l-facts)
        (:instance int-divshift-shr-bits-from-nat
                   (bits (take n (int->lebits (* (lebits=>nat (rev b))
                                                 (expt 2 s))
                                              (* 2 n))))
                   (v (mod (* (lebits=>nat (rev b)) (expt 2 s)) (expt 2 n))))
        (:instance int-divshift-shr-bits-from-nat
                   (bits (rev (append (nthcdr s b) (repeat s 0))))
                   (v (mod (* (lebits=>nat (rev b)) (expt 2 s)) (expt 2 n)))))
  :enable (len-of-int->lebits bit-listp-of-int->lebits-explicit
           acl2::len-of-take)
  :disable (int->lebits int-divshift-shr-take-value
            int-shr-mod-is-rev-floor-bits int-divshift-shr-l-facts
            int-divshift-shr-bits-from-nat
            acl2::rev-of-append acl2::lebits=>nat-of-append
            take nthcdr repeat mod rev))

(defruled int-divshift-shr-result-bits
  :short "Reversing the low @('n') bits of @('R * 2^s') gives the bits of
          @('floor(N(x) / 2^s)')."
  (implies (and (integer-widthp n)
                (natp s)
                (< s n))
           (and (equal (rev (take n (int->lebits
                                     (* (int-divshift-rev-value x n)
                                        (expt 2 s))
                                     (* 2 n))))
                       (append (nthcdr s (int->lebits x n))
                               (repeat s 0)))
                (equal (lebits=>nat
                        (rev (take n (int->lebits
                                      (* (int-divshift-rev-value x n)
                                         (expt 2 s))
                                      (* 2 n)))))
                       (floor (int-spec-unsigned x n) (expt 2 s)))))
  :do-not-induct t
  :use ((:instance int-divshift-shr-take-is-rev-l
                   (b (int->lebits x n)))
        (:instance int-floor-lebits-nthcdr
                   (bits (int->lebits x n)) (e s))
        (:instance lebits=>nat-of-int->lebits (x x) (n n))
        (:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (nthcdr s (int->lebits x n)))
                   (acl2::hidigits (repeat s 0))))
  :enable (int-divshift-rev-value
           int-spec-unsigned
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           lebits=>nat-of-repeat-0
           posp-when-integer-widthp
           acl2::ifix-when-integerp)
  :disable (int->lebits
            int-divshift-shr-take-is-rev-l
            lebits=>nat-of-int->lebits
            int-floor-lebits-nthcdr
            acl2::lebits=>nat-of-append
            acl2::rev-of-append
            take nthcdr repeat mod floor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-shru-wire-facts
  (implies (and (symbol-listp xs)
                (r1cs::valuation-binds-allp asg xs)
                (integer-widthp n)
                (equal (len xs) n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits)))
           (and (symbol-listp (rev xs))
                (r1cs::valuation-binds-allp asg (rev xs))
                (equal (len (rev xs)) n)
                (consp xs)
                (consp nexts)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list (rev xs) asg)
                       (int->lebits (int-divshift-rev-value x n) n))
                (int-valuep (int-divshift-rev-value x n) nil n)
                (equal (int-spec-unsigned (int-divshift-rev-value x n) n)
                       (int-divshift-rev-value x n))))
  :do-not-induct t
  :use ((:instance int-divshift-rev-value-facts)
        (:instance int-divshift-binds-allp-of-rev))
  :enable (lookup-equal-list-of-rev
           bit-listp-of-int->lebits-explicit
           integer-widthp
           posp-when-integer-widthp)
  :disable (int-divshift-rev-value-facts int->lebits))

(defruledl int-divshift-shru-spec
  (implies (and (integer-widthp n)
                (int-valuep x nil n)
                (natp e))
           (and (equal (floor (int-spec-unsigned x n) (expt 2 (mod e n)))
                       (int-shr-wrapped-spec x e nil n))
                (natp (mod e n))
                (< (mod e n) n)))
  :enable (int-shr-wrapped-spec int-spec-unsigned int-valuep int-min int-max
           acl2::mod-when-< acl2::ifix-when-integerp
           posp-when-integer-widthp integer-widthp))

(defmacro int-divshift-shru-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (integer-widthp n)
        (not (equal n 128))
        (int-valuep x nil n)
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
               (int->lebits (mod e n) (1- (integer-length n))))))

(defruled int-divshift-shr-wrapped-unsigned-gadget-sound
  :short "R1CS-SOUND of variable-mode unsigned @('shr_wrapped') for every
          width other than 128.  The result integer is the low @('n')
          bits of @('zs'), reversed."
  (implies (and (int-divshift-shru-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-wrapped-gadget xs ebits nexts zs p) asg p))
           (and (equal (rev (take n (lookup-equal-list zs asg)))
                       (append (nthcdr (mod e n) (int->lebits x n))
                               (repeat (mod e n) 0)))
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    nil)
                       (int-shr-wrapped-spec x e nil n))))
  :do-not-induct t
  :use ((:instance int-divshift-shru-wire-facts)
        (:instance int-divshift-shru-spec)
        (:instance int-divshift-shr-wrapped-is-shl-of-rev)
        (:instance int-divshift-shl-wrapped-gadget-sound
                   (xs (rev xs))
                   (x (int-divshift-rev-value x n))
                   (signedp nil))
        (:instance int-divshift-shr-result-bits (s (mod e n)))
        (:instance lebits->int-when-unsigned
                   (bits (rev (take n (lookup-equal-list zs asg))))))
  :in-theory (union-theories '(booleanp (:e booleanp))
                             (theory 'minimal-theory)))

(defruled int-divshift-shr-wrapped-unsigned-gadget-complete
  :short "R1CS-COMPLETE of variable-mode unsigned @('shr_wrapped') for
          every width other than 128: the canonical witnesses (the
          left-shift witnesses of the reversed value) satisfy the gadget."
  (implies (and (int-divshift-shru-common-hyps)
                (equal (lookup-equal-list nexts asg)
                       (int-shift-witness-values
                        (int-divshift-rev-value x n)
                        (lookup-equal-list ebits asg)
                        0))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (* (int-divshift-rev-value x n)
                                       (expt 2 (mod e n)))
                                    (* 2 n))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-shr-wrapped-gadget xs ebits nexts zs p) asg p)
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    nil)
                       (int-shr-wrapped-spec x e nil n))))
  :do-not-induct t
  :use ((:instance int-divshift-shru-wire-facts)
        (:instance int-divshift-shru-spec)
        (:instance int-divshift-shr-wrapped-is-shl-of-rev)
        (:instance int-shl-wrapped-gadget-complete
                   (xs (rev xs))
                   (x (int-divshift-rev-value x n))
                   (signedp nil))
        (:instance int-divshift-shr-result-bits (s (mod e n)))
        (:instance lebits->int-when-unsigned
                   (bits (rev (take n (lookup-equal-list zs asg))))))
  :in-theory (union-theories '(booleanp (:e booleanp))
                             (theory 'minimal-theory)))
