; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS for snarkVM IdentifierLiteral::new (private or public mode).
;
; U8::new of each of the 31 bytes is a boolean check per bit (8 per byte).
; validate_identifier_bits then emits, per byte:
;
;   assert_eq(b7, false)                         (b7) * (1) = (0)
;   b4b3 = b4 AND b3,  b1b0 = b1 AND b0
;   is_not_equal of (b0+...+b4) with 0, two constraints;
;     all_zero_5 is the linear combination 1-r, and any_low5 is r
;   null = (NOT b6) AND (NOT b5)                 one constraint, NOT inlined
;   lower = b6 AND b5
;   (null) * (r) = (0)
;   invalid digit / upper / lower offsets, each an OR or XOR, an AND,
;     and one enforce of a linear combination against 0
;   on the first byte only: underscore AND-chain, letter = b6 AND NOT underscore,
;     and assert(letter)
;
; Trailing nulls: (null_i) * (1 - null_{i+1}) = (0) for each consecutive pair.
;
; NOT is the linear combination 1-x (pseudo-variable 1), not a fresh variable.
; The hash-free constraints are exactly the ones below.  Constant mode
; host-checks the same predicates and emits nothing.

(in-package "ALEOVM")

(include-book "environment-r1cs")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-xor")
(include-book "../fun-specs/values-string")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/typed-lists/symbol-listp" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule primep-when-equal-base-prime
  (implies (equal p (base-prime))
           (primep p))
  :hints (("Goal" :use primep-of-base-prime)))

(defrule member-equal-of-nth
  (implies (and (natp i) (< i (len x)))
           (member-equal (nth i x) x))
  :hints (("Goal" :in-theory (enable nth member-equal len))))

(defrule symbolp-of-nth
  (implies (symbol-listp x)
           (symbolp (nth i x)))
  :hints (("Goal" :in-theory (enable nth symbol-listp))))

(defrule bitp-of-nth-when-bit-listp
  (implies (and (bit-listp xs) (natp i) (< i (len xs)))
           (bitp (nth i xs)))
  :hints (("Goal" :in-theory (enable bit-listp nth))))

(defrule lookup-equal-of-nth
  (implies (and (natp i) (< i (len keys)))
           (equal (lookup-equal (nth i keys) alist)
                  (nth i (lookup-equal-list keys alist))))
  :hints (("Goal" :in-theory (enable nth lookup-equal-list))))

(defruled id-coeff-neg-one
  (implies (equal p (base-prime))
           (equal (mod (1- p) p) (pfield::neg 1 p)))
  :hints (("Goal"
           :in-theory (enable (:e base-prime)
                              base-prime
                              pfield::neg))))

(defruled values-b-and-is-bitand
  (implies (and (bitp a) (bitp b))
           (equal (values-b-and a b) (bitand a b)))
  :enable (values-b-and bitand))

(defruled values-b-or-is-bitor
  (implies (and (bitp a) (bitp b))
           (equal (values-b-or a b) (bitor a b)))
  :enable (values-b-or bitor))

(defruled values-b-xor-is-bitxor
  (implies (and (bitp a) (bitp b))
           (equal (values-b-xor a b) (bitxor a b)))
  :enable (values-b-xor bitxor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-b7-zero-gadget ((b7 symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "assert_eq of bit 7 with constant false."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b7))
         :b (list (list 1 1))
         :c nil)))

(defruled id-b7-zero-gadget-to-zero
  (implies (and (symbolp b7)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b7))
           (equal (r1cs::r1cs-constraints-holdp (id-b7-zero-gadget b7) asg p)
                  (equal (lookup-equal b7 asg) 0)))
  :hints (("Goal"
           :in-theory (e/d (id-b7-zero-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           (pfield::mul-commutative)))))

(define id-low5-sum ((b0 integerp) (b1 integerp) (b2 integerp)
                     (b3 integerp) (b4 integerp) (p primep))
  :verify-guards nil
  :returns (s integerp :hyp :guard)
  (pfield::add b0
               (pfield::add b1
                            (pfield::add b2
                                         (pfield::add b3 b4 p)
                                         p)
                            p)
               p))

(define id-low5-neq-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp)
                            (b3 symbolp) (b4 symbolp)
                            (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "is_not_equal of the low-5-bit sum with constant 0."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b0) (list 1 b1) (list 1 b2) (list 1 b3) (list 1 b4))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 b0) (list 1 b1) (list 1 b2) (list 1 b3) (list 1 b4))
         :b (list (list 1 1) (list (1- p) r))
         :c nil)))

(defruled id-low5-neq-gadget-to-equations
  (implies (and (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b3) (symbolp b4)
                (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b3)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-low5-neq-gadget b0 b1 b2 b3 b4 m r p) asg p)
                  (and (equal (pfield::mul (id-low5-sum (lookup-equal b0 asg)
                                                       (lookup-equal b1 asg)
                                                       (lookup-equal b2 asg)
                                                       (lookup-equal b3 asg)
                                                       (lookup-equal b4 asg)
                                                       p)
                                           (lookup-equal m asg)
                                           p)
                              (lookup-equal r asg))
                       (equal (pfield::mul (id-low5-sum (lookup-equal b0 asg)
                                                       (lookup-equal b1 asg)
                                                       (lookup-equal b2 asg)
                                                       (lookup-equal b3 asg)
                                                       (lookup-equal b4 asg)
                                                       p)
                                           (pfield::sub 1 (lookup-equal r asg) p)
                                           p)
                              0))))
  :hints (("Goal"
           :in-theory (e/d (id-low5-neq-gadget
                            id-low5-sum
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-null-gadget ((b6 symbolp) (b5 symbolp) (null symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(NOT b6) * (NOT b5) = null, with NOT inlined as @($1 - x$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1) (list (1- p) b6))
         :b (list (list 1 1) (list (1- p) b5))
         :c (list (list 1 null)))))

(defruled id-null-gadget-to-mul
  (implies (and (symbolp b6) (symbolp b5) (symbolp null)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg null))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-null-gadget b6 b5 null p) asg p)
                  (equal (lookup-equal null asg)
                         (pfield::mul (pfield::sub 1 (lookup-equal b6 asg) p)
                                      (pfield::sub 1 (lookup-equal b5 asg) p)
                                      p))))
  :hints (("Goal"
           :in-theory (e/d (id-null-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-zero-prod-gadget ((a symbolp) (b symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(a) * (b) = (0)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a))
         :b (list (list 1 b))
         :c nil)))

(defruled id-zero-prod-gadget-to-mul
  (implies (and (symbolp a) (symbolp b)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-zero-prod-gadget a b) asg p)
                  (equal (pfield::mul (lookup-equal a asg)
                                      (lookup-equal b asg)
                                      p)
                         0)))
  :hints (("Goal"
           :in-theory (e/d (id-zero-prod-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           (pfield::mul-commutative)))))

(define id-digit-enforce-gadget ((b5 symbolp) (lower symbolp)
                                 (b4 symbolp) (idig symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(b5 - lower) * ((1 - b4) + invalid) = 0."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b5) (list (1- p) lower))
         :b (list (list 1 1) (list (1- p) b4) (list 1 idig))
         :c nil)))

(defruled id-digit-enforce-gadget-to-mul
  (implies (and (symbolp b5) (symbolp lower) (symbolp b4) (symbolp idig)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b5)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg b4)
                (r1cs::valuation-bindsp asg idig))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-digit-enforce-gadget b5 lower b4 idig p) asg p)
                  (equal (pfield::mul
                          (pfield::sub (lookup-equal b5 asg)
                                       (lookup-equal lower asg) p)
                          (pfield::add (pfield::sub 1 (lookup-equal b4 asg) p)
                                       (lookup-equal idig asg)
                                       p)
                          p)
                         0)))
  :hints (("Goal"
           :in-theory (e/d (id-digit-enforce-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-category-enforce-gadget ((left symbolp)
                                    (r symbolp) (bad symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(left) * ((1 - r) + bad) = 0, where @($1 - r$) is all_zero_5."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 left))
         :b (list (list 1 1) (list (1- p) r) (list 1 bad))
         :c nil)))

(defruled id-category-enforce-gadget-to-mul
  (implies (and (symbolp left) (symbolp r) (symbolp bad)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg left)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg bad))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-category-enforce-gadget left r bad p) asg p)
                  (equal (pfield::mul (lookup-equal left asg)
                                      (pfield::add (pfield::sub 1 (lookup-equal r asg) p)
                                                   (lookup-equal bad asg)
                                                   p)
                                      p)
                         0)))
  :hints (("Goal"
           :in-theory (e/d (id-category-enforce-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-upper-lc-enforce-gadget ((b6 symbolp) (lower symbolp)
                                    (r symbolp) (bad symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(b6 - lower) * ((1 - r) + bad_upper) = 0."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b6) (list (1- p) lower))
         :b (list (list 1 1) (list (1- p) r) (list 1 bad))
         :c nil)))

(defruled id-upper-lc-enforce-gadget-to-mul
  (implies (and (symbolp b6) (symbolp lower) (symbolp r) (symbolp bad)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg lower)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg bad))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-upper-lc-enforce-gadget b6 lower r bad p) asg p)
                  (equal (pfield::mul
                          (pfield::sub (lookup-equal b6 asg)
                                       (lookup-equal lower asg) p)
                          (pfield::add (pfield::sub 1 (lookup-equal r asg) p)
                                       (lookup-equal bad asg)
                                       p)
                          p)
                         0)))
  :hints (("Goal"
           :in-theory (e/d (id-upper-lc-enforce-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-letter-gadget ((b6 symbolp) (uscore symbolp) (islet symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "b6 AND (NOT underscore)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b6))
         :b (list (list 1 1) (list (1- p) uscore))
         :c (list (list 1 islet)))))

(defruled id-letter-gadget-to-mul
  (implies (and (symbolp b6) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-letter-gadget b6 uscore islet p) asg p)
                  (equal (lookup-equal islet asg)
                         (pfield::mul (lookup-equal b6 asg)
                                      (pfield::sub 1 (lookup-equal uscore asg) p)
                                      p))))
  :hints (("Goal"
           :in-theory (e/d (id-letter-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(define id-trail-gadget ((prev symbolp) (next symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(prev) * (1 - next) = 0."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 prev))
         :b (list (list 1 1) (list (1- p) next))
         :c nil)))

(defruled id-trail-gadget-to-mul
  (implies (and (symbolp prev) (symbolp next)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-bindsp asg next))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-trail-gadget prev next p) asg p)
                  (equal (pfield::mul (lookup-equal prev asg)
                                      (pfield::sub 1 (lookup-equal next asg) p)
                                      p)
                         0)))
  :hints (("Goal"
           :in-theory (e/d (id-trail-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product
                            id-coeff-neg-one)
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Witness layout, 12 symbols: b4b3, b1b0, m, r, null, lower,
; digit-or, invalid-digit, xor, bad-upper, lower-or, bad-lower.

(define id-byte-gadget ((bits symbol-listp) (wits symbol-listp) (p primep))
  :guard (and (equal (len bits) 8) (equal (len wits) 12))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "validate_byte constraints other than the first-byte letter assert."
  (b* ((b0 (nth 0 bits)) (b1 (nth 1 bits)) (b2 (nth 2 bits))
       (b3 (nth 3 bits)) (b4 (nth 4 bits)) (b5 (nth 5 bits))
       (b6 (nth 6 bits)) (b7 (nth 7 bits))
       (b4b3 (nth 0 wits)) (b1b0 (nth 1 wits))
       (m (nth 2 wits)) (r (nth 3 wits))
       (null (nth 4 wits)) (lower (nth 5 wits))
       (dor (nth 6 wits)) (idig (nth 7 wits))
       (xor (nth 8 wits)) (bu (nth 9 wits))
       (lor (nth 10 wits)) (bl (nth 11 wits)))
    (append (id-b7-zero-gadget b7)
            (boolean-and-gadget b4 b3 b4b3)
            (boolean-and-gadget b1 b0 b1b0)
            (id-low5-neq-gadget b0 b1 b2 b3 b4 m r p)
            (id-null-gadget b6 b5 null p)
            (boolean-and-gadget b6 b5 lower)
            (id-zero-prod-gadget null r)
            (boolean-or-gadget b2 b1 dor p)
            (boolean-and-gadget b3 dor idig)
            (id-digit-enforce-gadget b5 lower b4 idig p)
            (boolean-xor-gadget b2 b1b0 xor p)
            (boolean-and-gadget b4b3 xor bu)
            (id-upper-lc-enforce-gadget b6 lower r bu p)
            (boolean-or-gadget b2 b1b0 lor p)
            (boolean-and-gadget b4b3 lor bl)
            (id-category-enforce-gadget lower r bl p))))

(define id-byte-equations
  ((b0 integerp) (b1 integerp) (b2 integerp) (b3 integerp)
   (b4 integerp) (b5 integerp) (b6 integerp) (b7 integerp)
   (b4b3 integerp) (b1b0 integerp) (m integerp) (r integerp)
   (null integerp) (lower integerp) (dor integerp) (idig integerp)
   (xor integerp) (bu integerp) (lor integerp) (bl integerp)
   (p primep))
  :verify-guards nil
  :returns (yes/no booleanp)
  (and (equal b7 0)
       (equal b4b3 (bitand b4 b3))
       (equal b1b0 (bitand b1 b0))
       (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p) m p) r)
       (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p)
                           (pfield::sub 1 r p) p)
              0)
       (equal null (pfield::mul (pfield::sub 1 b6 p)
                                (pfield::sub 1 b5 p) p))
       (equal lower (bitand b6 b5))
       (equal (pfield::mul null r p) 0)
       (equal dor (bitor b2 b1))
       (equal idig (bitand b3 dor))
       (equal (pfield::mul (pfield::sub b5 lower p)
                           (pfield::add (pfield::sub 1 b4 p) idig p)
                           p)
              0)
       (equal xor (bitxor b2 b1b0))
       (equal bu (bitand b4b3 xor))
       (equal (pfield::mul (pfield::sub b6 lower p)
                           (pfield::add (pfield::sub 1 r p) bu p)
                           p)
              0)
       (equal lor (bitor b2 b1b0))
       (equal bl (bitand b4b3 lor))
       (equal (pfield::mul lower
                           (pfield::add (pfield::sub 1 r p) bl p)
                           p)
              0)))

(defruled id-byte-gadget-to-equations
  :short "R1CS-SPEC of one @('validate_byte'), apart from the first-byte letter."
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))
                (bitp (lookup-equal (nth 0 wits) asg))
                (bitp (lookup-equal (nth 1 wits) asg))
                (bitp (lookup-equal (nth 6 wits) asg))
                (bitp (lookup-equal (nth 8 wits) asg))
                (bitp (lookup-equal (nth 10 wits) asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-byte-gadget bits wits p) asg p)
                  (id-byte-equations
                   (lookup-equal (nth 0 bits) asg)
                   (lookup-equal (nth 1 bits) asg)
                   (lookup-equal (nth 2 bits) asg)
                   (lookup-equal (nth 3 bits) asg)
                   (lookup-equal (nth 4 bits) asg)
                   (lookup-equal (nth 5 bits) asg)
                   (lookup-equal (nth 6 bits) asg)
                   (lookup-equal (nth 7 bits) asg)
                   (lookup-equal (nth 0 wits) asg)
                   (lookup-equal (nth 1 wits) asg)
                   (lookup-equal (nth 2 wits) asg)
                   (lookup-equal (nth 3 wits) asg)
                   (lookup-equal (nth 4 wits) asg)
                   (lookup-equal (nth 5 wits) asg)
                   (lookup-equal (nth 6 wits) asg)
                   (lookup-equal (nth 7 wits) asg)
                   (lookup-equal (nth 8 wits) asg)
                   (lookup-equal (nth 9 wits) asg)
                   (lookup-equal (nth 10 wits) asg)
                   (lookup-equal (nth 11 wits) asg)
                   p)))
  :do-not-induct t
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (id-byte-gadget
                            id-byte-equations
                            id-b7-zero-gadget-to-zero
                            boolean-and-gadget-to-bitand
                            id-low5-neq-gadget-to-equations
                            id-null-gadget-to-mul
                            id-zero-prod-gadget-to-mul
                            boolean-or-gadget-to-bitor
                            id-digit-enforce-gadget-to-mul
                            boolean-xor-gadget-to-bitxor
                            id-upper-lc-enforce-gadget-to-mul
                            id-category-enforce-gadget-to-mul
                            r1cs::r1cs-constraints-holdp-of-append)
                           (lookup-equal-of-nth
                            lookup-equal-list
                            (:definition nth)
                            (:definition r1cs::valuation-binds-allp)
                            (:definition r1cs::dot-product)
                            (:definition r1cs::r1cs-constraint-holdsp)
                            (:definition bit-listp)
                            (:definition pfield::mul)
                            (:definition pfield::add)
                            (:definition pfield::sub)
                            pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-first-extra-gadget ((b4b3 symbolp) (b1b0 symbolp) (b2 symbolp)
                               (b6 symbolp)
                               (partial symbolp) (uscore symbolp) (islet symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "First-byte letter check: underscore offset, then assert the letter bit."
  (append (boolean-and-gadget b4b3 b1b0 partial)
          (boolean-and-gadget partial b2 uscore)
          (id-letter-gadget b6 uscore islet p)
          (assert-gadget islet)))

(define id-first-extra-equations ((b4b3 integerp) (b1b0 integerp)
                                  (b2 integerp) (b6 integerp)
                                  (partial integerp) (uscore integerp)
                                  (islet integerp) (p primep))
  :verify-guards nil
  :returns (yes/no booleanp)
  (and (equal partial (bitand b4b3 b1b0))
       (equal uscore (bitand partial b2))
       (equal islet (pfield::mul b6 (pfield::sub 1 uscore p) p))
       (assert-funspec islet)))

(defruled id-first-extra-gadget-to-equations
  (implies (and (symbolp b4b3) (symbolp b1b0) (symbolp b2) (symbolp b6)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b4b3)
                (r1cs::valuation-bindsp asg b1b0)
                (r1cs::valuation-bindsp asg b2)
                (r1cs::valuation-bindsp asg b6)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (bitp (lookup-equal b4b3 asg))
                (bitp (lookup-equal b1b0 asg))
                (bitp (lookup-equal b2 asg))
                (bitp (lookup-equal partial asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (id-first-extra-gadget b4b3 b1b0 b2 b6
                                          partial uscore islet p)
                   asg p)
                  (id-first-extra-equations
                   (lookup-equal b4b3 asg) (lookup-equal b1b0 asg)
                   (lookup-equal b2 asg) (lookup-equal b6 asg)
                   (lookup-equal partial asg) (lookup-equal uscore asg)
                   (lookup-equal islet asg) p)))
  :do-not-induct t
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (id-first-extra-gadget
                            id-first-extra-equations
                            boolean-and-gadget-to-bitand
                            id-letter-gadget-to-mul
                            assert-gadget-to-funspec
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition nth)
                            (:definition r1cs::dot-product)
                            (:definition r1cs::r1cs-constraint-holdsp)
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-sub1-of-bit
  (implies (and (bitp b) (equal p (base-prime)))
           (equal (pfield::sub 1 b p) (values-b-not b)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (enable pfield::sub pfield::add pfield::neg
                              values-b-not bitp))))

(defruled id-mul-of-bits
  (implies (and (bitp x) (bitp y) (equal p (base-prime)))
           (equal (pfield::mul x y p) (* x y)))
  :hints (("Goal" :in-theory (enable pfield::mul bitp))))

(defruled id-null-mul-is-spec
  (implies (and (bitp b6) (bitp b5) (equal p (base-prime)))
           (equal (pfield::mul (pfield::sub 1 b6 p)
                               (pfield::sub 1 b5 p) p)
                  (values-b-and (values-b-not b6) (values-b-not b5))))
  :hints (("Goal"
           :in-theory (enable id-sub1-of-bit id-mul-of-bits
                              values-b-and values-b-not))))

(defruled id-low5-sum-is-plus
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal p (base-prime)))
           (equal (id-low5-sum b0 b1 b2 b3 b4 p)
                  (+ b0 b1 b2 b3 b4)))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b1 0) (equal b2 0)
                   (equal b3 0) (equal b4 0))
           :in-theory (enable id-low5-sum pfield::add bitp
                              (:e base-prime) (:e <)))))

(defruled id-mul-zero-factors
  (implies (and (equal p (base-prime))
                (pfield::fep x p)
                (pfield::fep y p)
                (equal (pfield::mul x y p) 0))
           (or (equal x 0) (equal y 0)))
  :hints (("Goal"
           :use (:instance pfield::equal-of-0-and-mul
                           (x x) (y y) (p p))
           :in-theory (disable pfield::equal-of-0-and-mul
                               pfield::equal-of-0-and-mul-gen))))

(defruled id-r-when-neq
  :short "The is_not_equal witness r is 0 exactly when the low-5 sum is 0."
  (implies (and (equal p (base-prime))
                (natp s) (< s p)
                (pfield::fep m p) (pfield::fep r p)
                (equal (pfield::mul s m p) r)
                (equal (pfield::mul s (pfield::sub 1 r p) p) 0))
           (and (bitp r)
                (equal (if (equal s 0) 0 1) r)))
  :hints (("Goal"
           :cases ((equal s 0))
           :in-theory (e/d (bitp pfield::fep id-mul-zero-factors
                                 pfield::mul-of-0-arg1)
                           (pfield::mul-commutative
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-sub
                            (x 1) (y r) (p p))))))

(define id-spec-data ((b0 bitp) (b1 bitp) (b2 bitp) (b3 bitp) (b4 bitp))
  :returns (data byte-validation-datap)
  (byte-validation-data-new b0 b1 b2 b3 b4))

(defruled id-validate-byte-rest-when-checks
  :short "The non-first-byte funspec returns the null bit when each
          snarkVM check holds on the spec intermediates."
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (equal b7 0)
                (equal (* (values-b-and (values-b-not b6) (values-b-not b5))
                          (values-b-not
                           (byte-validation-data->all-zero-5
                            (byte-validation-data-new b0 b1 b2 b3 b4))))
                       0)
                (equal (* (- b5 (values-b-and b6 b5))
                          (+ (- 1 b4)
                             (is-invalid-digit-offset b1 b2 b3)))
                       0)
                (equal (* (- b6 (values-b-and b6 b5))
                          (+ (byte-validation-data->all-zero-5
                              (byte-validation-data-new b0 b1 b2 b3 b4))
                             (is-invalid-uppercase-offset
                              (byte-validation-data-new b0 b1 b2 b3 b4) b2)))
                       0)
                (equal (* (values-b-and b6 b5)
                          (+ (byte-validation-data->all-zero-5
                              (byte-validation-data-new b0 b1 b2 b3 b4))
                             (is-invalid-lowercase-offset
                              (byte-validation-data-new b0 b1 b2 b3 b4) b2)))
                       0))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) nil)
                  (values-b-and (values-b-not b6) (values-b-not b5))))
  :do-not-induct t
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (enable validate-byte acl2::bfix-when-bitp nth))))

(defruled id-validate-byte-first-when-checks
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (equal b7 0)
                (equal (* (values-b-and (values-b-not b6) (values-b-not b5))
                          (values-b-not
                           (byte-validation-data->all-zero-5
                            (byte-validation-data-new b0 b1 b2 b3 b4))))
                       0)
                (equal (* (- b5 (values-b-and b6 b5))
                          (+ (- 1 b4)
                             (is-invalid-digit-offset b1 b2 b3)))
                       0)
                (equal (* (- b6 (values-b-and b6 b5))
                          (+ (byte-validation-data->all-zero-5
                              (byte-validation-data-new b0 b1 b2 b3 b4))
                             (is-invalid-uppercase-offset
                              (byte-validation-data-new b0 b1 b2 b3 b4) b2)))
                       0)
                (equal (* (values-b-and b6 b5)
                          (+ (byte-validation-data->all-zero-5
                              (byte-validation-data-new b0 b1 b2 b3 b4))
                             (is-invalid-lowercase-offset
                              (byte-validation-data-new b0 b1 b2 b3 b4) b2)))
                       0)
                (equal (values-b-and
                        b6
                        (values-b-not
                         (values-b-and
                          (values-b-and
                           (byte-validation-data->b4b3
                            (byte-validation-data-new b0 b1 b2 b3 b4))
                           (byte-validation-data->b1b0
                            (byte-validation-data-new b0 b1 b2 b3 b4)))
                          b2)))
                       1))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) t)
                  (values-b-and (values-b-not b6) (values-b-not b5))))
  :do-not-induct t
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (enable validate-byte acl2::bfix-when-bitp nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-bitrows-p (rows)
  :returns (yes/no booleanp)
  (if (atom rows)
      (eq rows nil)
    (and (symbol-listp (car rows))
         (equal (len (car rows)) 8)
         (id-bitrows-p (cdr rows)))))

(define id-witrows-p (rows)
  :returns (yes/no booleanp)
  (if (atom rows)
      (eq rows nil)
    (and (symbol-listp (car rows))
         (equal (len (car rows)) 12)
         (id-witrows-p (cdr rows)))))

(define id-rows-boundp ((bitrows true-listp) (witrows true-listp) (asg alistp))
  :verify-guards nil
  :returns (yes/no booleanp)
  (if (atom bitrows)
      t
    (and (consp witrows)
         (r1cs::valuation-binds-allp asg (car bitrows))
         (r1cs::valuation-binds-allp asg (car witrows))
         (id-rows-boundp (cdr bitrows) (cdr witrows) asg))))

(define id-bits-matchp ((bytes acl2::ubyte8-listp)
                        (bitrows true-listp)
                        (asg alistp))
  :verify-guards nil
  :returns (yes/no booleanp)
  (if (atom bytes)
      (atom bitrows)
    (and (consp bitrows)
         (equal (lookup-equal-list (car bitrows) asg)
                (values-nat-to-lebits 8 (acl2::ubyte8-fix (car bytes))))
         (id-bits-matchp (cdr bytes) (cdr bitrows) asg))))

(define id-null-symbols ((witrows true-listp))
  :guard (id-witrows-p witrows)
  :verify-guards nil
  :returns (syms symbol-listp
                 :hyp (id-witrows-p witrows)
                 :hints (("Goal"
                          :in-theory (enable id-null-symbols
                                             id-witrows-p
                                             symbolp-of-nth))))
  (if (atom witrows)
      nil
    (cons (nth 4 (car witrows))
          (id-null-symbols (cdr witrows)))))

(define id-rest-bytes-gadget ((bitrows true-listp) (witrows true-listp) (p primep))
  :guard (and (id-bitrows-p bitrows) (id-witrows-p witrows))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (id-bitrows-p bitrows)
                              (id-witrows-p witrows)
                              (primep p))
                    :hints (("Goal"
                             :in-theory (enable id-rest-bytes-gadget
                                                id-bitrows-p
                                                id-witrows-p))))
  (if (or (endp bitrows) (endp witrows))
      nil
    (append (id-byte-gadget (car bitrows) (car witrows) p)
            (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p))))

(define id-trailing-gadget ((nulls symbol-listp) (p primep))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp nulls) (endp (cdr nulls)))
      nil
    (append (id-trail-gadget (car nulls) (cadr nulls) p)
            (id-trailing-gadget (cdr nulls) p))))

(define id-bit-checks ((bitrows true-listp) (p primep))
  :guard (id-bitrows-p bitrows)
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (id-bitrows-p bitrows) (primep p))
                    :hints (("Goal" :in-theory (enable id-bit-checks id-bitrows-p))))
  (if (endp bitrows)
      nil
    (append (boolean-check-gadget-list (car bitrows) p)
            (id-bit-checks (cdr bitrows) p))))

(defrule id-bitrows-p-of-car
  (implies (and (id-bitrows-p rows) (consp rows))
           (and (symbol-listp (car rows))
                (equal (len (car rows)) 8)
                (id-bitrows-p (cdr rows))))
  :do-not-induct t
  :hints (("Goal" :in-theory (enable id-bitrows-p))))

(defrule id-witrows-p-of-car
  (implies (and (id-witrows-p rows) (consp rows))
           (and (symbol-listp (car rows))
                (equal (len (car rows)) 12)
                (id-witrows-p (cdr rows))))
  :do-not-induct t
  :hints (("Goal" :in-theory (enable id-witrows-p))))

(define identifier-new-gadget ((bitrows true-listp)
                               (witrows true-listp)
                               (partial symbolp) (uscore symbolp) (islet symbolp)
                               (p primep))
  :guard (and (consp bitrows)
              (consp witrows)
              (id-bitrows-p bitrows)
              (id-witrows-p witrows))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (consp bitrows)
                              (consp witrows)
                              (id-bitrows-p bitrows)
                              (id-witrows-p witrows)
                              (primep p)
                              (symbolp partial)
                              (symbolp uscore)
                              (symbolp islet))
                    :hints (("Goal"
                             :do-not-induct t
                             :in-theory (e/d (identifier-new-gadget
                                              id-bitrows-p-of-car
                                              id-witrows-p-of-car
                                              symbolp-of-nth)
                                             (id-bitrows-p
                                              id-witrows-p
                                              (:definition nth))))))
  :short "Variable-mode constraints of @('IdentifierLiteral::new'):
          boolean checks, validate_byte of each byte, and trailing nulls.
          snarkVM always passes 31 bytes; the gadget is that circuit for
          whatever length the funspec's byte list has."
  (append (id-bit-checks bitrows p)
          (id-byte-gadget (car bitrows) (car witrows) p)
          (id-first-extra-gadget (nth 0 (car witrows))
                                 (nth 1 (car witrows))
                                 (nth 2 (car bitrows))
                                 (nth 6 (car bitrows))
                                 partial uscore islet p)
          (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p)
          (id-trailing-gadget (id-null-symbols witrows) p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field equations imply the integer checks in validate-byte.

(defruled id-add-of-bits
  (implies (and (bitp x) (bitp y) (equal p (base-prime)))
           (equal (pfield::add x y p) (+ x y)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal x 0) (equal y 0))
           :in-theory (enable pfield::add bitp (:e base-prime)))))

(defruled id-diff-prod-when-bits
  :short "A field product of a bit difference with a 0/1/2 sum is zero
          exactly when the same integer product is zero."
  (implies (and (bitp a) (bitp b)
                (natp k) (< k 3)
                (equal p (base-prime))
                (equal (pfield::mul (pfield::sub a b p) k p) 0))
           (equal (* (- a b) k) 0))
  :do-not-induct t
  :hints (("Goal"
           :cases ((and (equal a 0) (equal b 0) (equal k 0))
                   (and (equal a 0) (equal b 0) (equal k 1))
                   (and (equal a 0) (equal b 0) (equal k 2))
                   (and (equal a 0) (equal b 1) (equal k 0))
                   (and (equal a 0) (equal b 1) (equal k 1))
                   (and (equal a 0) (equal b 1) (equal k 2))
                   (and (equal a 1) (equal b 0) (equal k 0))
                   (and (equal a 1) (equal b 0) (equal k 1))
                   (and (equal a 1) (equal b 0) (equal k 2))
                   (and (equal a 1) (equal b 1) (equal k 0))
                   (and (equal a 1) (equal b 1) (equal k 1))
                   (and (equal a 1) (equal b 1) (equal k 2)))
           :in-theory (e/d (pfield::sub pfield::mul pfield::neg pfield::add bitp
                                        (:e base-prime))
                           (pfield::mul-commutative
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled id-bit-times-small-is-int
  (implies (and (bitp a) (natp k) (< k 3) (equal p (base-prime))
                (equal (pfield::mul a k p) 0))
           (equal (* a k) 0))
  :do-not-induct t
  :hints (("Goal"
           :cases ((and (equal a 0) (equal k 0))
                   (and (equal a 0) (equal k 1))
                   (and (equal a 0) (equal k 2))
                   (and (equal a 1) (equal k 0))
                   (and (equal a 1) (equal k 1))
                   (and (equal a 1) (equal k 2)))
           :in-theory (e/d (pfield::mul bitp (:e base-prime))
                           (pfield::mul-commutative)))))

; id-byte-equations imply the integer checks of validate-byte only after
; the field products are rewritten back to those integer products.
; id-validate-byte-rest-when-checks / id-validate-byte-first-when-checks
; are that integer step.  The field-to-integer product lemmas above
; (id-diff-prod-when-bits, id-bit-times-small-is-int, id-add-of-bits)
; are the arithmetic step.  The list of bytes and the trailing-null
; constraints are composed in identifier-list-sound.lisp.
