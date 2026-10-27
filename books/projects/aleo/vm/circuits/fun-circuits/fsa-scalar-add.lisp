; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::add and Scalar::add_assign (circuit/types/scalar/src/add.rs),
; variable mode.  add is add_assign on a clone; both emit the same list.
;
;   sum      = a + b                         (linear combination)
;   bits     = sum.to_lower_bits_le(252)     252 boolean checks and
;                                            (a + b) * 1 = sum 2^i b_i
;   sum'     = Field::from_bits_le(bits)     no constraint (252 <= data bits);
;                                            caches bits plus constant false
;   L        = sum'.is_less_than(r)          Field compare, variable < constant:
;              fold from the LSB over the cached bits with r's bits;
;              acc_0 = constant false, step i is
;                r_i = 1:  (!b_i) OR  acc     r_i = 0:  (!b_i) AND acc
;              Constant folding: step 0 (r_0 = 1, acc false) is the linear
;              combination 1 - b_0; step 252 (b_252 constant false) is acc.
;              Steps 1..251 are one gate each:
;                AND: (1 - b_i) * acc = z_i
;                OR:  (b_i) * (1 - acc) = (1 - z_i)
;   w        = ternary(L, sum', sum' - r)    (sum' - (sum' - r)) * L = w - (sum' - r),
;                                            i.e. (r) * (z_251) = (w - sum 2^i b_i + r)
;   out bits = w.to_lower_bits_le(251)       251 boolean checks and w * 1 = sum 2^i c_i
;
; 252 + 1 + 251 + 1 + 251 + 1 = 757 constraints and 252 + 251 + 1 + 251 =
; 755 private variables, matching snarkVM's Count::is(1, 0, 755, 757).
; The gates are written over their semantic linear combinations (for
; example (r) for sum' - (sum' - r)); snarkVM may carry zero-coefficient
; terms in the same linear combinations.

(in-package "ALEOVM")

(include-book "fb-field-bits")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")
(include-book "../r1cs/pow2sum-vectors")
(include-book "../fun-specs/primitives-scalar")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The comparison fold, over integers.

(define fsa-step (x r acc)
  :verify-guards nil
  (if (equal r 1)
      (if (equal x 0) 1 acc)
    (if (equal x 1) 0 acc)))

(define fsa-ltc (xs rs acc)
  :verify-guards nil
  (if (endp xs)
      acc
    (fsa-ltc (cdr xs) (cdr rs) (fsa-step (car xs) (car rs) acc))))

(define fsa-ltc-vals (xs rs acc)
  :verify-guards nil
  (if (endp xs)
      nil
    (b* ((acc2 (fsa-step (car xs) (car rs) acc)))
      (cons acc2 (fsa-ltc-vals (cdr xs) (cdr rs) acc2)))))

(defruled fsa-bitp-of-step
  (implies (and (bitp x) (bitp acc))
           (bitp (fsa-step x r acc)))
  :enable (fsa-step bitp))

(defruled fsa-last-of-ltc-vals
  (implies (consp xs)
           (equal (car (last (fsa-ltc-vals xs rs acc)))
                  (fsa-ltc xs rs acc)))
  :induct (fsa-ltc xs rs acc)
  :enable (fsa-ltc fsa-ltc-vals))

(defruled fsa-ltc-is-compare
  (implies (and (bit-listp xs) (bit-listp rs)
                (equal (len xs) (len rs))
                (bitp acc))
           (equal (fsa-ltc xs rs acc)
                  (cond ((< (lebits=>nat xs) (lebits=>nat rs)) 1)
                        ((< (lebits=>nat rs) (lebits=>nat xs)) 0)
                        (t acc))))
  :induct (fsa-ltc xs rs acc)
  :enable (fsa-ltc fsa-step bit-listp bitp fsa-bitp-of-step
           acl2::lebits=>nat-of-cons)
  :prep-books ((include-book "arithmetic/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The gates.

(define fsa-gate ((b symbolp) (rbit bitp) (av true-listp) (nav true-listp)
                  (z symbolp) (p primep))
  :verify-guards nil
  (if (equal rbit 1)
      (list (r1cs::make-r1cs-constraint
             :a (list (list 1 b))
             :b nav
             :c (list (list 1 1) (list (1- p) z))))
    (list (r1cs::make-r1cs-constraint
           :a (list (list 1 1) (list (1- p) b))
           :b av
           :c (list (list 1 z))))))

(define fsa-ltc-gates ((bs symbol-listp) (rs bit-listp) (zs symbol-listp)
                       (av true-listp) (nav true-listp) (p primep))
  :verify-guards nil
  (if (endp bs)
      nil
    (append (fsa-gate (car bs) (car rs) av nav (car zs) p)
            (fsa-ltc-gates (cdr bs) (cdr rs) (cdr zs)
                           (list (list 1 (car zs)))
                           (list (list 1 1) (list (1- p) (car zs)))
                           p))))

(defruled fsa-gate-iff
  (implies (and (symbolp b) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg z)
                (bitp rbit)
                (bitp (lookup-equal b asg))
                (bitp acc)
                (equal (r1cs::dot-product av asg p) acc)
                (equal (r1cs::dot-product nav asg p) (pfield::sub 1 acc p)))
           (equal (r1cs::r1cs-constraints-holdp
                   (fsa-gate b rbit av nav z p) asg p)
                  (equal (lookup-equal z asg)
                         (fsa-step (lookup-equal b asg) rbit acc))))
  :do-not-induct t
  :cases ((and (equal (lookup-equal b asg) 0) (equal acc 0))
          (and (equal (lookup-equal b asg) 0) (equal acc 1))
          (and (equal (lookup-equal b asg) 1) (equal acc 0)))
  :in-theory (e/d (fsa-gate fsa-step bitp
                   r1cs::r1cs-constraint-holdsp
                   r1cs::r1cs-constraints-holdp
                   r1cs::dot-product
                   r1cs::fep-of-lookup-equal)
                  ((:e base-prime)))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
  :use ((:instance r1cs::fep-of-lookup-equal (var z) (valuation asg)
                   (prime p))
        (:instance pfield::equal-of-sub-and-sub-cancel-1
                   (x 1) (y (lookup-equal z asg)) (z 0) (p p))))

(defruled fsa-dot-of-single
  (implies (and (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z))
           (and (equal (r1cs::dot-product (list (list 1 z)) asg p)
                       (lookup-equal z asg))
                (equal (r1cs::dot-product (list (list 1 1) (list (1- p) z))
                                          asg p)
                       (pfield::sub 1 (lookup-equal z asg) p))))
  :enable (r1cs::dot-product r1cs::fep-of-lookup-equal pfield::sub
           pfield::neg pfield::add pfield::mul)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defun fsa-gates-induct (bs rs zs acc av nav asg p)
  (if (endp bs)
      (list rs zs acc av nav asg p)
    (fsa-gates-induct (cdr bs) (cdr rs) (cdr zs)
                      (lookup-equal (car zs) asg)
                      (list (list 1 (car zs)))
                      (list (list 1 1) (list (1- p) (car zs)))
                      asg p)))

(defruled fsa-ltc-gates-iff
  (implies (and (symbol-listp bs) (symbol-listp zs)
                (bit-listp rs)
                (equal (len rs) (len bs))
                (equal (len zs) (len bs))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (bit-listp (lookup-equal-list bs asg))
                (bitp acc)
                (equal (r1cs::dot-product av asg p) acc)
                (equal (r1cs::dot-product nav asg p) (pfield::sub 1 acc p)))
           (equal (r1cs::r1cs-constraints-holdp
                   (fsa-ltc-gates bs rs zs av nav p) asg p)
                  (equal (lookup-equal-list zs asg)
                         (fsa-ltc-vals (lookup-equal-list bs asg) rs acc))))
  :induct (fsa-gates-induct bs rs zs acc av nav asg p)
  :in-theory (e/d (fsa-ltc-gates fsa-ltc-vals lookup-equal-list
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp symbol-listp
                   fsa-bitp-of-step)
                  ((:e base-prime) fsa-step fsa-gate))
  :hints (("Subgoal *1/2"
           :use ((:instance fsa-gate-iff
                            (b (car bs)) (rbit (car rs)) (z (car zs)))
                 (:instance fsa-dot-of-single (z (car zs)))
                 (:instance fsa-bitp-of-step
                            (x (lookup-equal (car bs) asg))
                            (r (car rs))))))
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The whole gadget.  bs: 252 sum bits; zs: 251 fold outputs (steps 1..251);
; w: result; cs: 251 result bits.

(define fsa-rbits ()
  :verify-guards nil
  (acl2::nat=>lebits 252 (scalar-prime)))

(define fsa-scalar-add-gadget ((a symbolp) (b symbolp) (bs symbol-listp)
                               (zs symbol-listp) (w symbolp)
                               (cs symbol-listp) (p primep))
  :verify-guards nil
  (append (boolean-check-gadget-list bs p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 a) (list 1 b))
                 :b (list (list 1 1))
                 :c (pow2sum-vector bs 0)))
          (fsa-ltc-gates (cdr bs) (cdr (fsa-rbits)) zs
                         (list (list 1 1) (list (1- p) (car bs)))
                         (list (list 1 (car bs)))
                         p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list (scalar-prime) 1))
                 :b (list (list 1 (car (last zs))))
                 :c (append (list (list 1 w) (list (scalar-prime) 1))
                            (pow2sum-neg-vector bs 0))))
          (fb-field-to-lower-bits-le-gadget w cs p)))

(defruled fsa-prime-facts
  (and (< (* 2 (scalar-prime)) (expt 2 252))
       (< (expt 2 252) (base-prime))
       (< (scalar-prime) (expt 2 251))
       (< (expt 2 250) (scalar-prime))
       (equal (car (fsa-rbits)) 1)
       (bit-listp (fsa-rbits))
       (equal (len (fsa-rbits)) 252)
       (equal (len (cdr (fsa-rbits))) 251)
       (equal (lebits=>nat (fsa-rbits)) (scalar-prime)))
  :enable (fsa-rbits))

(defruled fsa-lookup-of-car-last
  (implies (consp zs)
           (equal (lookup-equal (car (last zs)) asg)
                  (car (last (lookup-equal-list zs asg)))))
  :induct (len zs)
  :enable (lookup-equal-list))

(defruled fsa-ltc-of-cons
  (equal (fsa-ltc (cons x xs) (cons r rs) acc)
         (fsa-ltc xs rs (fsa-step x r acc)))
  :enable fsa-ltc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *fsa-r* (scalar-prime))
(defrule fsa-r-lt-p (< (scalar-prime) (base-prime)))

(defruled fsa-dot-sum
  (implies (and (symbolp a) (symbolp b) (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a) (r1cs::valuation-bindsp asg b))
           (and (equal (r1cs::dot-product (list (list 1 a) (list 1 b)) asg p)
                       (pfield::add (lookup-equal a asg) (lookup-equal b asg) p))
                (equal (r1cs::dot-product (list (list 1 1)) asg p) 1)
                (equal (r1cs::dot-product (list (list *fsa-r* 1)) asg p)
                       (scalar-prime))
                (equal (r1cs::dot-product (list (list 1 1) (list (1- p) a)) asg p)
                       (pfield::sub 1 (lookup-equal a asg) p))
                (equal (r1cs::dot-product (list (list 1 a)) asg p)
                       (lookup-equal a asg))))
  :in-theory (e/d (r1cs::dot-product r1cs::fep-of-lookup-equal pfield::sub
           pfield::neg pfield::add pfield::mul) ((:e base-prime)))
  :use ((:instance r1cs::fep-of-lookup-equal (var a) (valuation asg) (prime p))
        (:instance r1cs::fep-of-lookup-equal (var b) (valuation asg) (prime p))
        (:instance fsa-dot-of-single (z a)) fsa-r-lt-p))

(defruled fsa-car-of-lookup-equal-list
  (implies (consp xs)
           (equal (car (lookup-equal-list xs asg)) (lookup-equal (car xs) asg)))
  :enable lookup-equal-list)
(defruled fsa-cdr-of-lookup-equal-list
  (equal (cdr (lookup-equal-list xs asg)) (lookup-equal-list (cdr xs) asg))
  :enable lookup-equal-list)

(defruled fsa-bit-list-parts
  (implies (and (bit-listp (lookup-equal-list xs asg)) (consp xs))
           (and (bit-listp (lookup-equal-list (cdr xs) asg))
                (bitp (lookup-equal (car xs) asg))))
  :enable (lookup-equal-list bit-listp))

(defruled fsa-bitp-of-one-minus
  (implies (and (bitp x) (equal p (base-prime)))
           (and (bitp (pfield::add 1 (pfield::neg x p) p))
                (bitp (mod (+ 1 (pfield::neg x p)) p))))
  :in-theory (e/d (bitp pfield::add) ((:e base-prime))))

(defruled fsa-car-last-facts
  (implies (and (symbol-listp zs) (consp zs)
                (r1cs::valuation-binds-allp asg zs))
           (and (symbolp (car (last zs)))
                (r1cs::valuation-bindsp asg (car (last zs)))))
  :induct (len zs)
  :enable (r1cs::valuation-binds-allp))

(defruled fsa-one-minus-twice
  (implies (and (bitp x) (equal p (base-prime)))
           (and (equal (pfield::add 1 (pfield::add (+ -1 p) x p) p) x)
                (equal (pfield::sub 1 (pfield::sub 1 x p) p) x)
                (equal (pfield::add 1 (pfield::neg (pfield::add 1 (pfield::neg x p) p) p) p) x)))
  :in-theory (e/d (bitp) ()))

(defruled fsa-dot-ternary-c
  (implies (and (symbolp w) (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w))
           (equal (r1cs::dot-product
                   (list* (list 1 w) (list *fsa-r* 1) v) asg p)
                  (pfield::add (pfield::add (lookup-equal w asg) (scalar-prime) p)
                               (r1cs::dot-product v asg p) p)))
  :in-theory (e/d (r1cs::dot-product r1cs::fep-of-lookup-equal pfield::add
                   pfield::mul) ((:e base-prime)))
  :use ((:instance r1cs::fep-of-lookup-equal (var w) (valuation asg) (prime p))
        fsa-r-lt-p))

(defruled fsa-len-cdr
  (implies (consp x) (equal (len (cdr x)) (+ -1 (len x)))))

(defruled fsa-scalar-add-gadget-iff
  (implies (and (symbolp a) (symbolp b) (symbolp w)
                (symbol-listp bs) (symbol-listp zs) (symbol-listp cs)
                (equal (len bs) 252) (equal (len zs) 251)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a) (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg cs))
           (b* ((bs$ (lookup-equal-list bs asg))
                (zs$ (lookup-equal-list zs asg))
                (cs$ (lookup-equal-list cs asg))
                (w$ (lookup-equal w asg))
                (n (lebits=>nat bs$)))
             (equal (r1cs::r1cs-constraints-holdp
                     (fsa-scalar-add-gadget a b bs zs w cs p) asg p)
                    (and (bit-listp bs$)
                         (equal (pfield::add (lookup-equal a asg)
                                             (lookup-equal b asg) p)
                                (mod n p))
                         (equal zs$ (fsa-ltc-vals (cdr bs$) (cdr (fsa-rbits))
                                                  (pfield::sub 1 (car bs$) p)))
                         (equal (pfield::mul (scalar-prime) (lookup-equal (car (last zs)) asg) p)
                                (r1cs::dot-product
                                 (list* (list 1 w) (list *fsa-r* 1)
                                        (pow2sum-neg-vector bs 0))
                                 asg p))
                         (bit-listp cs$)
                         (equal w$ (mod (lebits=>nat cs$) p))))))
  :do-not-induct t
  :in-theory (e/d (fsa-scalar-add-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product-of-append
                   boolean-check-gadget-list-to-bit-listp
                   fb-field-to-lower-bits-le-gadget-to-mod
                   pow2sum-vector-to-mod-of-lebits=>nat
                   pow2sum-neg-vector-to-mod-of-lebits=>nat
                   fsa-car-of-lookup-equal-list
                   fsa-bit-list-parts fsa-len-cdr fsa-one-minus-twice fsa-bitp-of-one-minus
                   fsa-cdr-of-lookup-equal-list
                   fsa-dot-sum)
                  ((:e base-prime) bitp fsa-ltc-vals fsa-rbits (:e fsa-rbits)))
  :use ((:instance fsa-ltc-gates-iff
                   (bs (cdr bs)) (rs (cdr (fsa-rbits)))
                   (acc (pfield::sub 1 (lookup-equal (car bs) asg) (base-prime)))
                   (av (list (list 1 1) (list (1- (base-prime)) (car bs))))
                   (nav (list (list 1 (car bs)))))
        (:instance fsa-car-last-facts)
        (:instance fsa-dot-of-single (z (car (last zs))))
        fsa-prime-facts))

(defrule fsa-ternary-solve
  (implies (and (equal p (base-prime))
                (pfield::fep w p) (natp n) (< n p) (bitp z)
                (equal m (mod (- n) p))
                (equal (pfield::mul *fsa-r* z p)
                       (pfield::add (pfield::add w *fsa-r* p) m p)))
           (equal w (if (equal z 1) n (mod (- n *fsa-r*) p))))
  :in-theory (e/d (bitp pfield::add pfield::mul pfield::fep) ((:e base-prime)))
  :rule-classes nil
  :use fsa-r-lt-p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled fsa-nat-bound
  (< (lebits=>nat bits) (expt 2 (len bits)))
  :enable lebits=>nat
  :use (:instance acl2::lendian=>nat-upper-bound (base 2) (digits bits)))

(defrule fsa-sum-is-n
  (implies (and (equal p (base-prime))
                (scalarp a) (scalarp b) (natp n) (< n (expt 2 252))
                (equal (pfield::add a b p) (mod n p)))
           (equal n (+ a b)))
  :rule-classes nil
  :in-theory (e/d (scalarp pfield::add pfield::fep) ((:e base-prime)))
  :use fsa-prime-facts)

(defruled fsa-step-first
  (implies (and (bitp x) (equal p (base-prime)))
           (equal (pfield::add 1 (pfield::neg x p) p)
                  (fsa-step x 1 0)))
  :enable (bitp fsa-step))

(defrule fsa-flag-is-lt
  (implies (and (bit-listp bs$) (equal (len bs$) 252)
                (equal p (base-prime))
                (equal zs$ (fsa-ltc-vals (cdr bs$) (cdr (fsa-rbits))
                                         (pfield::add 1 (pfield::neg (car bs$) p) p))))
           (equal (car (last zs$))
                  (if (< (lebits=>nat bs$) *fsa-r*) 1 0)))
  :rule-classes nil
  :do-not-induct t
  :in-theory (e/d (fsa-step-first fsa-ltc-of-cons bit-listp)
                  ((:e base-prime) fsa-rbits (:e fsa-rbits) fsa-ltc-vals))
  :use ((:instance fsa-last-of-ltc-vals (xs (cdr bs$)) (rs (cdr (fsa-rbits)))
                   (acc (fsa-step (car bs$) 1 0)))
        (:instance fsa-ltc-is-compare (xs bs$) (rs (fsa-rbits)) (acc 0))
        fsa-prime-facts)
  :expand ((fsa-ltc bs$ (fsa-rbits) 0)))

(defruled fsa-funspec-cases
  (implies (and (scalarp a) (scalarp b))
           (equal (scalar-add-funspec a b)
                  (if (< (+ a b) *fsa-r*) (+ a b) (- (+ a b) *fsa-r*))))
  :in-theory (e/d (scalar-add-funspec scalarp pfield::add pfield::fep) ())
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrule fsa-ternary-gate-solve
  (implies (and (equal p (base-prime))
                (symbolp w) (symbol-listp bs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg))
                (< (lebits=>nat (lookup-equal-list bs asg)) p)
                (bitp z)
                (equal (pfield::mul *fsa-r* z p)
                       (r1cs::dot-product
                        (list* (list 1 w) (list *fsa-r* 1)
                               (pow2sum-neg-vector bs 0))
                        asg p)))
           (equal (lookup-equal w asg)
                  (if (equal z 1)
                      (lebits=>nat (lookup-equal-list bs asg))
                    (mod (- (lebits=>nat (lookup-equal-list bs asg)) *fsa-r*)
                         p))))
  :rule-classes nil
  :in-theory (e/d (fsa-dot-ternary-c)
                  ((:e base-prime)))
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs bs) (i 0))
        (:instance fsa-ternary-solve
                   (m (r1cs::dot-product (pow2sum-neg-vector bs 0) asg p))
                   (w (lookup-equal w asg))
                   (n (lebits=>nat (lookup-equal-list bs asg))))
        (:instance r1cs::fep-of-lookup-equal (var w) (valuation asg) (prime p))))

(defruled fsa-scalar-add-gadget-sound
  (implies (and (symbolp a) (symbolp b) (symbolp w)
                (symbol-listp bs) (symbol-listp zs) (symbol-listp cs)
                (equal (len bs) 252) (equal (len zs) 251) (equal (len cs) 251)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a) (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg cs)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (fsa-scalar-add-gadget a b bs zs w cs p) asg p))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (w$ (lookup-equal w asg)))
             (and (equal w$ (scalar-add-funspec a$ b$))
                  (equal (lookup-equal-list cs asg)
                         (acl2::nat=>lebits 251 w$)))))
  :do-not-induct t
  :in-theory (e/d (fsa-scalar-add-gadget-iff
                   fsa-funspec-cases)
                  ((:e base-prime) fsa-ltc-vals fsa-rbits (:e fsa-rbits)
                   fsa-scalar-add-gadget scalar-add-funspec))
  :use ((:instance fsa-nat-bound (bits (lookup-equal-list bs asg)))
        (:instance fsa-sum-is-n
                   (a (lookup-equal a asg)) (b (lookup-equal b asg))
                   (n (lebits=>nat (lookup-equal-list bs asg))))
        (:instance fsa-lookup-of-car-last)
        (:instance fsa-flag-is-lt
                   (bs$ (lookup-equal-list bs asg))
                   (zs$ (lookup-equal-list zs asg)))
        (:instance fsa-ternary-gate-solve
                   (z (lookup-equal (car (last zs)) asg)))
        (:instance fb-nat=>lebits-when-mod-lebits=>nat
                   (v (lookup-equal w asg))
                   (bs (lookup-equal-list cs asg)))
        fsa-prime-facts
        fsa-r-lt-p))

(defrule fsa-ternary-holds
  (implies (and (equal p (base-prime))
                (natp n) (< n p) (bitp z)
                (equal m (mod (- n) p))
                (equal w (if (equal z 1) n (- n *fsa-r*)))
                (or (equal z 1) (<= *fsa-r* n)))
           (equal (pfield::mul *fsa-r* z p)
                  (pfield::add (pfield::add w *fsa-r* p) m p)))
  :rule-classes nil
  :in-theory (e/d (bitp pfield::add pfield::mul pfield::fep) ((:e base-prime)))
  :use fsa-r-lt-p
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrule fsa-ternary-gate-holds
  (implies (and (equal p (base-prime))
                (symbolp w) (symbol-listp bs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg))
                (< (lebits=>nat (lookup-equal-list bs asg)) p)
                (bitp z)
                (equal (lookup-equal w asg)
                       (if (equal z 1)
                           (lebits=>nat (lookup-equal-list bs asg))
                         (- (lebits=>nat (lookup-equal-list bs asg)) *fsa-r*)))
                (or (equal z 1)
                    (<= *fsa-r* (lebits=>nat (lookup-equal-list bs asg)))))
           (equal (pfield::mul *fsa-r* z p)
                  (r1cs::dot-product
                   (list* (list 1 w) (list *fsa-r* 1)
                          (pow2sum-neg-vector bs 0))
                   asg p)))
  :rule-classes nil
  :in-theory (e/d (fsa-dot-ternary-c) ((:e base-prime)))
  :use ((:instance pow2sum-neg-vector-to-mod-of-lebits=>nat (xs bs) (i 0))
        (:instance fsa-ternary-holds
                   (m (r1cs::dot-product (pow2sum-neg-vector bs 0) asg p))
                   (w (lookup-equal w asg))
                   (n (lebits=>nat (lookup-equal-list bs asg))))))

(defruled fsa-add-small
  (implies (and (scalarp a) (scalarp b) (equal p (base-prime)))
           (equal (pfield::add a b p) (+ a b)))
  :in-theory (e/d (scalarp pfield::add pfield::fep) ((:e base-prime)))
  :use fsa-prime-facts)

(defrule fsa-n-of-witness
  (implies (and (scalarp a) (scalarp b)
                (equal bs$ (acl2::nat=>lebits 252 (+ a b))))
           (and (equal (lebits=>nat bs$) (+ a b))
                (bit-listp bs$)
                (equal (len bs$) 252)))
  :rule-classes nil
  :in-theory (enable scalarp pfield::fep acl2::lebits=>nat-of-nat=>lebits
                     acl2::bit-listp-of-nat=>lebits)
  :use fsa-prime-facts)

(defruled fsa-251-roundtrip
  (implies (scalarp w)
           (equal (lebits=>nat (acl2::nat=>lebits 251 w)) w))
  :in-theory (enable scalarp pfield::fep acl2::lebits=>nat-of-nat=>lebits)
  :use fsa-prime-facts)

(defrule fsa-cs-of-witness
  (implies (and (scalarp a) (scalarp b)
                (equal w (scalar-add-funspec a b))
                (equal cs$ (acl2::nat=>lebits 251 w)))
           (and (equal (lebits=>nat cs$) w)
                (bit-listp cs$)))
  :rule-classes nil
  :in-theory (e/d (acl2::bit-listp-of-nat=>lebits) (scalar-add-funspec))
  :use ((:instance fsa-251-roundtrip (w (scalar-add-funspec a b)))))

(defruled fsa-scalar-add-gadget-complete
  (implies (and (symbolp a) (symbolp b) (symbolp w)
                (symbol-listp bs) (symbol-listp zs) (symbol-listp cs)
                (equal (len bs) 252) (equal (len zs) 251) (equal (len cs) 251)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a) (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg cs)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (equal (lookup-equal-list bs asg)
                       (acl2::nat=>lebits 252 (+ (lookup-equal a asg)
                                                 (lookup-equal b asg))))
                (equal (lookup-equal-list zs asg)
                       (fsa-ltc-vals (cdr (lookup-equal-list bs asg))
                                     (cdr (fsa-rbits))
                                     (fsa-step (car (lookup-equal-list bs asg))
                                               1 0)))
                (equal (lookup-equal w asg)
                       (scalar-add-funspec (lookup-equal a asg)
                                           (lookup-equal b asg)))
                (equal (lookup-equal-list cs asg)
                       (acl2::nat=>lebits 251 (lookup-equal w asg))))
           (r1cs::r1cs-constraints-holdp
            (fsa-scalar-add-gadget a b bs zs w cs p) asg p))
  :do-not-induct t
  :in-theory (e/d (fsa-scalar-add-gadget-iff
                   fsa-funspec-cases fsa-add-small fsa-car-of-lookup-equal-list
                   acl2::lebits=>nat-of-nat=>lebits
                   acl2::bit-listp-of-nat=>lebits)
                  ((:e base-prime) fsa-ltc-vals fsa-rbits (:e fsa-rbits)
                   fsa-scalar-add-gadget scalar-add-funspec))
  :use ((:instance fsa-n-of-witness (a (lookup-equal a asg)) (b (lookup-equal b asg))
                   (bs$ (lookup-equal-list bs asg)))
        (:instance fsa-cs-of-witness (a (lookup-equal a asg)) (b (lookup-equal b asg))
                   (w (lookup-equal w asg)) (cs$ (lookup-equal-list cs asg)))
        (:instance fsa-step-first (x (car (lookup-equal-list bs asg))))
        (:instance fsa-bit-list-parts (xs bs))
        (:instance fsa-lookup-of-car-last)
        (:instance fsa-flag-is-lt
                   (bs$ (lookup-equal-list bs asg))
                   (zs$ (lookup-equal-list zs asg)))
        (:instance fsa-ternary-gate-holds
                   (z (lookup-equal (car (last zs)) asg)))
        fsa-prime-facts
        fsa-r-lt-p)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))
