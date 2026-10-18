; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BooleanHash<VARIANT> is_equal, is_not_equal and ternary for any VARIANT
; (snarkVM circuit/collections/src/kary_merkle_tree/helpers/mod.rs), with
; every bit a variable.
;
; is_equal: Boolean::is_equal is !(a ^ b), so each bit emits the xor
; constraint (a + a) * b = a + b - z and the equality bit is the linear
; combination 1 - z.  The fold starts from the constant true, which
; Boolean::bitand drops, so the first equality bit is the accumulator
; (1 - z0) without a constraint; each later bit emits acc * (1 - zi) = wi
; and wi becomes the accumulator.  The output is 1 (VARIANT = 0), 1 - z0
; (VARIANT = 1), or the last w.
;
; is_not_equal is the boolean not of that output, a linear combination.
;
; ternary: Boolean::ternary per bit, c * (a - b) = w - b.

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "../fun-specs/crypto-merkle")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/if")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gap-and-chain-gadget ((acc r1cs::sparse-vectorp)
                              (zs symbol-listp)
                              (ws symbol-listp)
                              (p primep))
  :guard (equal (len zs) (len ws))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "acc * (1 - z) = w for each z, w; w is the next accumulator."
  (if (endp zs)
      nil
    (cons (r1cs::make-r1cs-constraint
           :a acc
           :b (val-not-lc (car zs) p)
           :c (list (list 1 (car ws))))
          (gap-and-chain-gadget (list (list 1 (car ws))) (cdr zs) (cdr ws) p))))

(define gap-and-step (a z (p primep))
  :verify-guards nil
  (pfield::mul a (pfield::sub 1 z p) p))

(define gap-and-fold (a zs (p primep))
  :verify-guards nil
  :short "a * (1 - z0) * (1 - z1) * ..."
  (if (endp zs)
      a
    (gap-and-fold (gap-and-step a (car zs) p) (cdr zs) p)))

(define gap-and-chain-vals (a zs (p primep))
  :verify-guards nil
  :short "The accumulators after each step."
  (if (endp zs)
      nil
    (let ((a1 (gap-and-step a (car zs) p)))
      (cons a1 (gap-and-chain-vals a1 (cdr zs) p)))))

(defruledl gap-dot-product-of-single
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w))
           (equal (r1cs::dot-product (list (list 1 w)) asg p)
                  (lookup-equal w asg)))
  :enable r1cs::dot-product)

(defruledl gap-dot-product-of-not-lc
  (implies (and (primep p)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::dot-product (val-not-lc z p) asg p)
                  (pfield::sub 1 (lookup-equal z asg) p)))
  :enable (r1cs::dot-product val-not-lc))

(defruledl gap-and-constraint-holds
  (implies (and (primep p)
                (symbolp z)
                (symbolp w)
                (r1cs::sparse-vectorp acc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w))
           (equal (r1cs::r1cs-constraint-holdsp
                   (r1cs::r1cs-constraint acc (val-not-lc z p) (list (list 1 w)))
                   asg p)
                  (equal (lookup-equal w asg)
                         (gap-and-step (r1cs::dot-product acc asg p)
                                       (lookup-equal z asg)
                                       p))))
  :enable (r1cs::r1cs-constraint-holdsp
           gap-and-step
           gap-dot-product-of-single
           gap-dot-product-of-not-lc)
  :disable (r1cs::dot-product))

(defruled gap-and-chain-gadget-sound
  (implies (and (symbol-listp zs)
                (symbol-listp ws)
                (equal (len zs) (len ws))
                (primep p)
                (r1cs::sparse-vectorp acc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::r1cs-constraints-holdp
                 (gap-and-chain-gadget acc zs ws p) asg p))
           (equal (lookup-equal-list ws asg)
                  (gap-and-chain-vals (r1cs::dot-product acc asg p)
                                      (lookup-equal-list zs asg)
                                      p)))
  :induct (gap-and-chain-gadget acc zs ws p)
  :enable (gap-and-chain-gadget
           gap-and-chain-vals
           lookup-equal-list
           gap-and-constraint-holds
           gap-dot-product-of-single)
  :disable (r1cs::dot-product val-not-lc))

(defruled gap-and-chain-gadget-complete
  (implies (and (symbol-listp zs)
                (symbol-listp ws)
                (equal (len zs) (len ws))
                (primep p)
                (r1cs::sparse-vectorp acc)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (equal (lookup-equal-list ws asg)
                       (gap-and-chain-vals (r1cs::dot-product acc asg p)
                                           (lookup-equal-list zs asg)
                                           p)))
           (r1cs::r1cs-constraints-holdp
            (gap-and-chain-gadget acc zs ws p) asg p))
  :induct (gap-and-chain-gadget acc zs ws p)
  :enable (gap-and-chain-gadget
           gap-and-chain-vals
           lookup-equal-list
           gap-and-constraint-holds
           gap-dot-product-of-single)
  :disable (r1cs::dot-product val-not-lc))

(defruled gap-last-of-and-chain-vals
  (implies (consp zs)
           (equal (car (last (gap-and-chain-vals a zs p)))
                  (gap-and-fold a zs p)))
  :induct (gap-and-chain-vals a zs p)
  :enable (gap-and-chain-vals gap-and-fold))

(defruled gap-and-fold-of-bits
  (implies (and (bitp a) (bit-listp zs) (primep p))
           (equal (gap-and-fold a zs p)
                  (if (and (equal a 1)
                           (equal zs (repeat (len zs) 0)))
                      1
                    0)))
  :induct (gap-and-fold a zs p)
  :enable (gap-and-fold gap-and-step bit-listp repeat bitp))

(defruled gap-bitxor-list-zero-iff
  (implies (and (bit-listp xs) (bit-listp ys) (equal (len xs) (len ys)))
           (equal (equal (bitxor-list xs ys) (repeat (len xs) 0))
                  (equal xs ys)))
  :induct (bitxor-list xs ys)
  :enable (bitxor-list bitxor bit-listp repeat bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_equal over bit wires as, bs, xor witnesses zs, and witnesses ws
; (one fewer than the bits, or none when there are no bits).

(define gap-bh-is-equal-gadget ((as symbol-listp) (bs symbol-listp)
                                (zs symbol-listp) (ws symbol-listp)
                                (p primep))
  :guard (and (equal (len as) (len bs))
              (equal (len zs) (len as))
              (equal (len ws) (nfix (1- (len as)))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (endp zs)
      nil
    (append (boolean-xor-gadget-list as bs zs p)
            (gap-and-chain-gadget (val-not-lc (car zs) p) (cdr zs) ws p))))

(define gap-bh-is-equal-out ((zs symbol-listp) (ws symbol-listp)
                             asg (p primep))
  :verify-guards nil
  :short "The value of the output linear combination."
  (cond ((endp zs) 1)
        ((endp ws) (pfield::sub 1 (lookup-equal (car zs) asg) p))
        (t (lookup-equal (car (last ws)) asg))))

(defruledl gap-car-last-of-lookup-equal-list
  (implies (consp ws)
           (equal (car (last (lookup-equal-list ws asg)))
                  (lookup-equal (car (last ws)) asg)))
  :induct (len ws)
  :enable lookup-equal-list)

(defruledl gap-and-fold-of-cons
  (equal (gap-and-fold a (cons z r) p)
         (gap-and-fold (gap-and-step a z p) r p))
  :enable gap-and-fold)

(defruledl gap-and-fold-of-nil
  (equal (gap-and-fold a nil p) a)
  :enable gap-and-fold)

(defruledl gap-lookup-equal-list-of-atom
  (implies (atom ws)
           (equal (lookup-equal-list ws asg) nil))
  :enable lookup-equal-list)

(defruledl gap-and-step-of-1
  (implies (primep p)
           (equal (gap-and-step 1 z p)
                  (pfield::sub 1 z p)))
  :enable gap-and-step)

(defruled gap-bh-is-equal-gadget-xor
  (implies (and (symbol-listp as) (symbol-listp bs) (symbol-listp zs)
                (equal (len as) (len bs))
                (equal (len zs) (len as))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (bit-listp (lookup-equal-list as asg))
                (bit-listp (lookup-equal-list bs asg))
                (r1cs::r1cs-constraints-holdp
                 (gap-bh-is-equal-gadget as bs zs ws p) asg p))
           (equal (lookup-equal-list zs asg)
                  (bitxor-list (lookup-equal-list as asg)
                               (lookup-equal-list bs asg))))
  :cases ((consp zs))
  :enable (gap-bh-is-equal-gadget
           boolean-xor-gadget-list-to-bitxor-list)
  :hints (("Subgoal 2" :in-theory (enable lookup-equal-list bitxor-list len))))

(defruled gap-bh-is-equal-out-when-holds
  (implies (and (symbol-listp zs) (symbol-listp ws)
                (consp zs)
                (equal (len ws) (1- (len zs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::r1cs-constraints-holdp
                 (gap-and-chain-gadget (val-not-lc (car zs) p) (cdr zs) ws p)
                 asg p))
           (equal (gap-bh-is-equal-out zs ws asg p)
                  (gap-and-fold 1 (lookup-equal-list zs asg) p)))
  :enable (gap-bh-is-equal-out
           gap-and-step-of-1
           gap-and-fold-of-cons
           gap-and-fold-of-nil
           gap-lookup-equal-list-of-atom
           gap-dot-product-of-not-lc
           gap-car-last-of-lookup-equal-list)
  :disable (val-not-lc r1cs::dot-product)
  :use ((:instance gap-and-chain-gadget-sound
         (acc (val-not-lc (car zs) p)) (zs (cdr zs)))
        (:instance gap-last-of-and-chain-vals
         (a (pfield::sub 1 (lookup-equal (car zs) asg) p))
         (zs (lookup-equal-list (cdr zs) asg))))
  :hints (("Goal" :cases ((consp ws))
           :expand ((lookup-equal-list zs asg)
                    (lookup-equal-list (cdr zs) asg)))))

(defruled gap-bh-is-equal-gadget-sound
  (implies (and (symbol-listp as) (symbol-listp bs)
                (symbol-listp zs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len zs) (len as))
                (equal (len ws) (nfix (1- (len as))))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list as asg))
                (bit-listp (lookup-equal-list bs asg))
                (r1cs::r1cs-constraints-holdp
                 (gap-bh-is-equal-gadget as bs zs ws p) asg p))
           (b* ((out (gap-bh-is-equal-out zs ws asg p)))
             (and (bitp out)
                  (equal (crypto-boolean-hash-is-equal
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         out))))
  :cases ((consp zs))
  :use (gap-bh-is-equal-gadget-xor
        (:instance gap-and-fold-of-bits
         (a 1) (zs (lookup-equal-list zs asg)))
        (:instance gap-bitxor-list-zero-iff
         (xs (lookup-equal-list as asg)) (ys (lookup-equal-list bs asg))))
  :enable (crypto-boolean-hash-is-equal
           len-of-lookup-equal-list)
  :hints (("Subgoal 2" :in-theory (enable gap-bh-is-equal-out
                                          lookup-equal-list
                                          crypto-boolean-hash-is-equal
                                          len))
          ("Subgoal 1" :use (:instance gap-bh-is-equal-out-when-holds)
           :in-theory (enable gap-bh-is-equal-gadget
                              crypto-boolean-hash-is-equal
                              len-of-lookup-equal-list))))

(defruled gap-bh-is-not-equal-gadget-sound
  (implies (and (symbol-listp as) (symbol-listp bs)
                (symbol-listp zs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len zs) (len as))
                (equal (len ws) (nfix (1- (len as))))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list as asg))
                (bit-listp (lookup-equal-list bs asg))
                (r1cs::r1cs-constraints-holdp
                 (gap-bh-is-equal-gadget as bs zs ws p) asg p))
           (b* ((out (pfield::sub 1 (gap-bh-is-equal-out zs ws asg p) p)))
             (and (bitp out)
                  (equal (crypto-boolean-hash-is-not-equal
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         out))))
  :use gap-bh-is-equal-gadget-sound
  :enable (crypto-boolean-hash-is-not-equal bitp))

(defruled gap-bh-is-equal-gadget-complete
  (implies (and (symbol-listp as) (symbol-listp bs)
                (symbol-listp zs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len zs) (len as))
                (equal (len ws) (nfix (1- (len as))))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (bit-listp (lookup-equal-list as asg))
                (bit-listp (lookup-equal-list bs asg))
                (equal (lookup-equal-list zs asg)
                       (bitxor-list (lookup-equal-list as asg)
                                    (lookup-equal-list bs asg)))
                (equal (lookup-equal-list ws asg)
                       (gap-and-chain-vals
                        (pfield::sub 1 (lookup-equal (car zs) asg) p)
                        (lookup-equal-list (cdr zs) asg)
                        p)))
           (r1cs::r1cs-constraints-holdp
            (gap-bh-is-equal-gadget as bs zs ws p) asg p))
  :enable (gap-bh-is-equal-gadget
           boolean-xor-gadget-list-to-bitxor-list
           gap-dot-product-of-not-lc)
  :disable (val-not-lc r1cs::dot-product)
  :use ((:instance gap-and-chain-gadget-complete
         (acc (val-not-lc (car zs) p)) (zs (cdr zs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ternary: c * (a - b) = w - b per bit, the condition shared.

(defruled gap-symbol-listp-of-repeat
  (implies (symbolp c) (symbol-listp (repeat n c)))
  :enable repeat)

(define gap-bh-ternary-gadget ((c symbolp) (as symbol-listp) (bs symbol-listp)
                               (ws symbol-listp) (p primep))
  :guard (and (equal (len as) (len bs))
              (equal (len ws) (len as)))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal" :in-theory (enable gap-symbol-listp-of-repeat))))
  (if-gadget-list (repeat (len as) c) as bs ws p)
  :guard-hints (("Goal" :in-theory (enable gap-symbol-listp-of-repeat))))

(defruledl gap-binds-allp-of-repeat
  (implies (r1cs::valuation-bindsp asg c)
           (r1cs::valuation-binds-allp asg (repeat n c)))
  :enable (repeat r1cs::valuation-binds-allp))

(defruledl gap-lookup-equal-list-of-repeat
  (equal (lookup-equal-list (repeat n c) asg)
         (repeat n (lookup-equal c asg)))
  :enable (repeat lookup-equal-list))

(defruledl gap-bit-listp-of-repeat
  (implies (bitp c) (bit-listp (repeat n c)))
  :enable (repeat bit-listp))

(defruledl gap-if-list-of-repeat-n
  (implies (and (equal (len as) (nfix n)) (equal (len bs) (nfix n)))
           (equal (if-list (repeat n c) as bs p)
                  (if (equal c 1) (true-list-fix as) (true-list-fix bs))))
  :induct (gap-ind3 n as bs)
  :enable (if-list repeat)
  :prep-lemmas
  ((defun gap-ind3 (n as bs)
     (if (zp n) (list as bs) (gap-ind3 (1- n) (cdr as) (cdr bs))))))

(defruledl gap-if-list-of-repeat
  (implies (equal (len as) (len bs))
           (equal (if-list (repeat (len as) c) as bs p)
                  (if (equal c 1) (true-list-fix as) (true-list-fix bs))))
  :use (:instance gap-if-list-of-repeat-n (n (len as))))

(defruled gap-bh-ternary-gadget-iff
  (implies (and (symbolp c) (symbol-listp as) (symbol-listp bs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len ws) (len as))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ws)
                (bitp (lookup-equal c asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (gap-bh-ternary-gadget c as bs ws p) asg p)
                  (equal (lookup-equal-list ws asg)
                         (if (equal (lookup-equal c asg) 1)
                             (lookup-equal-list as asg)
                           (lookup-equal-list bs asg)))))
  :enable (gap-bh-ternary-gadget
           gap-symbol-listp-of-repeat
           gap-binds-allp-of-repeat
           gap-lookup-equal-list-of-repeat
           gap-bit-listp-of-repeat
           len-of-lookup-equal-list)
  :use ((:instance if-gadget-list-to-if-list
         (xs (repeat (len as) c)) (ys as) (zs bs))
        (:instance gap-if-list-of-repeat
         (c (lookup-equal c asg))
         (as (lookup-equal-list as asg))
         (bs (lookup-equal-list bs asg)))))

(defruled gap-bh-ternary-gadget-sound
  (implies (and (symbolp c) (symbol-listp as) (symbol-listp bs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len ws) (len as))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ws)
                (bitp (lookup-equal c asg))
                (bit-listp (lookup-equal-list as asg))
                (bit-listp (lookup-equal-list bs asg))
                (r1cs::r1cs-constraints-holdp
                 (gap-bh-ternary-gadget c as bs ws p) asg p))
           (b* ((out (lookup-equal-list ws asg)))
             (and (bit-listp out)
                  (equal (len out) (len as))
                  (equal (crypto-boolean-hash-ternary
                          (lookup-equal c asg)
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         out))))
  :use gap-bh-ternary-gadget-iff
  :enable (crypto-boolean-hash-ternary len-of-lookup-equal-list))

(defruled gap-bh-ternary-gadget-complete
  (implies (and (symbolp c) (symbol-listp as) (symbol-listp bs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len ws) (len as))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ws)
                (bitp (lookup-equal c asg))
                (equal (lookup-equal-list ws asg)
                       (if (equal (lookup-equal c asg) 1)
                           (lookup-equal-list as asg)
                         (lookup-equal-list bs asg))))
           (r1cs::r1cs-constraints-holdp
            (gap-bh-ternary-gadget c as bs ws p) asg p))
  :use gap-bh-ternary-gadget-iff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness with the inputs made by BooleanHash::new / Boolean::new
; (one boolean check per bit) instead of bit-listp hypotheses.

(defruled gap-bh-is-equal-with-new-sound
  (implies (and (symbol-listp as) (symbol-listp bs)
                (symbol-listp zs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len zs) (len as))
                (equal (len ws) (nfix (1- (len as))))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::r1cs-constraints-holdp
                 (append (boolean-check-gadget-list as p)
                         (boolean-check-gadget-list bs p)
                         (gap-bh-is-equal-gadget as bs zs ws p))
                 asg p))
           (b* ((out (gap-bh-is-equal-out zs ws asg p)))
             (and (bitp out)
                  (equal (crypto-boolean-hash-is-equal
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         out)
                  (equal (crypto-boolean-hash-is-not-equal
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         (pfield::sub 1 out p)))))
  :use (gap-bh-is-equal-gadget-sound
        gap-bh-is-not-equal-gadget-sound
        (:instance boolean-check-gadget-list-to-bit-listp (xs as))
        (:instance boolean-check-gadget-list-to-bit-listp (xs bs))))

(defruled gap-bh-ternary-with-new-sound
  (implies (and (symbolp c) (symbol-listp as) (symbol-listp bs) (symbol-listp ws)
                (equal (len as) (len bs))
                (equal (len ws) (len as))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg as)
                (r1cs::valuation-binds-allp asg bs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::r1cs-constraints-holdp
                 (append (boolean-check-gadget c p)
                         (boolean-check-gadget-list as p)
                         (boolean-check-gadget-list bs p)
                         (gap-bh-ternary-gadget c as bs ws p))
                 asg p))
           (b* ((out (lookup-equal-list ws asg)))
             (and (bit-listp out)
                  (equal (crypto-boolean-hash-ternary
                          (lookup-equal c asg)
                          (lookup-equal-list as asg)
                          (lookup-equal-list bs asg))
                         out))))
  :use (gap-bh-ternary-gadget-sound
        (:instance boolean-check-gadget-to-bitp (x c))
        (:instance boolean-check-gadget-list-to-bit-listp (xs as))
        (:instance boolean-check-gadget-list-to-bit-listp (xs bs))))
