; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE of variable-mode signed shl_checked (and shl, shl_assign)
; for widths 8, 16, 32 and 64: when the exponent is below n and x * 2^e is
; in the signed range, the canonical witnesses (the select chain from the
; 2n-bit sign extension and the 3n lower bits of its final value) satisfy
; every constraint, and the low n bits decode to the funspec value.

(in-package "ALEOVM")

(include-book "int-divshift-shl-checked-signed-sound")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(set-prover-step-limit 20000000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sslcc-hyps ()
  '(and (int-divshift-sslc-base-hyps)
        (< e n)
        (int-valuep (* x (expt 2 e)) t n)
        (equal (lookup-equal-list nexts asg)
               (int-shift-witness-values
                (mod x (expt 2 (* 2 n)))
                (int->lebits (mod e n) (1- (integer-length n)))
                0))
        (equal (lookup-equal-list zs asg)
               (int->lebits (* (mod x (expt 2 (* 2 n))) (expt 2 e))
                            (* 3 n)))))

(defrulel int-divshift-sslcc-chain
  (implies (int-divshift-sslcc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-shl-chain-gadget (int-divshift-sext-wires xs) ebits nexts p)
            asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-low-bits)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sext-wire-facts)
        (:instance bit-listp-of-int->lebits-explicit
                   (x (mod e n)) (n (1- (integer-length n))))
        (:instance int-divshift-wide-chain-complete
                   (ys (int-divshift-sext-wires xs))
                   (w (* 2 n))))
  :in-theory (e/d (int-divshift-sslc-consp-when-len)
                  (int-divshift-sslc-sext-small
                   int-divshift-sext-wire-facts
                   int-divshift-wide-chain-complete
                   int-divshift-sl-prime-bound
                   int-divshift-shlc-low-bits
                   int-divshift-shlc-width-facts
                   bit-listp-of-int->lebits-explicit
                   int->lebits
                   mod
                   take
                   nthcdr)))

(defrulel int-divshift-sslcc-lower
  (implies (int-divshift-sslcc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-shift-lower-gadget (car (last nexts)) zs p) asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sl-prime-bound)
        (:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sl-v-bound (s (mod x (expt 2 (* 2 n)))))
        (:instance int-divshift-sslc-final-value
                   (s (mod x (expt 2 (* 2 n)))))
        (:instance int-divshift-wide-lower-complete
                   (final (car (last nexts)))
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e)))))
  :in-theory (e/d (int-divshift-sslc-consp-when-len
                   posp-when-integer-widthp)
                  (int-divshift-wide-lower-complete
                   int-divshift-sslc-final-value
                   int-divshift-sl-v-bound
                   int-divshift-sslc-sext-small
                   int-divshift-sl-prime-bound
                   int->lebits mod lookup-equal)))

(defrulel int-divshift-sslcc-check
  (implies (int-divshift-sslcc-hyps)
           (b* ((v (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
             (and (equal (nthcdr n (int->lebits v (* 2 n)))
                         (repeat n (car (last (int->lebits v n)))))
                  (equal (lebits->int (int->lebits v n) t)
                         (* x (expt 2 e))))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslc-sext-small)
        (:instance int-divshift-sl-mod-shift (m (expt 2 (* 2 n))))
        (:instance int-divshift-sl-product-small)
        (:instance int-divshift-slc-check-complete
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e)))
                   (y (* x (expt 2 e)))))
  :in-theory (e/d (posp-when-integer-widthp)
                  (int-divshift-sslc-sext-small
                   int-divshift-sl-mod-shift
                   int-divshift-sl-product-small
                   int-divshift-slc-check-complete
                   int-valuep
                   int->lebits lebits->int mod nthcdr repeat)))

(defrulel int-divshift-sslcc-msb
  (implies (int-divshift-sslcc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-divshift-msb-eq-gadget (take n (nthcdr n zs))
                                        (nth (1- n) zs))
            asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sslcc-check)
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

(defrulel int-divshift-sslcc-bound
  (implies (int-divshift-sslcc-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-shl-checked-bound-gadget excess) asg p))
  :rule-classes nil
  :do-not-induct t
  :use (:instance int-divshift-sl-sext-excess-holds)
  :in-theory (theory 'minimal-theory))

(defruled int-divshift-shl-checked-signed-gadget-complete
  :short "R1CS-COMPLETE of variable-mode signed @('shl_checked'), @('shl')
          and @('shl_assign') for widths 8 to 64."
  (implies (int-divshift-sslcc-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-shl-checked-signed-gadget
                  xs ebits excess nexts zs p)
                 asg p)
                (equal (lebits->int (take n (lookup-equal-list zs asg)) t)
                       (int-shl-checked-spec x e t n))))
  :do-not-induct t
  :use ((:instance int-divshift-sslcc-chain)
        (:instance int-divshift-sslcc-lower)
        (:instance int-divshift-sslcc-msb)
        (:instance int-divshift-sslcc-bound)
        (:instance int-divshift-sslcc-check)
        (:instance int-divshift-sl-high-of-bits
                   (v (* (mod x (expt 2 (* 2 n))) (expt 2 e))))
        (:instance int-divshift-sl-spec))
  :in-theory (e/d (int-divshift-shl-checked-signed-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   posp-when-integer-widthp)
                  (int-divshift-sl-high-of-bits
                   int-divshift-sl-spec
                   int-shl-checked-spec
                   int-valuep
                   int->lebits lebits->int mod take nthcdr nth repeat
                   lookup-equal)))
