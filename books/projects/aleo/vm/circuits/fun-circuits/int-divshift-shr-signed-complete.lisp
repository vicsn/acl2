; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness of variable-mode signed shr_wrapped for widths other than 128.

(in-package "ALEOVM")

(include-book "int-divshift-shr-signed")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/last" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sshr-witness-hyps ()
  '(and (equal (lookup-equal-list nexts asg)
               (int-divshift-sub-each
                (int-shift-witness-values
                 (+ (lebits=>nat (rev (int->lebits x n)))
                    (car (last (int->lebits x n))))
                 (lookup-equal-list ebits asg)
                 0)
                (car (last (int->lebits x n)))))
        (equal (lookup-equal-list zs asg)
               (int->lebits
                (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                         (car (last (int->lebits x n))))
                      (expt 2 (mod e n)))
                   (- (car (last (int->lebits x n)))))
                (* 2 n)))))

(defruledl int-divshift-sshr-chain-holds
  (implies (and (int-divshift-sshr-common-hyps)
                (int-divshift-sshr-witness-hyps))
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-first-step (car ebits) xs (car nexts)
                                               (car (last xs)) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-var-chain (car nexts) (cdr ebits)
                                              (cdr nexts) (car (last xs)) 1 p)
                 asg p)))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-value-facts)
        (:instance int-divshift-sshr-msb-wire)
        (:instance int-divshift-sshr-ilen)
        (:instance int-divshift-sshr-chain-complete (m (car (last xs)))))
  :in-theory (e/d (bitp posp-when-integer-widthp)
                  (int-divshift-sshr-value-facts
                   int-divshift-sshr-msb-wire
                   int-divshift-sshr-ilen
                   int-divshift-sshr-chain-complete
                   int-divshift-sshr-first-step
                   int-divshift-sshr-var-chain
                   int-shift-witness-values
                   int-divshift-sub-each
                   integer-widthp
                   int->lebits mod lookup-equal lookup-equal-list
                   int-shift-after int-shift-pow)))

(defruledl int-divshift-sshr-final-value
  (implies (and (int-divshift-sshr-common-hyps)
                (int-divshift-sshr-witness-hyps))
           (and (equal (lookup-equal (car (last nexts)) asg)
                       (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                                (car (last (int->lebits x n))))
                             (expt 2 (mod e n)))
                          (- (car (last (int->lebits x n))))))
                (natp (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                               (car (last (int->lebits x n))))
                            (expt 2 (mod e n)))
                         (- (car (last (int->lebits x n))))))
                (< (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                            (car (last (int->lebits x n))))
                         (expt 2 (mod e n)))
                      (- (car (last (int->lebits x n)))))
                   (expt 2 (* 2 n)))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-value-facts)
        (:instance int-divshift-sshr-ilen)
        (:instance int-divshift-sshr-msb-wire (xs nexts))
        (:instance int-shift-witness-last-is-run
                   (cur (+ (lebits=>nat (rev (int->lebits x n)))
                           (car (last (int->lebits x n)))))
                   (bits (lookup-equal-list ebits asg))
                   (i 0))
        (:instance int-divshift-sshr-run-final
                   (c (+ (lebits=>nat (rev (int->lebits x n)))
                         (car (last (int->lebits x n))))))
        (:instance int-divshift-sshr-last-sub-each
                   (vals (int-shift-witness-values
                          (+ (lebits=>nat (rev (int->lebits x n)))
                             (car (last (int->lebits x n))))
                          (lookup-equal-list ebits asg)
                          0))
                   (m (car (last (int->lebits x n)))))
        (:instance int-divshift-sshr-final-bound
                   (r (lebits=>nat (rev (int->lebits x n))))
                   (mv (car (last (int->lebits x n))))
                   (s (mod e n))))
  :in-theory (e/d (bitp posp-when-integer-widthp
                   consp-of-int-shift-witness-values
                   acl2::mod-when-<)
                  (int-divshift-sshr-value-facts
                   int-divshift-sshr-msb-wire
                   int-divshift-sshr-ilen
                   int-shift-witness-last-is-run
                   int-divshift-sshr-run-final
                   int-divshift-sshr-last-sub-each
                   int-divshift-sshr-final-bound
                   int-shift-witness-values
                   int-divshift-sub-each
                   integer-widthp
                   int->lebits lookup-equal lookup-equal-list
                   int-shift-run int-shift-after int-shift-pow)))

(defruledl int-divshift-sshr-lower-holds
  (implies (and (int-divshift-sshr-common-hyps)
                (int-divshift-sshr-witness-hyps))
           (r1cs::r1cs-constraints-holdp
            (int-shift-lower-gadget (car (last nexts)) zs p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-final-value)
        (:instance int-divshift-sshr-ilen)
        (:instance int-divshift-sshr-msb-wire (xs nexts))
        (:instance int-shift-below-prime
                   (v (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                               (car (last (int->lebits x n))))
                            (expt 2 (mod e n)))
                         (- (car (last (int->lebits x n)))))))
        (:instance lebits=>nat-of-int->lebits
                   (x (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                               (car (last (int->lebits x n))))
                            (expt 2 (mod e n)))
                         (- (car (last (int->lebits x n))))))
                   (n (* 2 n)))
        (:instance int-shift-lower-when-bits
                   (final (car (last nexts)))))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit
                   acl2::mod-when-< acl2::ifix-when-integerp)
                  (int-divshift-sshr-final-value
                   int-divshift-sshr-ilen
                   int-divshift-sshr-msb-wire
                   int-shift-below-prime
                   lebits=>nat-of-int->lebits
                   int-shift-lower-when-bits
                   int-shift-lower-gadget
                   integer-widthp
                   int->lebits lookup-equal lookup-equal-list mod)))

(defruled int-divshift-shr-wrapped-signed-gadget-complete
  :short "R1CS-COMPLETE of variable-mode signed @('shr_wrapped') for every
          width other than 128: the running values are the left-shift
          witnesses of @('R + msb') minus the msb, and @('zs') is the
          @('2n')-bit image of @('(R + msb) * 2^(e mod n) - msb')."
  (implies (and (int-divshift-sshr-common-hyps)
                (int-divshift-sshr-witness-hyps))
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-signed-gadget xs ebits nexts zs p) asg p)
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    t)
                       (int-shr-wrapped-spec x e t n))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-chain-holds)
        (:instance int-divshift-sshr-lower-holds)
        (:instance int-divshift-sshr-ilen)
        (:instance int-divshift-shr-wrapped-signed-gadget-sound))
  :in-theory (e/d (int-divshift-shr-signed-gadget
                   r1cs::r1cs-constraints-holdp-of-append)
                  (int-divshift-sshr-chain-holds
                   int-divshift-sshr-lower-holds
                   int-divshift-sshr-ilen
                   int-divshift-shr-wrapped-signed-gadget-sound
                   int-divshift-sshr-first-step
                   int-divshift-sshr-var-chain
                   int-shift-lower-gadget
                   integer-widthp
                   int->lebits lookup-equal lookup-equal-list mod)))
