; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode unsigned shr_wrapped at width 128.  snarkVM computes
; 2^(e mod 128) with the same field power chain as shl_wrapped
; (int-divshift-pow2-gadget), takes its 128 low bits as a u128 divisor, and
; calls div_wrapped, which for unsigned operands is
; unsigned_division_via_witness (unsigned-medium-div-gadget at width 128).

(in-package "ALEOVM")

(include-book "int-divshift-shl-wrapped-128")
(include-book "int-divshift-medium-div-complete")
(include-book "int-divshift-unsigned-div")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-shr-unsigned-128-gadget ((xs symbol-listp)
                                              (rbits symbol-listp)
                                              (sqs symbol-listp)
                                              (ts symbol-listp)
                                              (ys symbol-listp)
                                              (qs symbol-listp)
                                              (rs symbol-listp)
                                              (ll symbolp) (hl symbolp)
                                              (lh symbolp) (hh symbolp)
                                              (ms symbol-listp)
                                              (mcl symbol-listp)
                                              (mch symbol-listp)
                                              (ls symbol-listp)
                                              (l symbolp)
                                              (ds symbol-listp)
                                              (d symbolp)
                                              (one symbolp)
                                              (p primep))
  :verify-guards nil
  :short "Variable-mode unsigned @('shr_wrapped') at width 128."
  (append (int-divshift-pow2-gadget rbits sqs ts p)
          (int-shift-lower-gadget (car (last ts)) ys p)
          (unsigned-medium-div-gadget xs ys qs rs ll hl lh hh
                                      ms mcl mch ls l ds d one p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-su128-pow-facts
  (implies (natp e)
           (and (natp (expt 2 (mod e 128)))
                (< (expt 2 (mod e 128)) (expt 2 128))
                (int-valuep (expt 2 (mod e 128)) nil 128)
                (not (equal (expt 2 (mod e 128)) 0))))
  :use (:instance acl2::<-of-expt-and-expt-same-base
                  (r 2) (i (mod e 128)) (j 128))
  :enable (int-valuep int-min int-max)
  :disable acl2::<-of-expt-and-expt-same-base)

(defruled int-divshift-pow2-lower-128-sound
  :short "The power chain and the 128-bit decomposition force the divisor
          bits to be those of @('2^(e mod 128)')."
  (implies (and (equal p (base-prime))
                (primep p)
                (natp e)
                (symbol-listp rbits)
                (symbol-listp sqs)
                (symbol-listp ts)
                (symbol-listp ys)
                (equal (len rbits) 7)
                (equal (len sqs) 6)
                (equal (len ts) 6)
                (equal (len ys) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rbits)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ts)
                (r1cs::valuation-bindsp asg (car (last ts)))
                (r1cs::valuation-binds-allp asg ys)
                (equal (lookup-equal-list rbits asg)
                       (rev (int->lebits (mod e 128) 7)))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last ts)) ys p) asg p))
           (equal (lookup-equal-list ys asg)
                  (int->lebits (expt 2 (mod e 128)) 128)))
  :do-not-induct t
  :use ((:instance int-divshift-rbits-facts
                   (vals (lookup-equal-list rbits asg)))
        (:instance int-divshift-pow2-gadget-iff)
        (:instance int-divshift-final-of-lookup)
        (:instance int-divshift-pow2-final-value
                   (rbitvals (lookup-equal-list rbits asg)))
        (:instance car-of-lookup-equal-list (keys rbits) (alist asg))
        (:instance lookup-equal-list-of-cdr (keys rbits) (alist asg))
        (:instance int-divshift-su128-pow-facts)
        (:instance int-divshift-lower-128-sound
                   (final (car (last ts)))
                   (v (expt 2 (mod e 128)))))
  :in-theory (union-theories '(consp-when-len-6c
                               consp-when-len-7c
                               len-of-cdr-when-len-7c
                               symbolp-of-car-of-last-c)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule consp-when-len-6c
     (implies (equal (len x) 6) (consp x)))
   (defrule consp-when-len-7c
     (implies (equal (len x) 7) (consp x)))
   (defrule len-of-cdr-when-len-7c
     (implies (equal (len x) 7) (equal (+ -1 (len x)) 6)))
   (defrule symbolp-of-car-of-last-c
     (implies (symbol-listp x) (symbolp (car (last x)))))))

(defruled int-divshift-pow2-lower-128-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (natp e)
                (symbol-listp rbits)
                (symbol-listp sqs)
                (symbol-listp ts)
                (symbol-listp ys)
                (equal (len rbits) 7)
                (equal (len sqs) 6)
                (equal (len ts) 6)
                (equal (len ys) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rbits)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ts)
                (r1cs::valuation-bindsp asg (car (last ts)))
                (r1cs::valuation-binds-allp asg ys)
                (equal (lookup-equal-list rbits asg)
                       (rev (int->lebits (mod e 128) 7)))
                (equal (lookup-equal-list sqs asg)
                       (int-divshift-pow2-sqs
                        (car (rev (int->lebits (mod e 128) 7)))
                        (cdr (rev (int->lebits (mod e 128) 7)))))
                (equal (lookup-equal-list ts asg)
                       (int-divshift-pow2-ts
                        (car (rev (int->lebits (mod e 128) 7)))
                        (cdr (rev (int->lebits (mod e 128) 7)))))
                (equal (lookup-equal-list ys asg)
                       (int->lebits (expt 2 (mod e 128)) 128)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last ts)) ys p) asg p)))
  :do-not-induct t
  :use ((:instance int-divshift-rbits-facts
                   (vals (lookup-equal-list rbits asg)))
        (:instance int-divshift-pow2-gadget-iff)
        (:instance int-divshift-final-of-lookup)
        (:instance int-divshift-pow2-final-value
                   (rbitvals (lookup-equal-list rbits asg)))
        (:instance car-of-lookup-equal-list (keys rbits) (alist asg))
        (:instance lookup-equal-list-of-cdr (keys rbits) (alist asg))
        (:instance int-divshift-su128-pow-facts)
        (:instance int-shift-lower-when-bits
                   (final (car (last ts))) (zs ys))
        (:instance lebits=>nat-of-int->lebits
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance bit-listp-of-int->lebits-explicit
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance mod-small-c (x (expt 2 (mod e 128)))))
  :in-theory (union-theories '(consp-when-len-6d
                               consp-when-len-7d
                               len-of-cdr-when-len-7d
                               symbolp-of-car-of-last-d
                               (:e expt) (:e base-prime) (:e natp)
                               (:e ecurve::edwards-bls12-q)
                               ifix-when-natp-c)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule consp-when-len-6d
     (implies (equal (len x) 6) (consp x)))
   (defrule consp-when-len-7d
     (implies (equal (len x) 7) (consp x)))
   (defrule len-of-cdr-when-len-7d
     (implies (equal (len x) 7) (equal (+ -1 (len x)) 6)))
   (defrule symbolp-of-car-of-last-d
     (implies (symbol-listp x) (symbolp (car (last x)))))
   (defrule ifix-when-natp-c
     (implies (natp x) (equal (ifix x) x)))
   (defruled mod-small-c
     (implies (and (natp x) (< x (expt 2 128)))
              (and (equal (mod x (expt 2 128)) x)
                   (< x (base-prime))))
     :enable (acl2::mod-when-< (:e base-prime)
                               (:e ecurve::edwards-bls12-q)))))

(defruled int-divshift-shr-unsigned-128-spec
  (implies (and (int-valuep x nil 128)
                (natp e))
           (equal (int-div-wrapped-spec x (expt 2 (mod e 128)) nil 128)
                  (int-shr-wrapped-spec x e nil 128)))
  :do-not-induct t
  :use ((:instance int-divshift-su128-pow-facts)
        (:instance acl2::floor-bound-copy
                   (x x) (y (expt 2 (mod e 128)))))
  :enable (int-div-wrapped-spec int-shr-wrapped-spec int-wrap
           int-valuep int-min int-max
           acl2::truncate-becomes-floor
           acl2::mod-when-<)
  :disable (truncate floor)
  :prep-lemmas
  ((defruled acl2::floor-bound-copy
     (implies (and (natp x) (posp y))
              (and (<= 0 (floor x y))
                   (<= (floor x y) x)))
     :enable acl2::floor-when-<-of-0-arg2-copy
     :prep-lemmas
     ((defrule acl2::floor-when-<-of-0-arg2-copy
        (implies (and (natp x) (posp y))
                 (<= (floor x y) x))
        :use (:instance acl2::floor-bound-arg1-linear-copy)
        :prep-lemmas
        ((defruled acl2::floor-bound-arg1-linear-copy
           (implies (and (natp x) (posp y))
                    (<= (floor x y) (/ x y)))
           :enable acl2::my-floor-upper-bound)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-su128-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (int-valuep x nil 128)
        (natp e)
        (symbol-listp xs) (symbol-listp rbits) (symbol-listp sqs)
        (symbol-listp ts) (symbol-listp ys)
        (symbol-listp qs) (symbol-listp rs)
        (symbolp ll) (symbolp hl) (symbolp lh) (symbolp hh)
        (symbol-listp ms) (symbol-listp mcl) (symbol-listp mch)
        (symbol-listp ls) (symbolp l) (symbol-listp ds) (symbolp d)
        (symbolp one)
        (equal (len xs) 128) (equal (len rbits) 7)
        (equal (len sqs) 6) (equal (len ts) 6) (equal (len ys) 128)
        (equal (len qs) 128) (equal (len rs) 128) (equal (len ms) 128)
        (equal (len mcl) 65) (equal (len mch) 128) (equal (len ls) 128)
        (equal (len ds) 128)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rbits)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg ts)
        (r1cs::valuation-bindsp asg (car (last ts)))
        (r1cs::valuation-binds-allp asg ys)
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
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))
        (equal (lookup-equal-list rbits asg)
               (rev (int->lebits (mod e 128) 7)))))

(defruled int-divshift-shr-unsigned-128-gadget-sound
  :short "R1CS-SOUND of variable-mode unsigned @('shr_wrapped') at width
          128."
  (implies (and (int-divshift-su128-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-unsigned-128-gadget
                  xs rbits sqs ts ys qs rs ll hl lh hh ms mcl mch ls l ds d
                  one p)
                 asg p))
           (and (bit-listp (lookup-equal-list qs asg))
                (equal (lebits->int (lookup-equal-list qs asg) nil)
                       (int-shr-wrapped-spec x e nil 128))))
  :do-not-induct t
  :use ((:instance int-divshift-pow2-lower-128-sound)
        (:instance int-divshift-su128-pow-facts)
        (:instance int-divshift-unsigned-division-128-sound
                   (y (expt 2 (mod e 128)))
                   (low-low ll) (high-low hl) (low-high lh) (high-high hh)
                   (ms-carry-low mcl) (ms-carry-high mch))
        (:instance int-divshift-shr-unsigned-128-spec)
        (:instance lebits->int-when-unsigned
                   (bits (lookup-equal-list qs asg))))
  :in-theory (union-theories '(int-divshift-shr-unsigned-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defruled int-divshift-shr-unsigned-128-gadget-complete
  :short "R1CS-COMPLETE of variable-mode unsigned @('shr_wrapped') at width
          128: the power-chain witnesses and the canonical division
          witnesses for the divisor @('2^(e mod 128)') satisfy the gadget."
  (implies (and (int-divshift-su128-common-hyps)
                (equal y (expt 2 (mod e 128)))
                (equal (lookup-equal-list sqs asg)
                       (int-divshift-pow2-sqs
                        (car (rev (int->lebits (mod e 128) 7)))
                        (cdr (rev (int->lebits (mod e 128) 7)))))
                (equal (lookup-equal-list ts asg)
                       (int-divshift-pow2-ts
                        (car (rev (int->lebits (mod e 128) 7)))
                        (cdr (rev (int->lebits (mod e 128) 7)))))
                (equal (lookup-equal-list ys asg) (int->lebits y 128))
                (equal (lookup-equal-list qs asg)
                       (int->lebits (truncate x y) 128))
                (equal (lookup-equal-list rs asg)
                       (int->lebits (rem x y) 128))
                (equal (lookup-equal ll asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal hl asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (take 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal lh asg)
                       (* (lebits=>nat (take 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal hh asg)
                       (* (lebits=>nat (nthcdr 64 (lookup-equal-list qs asg)))
                          (lebits=>nat (nthcdr 64 (lookup-equal-list ys asg)))))
                (equal (lookup-equal-list ms asg)
                       (int->lebits (* (truncate x y) y) 128))
                (equal (lookup-equal-list mcl asg) (repeat 65 0))
                (equal (lookup-equal-list mch asg) (repeat 128 0))
                (equal (lookup-equal-list ls asg) (int->lebits x 128))
                (equal (lookup-equal l asg) 0)
                (equal (lookup-equal-list ds asg)
                       (int->lebits (+ (expt 2 128) (rem x y) (- y)) 128))
                (equal (lookup-equal d asg) 0))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-shr-unsigned-128-gadget
             xs rbits sqs ts ys qs rs ll hl lh hh ms mcl mch ls l ds d one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-pow2-lower-128-complete)
        (:instance int-divshift-su128-pow-facts)
        (:instance int-divshift-unsigned-division-128-complete
                   (low-low ll) (high-low hl) (low-high lh) (high-high hh)
                   (ms-carry-low mcl) (ms-carry-high mch)))
  :in-theory (union-theories '(int-divshift-shr-unsigned-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))
