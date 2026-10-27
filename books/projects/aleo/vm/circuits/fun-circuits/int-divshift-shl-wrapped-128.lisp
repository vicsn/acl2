; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode shl_wrapped at width 128, both signednesses.
;
; snarkVM computes 2^(e mod 128) in the field from the low 7 exponent bits,
; most significant first: shift = 1; for each bit, shift = shift^2 then
; shift = ternary(bit, 2 * shift, shift).  The first iteration has constant
; operands, so it folds to the linear combination 1 + b6 with no
; constraint.  Every later iteration emits one squaring constraint
;   (cur) * (cur) = (sq)
; and one Field::ternary constraint, which is int-shift-var-step-gadget
; with index 0:
;   (bit) * (sq) = (t - sq)
; Then Field::to_lower_bits_le(128) (int-shift-lower-gadget) gives the
; 128 bits of the shift as an integer of the same type, and mul_wrapped
; (int-mul-wrapped-gadget, proved at width 128) multiplies.

(in-package "ALEOVM")

(include-book "int-divshift-shift-sound")
(include-book "int-mulpow-wrapped")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/last" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-be-acc ((a natp) (bits bit-listp))
  :returns (v natp :rule-classes :type-prescription)
  :short "Most-significant-first accumulation of bits onto @('a')."
  (if (endp bits)
      (nfix a)
    (int-divshift-be-acc (+ (* 2 (nfix a)) (bfix (car bits))) (cdr bits))))

(define int-divshift-pow2-square-gadget ((cur r1cs::sparse-vectorp) (sq symbolp))
  :short "@('Field::square') of a variable: @('(cur) * (cur) = (sq)')."
  (list (r1cs::make-r1cs-constraint
         :a cur
         :b cur
         :c (list (list 1 sq)))))

(define int-divshift-pow2-chain ((cur r1cs::sparse-vectorp)
                                 (rbits symbol-listp)
                                 (sqs symbol-listp)
                                 (ts symbol-listp)
                                 (p primep))
  (if (or (endp rbits) (endp sqs) (endp ts))
      nil
    (append (int-divshift-pow2-square-gadget cur (car sqs))
            (int-shift-var-step-gadget (car rbits) (car sqs) (car ts) 0 p)
            (int-divshift-pow2-chain (list (list 1 (car ts)))
                                     (cdr rbits) (cdr sqs) (cdr ts) p))))

(define int-divshift-pow2-gadget ((rbits symbol-listp)
                                  (sqs symbol-listp)
                                  (ts symbol-listp)
                                  (p primep))
  :short "@('2^e') from the exponent bits @('rbits'), most significant first.
          The final value is @('(car (last ts))')."
  (int-divshift-pow2-chain (list (list 1 1) (list 1 (car rbits)))
                           (cdr rbits) sqs ts p))

(define int-divshift-shl-wrapped-128-gadget ((xs symbol-listp)
                                             (rbits symbol-listp)
                                             (sqs symbol-listp)
                                             (ts symbol-listp)
                                             (ys symbol-listp)
                                             (ll symbolp)
                                             (hl symbolp)
                                             (lh symbolp)
                                             (zs symbol-listp)
                                             (zh symbol-listp)
                                             (p primep))
  :guard (and (equal (len xs) 128)
              (equal (len ys) 128)
              (equal (len zs) 128)
              (equal (len zh) 65))
  :verify-guards nil
  :short "Variable-mode @('shl_wrapped') at width 128."
  (append (int-divshift-pow2-gadget rbits sqs ts p)
          (int-shift-lower-gadget (car (last ts)) ys p)
          (int-mul-wrapped-gadget xs ys ll hl lh zs zh p)))

(define int-divshift-pow2-sqs ((a natp) (bits bit-listp))
  :short "Canonical squaring witnesses when the running value is @('2^a')."
  (if (endp bits)
      nil
    (cons (expt 2 (* 2 (nfix a)))
          (int-divshift-pow2-sqs (+ (* 2 (nfix a)) (bfix (car bits)))
                                 (cdr bits)))))

(define int-divshift-pow2-ts ((a natp) (bits bit-listp))
  :short "Canonical select witnesses when the running value is @('2^a')."
  (if (endp bits)
      nil
    (cons (expt 2 (+ (* 2 (nfix a)) (bfix (car bits))))
          (int-divshift-pow2-ts (+ (* 2 (nfix a)) (bfix (car bits)))
                                (cdr bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-be-acc-lower
  (implies (natp a)
           (<= a (int-divshift-be-acc a bits)))
  :induct (int-divshift-be-acc a bits)
  :enable (int-divshift-be-acc bfix))

(defruledl int-divshift-be-acc-of-append
  (equal (int-divshift-be-acc a (append x (list b)))
         (+ (* 2 (int-divshift-be-acc a x)) (bfix b)))
  :induct (int-divshift-be-acc a x)
  :enable int-divshift-be-acc)

(defruled int-divshift-be-acc-of-rev
  (implies (bit-listp bits)
           (equal (int-divshift-be-acc 0 (rev bits))
                  (lebits=>nat bits)))
  :induct (len bits)
  :enable (rev int-divshift-be-acc-of-append acl2::lebits=>nat
           acl2::lendian=>nat int-divshift-be-acc bfix))

(defruledl int-divshift-pow2-last-ts
  (implies (consp bits)
           (equal (car (last (int-divshift-pow2-ts a bits)))
                  (expt 2 (int-divshift-be-acc a bits))))
  :induct (int-divshift-pow2-ts a bits)
  :enable (int-divshift-pow2-ts int-divshift-be-acc))

(defruled int-divshift-len-pow2-sqs
  (equal (len (int-divshift-pow2-sqs a bits)) (len bits))
  :enable int-divshift-pow2-sqs)

(defruled int-divshift-len-pow2-ts
  (equal (len (int-divshift-pow2-ts a bits)) (len bits))
  :enable int-divshift-pow2-ts)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-pow-below-prime
  (implies (and (natp k) (< k 252))
           (< (expt 2 k) (base-prime)))
  :use ((:instance acl2::<-of-expt-and-expt-same-base (r 2) (i k) (j 252)))
  :enable ((:e base-prime) (:e ecurve::edwards-bls12-q) (:e expt))
  :disable acl2::<-of-expt-and-expt-same-base)

(defruledl int-divshift-expt-square
  (implies (natp a)
           (equal (* (expt 2 a) (expt 2 a)) (expt 2 (* 2 a))))
  :use (:instance acl2::expt-of-+ (r 2) (i1 a) (i2 a))
  :disable acl2::expt-of-+)

(defruledl int-divshift-pow2-square-holds-iff
  (implies (and (primep p)
                (equal p (base-prime))
                (symbolp sq)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg sq)
                (natp a)
                (< (* 2 a) 252)
                (equal (r1cs::dot-product cur asg p) (expt 2 a)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-pow2-square-gadget cur sq) asg p)
                  (equal (lookup-equal sq asg) (expt 2 (* 2 a)))))
  :do-not-induct t
  :use ((:instance int-divshift-pow-below-prime (k (* 2 a)))
        (:instance int-divshift-expt-square))
  :in-theory (e/d (int-divshift-pow2-square-gadget
                   r1cs::r1cs-constraints-holdp
                   r1cs::r1cs-constraint-holdsp
                   pfield::mul
                   acl2::mod-when-<)
                  (mod floor lookup-equal
                   int-divshift-expt-square
                   int-divshift-pow-below-prime))
  :prep-lemmas
  ((defrule int-divshift-dot-single
     (implies (and (primep p)
                   (symbolp v)
                   (r1cs::r1cs-valuationp asg p)
                   (r1cs::valuation-bindsp asg v))
              (equal (r1cs::dot-product (list (list 1 v)) asg p)
                     (lookup-equal v asg)))
     :enable (r1cs::dot-product pfield::mul pfield::add acl2::mod-when-<))))

(defruledl int-divshift-dot-single-rw
  (implies (and (primep p)
                (symbolp v)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v))
           (equal (r1cs::dot-product (list (list 1 v)) asg p)
                  (lookup-equal v asg)))
  :enable (r1cs::dot-product pfield::mul pfield::add acl2::mod-when-<))

(defruledl int-divshift-dot-first
  (implies (and (primep p)
                (equal p (base-prime))
                (symbolp v)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg v)
                (bitp (lookup-equal v asg)))
           (equal (r1cs::dot-product (list (list 1 1) (list 1 v)) asg p)
                  (expt 2 (lookup-equal v asg))))
  :enable (r1cs::dot-product pfield::mul pfield::add acl2::mod-when-< bitp
           (:e base-prime) (:e ecurve::edwards-bls12-q))
  :disable lookup-equal)

(defruledl int-divshift-pow2-step-iff
  (implies (and (primep p)
                (equal p (base-prime))
                (symbolp bit)
                (symbolp sq)
                (symbolp tt)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg sq)
                (r1cs::valuation-bindsp asg tt)
                (bitp (lookup-equal bit asg))
                (natp a)
                (< (+ (* 2 a) (lookup-equal bit asg)) 252)
                (equal (r1cs::dot-product cur asg p) (expt 2 a)))
           (equal (r1cs::r1cs-constraints-holdp
                   (append (int-divshift-pow2-square-gadget cur sq)
                           (int-shift-var-step-gadget bit sq tt 0 p))
                   asg p)
                  (and (equal (lookup-equal sq asg) (expt 2 (* 2 a)))
                       (equal (lookup-equal tt asg)
                              (expt 2 (+ (* 2 a)
                                         (lookup-equal bit asg)))))))
  :do-not-induct t
  :cases ((equal (lookup-equal sq asg) (expt 2 (* 2 a))))
  :use ((:instance int-divshift-pow2-square-holds-iff)
        (:instance int-shift-var-step-to-after (cur sq) (next tt) (i 0))
        (:instance int-divshift-pow-below-prime (k (* 2 a)))
        (:instance int-divshift-pow-below-prime (k (+ 1 (* 2 a)))))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp-of-append
                   int-shift-after int-shift-pow bitp
                   acl2::expt-of-+)
                  (int-divshift-pow2-square-holds-iff
                   int-shift-var-step-to-after
                   int-divshift-pow-below-prime
                   int-shift-var-step-gadget
                   int-divshift-pow2-square-gadget
                   lookup-equal)))

(local
 (defun int-divshift-pow2-ind (cur rbits sqs ts a asg)
   (declare (ignorable cur))
   (if (or (endp rbits) (endp sqs) (endp ts))
       (list cur a asg)
     (int-divshift-pow2-ind (list (list 1 (car ts)))
                            (cdr rbits) (cdr sqs) (cdr ts)
                            (+ (* 2 (nfix a)) (bfix (lookup-equal (car rbits) asg)))
                            asg))))

(defruledl int-divshift-atom-when-len-zero
  (implies (equal (len x) 0)
           (not (consp x))))

(defruledl int-divshift-pow2-chain-iff
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp rbits)
                (symbol-listp sqs)
                (symbol-listp ts)
                (equal (len sqs) (len rbits))
                (equal (len ts) (len rbits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rbits)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ts)
                (bit-listp (lookup-equal-list rbits asg))
                (natp a)
                (< (int-divshift-be-acc a (lookup-equal-list rbits asg)) 252)
                (equal (r1cs::dot-product cur asg p) (expt 2 a)))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-pow2-chain cur rbits sqs ts p) asg p)
                  (and (equal (lookup-equal-list sqs asg)
                              (int-divshift-pow2-sqs
                               a (lookup-equal-list rbits asg)))
                       (equal (lookup-equal-list ts asg)
                              (int-divshift-pow2-ts
                               a (lookup-equal-list rbits asg))))))
  :induct (int-divshift-pow2-ind cur rbits sqs ts a asg)
  :in-theory (e/d (int-divshift-pow2-chain
                   int-divshift-pow2-sqs
                   int-divshift-pow2-ts
                   int-divshift-be-acc
                   int-divshift-atom-when-len-zero
                   lookup-equal-list
                   r1cs::valuation-binds-allp
                   r1cs::r1cs-constraints-holdp-of-append
                   bit-listp bfix nfix)
                  (int-divshift-pow2-step-iff
                   int-divshift-pow2-square-gadget
                   int-shift-var-step-gadget
                   lookup-equal))
  :hints (("Subgoal *1/2"
           :use ((:instance int-divshift-pow2-step-iff
                            (bit (car rbits)) (sq (car sqs)) (tt (car ts)))
                 (:instance int-divshift-be-acc-lower
                            (a (+ (* 2 a) (lookup-equal (car rbits) asg)))
                            (bits (lookup-equal-list (cdr rbits) asg)))
                 (:instance int-divshift-dot-single-rw (v (car ts)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-pow2-gadget-iff
  :short "The power chain holds exactly for the canonical witnesses, whose
          last select is @('2^v') with @('v') the value of the bits read
          most significant first."
  (implies (and (primep p)
                (equal p (base-prime))
                (symbol-listp rbits)
                (consp rbits)
                (symbol-listp sqs)
                (symbol-listp ts)
                (equal (len sqs) (1- (len rbits)))
                (equal (len ts) (1- (len rbits)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg rbits)
                (r1cs::valuation-binds-allp asg sqs)
                (r1cs::valuation-binds-allp asg ts)
                (bit-listp (lookup-equal-list rbits asg))
                (< (int-divshift-be-acc 0 (lookup-equal-list rbits asg)) 252))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                  (and (equal (lookup-equal-list sqs asg)
                              (int-divshift-pow2-sqs
                               (lookup-equal (car rbits) asg)
                               (lookup-equal-list (cdr rbits) asg)))
                       (equal (lookup-equal-list ts asg)
                              (int-divshift-pow2-ts
                               (lookup-equal (car rbits) asg)
                               (lookup-equal-list (cdr rbits) asg))))))
  :do-not-induct t
  :use ((:instance int-divshift-pow2-chain-iff
                   (cur (list (list 1 1) (list 1 (car rbits))))
                   (rbits (cdr rbits))
                   (a (lookup-equal (car rbits) asg)))
        (:instance int-divshift-dot-first (v (car rbits))))
  :in-theory (e/d (int-divshift-pow2-gadget
                   int-divshift-be-acc
                   lookup-equal-list
                   r1cs::valuation-binds-allp
                   bit-listp bitp bfix nfix)
                  (int-divshift-pow2-chain-iff
                   int-divshift-dot-first
                   lookup-equal)))

(defruled int-divshift-pow2-final-value
  (implies (and (consp (cdr rbitvals))
                (bit-listp rbitvals))
           (equal (car (last (int-divshift-pow2-ts (car rbitvals)
                                                   (cdr rbitvals))))
                  (expt 2 (int-divshift-be-acc 0 rbitvals))))
  :use (:instance int-divshift-pow2-last-ts
                  (a (car rbitvals)) (bits (cdr rbitvals)))
  :expand ((int-divshift-be-acc 0 rbitvals))
  :enable (bit-listp bitp bfix nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-final-of-lookup
  (implies (consp ts)
           (equal (lookup-equal (car (last ts)) asg)
                  (car (last (lookup-equal-list ts asg)))))
  :use ((:instance car-of-lookup-equal-list (keys (last ts)) (alist asg))
        (:instance lookup-equal-list-of-last (keys ts) (alist asg)))
  :disable (car-of-lookup-equal-list lookup-equal-list-of-last
            last-of-lookup-equal-list lookup-equal-of-car))

(defruled int-divshift-rbits-facts
  :short "The exponent select bits, most significant first."
  (implies (and (natp e)
                (equal vals (rev (int->lebits (mod e 128) 7))))
           (and (bit-listp vals)
                (consp vals)
                (consp (cdr vals))
                (equal (len vals) 7)
                (equal (int-divshift-be-acc 0 vals) (mod e 128))
                (< (int-divshift-be-acc 0 vals) 252)))
  :do-not-induct t
  :use ((:instance int-divshift-be-acc-of-rev
                   (bits (int->lebits (mod e 128) 7)))
        (:instance lebits=>nat-of-int->lebits (x (mod e 128)) (n 7))
        (:instance len-7-consp-cdr (v (rev (int->lebits (mod e 128) 7)))))
  :prep-lemmas
  ((defruled len-7-consp-cdr
     (implies (equal (len v) 7)
              (and (consp v) (consp (cdr v))))))
  :enable (bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::mod-when-<
           acl2::ifix-when-integerp)
  :disable (int->lebits int-divshift-be-acc-of-rev
            lebits=>nat-of-int->lebits))

(defruled int-divshift-lower-128-sound
  (implies (and (symbolp final)
                (symbol-listp ys)
                (equal p (base-prime))
                (primep p)
                (equal (len ys) 128)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg final)
                (r1cs::valuation-binds-allp asg ys)
                (natp v)
                (< v (expt 2 128))
                (equal (lookup-equal final asg) v)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget final ys p)
                 asg p))
           (equal (lookup-equal-list ys asg)
                  (int->lebits v 128)))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound
                   (digits (lookup-equal-list ys asg)))
        (:instance acl2::nat=>lebits-of-lebits=>nat
                   (digits (lookup-equal-list ys asg))))
  :in-theory (e/d (int-shift-lower-gadget
                   int->lebits
                   boolean-check-gadget-list-to-bit-listp
                   pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
                   r1cs::r1cs-constraints-holdp-of-append
                   len-of-lookup-equal-list
                   acl2::mod-when-<
                   (:e base-prime) (:e ecurve::edwards-bls12-q))
                  (boolean-check-gadget-list
                   pow2sum-gadget
                   acl2::nat=>lebits-of-lebits=>nat
                   mod
                   floor
                   lookup-equal)))

(defruled int-divshift-int->lebits-of-lebits->int
  (implies (and (bit-listp bits)
                (equal (len bits) n))
           (equal (int->lebits (lebits->int bits signedp) n) bits))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound (digits bits))
        (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits)))
  :enable (int->lebits lebits->int acl2::mod-when-<)
  :disable acl2::nat=>lebits-of-lebits=>nat)

(defruled int-divshift-mod-of-lebits->int
  (implies (and (bit-listp bits)
                (equal (len bits) n))
           (equal (mod (lebits->int bits signedp) (expt 2 n))
                  (lebits=>nat bits)))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound (digits bits)))
  :enable (lebits->int acl2::mod-when-<))

(defruled int-divshift-mul-by-congruent
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (posp m)
                (equal (mod y m) (mod z m)))
           (equal (mod (* x y) m) (mod (* x z) m)))
  :use ((:instance acl2::mod-of-*-of-mod (x x) (x1 y) (z m))
        (:instance acl2::mod-of-*-of-mod (x x) (x1 z) (z m)))
  :disable acl2::mod-of-*-of-mod)

(defruled int-divshift-mul-wrapped-is-shl
  (implies (and (int-valuep x signedp 128)
                (natp e))
           (equal (int-mul-wrapped-spec
                   x
                   (lebits->int (int->lebits (expt 2 (mod e 128)) 128) signedp)
                   signedp 128)
                  (int-shl-wrapped-spec x e signedp 128)))
  :do-not-induct t
  :use ((:instance int-divshift-mod-of-lebits->int
                   (bits (int->lebits (expt 2 (mod e 128)) 128))
                   (n 128))
        (:instance lebits=>nat-of-int->lebits
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance int-divshift-mul-by-congruent
                   (x (ifix x))
                   (y (lebits->int (int->lebits (expt 2 (mod e 128)) 128)
                                   signedp))
                   (z (expt 2 (mod e 128)))
                   (m (expt 2 128))))
  :enable (int-mul-wrapped-spec int-shl-wrapped-spec int-wrap
           bit-listp-of-int->lebits-explicit len-of-int->lebits)
  :disable (int->lebits lebits->int int-divshift-mod-of-lebits->int
            lebits=>nat-of-int->lebits int-divshift-mul-by-congruent))

(defruledl int-divshift-pow-below-128
  (implies (natp e)
           (and (natp (expt 2 (mod e 128)))
                (< (expt 2 (mod e 128)) (expt 2 128))))
  :use (:instance acl2::<-of-expt-and-expt-same-base
                  (r 2) (i (mod e 128)) (j 128))
  :disable acl2::<-of-expt-and-expt-same-base)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sw128-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (booleanp signedp)
        (int-valuep x signedp 128)
        (natp e)
        (symbol-listp xs)
        (symbol-listp rbits)
        (symbol-listp sqs)
        (symbol-listp ts)
        (symbol-listp ys)
        (symbolp ll) (symbolp hl) (symbolp lh)
        (symbol-listp zs)
        (symbol-listp zh)
        (equal (len xs) 128)
        (equal (len rbits) 7)
        (equal (len sqs) 6)
        (equal (len ts) 6)
        (equal (len ys) 128)
        (equal (len zs) 128)
        (equal (len zh) 65)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rbits)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg ts)
        (r1cs::valuation-bindsp asg (car (last ts)))
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-bindsp asg ll)
        (r1cs::valuation-bindsp asg hl)
        (r1cs::valuation-bindsp asg lh)
        (r1cs::valuation-binds-allp asg zs)
        (r1cs::valuation-binds-allp asg zh)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))
        (equal (lookup-equal-list rbits asg)
               (rev (int->lebits (mod e 128) 7)))))

(defmacro int-divshift-sw128-hyps ()
  '(and (int-divshift-sw128-common-hyps)
        (r1cs::r1cs-constraints-holdp
         (int-divshift-shl-wrapped-128-gadget
          xs rbits sqs ts ys ll hl lh zs zh p)
         asg p)))

(defrulel int-divshift-sw128-step-holds
  (implies (int-divshift-sw128-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last ts)) ys p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-mul-wrapped-gadget xs ys ll hl lh zs zh p) asg p)))
  :rule-classes nil
  :in-theory (union-theories '(int-divshift-shl-wrapped-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defrulel int-divshift-sw128-step-final
  (implies (int-divshift-sw128-hyps)
           (equal (lookup-equal (car (last ts)) asg)
                  (expt 2 (mod e 128))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sw128-step-holds)
        (:instance int-divshift-rbits-facts
                   (vals (lookup-equal-list rbits asg)))
        (:instance int-divshift-pow2-gadget-iff)
        (:instance int-divshift-final-of-lookup)
        (:instance int-divshift-pow2-final-value
                   (rbitvals (lookup-equal-list rbits asg)))
        (:instance car-of-lookup-equal-list (keys rbits) (alist asg))
        (:instance lookup-equal-list-of-cdr (keys rbits) (alist asg)))
  :in-theory (union-theories '(consp-when-len-6
                               consp-when-len-7
                               len-of-cdr-when-len-7)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule consp-when-len-6
     (implies (equal (len x) 6) (consp x)))
   (defrule consp-when-len-7
     (implies (equal (len x) 7) (consp x)))
   (defrule len-of-cdr-when-len-7
     (implies (equal (len x) 7) (equal (+ -1 (len x)) 6)))))

(defrulel int-divshift-sw128-step-ys
  (implies (int-divshift-sw128-hyps)
           (equal (lookup-equal-list ys asg)
                  (int->lebits (expt 2 (mod e 128)) 128)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sw128-step-holds)
        (:instance int-divshift-sw128-step-final)
        (:instance int-divshift-pow-below-128)
        (:instance int-divshift-lower-128-sound
                   (final (car (last ts)))
                   (v (expt 2 (mod e 128)))))
  :in-theory (union-theories '(symbolp-of-car-of-last-copy)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule symbolp-of-car-of-last-copy
     (implies (symbol-listp x) (symbolp (car (last x)))))))

(defrulel int-divshift-sw128-step-zs
  (implies (int-divshift-sw128-hyps)
           (equal (lookup-equal-list zs asg)
                  (int->lebits (int-shl-wrapped-spec x e signedp 128) 128)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sw128-step-holds)
        (:instance int-divshift-sw128-step-ys)
        (:instance int-mul-wrapped-gadget-sound
                   (n 128) (ys ys) (lowlow ll) (highlow hl) (lowhigh lh)
                   (zs zs) (zs-high zh)
                   (y (lebits->int (int->lebits (expt 2 (mod e 128)) 128)
                                   signedp)))
        (:instance int-valuep-of-lebits->int
                   (bits (int->lebits (expt 2 (mod e 128)) 128))
                   (n 128))
        (:instance int-divshift-int->lebits-of-lebits->int
                   (bits (int->lebits (expt 2 (mod e 128)) 128))
                   (n 128))
        (:instance bit-listp-of-int->lebits-explicit
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance len-of-int->lebits
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance int-divshift-mul-wrapped-is-shl))
  :in-theory (union-theories '((:e integer-widthp) (:e floor) (:e natp)
                               (:e posp) (:e binary-+))
                             (theory 'minimal-theory)))

(defruled int-divshift-shl-wrapped-128-gadget-sound
  :short "R1CS-SOUND of variable-mode @('shl_wrapped') at width 128, both
          signednesses.  The value wires are @('Integer::new') bits of
          @('x'); the exponent select wires are the low 7 exponent bits,
          most significant first."
  (implies (int-divshift-sw128-hyps)
           (and (equal (lookup-equal-list zs asg)
                       (int->lebits (int-shl-wrapped-spec x e signedp 128)
                                    128))
                (equal (lebits->int (lookup-equal-list zs asg) signedp)
                       (int-shl-wrapped-spec x e signedp 128))))
  :do-not-induct t
  :use ((:instance int-divshift-sw128-step-zs)
        (:instance lebits->int-of-int->lebits
                   (x (int-shl-wrapped-spec x e signedp 128))
                   (n 128))
        (:instance int-valuep-of-shl-wrapped-copy))
  :in-theory (union-theories '((:e posp) ifix-of-shl-wrapped-copy)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule int-valuep-of-shl-wrapped-copy
     (int-valuep (int-shl-wrapped-spec x e signedp 128) signedp 128)
     :enable (int-shl-wrapped-spec int-valuep-of-int-wrap-copy)
     :prep-lemmas
     ((defrule int-valuep-of-int-wrap-copy
        (int-valuep (int-wrap z signedp 128) signedp 128)
        :enable (int-wrap int-valuep int-min int-max))))
   (defrule ifix-of-shl-wrapped-copy
     (equal (ifix (int-shl-wrapped-spec x e signedp 128))
            (int-shl-wrapped-spec x e signedp 128)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sw128-witness-hyps ()
  '(and (int-divshift-sw128-common-hyps)
        (equal (lookup-equal-list sqs asg)
               (int-divshift-pow2-sqs
                (car (rev (int->lebits (mod e 128) 7)))
                (cdr (rev (int->lebits (mod e 128) 7)))))
        (equal (lookup-equal-list ts asg)
               (int-divshift-pow2-ts
                (car (rev (int->lebits (mod e 128) 7)))
                (cdr (rev (int->lebits (mod e 128) 7)))))
        (equal (lookup-equal-list ys asg)
               (int->lebits (expt 2 (mod e 128)) 128))
        (equal y (lebits->int (int->lebits (expt 2 (mod e 128)) 128)
                              signedp))
        (equal (lookup-equal ll asg)
               (* (int-mulpow-lo x 128) (int-mulpow-lo y 128)))
        (equal (lookup-equal hl asg)
               (* (int-mulpow-hi x 128) (int-mulpow-lo y 128)))
        (equal (lookup-equal lh asg)
               (* (int-mulpow-lo x 128) (int-mulpow-hi y 128)))
        (equal (lookup-equal-list zs asg)
               (int->lebits (int-mul-wrapped-spec x y signedp 128) 128))
        (equal (lookup-equal-list zh asg)
               (acl2::nat=>lebits 65
                                  (floor (int-mul-wrapped-sum x y 128)
                                         (expt 2 128))))))

(defrulel int-divshift-sw128-c-pow2
  (implies (int-divshift-sw128-witness-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (equal (lookup-equal (car (last ts)) asg)
                       (expt 2 (mod e 128)))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-rbits-facts
                   (vals (lookup-equal-list rbits asg)))
        (:instance int-divshift-pow2-gadget-iff)
        (:instance int-divshift-final-of-lookup)
        (:instance int-divshift-pow2-final-value
                   (rbitvals (lookup-equal-list rbits asg)))
        (:instance car-of-lookup-equal-list (keys rbits) (alist asg))
        (:instance lookup-equal-list-of-cdr (keys rbits) (alist asg)))
  :in-theory (union-theories '(consp-when-len-6b
                               consp-when-len-7b
                               len-of-cdr-when-len-7b)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule consp-when-len-6b
     (implies (equal (len x) 6) (consp x)))
   (defrule consp-when-len-7b
     (implies (equal (len x) 7) (consp x)))
   (defrule len-of-cdr-when-len-7b
     (implies (equal (len x) 7) (equal (+ -1 (len x)) 6)))))

(defrulel int-divshift-sw128-c-lower
  (implies (int-divshift-sw128-witness-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-shift-lower-gadget (car (last ts)) ys p) asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-sw128-c-pow2)
        (:instance int-divshift-pow-below-128)
        (:instance int-shift-lower-when-bits
                   (final (car (last ts))) (zs ys))
        (:instance lebits=>nat-of-int->lebits
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance int-divshift-pow-below-prime (k 128)))
  :in-theory (e/d (bit-listp-of-int->lebits-explicit
                   acl2::mod-when-<
                   acl2::ifix-when-integerp)
                  (int-shift-lower-when-bits
                   lebits=>nat-of-int->lebits
                   int-divshift-pow-below-prime
                   int-divshift-pow-below-128
                   int-shift-lower-gadget
                   int->lebits
                   lookup-equal mod floor)))

(defrulel int-divshift-sw128-c-mul
  (implies (int-divshift-sw128-witness-hyps)
           (r1cs::r1cs-constraints-holdp
            (int-mul-wrapped-gadget xs ys ll hl lh zs zh p) asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-mul-wrapped-gadget-complete
                   (n 128) (ys ys) (lowlow ll) (highlow hl) (lowhigh lh)
                   (zs zs) (zs-high zh))
        (:instance int-valuep-of-lebits->int
                   (bits (int->lebits (expt 2 (mod e 128)) 128))
                   (n 128))
        (:instance int-divshift-int->lebits-of-lebits->int
                   (bits (int->lebits (expt 2 (mod e 128)) 128))
                   (n 128))
        (:instance bit-listp-of-int->lebits-explicit
                   (x (expt 2 (mod e 128))) (n 128))
        (:instance len-of-int->lebits
                   (x (expt 2 (mod e 128))) (n 128)))
  :in-theory (union-theories '((:e integer-widthp) (:e floor) (:e natp)
                               (:e posp) (:e binary-+))
                             (theory 'minimal-theory)))

(defruled int-divshift-shl-wrapped-128-gadget-complete
  :short "R1CS-COMPLETE of variable-mode @('shl_wrapped') at width 128,
          both signednesses: the canonical witnesses satisfy the gadget and
          the result bits are the funspec."
  (implies (int-divshift-sw128-witness-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-shl-wrapped-128-gadget
                  xs rbits sqs ts ys ll hl lh zs zh p)
                 asg p)
                (equal (lookup-equal-list zs asg)
                       (int->lebits (int-shl-wrapped-spec x e signedp 128)
                                    128))))
  :do-not-induct t
  :use ((:instance int-divshift-sw128-c-pow2)
        (:instance int-divshift-sw128-c-lower)
        (:instance int-divshift-sw128-c-mul)
        (:instance int-divshift-mul-wrapped-is-shl))
  :in-theory (union-theories '(int-divshift-shl-wrapped-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))
