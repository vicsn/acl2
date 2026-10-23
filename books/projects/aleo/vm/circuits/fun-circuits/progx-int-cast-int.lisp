; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The constraints of the Integer-to-Integer arms of Integer::cast (snarkVM
; circuit/program/src/data/literal/cast/integer.rs) on the input bit wires
; xs, and that they hold exactly when progx-icast-predp holds of the bit
; values.  Integer::from_bits_le on a slice of at most the destination width
; adds no constraint, so each arm is:
;   (u,u)          assert_bits_are_zero(xs[n1..])
;   (u,s)          assert_bits_are_zero(xs[n1-1..])  (none if n0 < n1)
;   (s,u) n0 <= n1 E::assert(!msb), i.e. (1 - msb) * 1 = 1
;   (s,u) else     assert_bits_are_zero(xs[n1..])
;   (s,s) n0 <= n1 nothing
;   (s,s) else     E::assert_eq(msb, b) for b in xs[n1-1 .. n0-2]

(in-package "ALEOVM")

(include-book "progx-int-cast-vals")
(include-book "environment-r1cs")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-assert-not-gadget ((b symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint added by @('E::assert(!b)') for a Boolean variable b:
          @($(1 - b) \\cdot 1 = 1$)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1) (list (1- p) b))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

(defruled progx-assert-not-gadget-iff
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (progx-assert-not-gadget b p) asg p)
                  (equal (lookup-equal b asg) 0)))
  :cases ((equal (lookup-equal b asg) 0))
  :enable (progx-assert-not-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           bitp)
  :disable ((:e base-prime)))

(define progx-assert-eq-chain ((m symbolp) (ws symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('E::assert_eq(m, w)') for each w in ws."
  (if (endp ws)
      nil
    (append (assert-eq-gadget m (car ws))
            (progx-assert-eq-chain m (cdr ws)))))

(defruled progx-assert-eq-chain-iff
  (implies (and (symbolp m)
                (symbol-listp ws)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ws))
           (equal (r1cs::r1cs-constraints-holdp
                   (progx-assert-eq-chain m ws) asg p)
                  (equal (lookup-equal-list ws asg)
                         (repeat (len ws) (lookup-equal m asg)))))
  :induct (len ws)
  :enable (progx-assert-eq-chain
           assert-eq-gadget-to-funspec
           assert-eq-funspec
           enforce-funspec
           r1cs::r1cs-constraints-holdp-of-append
           lookup-equal-list
           repeat
           r1cs::valuation-binds-allp
           r1cs::fep-of-lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-lookup-of-car-last
  (implies (consp xs)
           (equal (lookup-equal (car (last xs)) asg)
                  (car (last (lookup-equal-list xs asg)))))
  :induct (len xs)
  :enable (lookup-equal-list last))

(defruled progx-repeat-of-snoc
  (equal (equal (append a (list m)) (repeat (+ 1 (len a)) m))
         (equal (true-list-fix a) (repeat (len a) m)))
  :induct (len a)
  :enable (repeat true-list-fix))

(defruled progx-snoc-of-take-last
  (implies (and (consp tl) (true-listp tl))
           (equal (append (take (1- (len tl)) tl) (list (car (last tl))))
                  tl))
  :induct (len tl)
  :enable (take last))

(defruled progx-repeat-iff-take-repeat
  (implies (and (consp tl) (true-listp tl) (equal m (car (last tl))))
           (equal (equal tl (repeat (len tl) m))
                  (equal (take (1- (len tl)) tl) (repeat (1- (len tl)) m))))
  :do-not-induct t
  :use (progx-snoc-of-take-last
        (:instance progx-repeat-of-snoc (a (take (1- (len tl)) tl))))
  :in-theory (disable repeat take last))

(defruledl progx-icast-base-prime-above-128
  (< 128 (base-prime))
  :enable base-prime)

(defruled progx-symbol-listp-of-nthcdr
  (implies (symbol-listp xs) (symbol-listp (nthcdr k xs)))
  :induct (nthcdr k xs)
  :enable nthcdr)

(defruled progx-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (nthcdr k xs)))
  :induct (nthcdr k xs)
  :enable (nthcdr r1cs::valuation-binds-allp))

(defruled progx-icast-zero-gadget-iff
  (implies (and (natp k)
                (symbol-listp xs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (<= (len xs) 128))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-from-bits-le-gadget (nthcdr k xs)) asg p)
                  (progx-icast-zerop k (lookup-equal-list xs asg))))
  :do-not-induct t
  :use ((:instance int-from-bits-le-gadget-iff-all-zero
                   (excess (nthcdr k xs)))
        progx-icast-base-prime-above-128)
  :enable (progx-icast-zerop lookup-equal-list-of-nthcdr
           progx-symbol-listp-of-nthcdr progx-binds-allp-of-nthcdr
           primep-of-base-prime
           int-bit-listp-of-nthcdr)
  :disable ((:e base-prime)))

(defruled progx-bindsp-of-car-last
  (implies (and (r1cs::valuation-binds-allp asg xs) (consp xs))
           (r1cs::valuation-bindsp asg (car (last xs))))
  :induct (len xs)
  :enable (r1cs::valuation-binds-allp last))

(defruled progx-symbolp-of-car-last
  (implies (symbol-listp xs) (symbolp (car (last xs))))
  :induct (len xs)
  :enable last)

(defruled progx-symbol-listp-of-take
  (implies (and (symbol-listp xs) (<= (nfix n) (len xs)))
           (symbol-listp (take n xs)))
  :induct (take n xs)
  :enable take)

(defruled progx-binds-allp-of-take
  (implies (and (r1cs::valuation-binds-allp asg xs) (<= (nfix n) (len xs)))
           (r1cs::valuation-binds-allp asg (take n xs)))
  :induct (take n xs)
  :enable (take r1cs::valuation-binds-allp))

(defruled progx-last-of-nthcdr
  (implies (< (nfix k) (len x))
           (equal (last (nthcdr k x)) (last x)))
  :induct (nthcdr k x)
  :enable (nthcdr last))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-icast-int-gadget ((xs symbol-listp) s0 s1 (n1 posp) (p primep))
  :verify-guards nil
  :short "The constraints of the Integer-to-Integer arm with source
          signedness s0 on bit wires xs and destination s1, n1.  For (u,s)
          with n0 < n1 the slice xs[n1-1..] is empty and so adds nothing."
  (b* ((n0 (len xs)) (msb (car (last xs))))
    (cond ((and s0 s1)
           (if (<= n0 n1)
               nil
             (progx-assert-eq-chain msb (take (- n0 n1) (nthcdr (1- n1) xs)))))
          (s1 (int-from-bits-le-gadget (nthcdr (1- n1) xs)))
          (s0 (if (<= n0 n1)
                  (progx-assert-not-gadget msb p)
                (int-from-bits-le-gadget (nthcdr n1 xs))))
          (t (int-from-bits-le-gadget (nthcdr n1 xs))))))

(defruled progx-icast-int-gadget-iff
  (implies (and (symbol-listp xs) (consp xs)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg))
                (<= (len xs) 128)
                (posp n1))
           (equal (r1cs::r1cs-constraints-holdp
                   (progx-icast-int-gadget xs s0 s1 n1 p) asg p)
                  (progx-icast-predp (lookup-equal-list xs asg) s0 s1 n1)))
  :do-not-induct t
  :cases ((and s0 s1 (<= (len xs) n1))
          (and s0 s1 (< n1 (len xs)))
          (and (not s0) s1)
          (and s0 (not s1) (<= (len xs) n1))
          (and s0 (not s1) (< n1 (len xs))))
  :hints (("Subgoal 6"
           :use (:instance progx-icast-zero-gadget-iff (k n1))
           :in-theory '(progx-icast-int-gadget progx-icast-predp posp natp))
          ("Subgoal 5"
           :in-theory '(progx-icast-int-gadget progx-icast-predp
                        r1cs::r1cs-constraints-holdp len-of-lookup-equal-list))
          ("Subgoal 4"
           :use ((:instance progx-assert-eq-chain-iff
                            (m (car (last xs)))
                            (ws (take (- (len xs) n1) (nthcdr (1- n1) xs))))
                 progx-lookup-of-car-last
                 progx-bindsp-of-car-last
                 progx-symbolp-of-car-last
                 (:instance progx-symbol-listp-of-take
                            (n (- (len xs) n1)) (xs (nthcdr (1- n1) xs)))
                 (:instance progx-binds-allp-of-take
                            (n (- (len xs) n1)) (xs (nthcdr (1- n1) xs)))
                 (:instance lookup-equal-list-of-take
                            (i (- (len xs) n1))
                            (keys (nthcdr (1- n1) xs)) (alist asg))
                 (:instance progx-repeat-iff-take-repeat
                            (tl (nthcdr (1- n1) (lookup-equal-list xs asg)))
                            (m (car (last (lookup-equal-list xs asg)))))
                 (:instance progx-last-of-nthcdr
                            (k (1- n1)) (x (lookup-equal-list xs asg))))
           :in-theory (e/d (progx-icast-int-gadget progx-icast-predp
                            lookup-equal-list-of-nthcdr
                            progx-symbol-listp-of-nthcdr
                            progx-binds-allp-of-nthcdr)
                           (progx-assert-eq-chain)))
          ("Subgoal 3"
           :use (:instance progx-icast-zero-gadget-iff (k (1- n1)))
           :in-theory '(progx-icast-int-gadget progx-icast-predp
                        posp natp))
          ("Subgoal 2"
           :use ((:instance progx-assert-not-gadget-iff (b (car (last xs))))
                 progx-lookup-of-car-last
                 (:instance progx-icast-zerop-iff
                            (k n1) (bs (lookup-equal-list xs asg)))
                 (:instance progx-lebits-bound (bs (lookup-equal-list xs asg)))
                 (:instance progx-expt-2-mono (a (len xs)) (b n1))
                 (:instance bitp-of-car-of-last-when-bit-listp
                            (bits (lookup-equal-list xs asg)))
                 progx-bindsp-of-car-last
                 progx-symbolp-of-car-last)
           :in-theory (e/d (progx-icast-int-gadget progx-icast-predp)
                           (progx-icast-zerop progx-assert-not-gadget)))
          ("Subgoal 1"
           :use ((:instance progx-icast-zero-gadget-iff (k n1))
                 (:instance progx-icast-zerop-iff
                            (k n1) (bs (lookup-equal-list xs asg)))
                 (:instance progx-msb-0-iff-small
                            (bs (lookup-equal-list xs asg)))
                 (:instance progx-expt-2-mono (a n1) (b (1- (len xs)))))
           :in-theory (e/d (progx-icast-int-gadget progx-icast-predp)
                           (progx-icast-zerop int-from-bits-le-gadget)))))
