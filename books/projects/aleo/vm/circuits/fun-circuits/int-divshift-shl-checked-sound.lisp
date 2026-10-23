; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND of variable-mode unsigned shl_checked (and shl, shl_assign,
; which emit the same circuit) for every width other than 128.  The
; exponent is a magnitude Integer::new of width m; its bits are split into
; the low log2(n) select bits and the excess bits that must be zero.  The
; excess check forces e < n, the wrapped shift forces the 2n result bits to
; be the bits of x * 2^e, and the high-zero check forces x * 2^e < 2^n.

(in-package "ALEOVM")

(include-book "int-divshift-shift-sound")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-shlc-bits-from-nat
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable (int->lebits acl2::mod-when-<))

(defruled int-divshift-shlc-mag-facts
  (implies (and (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m)))
           (and (bit-listp (int->lebits e m))
                (equal (len (int->lebits e m)) m)
                (equal (lebits=>nat (int->lebits e m)) e)))
  :use (:instance lebits=>nat-of-int->lebits (x e) (n m))
  :enable (bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           acl2::mod-when-<
           acl2::ifix-when-integerp))

(defruled int-divshift-shlc-width-facts
  (implies (integer-widthp n)
           (and (equal (expt 2 (1- (integer-length n))) n)
                (natp (1- (integer-length n)))
                (<= (1- (integer-length n)) 7)))
  :enable (integer-widthp)
  :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64) (equal n 128)))

(defruled int-divshift-shlc-len-small
  (implies (<= (len bits) 256)
           (< (len (nthcdr k bits)) (base-prime)))
  :use (:instance acl2::len-of-nthcdr (n k) (l bits))
  :enable ((:e base-prime) (:e ecurve::edwards-bls12-q))
  :disable acl2::len-of-nthcdr)

(defruled int-divshift-shlc-excess-len
  (implies (and (member-equal m '(8 16 32))
                (natp e)
                (< e (expt 2 m))
                (equal (lookup-equal-list excess asg)
                       (nthcdr k (int->lebits e m))))
           (< (len excess) (base-prime)))
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-len-small (bits (int->lebits e m)))
        (:instance len-of-lookup-equal-list (keys excess) (alist asg)))
  :disable (int->lebits len-of-lookup-equal-list int-divshift-shlc-len-small))

(defruledl int-divshift-shlc-high-len
  (implies (and (integer-widthp n)
                (equal (len zs) (* 2 n))
                (equal high (nthcdr n zs)))
           (< (len high) (base-prime)))
  :use (:instance int-divshift-shlc-len-small (bits zs) (k n))
  :enable integer-widthp
  :disable int-divshift-shlc-len-small)

(defruled int-divshift-shlc-low-bits
  (implies (and (member-equal m '(8 16 32))
                (integer-widthp n)
                (natp e)
                (< e n)
                (< e (expt 2 m))
                (<= (1- (integer-length n)) m))
           (equal (take (1- (integer-length n)) (int->lebits e m))
                  (int->lebits (mod e n) (1- (integer-length n)))))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-lebits-take-is-mod
                   (bits (int->lebits e m))
                   (n (1- (integer-length n))))
        (:instance int-divshift-shlc-bits-from-nat
                   (bits (take (1- (integer-length n)) (int->lebits e m)))
                   (n (1- (integer-length n)))
                   (v e)))
  :enable (acl2::mod-when-< acl2::len-of-take)
  :disable (int->lebits take mod))

(defruledl int-divshift-shlc-high-zero
  (implies (and (primep p)
                (symbol-listp high)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg high)
                (bit-listp zv)
                (natp n)
                (equal (lookup-equal-list high asg) (nthcdr n zv))
                (< (len high) p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget high) asg p))
           (< (lebits=>nat zv) (expt 2 n)))
  :do-not-induct t
  :use ((:instance int-excess-bits-sum-forces-all-zero (excess high))
        (:instance int-lebits-below-pow2-when-excess-zero (bits zv))
        (:instance len-of-lookup-equal-list (keys high) (alist asg)))
  :enable (int-bit-listp-of-nthcdr)
  :disable (int-excess-bits-sum-forces-all-zero
            int-lebits-below-pow2-when-excess-zero
            len-of-lookup-equal-list
            acl2::len-of-nthcdr acl2::repeat-of-nfix
            repeat nthcdr))

(defruledl int-divshift-shlc-spec
  (implies (and (integer-widthp n)
                (int-valuep x nil n)
                (natp e)
                (< e n)
                (< (* x (expt 2 e)) (expt 2 n)))
           (and (equal (int-shl-checked-spec x e nil n)
                       (int-shl-wrapped-spec x e nil n))
                (equal (int-shl-checked-spec x e nil n)
                       (* x (expt 2 e)))))
  :enable (int-shl-checked-spec
           int-shl-wrapped-spec
           int-wrap
           int-valuep
           int-min
           int-max
           acl2::mod-when-<
           acl2::ifix-when-integerp
           posp-when-integer-widthp
           integer-widthp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-shlc-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (integer-widthp n)
        (not (equal n 128))
        (int-valuep x nil n)
        (member-equal m '(8 16 32))
        (natp e)
        (< e (expt 2 m))
        (<= (1- (integer-length n)) m)
        (symbol-listp xs)
        (symbol-listp ebits)
        (symbol-listp excess)
        (symbol-listp nexts)
        (symbol-listp zs)
        (symbol-listp high)
        (equal (len xs) n)
        (equal (len ebits) (1- (integer-length n)))
        (equal (len nexts) (len ebits))
        (equal (len zs) (* 2 n))
        (equal high (nthcdr n zs))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ebits)
        (r1cs::valuation-binds-allp asg excess)
        (r1cs::valuation-binds-allp asg nexts)
        (r1cs::valuation-bindsp asg (car (last nexts)))
        (r1cs::valuation-binds-allp asg zs)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ebits asg)
               (take (1- (integer-length n)) (int->lebits e m)))
        (equal (lookup-equal-list excess asg)
               (nthcdr (1- (integer-length n)) (int->lebits e m)))
        (r1cs::r1cs-constraints-holdp
         (int-shl-checked-shift-gadget xs ebits excess nexts zs high p)
         asg p)))

(defrulel int-divshift-shlc-step-holds
  (implies (int-divshift-shlc-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-shl-checked-bound-gadget excess) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shl-wrapped-gadget xs ebits nexts zs p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget high) asg p)))
  :rule-classes nil
  :in-theory (union-theories '(int-shl-checked-shift-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defrulel int-divshift-shlc-step-bound
  (implies (int-divshift-shlc-hyps)
           (< e n))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-holds)
        (:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-shlc-excess-len
                   (k (1- (integer-length n))))
        (:instance int-shl-checked-bound-gadget-sound
                   (ebits (int->lebits e m))))
  :in-theory (theory 'minimal-theory))

(defrulel int-divshift-shlc-step-ebits
  (implies (int-divshift-shlc-hyps)
           (equal (lookup-equal-list ebits asg)
                  (int->lebits (mod e n) (1- (integer-length n)))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-bound)
        (:instance int-divshift-shlc-low-bits))
  :in-theory (theory 'minimal-theory))

(defrulel int-divshift-shlc-step-wrapped
  (implies (int-divshift-shlc-hyps)
           (and (equal (lookup-equal-list zs asg)
                       (int->lebits (* (int-spec-unsigned x n)
                                       (expt 2 (mod e n)))
                                    (* 2 n)))
                (equal (lebits->int (take n (lookup-equal-list zs asg)) nil)
                       (int-shl-wrapped-spec x e nil n))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-holds)
        (:instance int-divshift-shlc-step-ebits)
        (:instance int-divshift-shl-wrapped-gadget-sound (signedp nil)))
  :in-theory (union-theories '(booleanp)
                             (theory 'minimal-theory)))

(defrulel int-divshift-shlc-step-value
  (implies (int-divshift-shlc-hyps)
           (equal (lebits=>nat (lookup-equal-list zs asg))
                  (* x (expt 2 e))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-wrapped)
        (:instance int-divshift-shlc-step-bound)
        (:instance int-divshift-shifted-below-double-copy
                   (v x) (s e))
        (:instance lebits=>nat-of-int->lebits
                   (x (* x (expt 2 e))) (n (* 2 n))))
  :enable (int-spec-unsigned int-valuep int-min int-max
           acl2::mod-when-< acl2::ifix-when-integerp
           posp-when-integer-widthp integer-widthp)
  :disable (int->lebits lebits=>nat-of-int->lebits)
  :prep-lemmas
  ((defruled int-divshift-shifted-below-double-copy
     (implies (and (integer-widthp n)
                   (natp v)
                   (< v (expt 2 n))
                   (natp s)
                   (< s n))
              (< (* v (expt 2 s)) (expt 2 (* 2 n))))
     :do-not-induct t
     :use ((:instance acl2::<-of-*-and-*-cancel
                      (x1 v) (x2 (expt 2 n)) (y (expt 2 s)))
           (:instance acl2::expt-monotone-strong
                      (r 2) (j (* 2 n)) (i (+ n s))))
     :enable (acl2::expt-of-+ posp-when-integer-widthp)
     :disable acl2::<-of-*-and-*-cancel)))

(defrulel int-divshift-shlc-step-fits
  (implies (int-divshift-shlc-hyps)
           (< (* x (expt 2 e)) (expt 2 n)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-holds)
        (:instance int-divshift-shlc-step-wrapped)
        (:instance int-divshift-shlc-step-value)
        (:instance lookup-equal-list-of-nthcdr-copy
                   (k n) (keys zs) (alist asg))
        (:instance int-divshift-shlc-high-zero
                   (zv (lookup-equal-list zs asg)))
        (:instance bit-listp-of-int->lebits-explicit
                   (x (* (int-spec-unsigned x n) (expt 2 (mod e n))))
                   (n (* 2 n)))
        (:instance int-divshift-shlc-high-len))
  :in-theory (union-theories '(r1cs::valuation-binds-allp-of-nthcdr-copy
                               symbol-listp-of-nthcdr-copy
                               natp-when-integer-widthp-copy)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defruled lookup-equal-list-of-nthcdr-copy
     (equal (lookup-equal-list (nthcdr k keys) alist)
            (nthcdr k (lookup-equal-list keys alist)))
     :enable lookup-equal-list
     :induct (nthcdr k keys))
   (defruled r1cs::valuation-binds-allp-of-nthcdr-copy
     (implies (r1cs::valuation-binds-allp asg keys)
              (r1cs::valuation-binds-allp asg (nthcdr k keys)))
     :enable r1cs::valuation-binds-allp
     :induct (nthcdr k keys))
   (defruled symbol-listp-of-nthcdr-copy
     (implies (symbol-listp keys)
              (symbol-listp (nthcdr k keys)))
     :induct (nthcdr k keys))
   (defruled natp-when-integer-widthp-copy
     (implies (integer-widthp n) (natp n))
     :enable integer-widthp)))

(defruled int-divshift-shl-checked-unsigned-gadget-sound
  :short "R1CS-SOUND of variable-mode unsigned @('shl_checked'),
          @('shl') and @('shl_assign') for every width other than 128.
          A satisfying assignment forces the exponent below @('n'), the
          product to fit, and the low @('n') result bits to be the
          funspec value."
  (implies (int-divshift-shlc-hyps)
           (and (< e n)
                (< (* x (expt 2 e)) (expt 2 n))
                (equal (int-shl-checked-spec x e nil n) (* x (expt 2 e)))
                (equal (lebits->int (take n (lookup-equal-list zs asg)) nil)
                       (int-shl-checked-spec x e nil n))))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-step-bound)
        (:instance int-divshift-shlc-step-fits)
        (:instance int-divshift-shlc-step-wrapped)
        (:instance int-divshift-shlc-spec))
  :in-theory (theory 'minimal-theory))
