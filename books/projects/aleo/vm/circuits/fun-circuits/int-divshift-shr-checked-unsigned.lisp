; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode unsigned shr_checked (and shr, shr_assign, which emit the
; same circuit) for every width other than 128: the exponent bits at and
; above log2(n) are zero, then the unsigned shr_wrapped circuit.  The
; exponent is a magnitude Integer::new of width m, split as in
; int-divshift-shl-checked-sound.

(in-package "ALEOVM")

(include-book "int-divshift-shl-checked-sound")
(include-book "int-divshift-shr-unsigned")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-shrc-spec
  (implies (and (integer-widthp n)
                (int-valuep x nil n)
                (natp e)
                (< e n))
           (equal (int-shr-checked-spec x e nil n)
                  (int-shr-wrapped-spec x e nil n)))
  :use (:instance int-shr-checked-is-wrapped-when-in-range (signedp nil)))

(defruledl int-divshift-shrc-excess-holds
  (implies (and (primep p)
                (equal p (base-prime))
                (integer-widthp n)
                (member-equal m '(8 16 32))
                (natp e)
                (< e n)
                (< e (expt 2 m))
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr (1- (integer-length n)) (int->lebits e m))))
           (r1cs::r1cs-constraints-holdp
            (int-shr-checked-bound-gadget excess) asg p))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-shlc-excess-len
                   (k (1- (integer-length n))))
        (:instance int-excess-zero-when-lebits-below
                   (bits (int->lebits e m))
                   (n (1- (integer-length n))))
        (:instance int-excess-zero-implies-constraint)
        (:instance len-of-lookup-equal-list (keys excess) (alist asg)))
  :enable (int-shr-checked-bound-gadget int-bit-listp-of-nthcdr)
  :disable (int-excess-zero-when-lebits-below
            int-excess-zero-implies-constraint
            len-of-lookup-equal-list
            int->lebits nthcdr repeat
            acl2::len-of-nthcdr acl2::repeat-of-nfix))

(defmacro int-divshift-shrc-common-hyps ()
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
        (equal (len xs) n)
        (equal (len ebits) (1- (integer-length n)))
        (equal (len nexts) (len ebits))
        (equal (len zs) (* 2 n))
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
               (nthcdr (1- (integer-length n)) (int->lebits e m)))))

(defrulel int-divshift-shrc-step-bound
  (implies (and (int-divshift-shrc-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-bound-gadget excess) asg p))
           (< e n))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-width-facts)
        (:instance int-divshift-shlc-excess-len
                   (k (1- (integer-length n))))
        (:instance int-shr-checked-bound-gadget-sound
                   (ebits (int->lebits e m))))
  :in-theory (theory 'minimal-theory))

(defruled int-divshift-shr-checked-unsigned-gadget-sound
  :short "R1CS-SOUND of variable-mode unsigned @('shr_checked'), @('shr')
          and @('shr_assign') for every width other than 128."
  (implies (and (int-divshift-shrc-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-shift-gadget xs ebits excess nexts zs p)
                 asg p))
           (and (< e n)
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    nil)
                       (int-shr-checked-spec x e nil n))))
  :do-not-induct t
  :use ((:instance int-divshift-shrc-step-bound)
        (:instance int-divshift-shlc-low-bits)
        (:instance int-divshift-shrc-spec)
        (:instance int-divshift-shr-wrapped-unsigned-gadget-sound))
  :in-theory (union-theories '(int-shr-checked-shift-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defruled int-divshift-shr-checked-unsigned-gadget-complete
  :short "R1CS-COMPLETE of variable-mode unsigned @('shr_checked'),
          @('shr') and @('shr_assign') for every width other than 128:
          for an exponent below @('n') the canonical witnesses satisfy the
          gadget.  An exponent at or above @('n') is unsatisfiable by the
          soundness theorem."
  (implies (and (int-divshift-shrc-common-hyps)
                (< e n)
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
                 (int-shr-checked-shift-gadget xs ebits excess nexts zs p)
                 asg p)
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    nil)
                       (int-shr-checked-spec x e nil n))))
  :do-not-induct t
  :use ((:instance int-divshift-shrc-excess-holds)
        (:instance int-divshift-shlc-low-bits)
        (:instance int-divshift-shrc-spec)
        (:instance int-divshift-shr-wrapped-unsigned-gadget-complete))
  :in-theory (union-theories '(int-shr-checked-shift-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))
