; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode signed shr_checked (and shr, shr_assign) at width 128: the
; exponent bits at and above 7 are zero, then the signed 128-bit
; shr_wrapped circuit (int-divshift-shr-signed-128-gadget).  The exponent
; is a magnitude Integer::new of width m; the select wires hold its low 7
; bits, most significant first.

(in-package "ALEOVM")

(include-book "int-divshift-shr-signed-128-complete")
(include-book "int-divshift-shl-checked-sound")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund int-divshift-shr-checked-signed-128-gadget
  (excess xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl mch ls l ds d
          nqs nc zeros nz nw mqs mc rds res one p)
  (declare (xargs :verify-guards nil))
  (append (int-shr-checked-bound-gadget excess)
          (int-divshift-shr-signed-128-gadget
           xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl mch ls l ds d
           nqs nc zeros nz nw mqs mc rds res one p)))

(defruledl int-divshift-ssc128-width
  (and (integer-widthp 128)
       (equal (1- (integer-length 128)) 7))
  :enable integer-widthp)

(defruledl int-divshift-ssc128-spec
  (implies (and (int-valuep x t 128)
                (natp e)
                (< e 128))
           (equal (int-shr-checked-spec x e t 128)
                  (int-shr-wrapped-spec x e t 128)))
  :use (:instance int-shr-checked-is-wrapped-when-in-range
                  (signedp t) (n 128))
  :enable integer-widthp)

(defruledl int-divshift-ssc128-excess-holds
  (implies (and (primep p)
                (equal p (base-prime))
                (member-equal m '(8 16 32))
                (natp e)
                (< e 128)
                (< e (expt 2 m))
                (symbol-listp excess)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg excess)
                (equal (lookup-equal-list excess asg)
                       (nthcdr 7 (int->lebits e m))))
           (r1cs::r1cs-constraints-holdp
            (int-shr-checked-bound-gadget excess) asg p))
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-shlc-excess-len (k 7))
        (:instance int-excess-zero-when-lebits-below
                   (bits (int->lebits e m)) (n 7))
        (:instance int-excess-zero-implies-constraint)
        (:instance len-of-lookup-equal-list (keys excess) (alist asg)))
  :enable (int-shr-checked-bound-gadget int-bit-listp-of-nthcdr)
  :disable (int-excess-zero-when-lebits-below
            int-excess-zero-implies-constraint
            len-of-lookup-equal-list
            int->lebits nthcdr repeat
            acl2::len-of-nthcdr acl2::repeat-of-nfix))

(defmacro int-divshift-ssc128-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (int-valuep x t 128)
        (natp e)
        (symbol-listp xs) (symbol-listp rbits) (symbol-listp sqs)
        (symbol-listp ts) (symbol-listp ys)
        (symbol-listp axs) (symbol-listp mxs) (symbolp cx)
        (symbol-listp qs) (symbol-listp rs)
        (symbolp ll) (symbolp hl) (symbolp lh) (symbolp hh)
        (symbol-listp ms) (symbol-listp mcl) (symbol-listp mch)
        (symbol-listp ls) (symbolp l) (symbol-listp ds) (symbolp d)
        (symbol-listp nqs) (symbolp nc)
        (symbol-listp zeros) (symbolp nz) (symbolp nw)
        (symbol-listp mqs) (symbolp mc)
        (symbol-listp rds) (symbol-listp res)
        (symbolp one)
        (equal (len xs) 128) (equal (len rbits) 7)
        (equal (len sqs) 6) (equal (len ts) 6) (equal (len ys) 128)
        (equal (len axs) 128) (equal (len mxs) 128)
        (equal (len qs) 128) (equal (len rs) 128) (equal (len ms) 128)
        (equal (len mcl) 65) (equal (len mch) 128) (equal (len ls) 128)
        (equal (len ds) 128)
        (equal (len nqs) 128) (equal (len zeros) 128)
        (equal (len mqs) 128) (equal (len rds) 128) (equal (len res) 128)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rbits)
        (r1cs::valuation-binds-allp asg sqs)
        (r1cs::valuation-binds-allp asg ts)
        (r1cs::valuation-bindsp asg (car (last ts)))
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg axs)
        (r1cs::valuation-binds-allp asg mxs)
        (r1cs::valuation-bindsp asg cx)
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
        (r1cs::valuation-binds-allp asg nqs)
        (r1cs::valuation-bindsp asg nc)
        (r1cs::valuation-binds-allp asg zeros)
        (r1cs::valuation-bindsp asg nz)
        (r1cs::valuation-bindsp asg nw)
        (r1cs::valuation-binds-allp asg mqs)
        (r1cs::valuation-bindsp asg mc)
        (r1cs::valuation-binds-allp asg rds)
        (r1cs::valuation-binds-allp asg res)
        (r1cs::valuation-bindsp asg one)
        (equal (lookup-equal one asg) 1)
        (equal (lookup-equal-list xs asg) (int->lebits x 128))
        (member-equal m '(8 16 32))
        (< e (expt 2 m))
        (symbol-listp excess)
        (r1cs::valuation-binds-allp asg excess)
        (equal (lookup-equal-list rbits asg)
               (rev (take 7 (int->lebits e m))))
        (equal (lookup-equal-list excess asg)
               (nthcdr 7 (int->lebits e m)))
        (equal (lookup-equal-list zeros asg) (int->lebits 0 128))))

(defrulel int-divshift-ssc128-step-bound
  (implies (and (int-divshift-ssc128-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-bound-gadget excess) asg p))
           (< e 128))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-ssc128-width)
        (:instance int-divshift-shlc-excess-len (k 7))
        (:instance int-shr-checked-bound-gadget-sound
                   (n 128) (ebits (int->lebits e m))))
  :in-theory (theory 'minimal-theory))

(defrulel int-divshift-ssc128-step-rbits
  (implies (and (int-divshift-ssc128-common-hyps)
                (< e 128))
           (equal (lookup-equal-list rbits asg)
                  (rev (int->lebits (mod e 128) 7))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ssc128-width)
        (:instance int-divshift-shlc-low-bits (n 128)))
  :in-theory (union-theories '(mag-at-least-7)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule mag-at-least-7
     (implies (member-equal m '(8 16 32)) (<= 7 m)))))

(defruled int-divshift-shr-checked-signed-128-gadget-sound
  :short "R1CS-SOUND of variable-mode signed @('shr_checked'), @('shr')
          and @('shr_assign') at width 128."
  (implies (and (int-divshift-ssc128-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-checked-signed-128-gadget
                  excess xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl
                  mch ls l ds d nqs nc zeros nz nw mqs mc rds res one p)
                 asg p))
           (and (< e 128)
                (equal (lebits->int (lookup-equal-list res asg) t)
                       (int-shr-checked-spec x e t 128))))
  :do-not-induct t
  :use ((:instance int-divshift-ssc128-step-bound)
        (:instance int-divshift-ssc128-step-rbits)
        (:instance int-divshift-ssc128-spec)
        (:instance int-divshift-shr-signed-128-gadget-sound))
  :in-theory (union-theories '(int-divshift-shr-checked-signed-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defmacro int-divshift-ssc128-witness-hyps ()
  '(and (int-divshift-ssc128-common-hyps)
        (< e 128)
        (equal dv (expt 2 (mod e 128)))
        (equal a (abs x))
        (equal q (truncate a dv))
        (equal r (rem a dv))
        (equal (lookup-equal-list sqs asg)
               (int-divshift-pow2-sqs
                (car (rev (int->lebits (mod e 128) 7)))
                (cdr (rev (int->lebits (mod e 128) 7)))))
        (equal (lookup-equal-list ts asg)
               (int-divshift-pow2-ts
                (car (rev (int->lebits (mod e 128) 7)))
                (cdr (rev (int->lebits (mod e 128) 7)))))
        (equal (lookup-equal-list ys asg) (int->lebits dv 128))
        (equal (lookup-equal-list axs asg) (int->lebits a 128))
        (equal (lookup-equal-list mxs asg) (int->lebits (- x) 128))
        (equal (lookup-equal cx asg) (int-sub-carry 0 x 128))
        (equal (lookup-equal-list qs asg) (int->lebits q 128))
        (equal (lookup-equal-list rs asg) (int->lebits r 128))
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
        (equal (lookup-equal-list ms asg) (int->lebits (* q dv) 128))
        (equal (lookup-equal-list mcl asg) (repeat 65 0))
        (equal (lookup-equal-list mch asg) (repeat 128 0))
        (equal (lookup-equal-list ls asg) (int->lebits a 128))
        (equal (lookup-equal l asg) 0)
        (equal (lookup-equal-list ds asg)
               (int->lebits (+ (expt 2 128) r (- dv)) 128))
        (equal (lookup-equal d asg) 0)
        (equal (lookup-equal-list nqs asg) (int->lebits (- q) 128))
        (equal (lookup-equal nc asg) (if (< 0 q) 0 1))
        (equal (lookup-equal nz asg) (int-is-not-equal-spec r 0 nil 128))
        (equal (lookup-equal nw asg)
               (if (equal r 0)
                   0
                 (pfield::inv
                  (pfield::sub (int-spec-unsigned r 128)
                               (int-spec-unsigned 0 128)
                               p)
                  p)))
        (equal (lookup-equal-list mqs asg)
               (int->lebits (int-sub-wrapped-spec (- q) 1 t 128) 128))
        (equal (lookup-equal mc asg)
               (if (< (mod (- q) (expt 2 128)) (mod 1 (expt 2 128))) 0 1))
        (equal (lookup-equal-list rds asg)
               (int->lebits (if (equal r 0)
                                (- q)
                              (int-sub-wrapped-spec (- q) 1 t 128))
                            128))
        (equal (lookup-equal-list res asg)
               (int->lebits (int-shr-wrapped-spec x e t 128) 128))))

(defruled int-divshift-shr-checked-signed-128-gadget-complete
  :short "R1CS-COMPLETE of variable-mode signed @('shr_checked'), @('shr')
          and @('shr_assign') at width 128, for an exponent below 128."
  (implies (int-divshift-ssc128-witness-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-checked-signed-128-gadget
                  excess xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl
                  mch ls l ds d nqs nc zeros nz nw mqs mc rds res one p)
                 asg p)
                (equal (lebits->int (lookup-equal-list res asg) t)
                       (int-shr-checked-spec x e t 128))))
  :do-not-induct t
  :use ((:instance int-divshift-ssc128-excess-holds)
        (:instance int-divshift-ssc128-step-rbits)
        (:instance int-divshift-ssc128-spec)
        (:instance int-divshift-shr-signed-128-gadget-complete))
  :in-theory (union-theories '(int-divshift-shr-checked-signed-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))
