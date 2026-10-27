; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode unsigned shr_checked (and shr, shr_assign) at width 128:
; the exponent bits at and above 7 are zero, then the unsigned 128-bit
; shr_wrapped circuit.  The exponent is a magnitude Integer::new of width
; m; the select wires hold its low 7 bits, most significant first.

(in-package "ALEOVM")

(include-book "int-divshift-shr-unsigned-128")
(include-book "int-divshift-shl-checked-sound")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-shr-checked-unsigned-128-gadget ((excess symbol-listp)
                                                      (xs symbol-listp)
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
  (append (int-shr-checked-bound-gadget excess)
          (int-divshift-shr-unsigned-128-gadget
           xs rbits sqs ts ys qs rs ll hl lh hh ms mcl mch ls l ds d one p)))

(defruledl int-divshift-suc128-width
  (and (integer-widthp 128)
       (equal (1- (integer-length 128)) 7))
  :enable integer-widthp)

(defruledl int-divshift-suc128-spec
  (implies (and (int-valuep x nil 128)
                (natp e)
                (< e 128))
           (equal (int-shr-checked-spec x e nil 128)
                  (int-shr-wrapped-spec x e nil 128)))
  :use (:instance int-shr-checked-is-wrapped-when-in-range
                  (signedp nil) (n 128))
  :enable integer-widthp)

(defruledl int-divshift-suc128-excess-holds
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

(defmacro int-divshift-suc128-common-hyps ()
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
        (member-equal m '(8 16 32))
        (< e (expt 2 m))
        (symbol-listp excess)
        (r1cs::valuation-binds-allp asg excess)
        (equal (lookup-equal-list rbits asg)
               (rev (take 7 (int->lebits e m))))
        (equal (lookup-equal-list excess asg)
               (nthcdr 7 (int->lebits e m)))))

(defrulel int-divshift-suc128-step-bound
  (implies (and (int-divshift-suc128-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-shr-checked-bound-gadget excess) asg p))
           (< e 128))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-shlc-mag-facts)
        (:instance int-divshift-suc128-width)
        (:instance int-divshift-shlc-excess-len (k 7))
        (:instance int-shr-checked-bound-gadget-sound
                   (n 128) (ebits (int->lebits e m))))
  :in-theory (theory 'minimal-theory))

(defrulel int-divshift-suc128-step-rbits
  (implies (and (int-divshift-suc128-common-hyps)
                (< e 128))
           (equal (lookup-equal-list rbits asg)
                  (rev (int->lebits (mod e 128) 7))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-suc128-width)
        (:instance int-divshift-shlc-low-bits (n 128)))
  :in-theory (union-theories '(mag-at-least-7)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defrule mag-at-least-7
     (implies (member-equal m '(8 16 32)) (<= 7 m)))))

(defruled int-divshift-shr-checked-unsigned-128-gadget-sound
  :short "R1CS-SOUND of variable-mode unsigned @('shr_checked'), @('shr')
          and @('shr_assign') at width 128."
  (implies (and (int-divshift-suc128-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-checked-unsigned-128-gadget
                  excess xs rbits sqs ts ys qs rs ll hl lh hh ms mcl mch ls l
                  ds d one p)
                 asg p))
           (and (< e 128)
                (equal (lebits->int (lookup-equal-list qs asg) nil)
                       (int-shr-checked-spec x e nil 128))))
  :do-not-induct t
  :use ((:instance int-divshift-suc128-step-bound)
        (:instance int-divshift-suc128-step-rbits)
        (:instance int-divshift-suc128-spec)
        (:instance int-divshift-shr-unsigned-128-gadget-sound))
  :in-theory (union-theories '(int-divshift-shr-checked-unsigned-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))

(defruled int-divshift-shr-checked-unsigned-128-gadget-complete
  :short "R1CS-COMPLETE of variable-mode unsigned @('shr_checked'),
          @('shr') and @('shr_assign') at width 128, for an exponent below
          128.  A larger exponent is unsatisfiable by the soundness
          theorem."
  (implies (and (int-divshift-suc128-common-hyps)
                (< e 128)
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
            (int-divshift-shr-checked-unsigned-128-gadget
             excess xs rbits sqs ts ys qs rs ll hl lh hh ms mcl mch ls l
             ds d one p)
            asg p))
  :do-not-induct t
  :use ((:instance int-divshift-suc128-excess-holds)
        (:instance int-divshift-suc128-step-rbits)
        (:instance int-divshift-shr-unsigned-128-gadget-complete))
  :in-theory (union-theories '(int-divshift-shr-checked-unsigned-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append)
                             (theory 'minimal-theory)))
