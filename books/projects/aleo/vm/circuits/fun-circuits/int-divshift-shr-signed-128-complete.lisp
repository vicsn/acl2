; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE of variable-mode signed shr_wrapped at width 128: the
; canonical snarkVM witnesses (power chain, abs_wrapped, division of |x| by
; 2^(e mod 128), negation, is_equal of the remainder with 0, subtraction of
; one, and the two ternaries) satisfy int-divshift-shr-signed-128-gadget.

(in-package "ALEOVM")

(include-book "int-divshift-shr-signed-128")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))

(set-prover-step-limit 20000000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-ss128c-hyps ()
  '(and (int-divshift-ss128-common-hyps)
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

(defrulel int-divshift-ss128c-front
  (implies (int-divshift-ss128c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-pow2-gadget rbits sqs ts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-shift-lower-gadget (car (last ts)) ys p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-abs-wrapped-signed-gadget xs axs mxs cx one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (unsigned-medium-div-gadget axs ys qs rs ll hl lh hh
                                             ms mcl mch ls l ds d one p)
                 asg p)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-values)
        (:instance int-divshift-pow2-lower-128-complete)
        (:instance int-divshift-sd128-abs-complete (n 128))
        (:instance int-divshift-unsigned-division-128-complete
                   (xs axs) (x (abs x)) (y (expt 2 (mod e 128)))
                   (low-low ll) (high-low hl) (low-high lh) (high-high hh)
                   (ms-carry-low mcl) (ms-carry-high mch)))
  :in-theory (union-theories '((:e integer-widthp) posp)
                             (theory 'minimal-theory)))

(defrulel int-divshift-ss128c-middle
  (implies (int-divshift-ss128c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (unsigned-small-sub-wrapped-const-var-gadget
                  (int->lebits 0 128) qs nqs nc one p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-is-not-equal-gadget rs zeros nz nw one p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sub-wrapped-var-const-gadget
                  nqs (int->lebits 1 128) mqs mc p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-negsel-gadget nz nqs mqs rds one p) asg p)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-values)
        (:instance int-divshift-sd128-neg-complete
                   (vs qs) (nvs nqs) (n 128) (v q))
        (:instance int-is-not-equal-gadget-complete
                   (xs rs) (ys zeros) (z nz) (w nw) (n 128) (signedp nil)
                   (x r) (y 0))
        (:instance int-divshift-sub-wrapped-var-const-complete
                   (xs nqs) (zs mqs) (z mc) (n 128) (signedp t)
                   (x (- q)) (y 1))
        (:instance int-divshift-negsel-gadget-complete
                   (c nz) (xs nqs) (ys mqs) (zs rds) (n 128)
                   (x (- q)) (y (int-sub-wrapped-spec (- q) 1 t 128))))
  :in-theory (union-theories '((:e integer-widthp) (:e expt)
                               int-is-not-equal-spec int-spec-bool
                               (:e bitp) (:e booleanp) (:e posp) (:e natp))
                             (theory 'minimal-theory)))

(defruled int-divshift-ss128c-select
  (implies (and (int-valuep x t 128)
                (natp e))
           (b* ((dv (expt 2 (mod e 128)))
                (q (truncate (abs x) dv))
                (r (rem (abs x) dv)))
             (equal (if (equal (if (< x 0) 1 0) 1)
                        (int->lebits (if (equal r 0)
                                         (- q)
                                       (int-sub-wrapped-spec (- q) 1 t 128))
                                     128)
                      (int->lebits q 128))
                    (int->lebits (int-shr-wrapped-spec x e t 128) 128))))
  :do-not-induct t
  :use ((:instance int-divshift-ss128-values)
        (:instance int-divshift-sshr128-floor-cases
                   (d (expt 2 (mod e 128))))
        (:instance int->lebits-of-int-wrap
                   (x (+ -1 (- (truncate (abs x) (expt 2 (mod e 128))))))
                   (signedp t) (n 128)))
  :in-theory (e/d (int-shr-wrapped-spec int-sub-wrapped-spec
                   acl2::ifix-when-integerp)
                  (int-divshift-sshr128-floor-cases
                   int-divshift-ss128-values
                   int->lebits-of-int-wrap
                   int->lebits int-wrap floor truncate rem abs mod)))

(defrulel int-divshift-ss128c-last
  (implies (int-divshift-ss128c-hyps)
           (r1cs::r1cs-constraints-holdp
            (integer-ternary-gadget (car (last xs)) rds qs res p)
            asg p))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance int-divshift-ss128-values)
        (:instance int-divshift-sd128-msb-lookup (n 128))
        (:instance int-divshift-sd128-msb-binds (n 128))
        (:instance integer-ternary-gadget-correctness
                   (x (car (last xs))) (ys rds) (zs qs) (ws res))
        (:instance int-divshift-ss128c-select))
  :in-theory (union-theories '((:e posp) (:e bitp) bitp)
                             (theory 'minimal-theory)))

(defruledl int-divshift-ss128c-spec-range
  (implies (and (int-valuep x t 128) (natp e))
           (and (int-valuep (int-shr-wrapped-spec x e t 128) t 128)
                (equal (ifix (int-shr-wrapped-spec x e t 128))
                       (int-shr-wrapped-spec x e t 128))))
  :use ((:instance int-divshift-ss128-floor-range (dv (expt 2 (mod e 128))))
        (:instance int-divshift-ss128-values))
  :enable (int-shr-wrapped-spec int-valuep acl2::ifix-when-integerp)
  :disable (floor mod int-divshift-ss128-values abs truncate rem))

(defruled int-divshift-shr-signed-128-gadget-complete
  :short "R1CS-COMPLETE of variable-mode signed @('shr_wrapped') at width
          128."
  (implies (int-divshift-ss128c-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-signed-128-gadget
                  xs rbits sqs ts ys axs mxs cx qs rs ll hl lh hh ms mcl mch
                  ls l ds d nqs nc zeros nz nw mqs mc rds res one p)
                 asg p)
                (equal (lebits->int (lookup-equal-list res asg) t)
                       (int-shr-wrapped-spec x e t 128))))
  :do-not-induct t
  :use ((:instance int-divshift-ss128c-front)
        (:instance int-divshift-ss128c-middle)
        (:instance int-divshift-ss128c-last)
        (:instance int-divshift-ss128c-spec-range)
        (:instance lebits->int-of-int->lebits
                   (x (int-shr-wrapped-spec x e t 128)) (signedp t) (n 128)))
  :in-theory (union-theories '(int-divshift-shr-signed-128-gadget
                               r1cs::r1cs-constraints-holdp-of-append
                               (:e posp))
                             (theory 'minimal-theory)))
