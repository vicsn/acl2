; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ViewKey::to_address (snarkVM circuit/account/src/view_key/to_address.rs):
;   Address::from_group(A::g_scalar_multiply(view_key))
; Address::from_group adds no constraint, so the circuit is net-gmul-gadget.
;
; ComputeKey::to_address (circuit/account/src/compute_key/to_address.rs):
;   pk_prf = A::g_scalar_multiply(sk_prf)          net-gmul-gadget
;   Address::from_group(pk_sig + pr_sig + pk_prf)  two Group::add gadgets
; The g_scalar_multiply output coordinates are the single wires (wx, wy) of
; its last fold step, so the second addition is the wire gadget of hpos-gadd.

(in-package "ALEOVM")

(include-book "net-gmul")
(include-book "hpos-gadd")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ViewKey::to_address

(defruled key-view-key-to-address-sound
  :short "R1CS-SOUND of ViewKey::to_address: the output point is
          view-key-to-address-funspec of the view key wire, a scalar."
  (implies (and (net-gmul-hyps)
                (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
           (b* ((out (net-gmul-out rbits sts p))
                (pt (ecurve::point-finite (r1cs::dot-product (car out) asg p)
                                          (r1cs::dot-product (cdr out) asg p))))
             (and (scalarp (lookup-equal s asg))
                  (equal pt (view-key-to-address-funspec (lookup-equal s asg))))))
  :do-not-induct t
  :use net-g-scalar-multiply-sound
  :in-theory '(view-key-to-address-funspec))

(defruled key-view-key-to-address-complete
  :short "R1CS-COMPLETE of ViewKey::to_address: the bits, range-check and
          canonical fold-step witnesses satisfy the constraints."
  (implies (and (net-gmul-hyps)
                (scalarp (lookup-equal s asg))
                (equal (lookup-equal-list rbits asg)
                       (scalar-bits-le (lookup-equal s asg)))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                                   (scalar-modulus-minus-one-bits)))
                (net-gfold-canonp (cdr rbits) sts 1
                                  (ecurve::edwards-bls12-mul (lookup-equal (car rbits) asg)
                                                             (curve-generator-g))
                                  asg))
           (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
  :use net-g-scalar-multiply-complete
  :in-theory nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The g_scalar_multiply output wires.

(defruled key-gfold-out-when-consp
  (implies (consp bits)
           (equal (net-gfold-out bits sts ax ay)
                  (cons (list (list 1 (nth 3 (nth (1- (len bits)) sts))))
                        (list (list 1 (nth 4 (nth (1- (len bits)) sts)))))))
  :induct (net-gfold-out bits sts ax ay)
  :enable (net-gfold-out nth len))

(define key-gmul-wires (sts)
  :verify-guards nil
  (cons (nth 3 (nth 249 sts)) (nth 4 (nth 249 sts))))

(defruled key-gmul-out-is-wires
  (implies (equal (len rbits) 251)
           (equal (net-gmul-out rbits sts p)
                  (cons (list (list 1 (car (key-gmul-wires sts))))
                        (list (list 1 (cdr (key-gmul-wires sts)))))))
  :use (:instance key-gfold-out-when-consp
                  (bits (cdr rbits))
                  (ax (hbhp-tern-x (car rbits) (curve-generator-g)))
                  (ay (hbhp-tern-y (car rbits) (curve-generator-g) p)))
  :do-not-induct t
  :expand ((len rbits) (len (cdr rbits)))
  :cases ((equal (len (cddr rbits)) 249))
  :in-theory (e/d (net-gmul-out key-gmul-wires) (key-gfold-out-when-consp len)))

(defruled key-gmul-wires-eval
  (implies (and (net-gmul-hyps)
                (hpos-pt-boundp (key-gmul-wires sts) asg)
                (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
           (and (scalarp (lookup-equal s asg))
                (equal (hpos-pt-eval (key-gmul-wires sts) asg)
                       (aleo-g-scalar-multiply-funspec (lookup-equal s asg)))))
  :do-not-induct t
  :use (net-g-scalar-multiply-sound
        key-gmul-out-is-wires
        (:instance net-dot-one-wire (w (car (key-gmul-wires sts))))
        (:instance net-dot-one-wire (w (cdr (key-gmul-wires sts)))))
  :in-theory '(hpos-pt-eval hpos-pt-boundp car-cons cdr-cons))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ComputeKey::to_address

(defund key-c-ck-to-address (pk pr s rbits rs sts vs asg)
  "Synthesis of ComputeKey::to_address: (mv out cs vs asg)."
  (declare (xargs :verify-guards nil))
  (b* ((gcs (net-gmul-gadget s rbits rs sts (base-prime)))
       ((mv sum cs1 vs asg) (hpos-c-gadd pr pk vs asg))
       ((mv out cs2 vs asg) (hpos-c-gadd (key-gmul-wires sts) sum vs asg)))
    (mv out (append gcs cs1 cs2) vs asg)))

(defmacro key-ck-addr-hyps ()
  '(and (net-gmul-hyps)
        (hpos-pt-boundp pk asg) (hpos-pt-boundp pr asg)
        (ecurve::edwards-bls12-pointp (hpos-pt-eval pk asg))
        (ecurve::edwards-bls12-pointp (hpos-pt-eval pr asg))
        (hpos-pt-boundp (key-gmul-wires sts) asg)))

(defruled key-gadd-outs
  (and (equal (mv-nth 0 (hpos-c-gadd a b vs asg)) (cons (nth 4 vs) (nth 5 vs)))
       (equal (mv-nth 1 (hpos-c-gadd a b vs asg)) (hpos-gadd-cs a b vs))
       (equal (mv-nth 2 (hpos-c-gadd a b vs asg)) (nthcdr 6 vs)))
  :enable hpos-c-gadd)

(defruled key-gadd-sound
  (implies (and (hpos-gadd-sound-hyps a b vs asg)
                (r1cs::r1cs-constraints-holdp (hpos-gadd-cs a b vs) asg p)
                (equal p (base-prime)))
           (equal (hpos-pt-eval (cons (nth 4 vs) (nth 5 vs)) asg)
                  (group-add-funspec (hpos-pt-eval a asg) (hpos-pt-eval b asg))))
  :use (:instance hpos-c-gadd-sound (asgx asg))
  :in-theory '(key-gadd-outs (:e base-prime)))

(defruled key-take-6-pt-boundp
  (implies (and (<= 6 (len vs))
                (symbol-listp (take 6 vs))
                (r1cs::valuation-binds-allp asg (take 6 vs)))
           (hpos-pt-boundp (cons (nth 4 vs) (nth 5 vs)) asg))
  :expand ((take 6 vs) (take 5 (cdr vs)) (take 4 (cddr vs)) (take 3 (cdddr vs))
           (take 2 (cddddr vs)) (take 1 (cdr (cddddr vs))))
  :enable (nth hpos-pt-boundp r1cs::valuation-binds-allp))

(defruled key-second-gadd-hyps
  (implies (and (<= 12 (len vs))
                (r1cs::r1cs-valuationp asg (base-prime))
                (symbol-listp (take 6 vs))
                (r1cs::valuation-binds-allp asg (take 6 vs))
                (symbol-listp (take 6 (nthcdr 6 vs)))
                (r1cs::valuation-binds-allp asg (take 6 (nthcdr 6 vs)))
                (hpos-pt-boundp g asg)
                (ecurve::edwards-bls12-pointp (hpos-pt-eval (cons (nth 4 vs) (nth 5 vs)) asg))
                (ecurve::edwards-bls12-pointp (hpos-pt-eval g asg)))
           (hpos-gadd-sound-hyps g (cons (nth 4 vs) (nth 5 vs)) (nthcdr 6 vs) asg))
  :use key-take-6-pt-boundp
  :in-theory (e/d (hpos-gadd-sound-hyps) (hpos-pt-boundp hpos-pt-eval take nthcdr)))

(defruled key-compute-key-to-address-sound
  :short "R1CS-SOUND of ComputeKey::to_address, given Group::new on pk_sig and
          pr_sig (points on the curve) and the bound allocated wires: the
          output point is compute-key-to-address-funspec of the wire compute
          key, whose sk_prf is a scalar."
  (b* (((mv out cs & &) (key-c-ck-to-address pk pr s rbits rs sts vs asg0)))
    (implies (and (key-ck-addr-hyps)
                  (<= 12 (len vs))
                  (symbol-listp (take 6 vs))
                  (r1cs::valuation-binds-allp asg (take 6 vs))
                  (symbol-listp (take 6 (nthcdr 6 vs)))
                  (r1cs::valuation-binds-allp asg (take 6 (nthcdr 6 vs)))
                  (r1cs::r1cs-constraints-holdp cs asg p))
             (and (scalarp (lookup-equal s asg))
                  (equal (hpos-pt-eval out asg)
                         (compute-key-to-address-funspec
                          (list (hpos-pt-eval pk asg)
                                (hpos-pt-eval pr asg)
                                (lookup-equal s asg)))))))
  :do-not-induct t
  :use (key-gmul-wires-eval
        key-take-6-pt-boundp
        (:instance key-gadd-sound (a pr) (b pk))
        (:instance hbhp-add-comm (a (hpos-pt-eval pr asg)) (b (hpos-pt-eval pk asg)))
        (:instance key-second-gadd-hyps (g (key-gmul-wires sts)))
        (:instance key-gadd-sound
                   (b (cons (nth 4 vs) (nth 5 vs)))
                   (a (key-gmul-wires sts))
                   (vs (nthcdr 6 vs)))
        (:instance hbhp-add-comm
                   (a (hpos-pt-eval (key-gmul-wires sts) asg))
                   (b (hpos-pt-eval (cons (nth 4 vs) (nth 5 vs)) asg)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (hpos-pt-eval pk asg))
                   (ecurve::point2 (hpos-pt-eval pr asg)))
        (:instance edwards-bls12-pointp-of-aleo-g-scalar-multiply-funspec
                   (s (lookup-equal s asg))))
  :in-theory '(key-c-ck-to-address key-gadd-outs r1cs::r1cs-constraints-holdp-of-append
               compute-key-to-address-funspec curve-compute-keyp group-add-funspec
               hpos-gadd-sound-hyps acl2::len-of-nthcdr nfix true-listp len
               car-cons cdr-cons (:e base-prime) (:e natp) (:e <) (:e binary-+)
               (:e unary--) fix))

(defruled key-c-ck-to-address-outs
  (b* (((mv & cs1 vs1 asg1) (hpos-c-gadd pr pk vs asg))
       ((mv & cs2 vs2 asg2) (hpos-c-gadd (key-gmul-wires sts)
                                         (cons (nth 4 vs) (nth 5 vs)) vs1 asg1)))
    (and (equal (mv-nth 1 (key-c-ck-to-address pk pr s rbits rs sts vs asg))
                (append (net-gmul-gadget s rbits rs sts (base-prime)) cs1 cs2))
         (equal (mv-nth 2 (key-c-ck-to-address pk pr s rbits rs sts vs asg)) vs2)
         (equal (mv-nth 3 (key-c-ck-to-address pk pr s rbits rs sts vs asg)) asg2)))
  :enable (key-c-ck-to-address key-gadd-outs))

(defruled hpos-wit-okp-holdp
  (implies (hpos-wit-okp asg vs asg2 vs2 cs p)
           (r1cs::r1cs-constraints-holdp cs asg2 p))
  :enable hpos-wit-okp)

(defruled key-ck-adds-complete
  (b* ((p (base-prime))
       ((mv & cs1 vs1 asg1) (hpos-c-gadd pr pk vs asg))
       ((mv & cs2 vs2 asg2) (hpos-c-gadd g (cons (nth 4 vs) (nth 5 vs)) vs1 asg1)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= 12 (len vs))
                  (hpos-pt-boundp pk asg) (hpos-pt-boundp pr asg)
                  (hpos-pt-boundp g asg)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval pk asg))
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval pr asg))
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval g asg)))
             (hpos-wit-okp asg vs asg2 vs2 (append cs1 cs2) p)))
  :do-not-induct t
  :use ((:instance hpos-c-gadd-complete (a pr) (b pk))
        (:instance hpos-c-gadd-complete
                   (b (cons (nth 4 vs) (nth 5 vs))) (a g)
                   (vs (nthcdr 6 vs))
                   (asg (mv-nth 3 (hpos-c-gadd pr pk vs asg))))
        (:instance hpos-wit-okp-append
                   (asg1 (mv-nth 3 (hpos-c-gadd pr pk vs asg)))
                   (vs1 (nthcdr 6 vs))
                   (cs1 (hpos-gadd-cs pr pk vs))
                   (asg2 (mv-nth 3 (hpos-c-gadd g (cons (nth 4 vs) (nth 5 vs))
                                                (nthcdr 6 vs)
                                                (mv-nth 3 (hpos-c-gadd pr pk vs asg)))))
                   (vs2 (nthcdr 6 (nthcdr 6 vs)))
                   (cs2 (hpos-gadd-cs g (cons (nth 4 vs) (nth 5 vs)) (nthcdr 6 vs)))
                   (p (base-prime)))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (hpos-c-gadd pr pk vs asg)))
                   (vs2 (nthcdr 6 vs))
                   (cs (hpos-gadd-cs pr pk vs))
                   (p (base-prime)))
        (:instance hpos-pt-boundp-when-ext-p
                   (pt g) (old asg) (new (mv-nth 3 (hpos-c-gadd pr pk vs asg))))
        (:instance hpos-pt-eval-when-ext-p
                   (pt g) (old asg) (new (mv-nth 3 (hpos-c-gadd pr pk vs asg))))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                   (asg (mv-nth 3 (hpos-c-gadd pr pk vs asg))) (p (base-prime)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (hpos-pt-eval pr asg))
                   (ecurve::point2 (hpos-pt-eval pk asg))))
  :in-theory '(key-gadd-outs group-add-funspec (:t len) acl2::len-of-nthcdr nfix (:e base-prime) (:e nfix)
               (:e natp) (:e <) (:e binary-+) (:e unary--) fix))

(defruled key-compute-key-to-address-complete
  :short "R1CS-COMPLETE of ComputeKey::to_address: from an assignment with
          the g_scalar_multiply witnesses (bits, range check, canonical fold
          steps) whose constraints mention only its wires, witness generation
          for the two additions yields an assignment satisfying all the
          constraints."
  (b* (((mv & cs & asg2) (key-c-ck-to-address pk pr s rbits rs sts vs asg)))
    (implies (and (key-ck-addr-hyps)
                  (scalarp (lookup-equal s asg))
                  (equal (lookup-equal-list rbits asg)
                         (scalar-bits-le (lookup-equal s asg)))
                  (equal (lookup-equal-list rs asg)
                         (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                                     (scalar-modulus-minus-one-bits)))
                  (net-gfold-canonp (cdr rbits) sts 1
                                    (ecurve::edwards-bls12-mul
                                     (lookup-equal (car rbits) asg)
                                     (curve-generator-g))
                                    asg)
                  (hpos-cs-boundp (net-gmul-gadget s rbits rs sts p) asg)
                  (hpos-supply-okp vs asg)
                  (<= 12 (len vs)))
             (r1cs::r1cs-constraints-holdp cs asg2 p)))
  :do-not-induct t
  :use (net-g-scalar-multiply-complete
        key-gmul-wires-eval
        (:instance key-ck-adds-complete (g (key-gmul-wires sts)))
        (:instance edwards-bls12-pointp-of-aleo-g-scalar-multiply-funspec
                   (s (lookup-equal s asg)))
        (:instance hpos-wit-okp-forward
                   (asg2 (mv-nth 3 (key-c-ck-to-address pk pr s rbits rs sts vs asg)))
                   (vs2 (mv-nth 2 (key-c-ck-to-address pk pr s rbits rs sts vs asg)))
                   (cs (append (hpos-gadd-cs pr pk vs)
                               (hpos-gadd-cs (key-gmul-wires sts)
                                             (cons (nth 4 vs) (nth 5 vs)) (nthcdr 6 vs))))
                   (p (base-prime)))
        (:instance hpos-holdp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (key-c-ck-to-address pk pr s rbits rs sts vs asg)))
                   (cs (net-gmul-gadget s rbits rs sts p)))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                   (asg (mv-nth 3 (key-c-ck-to-address pk pr s rbits rs sts vs asg)))
                   (p (base-prime))))
  :in-theory '(key-c-ck-to-address-outs key-gadd-outs r1cs::r1cs-constraints-holdp-of-append
               hpos-wit-okp-holdp (:e base-prime)))
