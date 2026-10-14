; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Compute-key and signature equality.
; ComputeKey::is_equal is group equality on pk_sig and on pr_sig and scalar
; equality on sk_prf, then boolean and of the three bits.
; The scalar is_equal bit is the linear combination 1 - r, so the last and
; is (t) * (1 - r) = (out).
; Signature::is_equal is the same shape on challenge, response, and the
; compute key.
; is_not_equal reuses the constraints; the result is 1 - out.

(in-package "ALEOVM")

(include-book "crv-equal")
(include-book "../r1cs/boolean-and")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-and-var-not-gadget ((x symbolp) (r symbolp) (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "(x) * (1 - r) = (out)."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1) (list (1- p) r))
         :c (list (list 1 out)))))

(defruled crv-and-var-not-gadget-to-mul
  (implies (and (symbolp x) (symbolp r) (symbolp out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg out))
           (equal (r1cs::r1cs-constraints-holdp
                   (crv-and-var-not-gadget x r out p) asg p)
                  (equal (pfield::mul (lookup-equal x asg)
                                      (pfield::sub 1 (lookup-equal r asg) p)
                                      p)
                         (lookup-equal out asg))))
  :enable (crv-and-var-not-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(define crv-compute-key-is-equal-gadget
  ((pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pkmx symbolp) (pkrx symbolp) (pkmy symbolp) (pkry symbolp) (pkout symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (prmx symbolp) (prrx symbolp) (prmy symbolp) (prry symbolp) (prout symbolp)
   (s1 symbolp) (s2 symbolp) (sm symbolp) (sr symbolp)
   (t1 symbolp) (out symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-group-is-equal-gadget
           pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout p)
          (crv-group-is-equal-gadget
           pr1x pr1y pr2x pr2y prmx prrx prmy prry prout p)
          (crv-scalar-is-equal-gadget s1 s2 sm sr p)
          (boolean-and-gadget pkout prout t1)
          (crv-and-var-not-gadget t1 sr out p)))

(defruled crv-compute-key-is-equal-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (curve-compute-keyp ck1)
                (curve-compute-keyp ck2)
                (bitp (lookup-equal 'pkrx asg))
                (bitp (lookup-equal 'pkry asg))
                (bitp (lookup-equal 'prrx asg))
                (bitp (lookup-equal 'prry asg))
                (bitp (lookup-equal 'sr asg))
                (bitp (lookup-equal 'pkout asg))
                (bitp (lookup-equal 'prout asg))
                (bitp (lookup-equal 't1 asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-is-equal-gadget
                  'pk1x 'pk1y 'pk2x 'pk2y 'pkmx 'pkrx 'pkmy 'pkry 'pkout
                  'pr1x 'pr1y 'pr2x 'pr2y 'prmx 'prrx 'prmy 'prry 'prout
                  's1 's2 'sm 'sr 't1 'out p)
                 asg p)
                (equal (lookup-equal 'pkout asg)
                       (group-is-equal-funspec (first ck1) (first ck2)))
                (equal (lookup-equal 'prout asg)
                       (group-is-equal-funspec (second ck1) (second ck2)))
                (equal (pfield::sub 1 (lookup-equal 'sr asg) p)
                       (scalar-is-equal-funspec (third ck1) (third ck2))))
           (equal (lookup-equal 'out asg)
                  (compute-key-is-equal-funspec ck1 ck2)))
  :enable (compute-key-is-equal-funspec
           boolean-and-funspec
           crv-bitand-is-boolean-and-funspec
           crv-and-var-not-gadget-to-mul
           crv-mul-of-bits-is-and
           boolean-not-funspec
           curve-compute-keyp))

(defconst *crv-compute-key-is-equal-sample*
  '((pk1x . 0) (pk1y . 1) (pk2x . 0) (pk2y . 1)
    (pkmx . 0) (pkrx . 0) (pkmy . 0) (pkry . 0) (pkout . 1)
    (pr1x . 0) (pr1y . 1) (pr2x . 0) (pr2y . 1)
    (prmx . 0) (prrx . 0) (prmy . 0) (prry . 0) (prout . 1)
    (s1 . 0) (s2 . 0) (sm . 0) (sr . 0)
    (t1 . 1) (out . 1)))

(defruled crv-compute-key-is-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-compute-key-is-equal-sample* p)
                (fieldp 0) (fieldp 1) (scalarp 0))
           (r1cs::r1cs-constraints-holdp
            (crv-compute-key-is-equal-gadget
             'pk1x 'pk1y 'pk2x 'pk2y 'pkmx 'pkrx 'pkmy 'pkry 'pkout
             'pr1x 'pr1y 'pr2x 'pr2y 'prmx 'prrx 'prmy 'prry 'prout
             's1 's2 'sm 'sr 't1 'out p)
            *crv-compute-key-is-equal-sample* p))
  :enable (crv-compute-key-is-equal-gadget
           crv-group-is-equal-gadget
           crv-field-is-not-equal-gadget-to-spec
           crv-and-not-gadget-to-mul
           crv-and-var-not-gadget-to-mul
           boolean-and-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal)
  :disable ((:definition pfield::sub) pfield::mul-of-sub-arg1))

(define crv-compute-key-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_compute_key_is_equal(pk1x, pk1y, pk2x, pk2y, pkmx, pkrx, pkmy, pkry, pkout, pr1x, pr1y, pr2x, pr2y, prmx, prrx, prmy, prry, prout, s1, s2, sm, sr, t1, out) := {
    (pk1x - pk2x) * (pkmx) == (pkrx),
    (pk1x - pk2x) * (1 - pkrx) == (0),
    (pk1y - pk2y) * (pkmy) == (pkry),
    (pk1y - pk2y) * (1 - pkry) == (0),
    (1 - pkrx) * (1 - pkry) == (pkout),
    (pr1x - pr2x) * (prmx) == (prrx),
    (pr1x - pr2x) * (1 - prrx) == (0),
    (pr1y - pr2y) * (prmy) == (prry),
    (pr1y - pr2y) * (1 - prry) == (0),
    (1 - prrx) * (1 - prry) == (prout),
    (s1 - s2) * (sm) == (sr),
    (s1 - s2) * (1 - sr) == (0),
    (pkout) * (prout) == (t1),
    (t1) * (1 - sr) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-compute-key-is-equal-circuit)
            :pred crv-compute-key-is-equal-pred
            :prime prime)

(define crv-compute-key-is-not-equal-gadget
  ((pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pkmx symbolp) (pkrx symbolp) (pkmy symbolp) (pkry symbolp) (pkout symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (prmx symbolp) (prrx symbolp) (prmy symbolp) (prry symbolp) (prout symbolp)
   (s1 symbolp) (s2 symbolp) (sm symbolp) (sr symbolp)
   (t1 symbolp) (out symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-compute-key-is-equal-gadget
   pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
   pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
   s1 s2 sm sr t1 out p))

(defruled crv-compute-key-is-not-equal-gadget-sound
  (implies (and (equal p (base-prime))
                (bitp (lookup-equal 'out asg))
                (equal (lookup-equal 'out asg)
                       (compute-key-is-equal-funspec ck1 ck2)))
           (equal (pfield::sub 1 (lookup-equal 'out asg) p)
                  (compute-key-is-not-equal-funspec ck1 ck2)))
  :enable (compute-key-is-not-equal-funspec
           compute-key-is-equal-funspec
           crv-not-of-equal-bit))

(defconst *crv-compute-key-is-not-equal-sample*
  *crv-compute-key-is-equal-sample*)

(defruled crv-compute-key-is-not-equal-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-compute-key-is-not-equal-sample* p)
                (fieldp 0) (fieldp 1) (scalarp 0))
           (r1cs::r1cs-constraints-holdp
            (crv-compute-key-is-not-equal-gadget
             'pk1x 'pk1y 'pk2x 'pk2y 'pkmx 'pkrx 'pkmy 'pkry 'pkout
             'pr1x 'pr1y 'pr2x 'pr2y 'prmx 'prrx 'prmy 'prry 'prout
             's1 's2 'sm 'sr 't1 'out p)
            *crv-compute-key-is-not-equal-sample* p))
  :enable (crv-compute-key-is-not-equal-gadget
           crv-compute-key-is-equal-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-signature-is-equal-gadget
  ((c1 symbolp) (c2 symbolp) (cm symbolp) (cr symbolp)
   (r1 symbolp) (r2 symbolp) (rm symbolp) (rr symbolp)
   (pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pkmx symbolp) (pkrx symbolp) (pkmy symbolp) (pkry symbolp) (pkout symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (prmx symbolp) (prrx symbolp) (prmy symbolp) (prry symbolp) (prout symbolp)
   (s1 symbolp) (s2 symbolp) (sm symbolp) (sr symbolp)
   (tck symbolp) (ckout symbolp)
   (ts symbolp) (out symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (crv-scalar-is-equal-gadget c1 c2 cm cr p)
          (crv-scalar-is-equal-gadget r1 r2 rm rr p)
          (crv-compute-key-is-equal-gadget
           pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
           pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
           s1 s2 sm sr tck ckout p)
          (crv-and-not-gadget cr rr ts p)
          (boolean-and-gadget ts ckout out)))

(defruled crv-signature-is-equal-gadget-sound
  (implies (and (equal p (base-prime))
                (curve-signaturep sig1)
                (curve-signaturep sig2)
                (bitp (lookup-equal 'out asg))
                (equal (pfield::sub 1 (lookup-equal 'cr asg) p)
                       (scalar-is-equal-funspec (first sig1) (first sig2)))
                (equal (pfield::sub 1 (lookup-equal 'rr asg) p)
                       (scalar-is-equal-funspec (second sig1) (second sig2)))
                (equal (lookup-equal 'ckout asg)
                       (compute-key-is-equal-funspec (third sig1) (third sig2)))
                (equal (lookup-equal 'out asg)
                       (boolean-and-funspec
                        (boolean-and-funspec
                         (pfield::sub 1 (lookup-equal 'cr asg) p)
                         (pfield::sub 1 (lookup-equal 'rr asg) p))
                        (lookup-equal 'ckout asg))))
           (equal (lookup-equal 'out asg)
                  (signature-is-equal-funspec sig1 sig2)))
  :enable (signature-is-equal-funspec
           boolean-and-funspec
           curve-signaturep))

(define crv-signature-is-not-equal-gadget
  ((c1 symbolp) (c2 symbolp) (cm symbolp) (cr symbolp)
   (r1 symbolp) (r2 symbolp) (rm symbolp) (rr symbolp)
   (pk1x symbolp) (pk1y symbolp) (pk2x symbolp) (pk2y symbolp)
   (pkmx symbolp) (pkrx symbolp) (pkmy symbolp) (pkry symbolp) (pkout symbolp)
   (pr1x symbolp) (pr1y symbolp) (pr2x symbolp) (pr2y symbolp)
   (prmx symbolp) (prrx symbolp) (prmy symbolp) (prry symbolp) (prout symbolp)
   (s1 symbolp) (s2 symbolp) (sm symbolp) (sr symbolp)
   (tck symbolp) (ckout symbolp)
   (ts symbolp) (out symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-signature-is-equal-gadget
   c1 c2 cm cr r1 r2 rm rr
   pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
   pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
   s1 s2 sm sr tck ckout ts out p))

(defruled crv-signature-is-not-equal-gadget-sound
  (implies (and (equal p (base-prime))
                (bitp out)
                (equal out (signature-is-equal-funspec sig1 sig2)))
           (equal (pfield::sub 1 out p)
                  (signature-is-not-equal-funspec sig1 sig2)))
  :enable (signature-is-not-equal-funspec
           signature-is-equal-funspec
           crv-not-of-equal-bit))
