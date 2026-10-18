; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Projections that allocate no constraint, and ComputeKey::from, whose only
; constraint is the abstract HashToScalar.  The theorem assumes that hash
; result equals aleo-hash-to-scalar-psd4-funspec, as required for hash calls.

(in-package "ALEOVM")

(include-book "crv-field")
(include-book "../fun-specs/curve-address")
(include-book "../fun-specs/curve-account")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-address-to-field-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: the field is the x-coordinate linear combination."
  nil)

(defruled crv-address-to-field-gadget-sound
  (implies (and (ecurve::edwards-bls12-pointp p0)
                (equal x (ecurve::point-finite->x p0)))
           (equal (address-to-field-funspec p0) x))
  :enable (address-to-field-funspec group-to-x-coordinate-funspec))

(defruled crv-address-to-field-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp p0)
                (equal x (ecurve::point-finite->x p0)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-address-to-field-gadget) asg p)
                (equal (address-to-field-funspec p0) x)))
  :enable (crv-address-to-field-gadget
           address-to-field-funspec
           group-to-x-coordinate-funspec))

(defconst *crv-address-to-field-sample* nil)

(defruled crv-address-to-field-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp
            *crv-address-to-field-sample* asg p))
  :enable (crv-address-to-field-gadget r1cs::r1cs-constraints-holdp))

(define crv-address-to-field-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_address_to_field() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-address-to-field-circuit)
            :pred crv-address-to-field-pred
            :prime prime)

(defruled crv-address-to-field-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (ecurve::edwards-bls12-pointp p0)
                (equal x (ecurve::point-finite->x p0))
                (crv-address-to-field-pred prime))
           (equal (address-to-field-funspec p0) x))
  :enable (crv-address-to-field-pred
           address-to-field-funspec
           group-to-x-coordinate-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-compute-key-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: the fields are the two x-coordinates."
  nil)

(defruled crv-compute-key-to-fields-gadget-sound
  (implies (curve-compute-keyp ck)
           (equal (list (ecurve::point-finite->x (first ck))
                        (ecurve::point-finite->x (second ck)))
                  (compute-key-to-fields-funspec ck)))
  :enable (compute-key-to-fields-funspec group-to-x-coordinate-funspec))

(defruled crv-compute-key-to-fields-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (curve-compute-keyp ck))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-to-fields-gadget) asg p)
                (equal (list (ecurve::point-finite->x (first ck))
                             (ecurve::point-finite->x (second ck)))
                       (compute-key-to-fields-funspec ck))))
  :enable (crv-compute-key-to-fields-gadget
           compute-key-to-fields-funspec
           group-to-x-coordinate-funspec))

(defconst *crv-compute-key-to-fields-sample* nil)

(defruled crv-compute-key-to-fields-sample-holds
  (implies (r1cs::r1cs-valuationp asg (base-prime))
           (r1cs::r1cs-constraints-holdp
            *crv-compute-key-to-fields-sample* asg (base-prime)))
  :enable r1cs::r1cs-constraints-holdp)

(define crv-compute-key-to-fields-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_compute_key_to_fields() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-compute-key-to-fields-circuit)
            :pred crv-compute-key-to-fields-pred
            :prime prime)

(defruled crv-compute-key-to-fields-pred-to-funspec
  (implies (and (curve-compute-keyp ck)
                (crv-compute-key-to-fields-pred prime))
           (equal (list (ecurve::point-finite->x (first ck))
                        (ecurve::point-finite->x (second ck)))
                  (compute-key-to-fields-funspec ck)))
  :enable (crv-compute-key-to-fields-pred
           compute-key-to-fields-funspec
           group-to-x-coordinate-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-signature-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: challenge and response are already field elements,
          and the compute key contributes its two x-coordinates."
  nil)

(defruled crv-signature-to-fields-gadget-sound
  (implies (curve-signaturep sig)
           (equal (list* (lnfix (first sig))
                         (lnfix (second sig))
                         (compute-key-to-fields-funspec (third sig)))
                  (signature-to-fields-funspec sig)))
  :enable signature-to-fields-funspec)

(defruled crv-signature-to-fields-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (curve-signaturep sig))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-signature-to-fields-gadget) asg p)
                (equal (list* (lnfix (first sig))
                              (lnfix (second sig))
                              (compute-key-to-fields-funspec (third sig)))
                       (signature-to-fields-funspec sig))))
  :enable (crv-signature-to-fields-gadget signature-to-fields-funspec))

(defconst *crv-signature-to-fields-sample* nil)

(defruled crv-signature-to-fields-sample-holds
  (implies (r1cs::r1cs-valuationp asg (base-prime))
           (r1cs::r1cs-constraints-holdp
            *crv-signature-to-fields-sample* asg (base-prime)))
  :enable r1cs::r1cs-constraints-holdp)

(define crv-signature-to-fields-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_signature_to_fields() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-signature-to-fields-circuit)
            :pred crv-signature-to-fields-pred
            :prime prime)

(defruled crv-signature-to-fields-pred-to-funspec
  (implies (and (curve-signaturep sig)
                (crv-signature-to-fields-pred prime))
           (equal (signature-to-fields-funspec sig)
                  (list* (lnfix (first sig))
                         (lnfix (second sig))
                         (compute-key-to-fields-funspec (third sig)))))
  :enable (crv-signature-to-fields-pred signature-to-fields-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-compute-key-from-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No non-hash constraints.  sk_prf is the abstract Poseidon hash."
  nil)

; Not an R1CS soundness theorem: the empty gadget does not constrain sk,
; and the hypothesis already sets sk to the abstract Poseidon hash.
; R1CS-SOUND stays 0.  Completeness of the empty constraint list is separate.
(defruled crv-compute-key-from-under-hash-assumption
  (implies (and (ecurve::edwards-bls12-pointp pk-sig)
                (ecurve::edwards-bls12-pointp pr-sig)
                (equal sk
                       (aleo-hash-to-scalar-psd4-funspec
                        (list (ecurve::point-finite->x pk-sig)
                              (ecurve::point-finite->x pr-sig)))))
           (equal (list pk-sig pr-sig sk)
                  (compute-key-from-funspec pk-sig pr-sig)))
  :enable compute-key-from-funspec)

(defruled crv-compute-key-from-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp pk-sig)
                (ecurve::edwards-bls12-pointp pr-sig)
                (equal sk
                       (aleo-hash-to-scalar-psd4-funspec
                        (list (ecurve::point-finite->x pk-sig)
                              (ecurve::point-finite->x pr-sig)))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-from-gadget) asg p)
                (equal (list pk-sig pr-sig sk)
                       (compute-key-from-funspec pk-sig pr-sig))))
  :enable (crv-compute-key-from-gadget
           crv-compute-key-from-under-hash-assumption))

(defconst *crv-compute-key-from-sample* nil)

(defruled crv-compute-key-from-sample-holds
  (implies (r1cs::r1cs-valuationp asg (base-prime))
           (r1cs::r1cs-constraints-holdp
            *crv-compute-key-from-sample* asg (base-prime)))
  :enable r1cs::r1cs-constraints-holdp)

(define crv-compute-key-from-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_compute_key_from() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-compute-key-from-circuit)
            :pred crv-compute-key-from-pred
            :prime prime)

(defruled crv-compute-key-from-pred-to-funspec
  (implies (and (ecurve::edwards-bls12-pointp pk-sig)
                (ecurve::edwards-bls12-pointp pr-sig)
                (equal sk
                       (aleo-hash-to-scalar-psd4-funspec
                        (list (ecurve::point-finite->x pk-sig)
                              (ecurve::point-finite->x pr-sig))))
                (crv-compute-key-from-pred prime))
           (equal (list pk-sig pr-sig sk)
                  (compute-key-from-funspec pk-sig pr-sig)))
  :enable (crv-compute-key-from-pred
           crv-compute-key-from-under-hash-assumption))
