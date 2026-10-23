; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey::to_fields and Signature::to_fields soundness and completeness
; with no type hypothesis.  Both circuits emit no constraint.  The funspecs
; read only the x-coordinates of pk_sig and pr_sig and (for a signature) the
; challenge and response through lnfix, never sk_prf, so any compute key or
; signature whose components the wires carry is mapped to the wire values.
; Wire values are natural numbers, so lnfix of the challenge and response
; wires is the wire value itself.

(in-package "ALEOVM")

(include-book "crv-project")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-natp-of-lookup-when-valuation
  (implies (and (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg w))
           (natp (lookup-equal w asg)))
  :hints (("Goal"
           :use (:instance r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type
                           (valuation asg) (prime p) (var w)))))

(defruled progx-compute-key-to-fields-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-to-fields-gadget) asg p)
                (equal (lookup-equal pkx asg)
                       (ecurve::point-finite->x (first ck)))
                (equal (lookup-equal prx asg)
                       (ecurve::point-finite->x (second ck))))
           (equal (list (lookup-equal pkx asg)
                        (lookup-equal prx asg))
                  (compute-key-to-fields-funspec ck)))
  :enable (compute-key-to-fields-funspec group-to-x-coordinate-funspec))

(defruled progx-compute-key-to-fields-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (equal (lookup-equal pkx asg)
                       (ecurve::point-finite->x (first ck)))
                (equal (lookup-equal prx asg)
                       (ecurve::point-finite->x (second ck))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-to-fields-gadget) asg p)
                (equal (list (lookup-equal pkx asg)
                             (lookup-equal prx asg))
                       (compute-key-to-fields-funspec ck))))
  :enable (crv-compute-key-to-fields-gadget
           compute-key-to-fields-funspec
           group-to-x-coordinate-funspec))

(defruled progx-signature-to-fields-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-to-fields-gadget) asg p)
                (equal (lookup-equal c asg) (first sig))
                (equal (lookup-equal r asg) (second sig))
                (equal (lookup-equal pkx asg)
                       (ecurve::point-finite->x (first (third sig))))
                (equal (lookup-equal prx asg)
                       (ecurve::point-finite->x (second (third sig)))))
           (equal (list (lookup-equal c asg)
                        (lookup-equal r asg)
                        (lookup-equal pkx asg)
                        (lookup-equal prx asg))
                  (signature-to-fields-funspec sig)))
  :hints (("Goal"
           :use ((:instance progx-natp-of-lookup-when-valuation (w c))
                 (:instance progx-natp-of-lookup-when-valuation (w r)))
           :in-theory (enable signature-to-fields-funspec
                              compute-key-to-fields-funspec
                              group-to-x-coordinate-funspec))))

(defruled progx-signature-to-fields-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal c asg) (first sig))
                (equal (lookup-equal r asg) (second sig))
                (equal (lookup-equal pkx asg)
                       (ecurve::point-finite->x (first (third sig))))
                (equal (lookup-equal prx asg)
                       (ecurve::point-finite->x (second (third sig)))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-signature-to-fields-gadget) asg p)
                (equal (list (lookup-equal c asg)
                             (lookup-equal r asg)
                             (lookup-equal pkx asg)
                             (lookup-equal prx asg))
                       (signature-to-fields-funspec sig))))
  :hints (("Goal"
           :use (progx-signature-to-fields-sound)
           :in-theory (enable crv-signature-to-fields-gadget))))
