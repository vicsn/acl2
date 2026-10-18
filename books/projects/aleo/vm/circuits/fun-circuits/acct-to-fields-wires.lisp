; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey::to_fields and Signature::to_fields soundness stated over the
; wires.  Both circuits emit no constraint: the output field wires are the
; x-coordinate wires of pk_sig and pr_sig (and, for a signature, the challenge
; and response wires before them).

(in-package "ALEOVM")

(include-book "crv-project")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acct-compute-key-to-fields-wires-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-to-fields-gadget) asg p)
                (curve-compute-keyp ck)
                (equal (lookup-equal pkx asg)
                       (ecurve::point-finite->x (first ck)))
                (equal (lookup-equal prx asg)
                       (ecurve::point-finite->x (second ck))))
           (equal (list (lookup-equal pkx asg)
                        (lookup-equal prx asg))
                  (compute-key-to-fields-funspec ck)))
  :hints (("Goal" :use crv-compute-key-to-fields-gadget-sound)))

(defruled acct-signature-to-fields-wires-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-to-fields-gadget) asg p)
                (curve-signaturep sig)
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
           :use (crv-signature-to-fields-gadget-sound
                 (:instance acct-compute-key-to-fields-wires-sound
                            (ck (third sig))))
           :in-theory (e/d (curve-signaturep scalarp)
                           (crv-compute-key-to-fields-gadget)))))
