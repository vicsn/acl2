; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey Inject::new (circuit/account/src/compute_key/mod.rs) in
; variable mode: Group::new on pk_sig and on pr_sig (each enforce_in_group,
; group-enforce-in-group-gadget), then ComputeKey::from (key-ck-from.lisp:
; hash_to_scalar_psd4 of the two x-coordinates).
;
; key-ck-new-sound: over the wires, with no hypothesis on internal wires,
; the constraints force compute-key-new-funspec of the two input points to
; be the compute key (pk_sig, pr_sig, sk_prf) read from the wires.
; key-ck-new-complete: the snarkVM witness (cofactor witnesses of
; group-enforce-in-group-witness-lookupsp, then the Poseidon witness)
; satisfies all constraints.

(in-package "ALEOVM")

(include-book "key-ck-from")
(include-book "group-unconditional")
(include-book "literal-new-group-complete")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund key-ck-new-gadget (pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime))
       ((mv bits cs vs asg) (key-ck-from-gadget pk-x pr-x u vs asg)))
    (mv bits
        (append (group-enforce-in-group-gadget pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 p)
                (group-enforce-in-group-gadget pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 p)
                cs)
        vs asg)))

(defrule key-ck-new-sound
  (b* (((mv bits cs & &) (key-ck-new-gadget pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg))
       ((mv & hcs & &) (key-ck-from-gadget pk-x pr-x u vs asg))
       ((mv bs rs x &) (key-ck-from-wires pk-x pr-x vs asg))
       (pk (ecurve::point-finite (lookup-equal pk-x asgx) (lookup-equal pk-y asgx)))
       (pr (ecurve::point-finite (lookup-equal pr-x asgx) (lookup-equal pr-y asgx))))
    (implies (and (symbolp pk-x) (symbolp pk-y) (symbolp pk-qx) (symbolp pk-qy) (symbolp pk-cx2) (symbolp pk-cy2) (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2) (symbolp pk-x3) (symbolp pk-y3) (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
                  (symbolp pr-x) (symbolp pr-y) (symbolp pr-qx) (symbolp pr-qy) (symbolp pr-cx2) (symbolp pr-cy2) (symbolp pr-dxy) (symbolp pr-dx2) (symbolp pr-dy2) (symbolp pr-x3) (symbolp pr-y3) (symbolp pr-exy) (symbolp pr-ex2) (symbolp pr-ey2)
                  (r1cs::valuation-bindsp asgx pk-x)
                  (r1cs::valuation-bindsp asgx pk-y)
                  (r1cs::valuation-bindsp asgx pk-qx)
                  (r1cs::valuation-bindsp asgx pk-qy)
                  (r1cs::valuation-bindsp asgx pk-cx2)
                  (r1cs::valuation-bindsp asgx pk-cy2)
                  (r1cs::valuation-bindsp asgx pk-dxy)
                  (r1cs::valuation-bindsp asgx pk-dx2)
                  (r1cs::valuation-bindsp asgx pk-dy2)
                  (r1cs::valuation-bindsp asgx pk-x3)
                  (r1cs::valuation-bindsp asgx pk-y3)
                  (r1cs::valuation-bindsp asgx pk-exy)
                  (r1cs::valuation-bindsp asgx pk-ex2)
                  (r1cs::valuation-bindsp asgx pk-ey2)
                  (r1cs::valuation-bindsp asgx pr-x)
                  (r1cs::valuation-bindsp asgx pr-y)
                  (r1cs::valuation-bindsp asgx pr-qx)
                  (r1cs::valuation-bindsp asgx pr-qy)
                  (r1cs::valuation-bindsp asgx pr-cx2)
                  (r1cs::valuation-bindsp asgx pr-cy2)
                  (r1cs::valuation-bindsp asgx pr-dxy)
                  (r1cs::valuation-bindsp asgx pr-dx2)
                  (r1cs::valuation-bindsp asgx pr-dy2)
                  (r1cs::valuation-bindsp asgx pr-x3)
                  (r1cs::valuation-bindsp asgx pr-y3)
                  (r1cs::valuation-bindsp asgx pr-exy)
                  (r1cs::valuation-bindsp asgx pr-ex2)
                  (r1cs::valuation-bindsp asgx pr-ey2)
                  (r1cs::r1cs-constraints-holdp cs asgx (base-prime))
                  (let ((rate 4) (cs hcs)) (key-h2s-hyps)))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (compute-key-new-funspec pk pr)
                         (list pk pr (key-sk-of-wires bs asgx))))))
  :do-not-induct t
  :enable (key-ck-new-gadget compute-key-new-funspec group-new-funspec)
  :disable (key-ck-from-sound)
  :use ((:instance group-enforce-in-group-sound-unconditional
                   (x pk-x) (y pk-y) (qx pk-qx) (qy pk-qy) (cx2 pk-cx2) (cy2 pk-cy2) (dxy pk-dxy) (dx2 pk-dx2) (dy2 pk-dy2) (x3 pk-x3) (y3 pk-y3) (exy pk-exy) (ex2 pk-ex2) (ey2 pk-ey2) (asg asgx) (p (base-prime)))
        (:instance group-enforce-in-group-sound-unconditional
                   (x pr-x) (y pr-y) (qx pr-qx) (qy pr-qy) (cx2 pr-cx2) (cy2 pr-cy2) (dxy pr-dxy) (dx2 pr-dx2) (dy2 pr-dy2) (x3 pr-x3) (y3 pr-y3) (exy pr-exy) (ex2 pr-ex2) (ey2 pr-ey2) (asg asgx) (p (base-prime)))
        (:instance key-ck-from-sound (px pk-x) (rx pr-x) (py pk-y) (ry pr-y))))

(defruledl key-gnew-holds-after-ext
  (implies (and (symbolp x) (symbolp y) (symbolp qx) (symbolp qy) (symbolp cx2) (symbolp cy2) (symbolp dxy) (symbolp dx2) (symbolp dy2) (symbolp x3) (symbolp y3) (symbolp exy) (symbolp ex2) (symbolp ey2)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::r1cs-valuationp asg2 (base-prime))
                (hpos-ext-p asg asg2)
                (r1cs::valuation-bindsp asg x)
                  (r1cs::valuation-bindsp asg y)
                  (r1cs::valuation-bindsp asg qx)
                  (r1cs::valuation-bindsp asg qy)
                  (r1cs::valuation-bindsp asg cx2)
                  (r1cs::valuation-bindsp asg cy2)
                  (r1cs::valuation-bindsp asg dxy)
                  (r1cs::valuation-bindsp asg dx2)
                  (r1cs::valuation-bindsp asg dy2)
                  (r1cs::valuation-bindsp asg x3)
                  (r1cs::valuation-bindsp asg y3)
                  (r1cs::valuation-bindsp asg exy)
                  (r1cs::valuation-bindsp asg ex2)
                  (r1cs::valuation-bindsp asg ey2)
                (groupp pt)
                (group-enforce-in-group-witness-lookupsp
                 x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 pt asg (base-prime)))
           (r1cs::r1cs-constraints-holdp
            (group-enforce-in-group-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 (base-prime))
            asg2 (base-prime)))
  :do-not-induct t
  :use ((:instance group-enforce-in-group-equations-when-witness-lookupsp
                   (asg asg2) (p (base-prime)))
        (:instance group-enforce-in-group-gadget-to-equations
                   (asg asg2) (p (base-prime)))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                   (asg asg2) (p (base-prime))))
  :enable (group-enforce-in-group-witness-lookupsp r1cs::valuation-bindsp))

(defrule key-ck-new-complete
  (b* (((mv & cs & asg2) (key-ck-new-gadget pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg))
       (p (base-prime)))
    (implies (and (symbolp pk-x) (symbolp pk-y) (symbolp pk-qx) (symbolp pk-qy) (symbolp pk-cx2) (symbolp pk-cy2) (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2) (symbolp pk-x3) (symbolp pk-y3) (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
                  (symbolp pr-x) (symbolp pr-y) (symbolp pr-qx) (symbolp pr-qy) (symbolp pr-cx2) (symbolp pr-cy2) (symbolp pr-dxy) (symbolp pr-dx2) (symbolp pr-dy2) (symbolp pr-x3) (symbolp pr-y3) (symbolp pr-exy) (symbolp pr-ex2) (symbolp pr-ey2)
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-bindsp asg pk-x)
                  (r1cs::valuation-bindsp asg pk-y)
                  (r1cs::valuation-bindsp asg pk-qx)
                  (r1cs::valuation-bindsp asg pk-qy)
                  (r1cs::valuation-bindsp asg pk-cx2)
                  (r1cs::valuation-bindsp asg pk-cy2)
                  (r1cs::valuation-bindsp asg pk-dxy)
                  (r1cs::valuation-bindsp asg pk-dx2)
                  (r1cs::valuation-bindsp asg pk-dy2)
                  (r1cs::valuation-bindsp asg pk-x3)
                  (r1cs::valuation-bindsp asg pk-y3)
                  (r1cs::valuation-bindsp asg pk-exy)
                  (r1cs::valuation-bindsp asg pk-ex2)
                  (r1cs::valuation-bindsp asg pk-ey2)
                  (r1cs::valuation-bindsp asg pr-x)
                  (r1cs::valuation-bindsp asg pr-y)
                  (r1cs::valuation-bindsp asg pr-qx)
                  (r1cs::valuation-bindsp asg pr-qy)
                  (r1cs::valuation-bindsp asg pr-cx2)
                  (r1cs::valuation-bindsp asg pr-cy2)
                  (r1cs::valuation-bindsp asg pr-dxy)
                  (r1cs::valuation-bindsp asg pr-dx2)
                  (r1cs::valuation-bindsp asg pr-dy2)
                  (r1cs::valuation-bindsp asg pr-x3)
                  (r1cs::valuation-bindsp asg pr-y3)
                  (r1cs::valuation-bindsp asg pr-exy)
                  (r1cs::valuation-bindsp asg pr-ex2)
                  (r1cs::valuation-bindsp asg pr-ey2)
                  (groupp pk)
                  (groupp pr)
                  (group-enforce-in-group-witness-lookupsp pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pk asg p)
                  (group-enforce-in-group-witness-lookupsp pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 pr asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-h2s-bound 4 2) (len vs))
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p))))
  :do-not-induct t
  :enable key-ck-new-gadget
  :disable (key-ck-from-complete)
  :use ((:instance key-ck-from-complete (px pk-x) (rx pr-x))
        (:instance key-gnew-holds-after-ext (x pk-x) (y pk-y) (qx pk-qx) (qy pk-qy) (cx2 pk-cx2) (cy2 pk-cy2) (dxy pk-dxy) (dx2 pk-dx2) (dy2 pk-dy2) (x3 pk-x3) (y3 pk-y3) (exy pk-exy) (ex2 pk-ex2) (ey2 pk-ey2) (pt pk)
                   (asg2 (mv-nth 3 (key-ck-from-gadget pk-x pr-x u vs asg))))
        (:instance key-gnew-holds-after-ext (x pr-x) (y pr-y) (qx pr-qx) (qy pr-qy) (cx2 pr-cx2) (cy2 pr-cy2) (dxy pr-dxy) (dx2 pr-dx2) (dy2 pr-dy2) (x3 pr-x3) (y3 pr-y3) (exy pr-exy) (ex2 pr-ex2) (ey2 pr-ey2) (pt pr)
                   (asg2 (mv-nth 3 (key-ck-from-gadget pk-x pr-x u vs asg))))))
