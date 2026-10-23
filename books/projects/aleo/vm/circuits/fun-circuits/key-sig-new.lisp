; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature Inject::new (circuit/account/src/signature/mod.rs) in variable
; mode: Scalar::new on the challenge and the response (with the range
; check, literal-scalar-new-gadget), then ComputeKey::new (key-ck-new.lisp),
; whose sk_prf is the Poseidon hash_to_scalar_psd4 circuit.  This is
; literal-signature-new-gadget plus the Poseidon constraints, so it
; discharges the hash hypothesis of literal-signature-new-sound: the sk_prf
; scalar read from the wires is values-hash-to-scalar-psd4 of the two
; x-coordinates (key-h2s-psd4-sound).

(in-package "ALEOVM")

(include-book "key-ck-new")
(include-book "hpos-ell2")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund key-sig-new-gadget (c cxs crs r rxs rrs pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime))
       ((mv bits cs vs asg) (key-ck-new-gadget pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg)))
    (mv bits
        (append (literal-scalar-new-gadget c cxs crs p)
                (literal-scalar-new-gadget r rxs rrs p)
                cs)
        vs asg)))

(defrule key-not-reserrp-of-cons-point-finite
  (not (reserrp (cons (ecurve::point-finite x y) rest)))
  :enable (reserrp ecurve::point-finite))

(defmacro key-sig-scalar-wire-hyps (a)
  `(and (symbolp c) (symbol-listp cxs) (symbol-listp crs)
        (symbolp r) (symbol-listp rxs) (symbol-listp rrs)
        (equal (len cxs) 251) (equal (len crs) 250)
        (equal (len rxs) 251) (equal (len rrs) 250)
        (r1cs::valuation-bindsp ,a c)
        (r1cs::valuation-binds-allp ,a cxs)
        (r1cs::valuation-binds-allp ,a crs)
        (r1cs::valuation-bindsp ,a r)
        (r1cs::valuation-binds-allp ,a rxs)
        (r1cs::valuation-binds-allp ,a rrs)))

(defrule key-sig-new-sound
  (b* (((mv bits cs & &) (key-sig-new-gadget c cxs crs r rxs rrs pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg))
       ((mv & hcs & &) (key-ck-from-gadget pk-x pr-x u vs asg))
       ((mv bs rs x &) (key-ck-from-wires pk-x pr-x vs asg))
       (c$ (lookup-equal c asgx))
       (r$ (lookup-equal r asgx))
       (pk (ecurve::point-finite (lookup-equal pk-x asgx) (lookup-equal pk-y asgx)))
       (pr (ecurve::point-finite (lookup-equal pr-x asgx) (lookup-equal pr-y asgx)))
       (sk (key-sk-of-wires bs asgx)))
    (implies (and (key-sig-scalar-wire-hyps asgx)
                  (symbolp pk-x) (symbolp pk-y) (symbolp pk-qx) (symbolp pk-qy) (symbolp pk-cx2) (symbolp pk-cy2) (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2) (symbolp pk-x3) (symbolp pk-y3) (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
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
                  (scalarp c$)
                  (scalarp r$)
                  (equal sk (values-hash-to-scalar-psd4
                             (list (lookup-equal pk-x asgx) (lookup-equal pr-x asgx))))
                  (equal (signature-new-funspec c$ r$ pk pr)
                         (list c$ r$ (list pk pr sk))))))
  :do-not-induct t
  :enable (key-sig-new-gadget signature-new-funspec key-ck-new-gadget
           key-sk-of-wires key-ck-from-wires key-ck-from-gadget)
  :disable (key-ck-new-sound key-h2s-psd4-sound key-h2s-sound
            hpos-c-hash-to-scalar-sound)
  :use ((:instance literal-scalar-new-sound (s c) (xs cxs) (rs crs)
                   (asg asgx) (p (base-prime)))
        (:instance literal-scalar-new-sound (s r) (xs rxs) (rs rrs)
                   (asg asgx) (p (base-prime)))
        (:instance key-ck-new-sound)
        (:instance key-h2s-psd4-sound
                   (xs (list (hpos-lc-var pk-x) (hpos-lc-var pr-x))))
        (:instance key-eval-of-two-vars-for-sig (px pk-x) (rx pr-x) (asg asgx)))
  :prep-lemmas
  ((defrule key-eval-of-two-vars-for-sig
     (implies (and (symbolp px) (symbolp rx)
                   (r1cs::r1cs-valuationp asg (base-prime))
                   (r1cs::valuation-bindsp asg px)
                   (r1cs::valuation-bindsp asg rx))
              (equal (hpos-lc-eval-list (list (hpos-lc-var px) (hpos-lc-var rx))
                                        asg (base-prime))
                     (list (lookup-equal px asg) (lookup-equal rx asg))))
     :enable hpos-lc-eval-list
     :use ((:instance r1cs::fep-of-lookup-equal (var px) (valuation asg)
                      (prime (base-prime)))
           (:instance r1cs::fep-of-lookup-equal (var rx) (valuation asg)
                      (prime (base-prime))))
     :disable r1cs::fep-of-lookup-equal)))

(defmacro key-sig-scalar-witness-hyps (a)
  `(and (scalarp (lookup-equal c ,a))
        (equal (lookup-equal-list cxs ,a) (scalar-bits-le (lookup-equal c ,a)))
        (equal (lookup-equal-list crs ,a)
               (crv-bits-lte-const-witness (lookup-equal-list cxs ,a)
                                           (scalar-modulus-minus-one-bits)))
        (scalarp (lookup-equal r ,a))
        (equal (lookup-equal-list rxs ,a) (scalar-bits-le (lookup-equal r ,a)))
        (equal (lookup-equal-list rrs ,a)
               (crv-bits-lte-const-witness (lookup-equal-list rxs ,a)
                                           (scalar-modulus-minus-one-bits)))))

(defrule key-sig-new-complete
  (b* (((mv & cs & asg2) (key-sig-new-gadget c cxs crs r rxs rrs pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg))
       (p (base-prime)))
    (implies (and (key-sig-scalar-wire-hyps asg)
                  (key-sig-scalar-witness-hyps asg)
                  (symbolp pk-x) (symbolp pk-y) (symbolp pk-qx) (symbolp pk-qy) (symbolp pk-cx2) (symbolp pk-cy2) (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2) (symbolp pk-x3) (symbolp pk-y3) (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
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
  :in-theory '(key-sig-new-gadget literal-scalar-new-gadget
               r1cs::r1cs-constraints-holdp-of-append
               (:definition mv-nth) car-cons cdr-cons (:e zp) (:e base-prime))
  :use ((:instance key-ck-new-complete)
        (:instance key-sig-scalar-holds-after-ext
                   (asg2 (mv-nth 3 (key-ck-new-gadget pk-x pk-y pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 pr-x pr-y pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 u vs asg)))))
  :prep-lemmas
  ((defruled key-sig-scalar-holds-after-ext
     (implies (and (key-sig-scalar-wire-hyps asg)
                   (key-sig-scalar-witness-hyps asg)
                   (r1cs::r1cs-valuationp asg (base-prime))
                   (r1cs::r1cs-valuationp asg2 (base-prime))
                   (hpos-ext-p asg asg2))
              (and (r1cs::r1cs-constraints-holdp
                    (scalar-new-gadget c cxs crs (base-prime)) asg2 (base-prime))
                   (r1cs::r1cs-constraints-holdp
                    (scalar-new-gadget r rxs rrs (base-prime)) asg2 (base-prime))))
     :do-not-induct t
     :use ((:instance scalar-new-gadget-complete (s c) (xs cxs) (rs crs)
                      (asg asg2) (p (base-prime)))
           (:instance scalar-new-gadget-complete (s r) (xs rxs) (rs rrs)
                      (asg asg2) (p (base-prime)))
           (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                      (asg asg2) (p (base-prime))))
     :in-theory '(hpos-lookup-equal-list-when-ext-p
                  hpos-valuation-binds-allp-when-ext-p
                  hpos-valuation-bindsp-when-ext-p
                  hpos-lookup-when-ext-p hpos-ext-p-member-strip-cars
                  r1cs::valuation-bindsp))))
