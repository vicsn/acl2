; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey::from (circuit/account/src/compute_key/from.rs) on variable
; groups pk_sig = (px, py), pr_sig = (rx, ry):
;   sk_prf = Aleo::hash_to_scalar_psd4([pk_sig.to_x_coordinate(),
;                                       pr_sig.to_x_coordinate()])
; The x-coordinates are the linear combinations of the wires px and rx, so
; the constraints are exactly those of hpos-c-hash-to-scalar with rate 4 on
; (px, rx).  sk_prf is the Scalar of the first 250 bit wires.
;
; key-ck-from-sound: if the constraints hold, the compute key built from the
; wires is compute-key-from-funspec of the two points.  The points are
; Group circuit values, so they are on the curve (prior circuit: the Group
; values pk_sig, pr_sig).
; key-ck-from-complete: the snarkVM witness satisfies the constraints.

(in-package "ALEOVM")

(include-book "key-h2s")
(include-book "../fun-specs/curve-account")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(defund key-ck-from-gadget (px rx u vs asg)
  (declare (xargs :verify-guards nil))
  (hpos-c-hash-to-scalar 4 (list (hpos-lc-var px) (hpos-lc-var rx)) u vs asg))

(defund key-ck-from-wires (px rx vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv & & vs1 &)
        (hpos-c-poseidon-hash-many 4 (list (hpos-lc-var px) (hpos-lc-var rx)) 1 vs asg)))
    (hpos-h2s-wires vs1)))

(defund key-sk-of-wires (bs asg)
  (declare (xargs :verify-guards nil))
  (lebits=>nat (take 250 (lookup-equal-list bs asg))))

(defrulel key-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg v))
           (equal (mod (ifix (lookup-equal v asg)) (base-prime))
                  (lookup-equal v asg)))
  :use (:instance r1cs::fep-of-lookup-equal (var v) (valuation asg)
                  (prime (base-prime)))
  :enable pfield::fep)

(defrulel key-eval-of-two-vars
  (implies (and (symbolp px) (symbolp rx)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg px)
                (r1cs::valuation-bindsp asg rx))
           (equal (hpos-lc-eval-list (list (hpos-lc-var px) (hpos-lc-var rx))
                                     asg (base-prime))
                  (list (lookup-equal px asg) (lookup-equal rx asg))))
  :enable hpos-lc-eval-list)

(defrule key-ck-from-sound
  (b* (((mv bits cs & &) (key-ck-from-gadget px rx u vs asg))
       ((mv bs rs x &) (key-ck-from-wires px rx vs asg))
       (pk (ecurve::point-finite (lookup-equal px asgx) (lookup-equal py asgx)))
       (pr (ecurve::point-finite (lookup-equal rx asgx) (lookup-equal ry asgx))))
    (implies (and (symbolp px) (symbolp rx)
                  (r1cs::valuation-bindsp asgx px)
                  (r1cs::valuation-bindsp asgx rx)
                  (ecurve::edwards-bls12-pointp pk)
                  (ecurve::edwards-bls12-pointp pr)
                  (let ((rate 4)) (key-h2s-hyps)))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (list pk pr (key-sk-of-wires bs asgx))
                         (compute-key-from-funspec pk pr)))))
  :do-not-induct t
  :enable (key-ck-from-gadget key-ck-from-wires key-sk-of-wires
           compute-key-from-funspec)
  :disable (key-h2s-psd4-sound key-h2s-sound hpos-c-hash-to-scalar-sound)
  :use (:instance key-h2s-psd4-sound
                  (xs (list (hpos-lc-var px) (hpos-lc-var rx)))))

(defrule key-hpos-lc-boundp-of-var
  (implies (and (symbolp v) (r1cs::valuation-bindsp asg v))
           (hpos-lc-boundp (hpos-lc-var v) asg))
  :enable (hpos-lc-boundp-alt hpos-lc-var hpos-terms-boundp hpos-pv))

(defrule key-ck-from-complete
  (b* (((mv & cs & asg2) (key-ck-from-gadget px rx u vs asg))
       (p (base-prime)))
    (implies (and (symbolp px) (symbolp rx)
                  (r1cs::valuation-bindsp asg px)
                  (r1cs::valuation-bindsp asg rx)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-h2s-bound 4 2) (len vs))
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p))))
  :do-not-induct t
  :enable (key-ck-from-gadget hpos-lc-list-boundp hpos-aleo-rate-p)
  :disable hpos-c-hash-to-scalar-complete
  :use (:instance hpos-c-hash-to-scalar-complete
                  (rate 4) (xs (list (hpos-lc-var px) (hpos-lc-var rx)))))
