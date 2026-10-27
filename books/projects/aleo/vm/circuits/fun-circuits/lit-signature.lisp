;AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; account ComputeKey / Signature: is_equal / is_not_equal completeness,
; write_bits_le / write_bits_be (gadgets, soundness, completeness), and
; ternary soundness over the wires and completeness.  All of these are
; hash-free in snarkVM (Scalar and Group gadgets only).  Soundness of
; is_equal / is_not_equal is in acct-equal-sound.lisp.

(in-package "ALEOVM")

(include-book "acct-equal-sound")
(include-book "crv-ternary")
(include-book "crv-bits")
(include-book "scalar-write-bits-r1cs")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lit-neq-r (a b)
  (declare (xargs :guard t))
  (if (equal a b) 0 1))

(defund lit-neq-m (a b p)
  (declare (xargs :verify-guards nil))
  (if (equal a b) 0 (pfield::inv (pfield::sub a b p) p)))

(defruled lit-ck-out-arith
  (implies (equal p (base-prime))
           (equal (pfield::mul (bitand (group-is-equal-funspec a b)
                                       (group-is-equal-funspec c d))
                               (pfield::sub 1 (lit-neq-r u v) p)
                               p)
                  (if (and (equal a b) (equal c d) (equal u v)) 1 0)))
  :enable (bitand group-is-equal-funspec lit-neq-r))

(defruled lit-ck-funspec-components
  (implies (and (curve-compute-keyp ck1)
                (curve-compute-keyp ck2))
           (equal (compute-key-is-equal-funspec ck1 ck2)
                  (if (and (equal (first ck1) (first ck2))
                           (equal (second ck1) (second ck2))
                           (equal (third ck1) (third ck2)))
                      1 0)))
  :enable (compute-key-is-equal-funspec crv-compute-key-equal-iff-components))

(defruled lit-group-is-equal-complete
  (implies (and (symbolp x1) (symbolp y1) (symbolp x2) (symbolp y2)
                (symbolp mx) (symbolp rx) (symbolp my) (symbolp ry)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x1)
                (r1cs::valuation-bindsp asg y1)
                (r1cs::valuation-bindsp asg x2)
                (r1cs::valuation-bindsp asg y2)
                (r1cs::valuation-bindsp asg mx)
                (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg my)
                (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg out)
                (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (lookup-equal x1 asg) (ecurve::point-finite->x p1))
                (equal (lookup-equal y1 asg) (ecurve::point-finite->y p1))
                (equal (lookup-equal x2 asg) (ecurve::point-finite->x p2))
                (equal (lookup-equal y2 asg) (ecurve::point-finite->y p2))
                (equal (lookup-equal rx asg)
                       (lit-neq-r (lookup-equal x1 asg) (lookup-equal x2 asg)))
                (equal (lookup-equal mx asg)
                       (lit-neq-m (lookup-equal x1 asg) (lookup-equal x2 asg) p))
                (equal (lookup-equal ry asg)
                       (lit-neq-r (lookup-equal y1 asg) (lookup-equal y2 asg)))
                (equal (lookup-equal my asg)
                       (lit-neq-m (lookup-equal y1 asg) (lookup-equal y2 asg) p))
                (equal (lookup-equal out asg)
                       (group-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
            asg p))
  :hints (("Goal" :use crv-group-is-equal-gadget-complete
           :in-theory '(lit-neq-r lit-neq-m))))

(defruled lit-scalar-is-equal-complete
  (implies (and (symbolp a) (symbolp b) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (scalarp (lookup-equal a asg))
                (scalarp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (lit-neq-r (lookup-equal a asg) (lookup-equal b asg)))
                (equal (lookup-equal m asg)
                       (lit-neq-m (lookup-equal a asg) (lookup-equal b asg) p)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-scalar-is-equal-gadget a b m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (scalar-is-equal-funspec (lookup-equal a asg)
                                                (lookup-equal b asg)))))
  :hints (("Goal" :use crv-scalar-is-equal-gadget-complete
           :in-theory '(lit-neq-r lit-neq-m))))

(defruled lit-compute-key-is-equal-complete
  (implies (and
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pkmx)
                (symbolp pkrx)
                (symbolp pkmy)
                (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp prmx)
                (symbolp prrx)
                (symbolp prmy)
                (symbolp prry)
                (symbolp prout)
                (symbolp s1)
                (symbolp s2)
                (symbolp sm)
                (symbolp sr)
                (symbolp t1)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pkmx)
                (r1cs::valuation-bindsp asg pkrx)
                (r1cs::valuation-bindsp asg pkmy)
                (r1cs::valuation-bindsp asg pkry)
                (r1cs::valuation-bindsp asg pkout)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg prmx)
                (r1cs::valuation-bindsp asg prrx)
                (r1cs::valuation-bindsp asg prmy)
                (r1cs::valuation-bindsp asg prry)
                (r1cs::valuation-bindsp asg prout)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg sm)
                (r1cs::valuation-bindsp asg sr)
                (r1cs::valuation-bindsp asg t1)
                (r1cs::valuation-bindsp asg out)
                (curve-compute-keyp ck1)
                (curve-compute-keyp ck2)
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal s2 asg) (third ck2))
                (equal (lookup-equal pkrx asg) (lit-neq-r (lookup-equal pk1x asg) (lookup-equal pk2x asg)))
                (equal (lookup-equal pkmx asg) (lit-neq-m (lookup-equal pk1x asg) (lookup-equal pk2x asg) p))
                (equal (lookup-equal pkry asg) (lit-neq-r (lookup-equal pk1y asg) (lookup-equal pk2y asg)))
                (equal (lookup-equal pkmy asg) (lit-neq-m (lookup-equal pk1y asg) (lookup-equal pk2y asg) p))
                (equal (lookup-equal pkout asg) (group-is-equal-funspec (first ck1) (first ck2)))
                (equal (lookup-equal prrx asg) (lit-neq-r (lookup-equal pr1x asg) (lookup-equal pr2x asg)))
                (equal (lookup-equal prmx asg) (lit-neq-m (lookup-equal pr1x asg) (lookup-equal pr2x asg) p))
                (equal (lookup-equal prry asg) (lit-neq-r (lookup-equal pr1y asg) (lookup-equal pr2y asg)))
                (equal (lookup-equal prmy asg) (lit-neq-m (lookup-equal pr1y asg) (lookup-equal pr2y asg) p))
                (equal (lookup-equal prout asg) (group-is-equal-funspec (second ck1) (second ck2)))
                (equal (lookup-equal sr asg) (lit-neq-r (lookup-equal s1 asg) (lookup-equal s2 asg)))
                (equal (lookup-equal sm asg) (lit-neq-m (lookup-equal s1 asg) (lookup-equal s2 asg) p))
                (equal (lookup-equal t1 asg)
                       (bitand (group-is-equal-funspec (first ck1) (first ck2))
                               (group-is-equal-funspec (second ck1) (second ck2))))
                (equal (lookup-equal out asg)
                       (compute-key-is-equal-funspec ck1 ck2)))
           (r1cs::r1cs-constraints-holdp
            (crv-compute-key-is-equal-gadget
             pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr t1 out p)
            asg p))
  :hints (("Goal"
           :in-theory '(crv-compute-key-is-equal-gadget
                         r1cs::r1cs-constraints-holdp-of-append
                         curve-compute-keyp-forward
                         bitp-of-group-is-equal-funspec
                         primep-of-base-prime)
           :use ((:instance lit-group-is-equal-complete
                            (x1 pk1x) (y1 pk1y) (x2 pk2x) (y2 pk2y)
                            (mx pkmx) (rx pkrx) (my pkmy) (ry pkry) (out pkout)
                            (p1 (first ck1)) (p2 (first ck2)))
                 (:instance lit-group-is-equal-complete
                            (x1 pr1x) (y1 pr1y) (x2 pr2x) (y2 pr2y)
                            (mx prmx) (rx prrx) (my prmy) (ry prry) (out prout)
                            (p1 (second ck1)) (p2 (second ck2)))
                 (:instance lit-scalar-is-equal-complete
                            (a s1) (b s2) (m sm) (r sr))
                 (:instance boolean-and-gadget-to-bitand
                            (x pkout) (y prout) (z t1))
                 (:instance crv-and-var-not-gadget-to-mul
                            (x t1) (r sr))
                 (:instance lit-ck-out-arith
                            (a (first ck1)) (b (first ck2))
                            (c (second ck1)) (d (second ck2))
                            (u (third ck1)) (v (third ck2)))
                 (:instance lit-ck-funspec-components)))))

(define lit-eq2 (a b c d)
  :returns (bit bitp)
  (if (and (equal a b) (equal c d)) 1 0))

(defruled lit-ts-arith
  (implies (equal p (base-prime))
           (equal (pfield::mul (pfield::sub 1 (lit-neq-r a b) p)
                               (pfield::sub 1 (lit-neq-r c d) p)
                               p)
                  (lit-eq2 a b c d)))
  :enable (lit-neq-r lit-eq2))

(defruled lit-sig-funspec-components
  (implies (and (curve-signaturep sig1)
                (curve-signaturep sig2))
           (equal (signature-is-equal-funspec sig1 sig2)
                  (bitand (lit-eq2 (first sig1) (first sig2)
                                   (second sig1) (second sig2))
                          (compute-key-is-equal-funspec (third sig1)
                                                        (third sig2)))))
  :enable (signature-is-equal-funspec compute-key-is-equal-funspec
           crv-signature-equal-iff-components lit-eq2 bitand))

(defruled lit-sig-not-equal-arith
  (implies (equal p (base-prime))
           (equal (pfield::sub 1 (signature-is-equal-funspec sig1 sig2) p)
                  (signature-is-not-equal-funspec sig1 sig2)))
  :enable (signature-is-equal-funspec signature-is-not-equal-funspec))

(defruled lit-ck-not-equal-arith
  (implies (equal p (base-prime))
           (equal (pfield::sub 1 (compute-key-is-equal-funspec ck1 ck2) p)
                  (compute-key-is-not-equal-funspec ck1 ck2)))
  :enable (compute-key-is-equal-funspec compute-key-is-not-equal-funspec))

(defruled lit-compute-key-is-not-equal-complete
  (implies (and
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pkmx)
                (symbolp pkrx)
                (symbolp pkmy)
                (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp prmx)
                (symbolp prrx)
                (symbolp prmy)
                (symbolp prry)
                (symbolp prout)
                (symbolp s1)
                (symbolp s2)
                (symbolp sm)
                (symbolp sr)
                (symbolp t1)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pkmx)
                (r1cs::valuation-bindsp asg pkrx)
                (r1cs::valuation-bindsp asg pkmy)
                (r1cs::valuation-bindsp asg pkry)
                (r1cs::valuation-bindsp asg pkout)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg prmx)
                (r1cs::valuation-bindsp asg prrx)
                (r1cs::valuation-bindsp asg prmy)
                (r1cs::valuation-bindsp asg prry)
                (r1cs::valuation-bindsp asg prout)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg sm)
                (r1cs::valuation-bindsp asg sr)
                (r1cs::valuation-bindsp asg t1)
                (r1cs::valuation-bindsp asg out)
                (curve-compute-keyp ck1)
                (curve-compute-keyp ck2)
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal s2 asg) (third ck2))
                (equal (lookup-equal pkrx asg) (lit-neq-r (lookup-equal pk1x asg) (lookup-equal pk2x asg)))
                (equal (lookup-equal pkmx asg) (lit-neq-m (lookup-equal pk1x asg) (lookup-equal pk2x asg) p))
                (equal (lookup-equal pkry asg) (lit-neq-r (lookup-equal pk1y asg) (lookup-equal pk2y asg)))
                (equal (lookup-equal pkmy asg) (lit-neq-m (lookup-equal pk1y asg) (lookup-equal pk2y asg) p))
                (equal (lookup-equal pkout asg) (group-is-equal-funspec (first ck1) (first ck2)))
                (equal (lookup-equal prrx asg) (lit-neq-r (lookup-equal pr1x asg) (lookup-equal pr2x asg)))
                (equal (lookup-equal prmx asg) (lit-neq-m (lookup-equal pr1x asg) (lookup-equal pr2x asg) p))
                (equal (lookup-equal prry asg) (lit-neq-r (lookup-equal pr1y asg) (lookup-equal pr2y asg)))
                (equal (lookup-equal prmy asg) (lit-neq-m (lookup-equal pr1y asg) (lookup-equal pr2y asg) p))
                (equal (lookup-equal prout asg) (group-is-equal-funspec (second ck1) (second ck2)))
                (equal (lookup-equal sr asg) (lit-neq-r (lookup-equal s1 asg) (lookup-equal s2 asg)))
                (equal (lookup-equal sm asg) (lit-neq-m (lookup-equal s1 asg) (lookup-equal s2 asg) p))
                (equal (lookup-equal t1 asg)
                       (bitand (group-is-equal-funspec (first ck1) (first ck2))
                               (group-is-equal-funspec (second ck1) (second ck2))))
                (equal (lookup-equal out asg)
                       (compute-key-is-equal-funspec ck1 ck2)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-is-not-equal-gadget
                  pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr t1 out p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal out asg) p)
                       (compute-key-is-not-equal-funspec ck1 ck2))))
  :hints (("Goal"
           :use lit-compute-key-is-equal-complete
           :in-theory '(crv-compute-key-is-not-equal-gadget
                        lit-ck-not-equal-arith))))

(defruled lit-signature-is-equal-complete
  (implies (and
                (symbolp c1)
                (symbolp c2)
                (symbolp cm)
                (symbolp cr)
                (symbolp r1)
                (symbolp r2)
                (symbolp rm)
                (symbolp rr)
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pkmx)
                (symbolp pkrx)
                (symbolp pkmy)
                (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp prmx)
                (symbolp prrx)
                (symbolp prmy)
                (symbolp prry)
                (symbolp prout)
                (symbolp s1)
                (symbolp s2)
                (symbolp sm)
                (symbolp sr)
                (symbolp tck)
                (symbolp ckout)
                (symbolp ts)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg cm)
                (r1cs::valuation-bindsp asg cr)
                (r1cs::valuation-bindsp asg r1)
                (r1cs::valuation-bindsp asg r2)
                (r1cs::valuation-bindsp asg rm)
                (r1cs::valuation-bindsp asg rr)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pkmx)
                (r1cs::valuation-bindsp asg pkrx)
                (r1cs::valuation-bindsp asg pkmy)
                (r1cs::valuation-bindsp asg pkry)
                (r1cs::valuation-bindsp asg pkout)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg prmx)
                (r1cs::valuation-bindsp asg prrx)
                (r1cs::valuation-bindsp asg prmy)
                (r1cs::valuation-bindsp asg prry)
                (r1cs::valuation-bindsp asg prout)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg sm)
                (r1cs::valuation-bindsp asg sr)
                (r1cs::valuation-bindsp asg tck)
                (r1cs::valuation-bindsp asg ckout)
                (r1cs::valuation-bindsp asg ts)
                (r1cs::valuation-bindsp asg out)
                (curve-signaturep sig1)
                (curve-signaturep sig2)
                (equal (lookup-equal c1 asg) (first sig1))
                (equal (lookup-equal c2 asg) (first sig2))
                (equal (lookup-equal r1 asg) (second sig1))
                (equal (lookup-equal r2 asg) (second sig2))
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (equal (lookup-equal cr asg) (lit-neq-r (lookup-equal c1 asg) (lookup-equal c2 asg)))
                (equal (lookup-equal cm asg) (lit-neq-m (lookup-equal c1 asg) (lookup-equal c2 asg) p))
                (equal (lookup-equal rr asg) (lit-neq-r (lookup-equal r1 asg) (lookup-equal r2 asg)))
                (equal (lookup-equal rm asg) (lit-neq-m (lookup-equal r1 asg) (lookup-equal r2 asg) p))
                (equal (lookup-equal pkrx asg) (lit-neq-r (lookup-equal pk1x asg) (lookup-equal pk2x asg)))
                (equal (lookup-equal pkmx asg) (lit-neq-m (lookup-equal pk1x asg) (lookup-equal pk2x asg) p))
                (equal (lookup-equal pkry asg) (lit-neq-r (lookup-equal pk1y asg) (lookup-equal pk2y asg)))
                (equal (lookup-equal pkmy asg) (lit-neq-m (lookup-equal pk1y asg) (lookup-equal pk2y asg) p))
                (equal (lookup-equal pkout asg) (group-is-equal-funspec (first (third sig1)) (first (third sig2))))
                (equal (lookup-equal prrx asg) (lit-neq-r (lookup-equal pr1x asg) (lookup-equal pr2x asg)))
                (equal (lookup-equal prmx asg) (lit-neq-m (lookup-equal pr1x asg) (lookup-equal pr2x asg) p))
                (equal (lookup-equal prry asg) (lit-neq-r (lookup-equal pr1y asg) (lookup-equal pr2y asg)))
                (equal (lookup-equal prmy asg) (lit-neq-m (lookup-equal pr1y asg) (lookup-equal pr2y asg) p))
                (equal (lookup-equal prout asg) (group-is-equal-funspec (second (third sig1)) (second (third sig2))))
                (equal (lookup-equal sr asg) (lit-neq-r (lookup-equal s1 asg) (lookup-equal s2 asg)))
                (equal (lookup-equal sm asg) (lit-neq-m (lookup-equal s1 asg) (lookup-equal s2 asg) p))
                (equal (lookup-equal tck asg)
                       (bitand (group-is-equal-funspec (first (third sig1)) (first (third sig2)))
                               (group-is-equal-funspec (second (third sig1)) (second (third sig2)))))
                (equal (lookup-equal ckout asg) (compute-key-is-equal-funspec (third sig1) (third sig2)))
                (equal (lookup-equal ts asg)
                       (lit-eq2 (first sig1) (first sig2) (second sig1) (second sig2)))
                (equal (lookup-equal out asg) (signature-is-equal-funspec sig1 sig2)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr tck ckout ts out p)
                 asg p)))
  :hints (("Goal"
           :in-theory '(crv-signature-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        curve-signaturep-forward
                        curve-compute-keyp-forward
                        bitp-of-compute-key-is-equal-funspec
                        bitp-of-lit-eq2
                        primep-of-base-prime)
           :use ((:instance lit-scalar-is-equal-complete
                            (a c1) (b c2) (m cm) (r cr))
                 (:instance lit-scalar-is-equal-complete
                            (a r1) (b r2) (m rm) (r rr))
                 (:instance lit-compute-key-is-equal-complete
                            (ck1 (third sig1)) (ck2 (third sig2)) (t1 tck) (out ckout))
                 (:instance crv-and-not-gadget-to-mul
                            (rx cr) (ry rr) (out ts))
                 (:instance boolean-and-gadget-to-bitand
                            (x ts) (y ckout) (z out))
                 (:instance lit-ts-arith
                            (a (first sig1)) (b (first sig2))
                            (c (second sig1)) (d (second sig2)))
                 (:instance lit-sig-funspec-components)))))

(defruled lit-signature-is-not-equal-complete
  (implies (and
                (symbolp c1)
                (symbolp c2)
                (symbolp cm)
                (symbolp cr)
                (symbolp r1)
                (symbolp r2)
                (symbolp rm)
                (symbolp rr)
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pkmx)
                (symbolp pkrx)
                (symbolp pkmy)
                (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp prmx)
                (symbolp prrx)
                (symbolp prmy)
                (symbolp prry)
                (symbolp prout)
                (symbolp s1)
                (symbolp s2)
                (symbolp sm)
                (symbolp sr)
                (symbolp tck)
                (symbolp ckout)
                (symbolp ts)
                (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg cm)
                (r1cs::valuation-bindsp asg cr)
                (r1cs::valuation-bindsp asg r1)
                (r1cs::valuation-bindsp asg r2)
                (r1cs::valuation-bindsp asg rm)
                (r1cs::valuation-bindsp asg rr)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pkmx)
                (r1cs::valuation-bindsp asg pkrx)
                (r1cs::valuation-bindsp asg pkmy)
                (r1cs::valuation-bindsp asg pkry)
                (r1cs::valuation-bindsp asg pkout)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg prmx)
                (r1cs::valuation-bindsp asg prrx)
                (r1cs::valuation-bindsp asg prmy)
                (r1cs::valuation-bindsp asg prry)
                (r1cs::valuation-bindsp asg prout)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg sm)
                (r1cs::valuation-bindsp asg sr)
                (r1cs::valuation-bindsp asg tck)
                (r1cs::valuation-bindsp asg ckout)
                (r1cs::valuation-bindsp asg ts)
                (r1cs::valuation-bindsp asg out)
                (curve-signaturep sig1)
                (curve-signaturep sig2)
                (equal (lookup-equal c1 asg) (first sig1))
                (equal (lookup-equal c2 asg) (first sig2))
                (equal (lookup-equal r1 asg) (second sig1))
                (equal (lookup-equal r2 asg) (second sig2))
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (equal (lookup-equal cr asg) (lit-neq-r (lookup-equal c1 asg) (lookup-equal c2 asg)))
                (equal (lookup-equal cm asg) (lit-neq-m (lookup-equal c1 asg) (lookup-equal c2 asg) p))
                (equal (lookup-equal rr asg) (lit-neq-r (lookup-equal r1 asg) (lookup-equal r2 asg)))
                (equal (lookup-equal rm asg) (lit-neq-m (lookup-equal r1 asg) (lookup-equal r2 asg) p))
                (equal (lookup-equal pkrx asg) (lit-neq-r (lookup-equal pk1x asg) (lookup-equal pk2x asg)))
                (equal (lookup-equal pkmx asg) (lit-neq-m (lookup-equal pk1x asg) (lookup-equal pk2x asg) p))
                (equal (lookup-equal pkry asg) (lit-neq-r (lookup-equal pk1y asg) (lookup-equal pk2y asg)))
                (equal (lookup-equal pkmy asg) (lit-neq-m (lookup-equal pk1y asg) (lookup-equal pk2y asg) p))
                (equal (lookup-equal pkout asg) (group-is-equal-funspec (first (third sig1)) (first (third sig2))))
                (equal (lookup-equal prrx asg) (lit-neq-r (lookup-equal pr1x asg) (lookup-equal pr2x asg)))
                (equal (lookup-equal prmx asg) (lit-neq-m (lookup-equal pr1x asg) (lookup-equal pr2x asg) p))
                (equal (lookup-equal prry asg) (lit-neq-r (lookup-equal pr1y asg) (lookup-equal pr2y asg)))
                (equal (lookup-equal prmy asg) (lit-neq-m (lookup-equal pr1y asg) (lookup-equal pr2y asg) p))
                (equal (lookup-equal prout asg) (group-is-equal-funspec (second (third sig1)) (second (third sig2))))
                (equal (lookup-equal sr asg) (lit-neq-r (lookup-equal s1 asg) (lookup-equal s2 asg)))
                (equal (lookup-equal sm asg) (lit-neq-m (lookup-equal s1 asg) (lookup-equal s2 asg) p))
                (equal (lookup-equal tck asg)
                       (bitand (group-is-equal-funspec (first (third sig1)) (first (third sig2)))
                               (group-is-equal-funspec (second (third sig1)) (second (third sig2)))))
                (equal (lookup-equal ckout asg) (compute-key-is-equal-funspec (third sig1) (third sig2)))
                (equal (lookup-equal ts asg)
                       (lit-eq2 (first sig1) (first sig2) (second sig1) (second sig2)))
                (equal (lookup-equal out asg) (signature-is-equal-funspec sig1 sig2)))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-not-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr tck ckout ts out p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal out asg) p)
                       (signature-is-not-equal-funspec sig1 sig2))))
  :hints (("Goal"
           :use lit-signature-is-equal-complete
           :in-theory '(crv-signature-is-not-equal-gadget
                        lit-sig-not-equal-arith))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature::write_bits_le / write_bits_be: Scalar::write_bits of the
; challenge and of the response, then Group::write_bits of pk_sig and pr_sig.
; The big-endian circuit has the same constraints; each component's bits are
; reversed.

(defruled lit-append-of-nil
  (equal (append nil x) x))

(defruled lit-base-prime-oddp
  (oddp (base-prime))
  :in-theory '((:e base-prime) (:e oddp) (:e ecurve::edwards-bls12-q)))

(defruled lit-scalar-bits-le-is-curve
  (implies (scalarp s)
           (equal (scalar-bits-le s) (curve-scalar-to-bits-le s)))
  :enable (scalar-bits-le curve-scalar-to-bits-le scalarp
           pfield::fep pfield::fep-fix-when-fep))

(defruled lit-scalar-bits-be-is-curve
  (implies (scalarp s)
           (equal (rev (scalar-bits-le s)) (curve-scalar-to-bits-be s)))
  :enable (lit-scalar-bits-le-is-curve
           curve-scalar-to-bits-le curve-scalar-to-bits-be
           acl2::nat=>bebits acl2::nat=>bendian acl2::nat=>lebits)
  :disable (acl2::nat=>lendian
            (:e acl2::nat=>lendian)
            (:e acl2::nat=>lebits)
            (:e acl2::nat=>bebits)
            (:e acl2::nat=>bendian)))

(defruled lit-rev-curve-scalar-bits-le
  (implies (scalarp s)
           (equal (rev (curve-scalar-to-bits-le s))
                  (curve-scalar-to-bits-be s)))
  :hints (("Goal" :use (lit-scalar-bits-be-is-curve lit-scalar-bits-le-is-curve))))

(define lit-signature-write-bits-le-gadget
  ((c symbolp) (cxs symbol-listp) (crs symbol-listp)
   (r symbolp) (rxs symbol-listp) (rrs symbol-listp)
   (pkx symbolp) (pkxs symbol-listp) (pkrs symbol-listp)
   (prx symbolp) (prxs symbol-listp) (prrs symbol-listp)
   (u symbolp)
   (p primep))
  :guard (and (oddp p)
              (equal (len cxs) 251) (equal (len crs) 250)
              (equal (len rxs) 251) (equal (len rrs) 250)
              (equal (len pkxs) (integer-length p))
              (equal (len pkrs) (bits-lt-prime-rlen p))
              (equal (len prxs) (integer-length p))
              (equal (len prrs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Signature::write_bits_le') and
          @('Signature::write_bits_be') (the same constraints)."
  (append (scalar-write-bits-le-gadget c cxs crs p)
          (scalar-write-bits-le-gadget r rxs rrs p)
          (crv-group-write-bits-le-gadget pkx pkxs pkrs u p)
          (crv-group-write-bits-le-gadget prx prxs prrs u p)))

(defmacro lit-sig-bits-common-hyps ()
  '(and (symbolp c) (symbol-listp cxs) (symbol-listp crs)
        (symbolp r) (symbol-listp rxs) (symbol-listp rrs)
        (symbolp pkx) (symbol-listp pkxs) (symbol-listp pkrs)
        (symbolp prx) (symbol-listp prxs) (symbol-listp prrs)
        (symbolp u)
        (equal (len cxs) 251) (equal (len crs) 250)
        (equal (len rxs) 251) (equal (len rrs) 250)
        (equal (len pkxs) 253) (equal (len pkrs) (bits-lt-prime-rlen p))
        (equal (len prxs) 253) (equal (len prrs) (bits-lt-prime-rlen p))
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg c)
        (r1cs::valuation-binds-allp asg cxs)
        (r1cs::valuation-binds-allp asg crs)
        (r1cs::valuation-bindsp asg r)
        (r1cs::valuation-binds-allp asg rxs)
        (r1cs::valuation-binds-allp asg rrs)
        (r1cs::valuation-bindsp asg pkx)
        (r1cs::valuation-binds-allp asg pkxs)
        (r1cs::valuation-binds-allp asg pkrs)
        (r1cs::valuation-bindsp asg prx)
        (r1cs::valuation-binds-allp asg prxs)
        (r1cs::valuation-binds-allp asg prrs)
        (r1cs::valuation-bindsp asg u)
        (curve-signaturep sig)
        (equal (lookup-equal c asg) (first sig))
        (equal (lookup-equal r asg) (second sig))
        (equal (lookup-equal pkx asg)
               (ecurve::point-finite->x (first (third sig))))
        (equal (lookup-equal prx asg)
               (ecurve::point-finite->x (second (third sig))))
        (equal (lookup-equal u asg) 1)))

(defruled lit-signature-write-bits-le-sound
  (implies (and (lit-sig-bits-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (lit-signature-write-bits-le-gadget
                  c cxs crs r rxs rrs pkx pkxs pkrs prx prxs prrs u p)
                 asg p))
           (equal (append (lookup-equal-list cxs asg)
                          (lookup-equal-list rxs asg)
                          (lookup-equal-list pkxs asg)
                          (lookup-equal-list prxs asg))
                  (signature-write-bits-le-funspec sig)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(lit-signature-write-bits-le-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        signature-write-bits-le-funspec
                        compute-key-write-bits-le-funspec
                        curve-signaturep-forward
                        curve-compute-keyp-forward
                        lit-scalar-bits-le-is-curve
                        lit-base-prime-oddp
                        crv-base-prime-integer-length
                        primep-of-base-prime
                        lit-append-of-nil
                        (:e bit-listp)
                        (:e base-field-size-in-bits))
           :use ((:instance scalar-write-bits-le-gadget-sound
                            (s c) (xs cxs) (rs crs) (acc nil))
                 (:instance scalar-write-bits-le-gadget-sound
                            (s r) (xs rxs) (rs rrs) (acc nil))
                 (:instance crv-group-write-bits-le-gadget-sound
                            (x pkx) (xs pkxs) (rs pkrs)
                            (p0 (first (third sig))))
                 (:instance crv-group-write-bits-le-gadget-sound
                            (x prx) (xs prxs) (rs prrs)
                            (p0 (second (third sig))))))))

(defruled lit-signature-write-bits-be-sound
  (implies (and (lit-sig-bits-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (lit-signature-write-bits-le-gadget
                  c cxs crs r rxs rrs pkx pkxs pkrs prx prxs prrs u p)
                 asg p))
           (equal (append (rev (lookup-equal-list cxs asg))
                          (rev (lookup-equal-list rxs asg))
                          (rev (lookup-equal-list pkxs asg))
                          (rev (lookup-equal-list prxs asg)))
                  (signature-write-bits-be-funspec sig)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(lit-signature-write-bits-le-gadget
                        crv-group-write-bits-be-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        signature-write-bits-be-funspec
                        compute-key-write-bits-be-funspec
                        curve-signaturep-forward
                        curve-compute-keyp-forward
                        lit-scalar-bits-be-is-curve
                        lit-base-prime-oddp
                        crv-base-prime-integer-length
                        primep-of-base-prime
                        lit-append-of-nil
                        (:e bit-listp)
                        (:e base-field-size-in-bits))
           :use ((:instance scalar-write-bits-le-gadget-sound
                            (s c) (xs cxs) (rs crs) (acc nil))
                 (:instance scalar-write-bits-le-gadget-sound
                            (s r) (xs rxs) (rs rrs) (acc nil))
                 (:instance crv-group-write-bits-be-gadget-sound
                            (x pkx) (xs pkxs) (rs pkrs)
                            (p0 (first (third sig))))
                 (:instance crv-group-write-bits-be-gadget-sound
                            (x prx) (xs prxs) (rs prrs)
                            (p0 (second (third sig))))))))

(defruled lit-signature-write-bits-le-complete
  (implies (and (lit-sig-bits-common-hyps)
                (equal (lookup-equal-list cxs asg) (scalar-bits-le (first sig)))
                (equal (lookup-equal-list crs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list cxs asg)
                        (scalar-modulus-minus-one-bits)))
                (equal (lookup-equal-list rxs asg) (scalar-bits-le (second sig)))
                (equal (lookup-equal-list rrs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list rxs asg)
                        (scalar-modulus-minus-one-bits)))
                (equal (lookup-equal-list pkxs asg)
                       (group-write-bits-le-funspec (first (third sig))))
                (equal (lookup-equal-list pkrs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list pkxs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list prxs asg)
                       (group-write-bits-le-funspec (second (third sig))))
                (equal (lookup-equal-list prrs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list prxs asg)
                        (nat=>lebits* (1- p)))))
           (and (r1cs::r1cs-constraints-holdp
                 (lit-signature-write-bits-le-gadget
                  c cxs crs r rxs rrs pkx pkxs pkrs prx prxs prrs u p)
                 asg p)
                (equal (append (lookup-equal-list cxs asg)
                               (lookup-equal-list rxs asg)
                               (lookup-equal-list pkxs asg)
                               (lookup-equal-list prxs asg))
                       (signature-write-bits-le-funspec sig))
                (equal (append (rev (lookup-equal-list cxs asg))
                               (rev (lookup-equal-list rxs asg))
                               (rev (group-write-bits-le-funspec
                                     (first (third sig))))
                               (rev (group-write-bits-le-funspec
                                     (second (third sig)))))
                       (signature-write-bits-be-funspec sig))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(lit-signature-write-bits-le-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        signature-write-bits-le-funspec
                        compute-key-write-bits-le-funspec
                        signature-write-bits-be-funspec
                        compute-key-write-bits-be-funspec
                        crv-group-write-bits-be-is-rev-le
                        curve-signaturep-forward
                        curve-compute-keyp-forward
                        lit-scalar-bits-le-is-curve
                        lit-rev-curve-scalar-bits-le
                        lit-base-prime-oddp
                        crv-base-prime-integer-length
                        primep-of-base-prime
                        lit-append-of-nil
                        (:e bit-listp))
           :use ((:instance scalar-write-bits-le-gadget-complete
                            (s c) (xs cxs) (rs crs) (acc nil))
                 (:instance scalar-write-bits-le-gadget-complete
                            (s r) (xs rxs) (rs rrs) (acc nil))
                 (:instance crv-group-write-bits-le-gadget-complete
                            (x pkx) (xs pkxs) (rs pkrs)
                            (pt (first (third sig))))
                 (:instance crv-group-write-bits-le-gadget-complete
                            (x prx) (xs prxs) (rs prrs)
                            (pt (second (third sig))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature::ternary: Scalar::ternary on challenge and response, and
; ComputeKey::ternary (Group::ternary on pk_sig and pr_sig, Scalar::ternary on
; sk_prf).  The output signature is built from the output wires; the output
; wires are field elements because the valuation is over the base field.

(defruled lit-signature-ternary-sound
  (implies (and
                (symbolp c)
                (symbolp ch1)
                (symbolp ch2)
                (symbolp rsp1)
                (symbolp rsp2)
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp s1)
                (symbolp s2)
                (symbolp ch)
                (symbolp rsp)
                (symbolp pkx)
                (symbolp pky)
                (symbolp prx)
                (symbolp pry)
                (symbolp s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg ch1)
                (r1cs::valuation-bindsp asg ch2)
                (r1cs::valuation-bindsp asg rsp1)
                (r1cs::valuation-bindsp asg rsp2)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg ch)
                (r1cs::valuation-bindsp asg rsp)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg s)
                (bitp (lookup-equal c asg))
                (curve-signaturep sig1)
                (curve-signaturep sig2)
                (equal (lookup-equal ch1 asg) (first sig1))
                (equal (lookup-equal ch2 asg) (first sig2))
                (equal (lookup-equal rsp1 asg) (second sig1))
                (equal (lookup-equal rsp2 asg) (second sig2))
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-ternary-gadget
                  c ch1 ch2 rsp1 rsp2 pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y s1 s2 ch rsp pkx pky prx pry s p)
                 asg p))
           (equal (list (lookup-equal ch asg)
                        (lookup-equal rsp asg)
                        (list (ecurve::point-finite (lookup-equal pkx asg)
                                                    (lookup-equal pky asg))
                              (ecurve::point-finite (lookup-equal prx asg)
                                                    (lookup-equal pry asg))
                              (lookup-equal s asg)))
                  (signature-ternary-funspec (lookup-equal c asg) sig1 sig2)))
  :hints (("Goal"
           :in-theory '(crv-signature-ternary-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        signature-ternary-funspec
                        compute-key-ternary-funspec
                        scalar-ternary-funspec
                        curve-signaturep-forward
                        crv-signature-of-components
                        fieldp
                        r1cs::fep-of-lookup-equal
                        primep-of-base-prime)
           :use ((:instance crv-scalar-ternary-gadget-sound
                            (a ch1) (b ch2) (r ch))
                 (:instance crv-scalar-ternary-gadget-sound
                            (a rsp1) (b rsp2) (r rsp))
                 (:instance crv-compute-key-ternary-gadget-sound
                            (ck1 (third sig1)) (ck2 (third sig2)))))))

(defruled lit-signature-ternary-complete
  (implies (and
                (symbolp c)
                (symbolp ch1)
                (symbolp ch2)
                (symbolp rsp1)
                (symbolp rsp2)
                (symbolp pk1x)
                (symbolp pk1y)
                (symbolp pk2x)
                (symbolp pk2y)
                (symbolp pr1x)
                (symbolp pr1y)
                (symbolp pr2x)
                (symbolp pr2y)
                (symbolp s1)
                (symbolp s2)
                (symbolp ch)
                (symbolp rsp)
                (symbolp pkx)
                (symbolp pky)
                (symbolp prx)
                (symbolp pry)
                (symbolp s)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg ch1)
                (r1cs::valuation-bindsp asg ch2)
                (r1cs::valuation-bindsp asg rsp1)
                (r1cs::valuation-bindsp asg rsp2)
                (r1cs::valuation-bindsp asg pk1x)
                (r1cs::valuation-bindsp asg pk1y)
                (r1cs::valuation-bindsp asg pk2x)
                (r1cs::valuation-bindsp asg pk2y)
                (r1cs::valuation-bindsp asg pr1x)
                (r1cs::valuation-bindsp asg pr1y)
                (r1cs::valuation-bindsp asg pr2x)
                (r1cs::valuation-bindsp asg pr2y)
                (r1cs::valuation-bindsp asg s1)
                (r1cs::valuation-bindsp asg s2)
                (r1cs::valuation-bindsp asg ch)
                (r1cs::valuation-bindsp asg rsp)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg s)
                (bitp (lookup-equal c asg))
                (curve-signaturep sig1)
                (curve-signaturep sig2)
                (equal (lookup-equal ch1 asg) (first sig1))
                (equal (lookup-equal ch2 asg) (first sig2))
                (equal (lookup-equal rsp1 asg) (second sig1))
                (equal (lookup-equal rsp2 asg) (second sig2))
                (equal (lookup-equal pk1x asg) (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg) (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg) (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg) (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg) (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg) (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg) (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg) (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (equal (lookup-equal ch asg)
                       (scalar-ternary-funspec (lookup-equal c asg)
                                               (lookup-equal ch1 asg)
                                               (lookup-equal ch2 asg)))
                (equal (lookup-equal rsp asg)
                       (scalar-ternary-funspec (lookup-equal c asg)
                                               (lookup-equal rsp1 asg)
                                               (lookup-equal rsp2 asg)))
                (equal (lookup-equal pkx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pk1x asg)
                                              (lookup-equal pk2x asg)))
                (equal (lookup-equal pky asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pk1y asg)
                                              (lookup-equal pk2y asg)))
                (equal (lookup-equal prx asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pr1x asg)
                                              (lookup-equal pr2x asg)))
                (equal (lookup-equal pry asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal pr1y asg)
                                              (lookup-equal pr2y asg)))
                (equal (lookup-equal s asg)
                       (scalar-ternary-funspec (lookup-equal c asg)
                                               (lookup-equal s1 asg)
                                               (lookup-equal s2 asg))))
           (r1cs::r1cs-constraints-holdp
            (crv-signature-ternary-gadget
                  c ch1 ch2 rsp1 rsp2 pk1x pk1y pk2x pk2y pr1x pr1y pr2x pr2y s1 s2 ch rsp pkx pky prx pry s p)
            asg p))
  :hints (("Goal"
           :in-theory '(crv-signature-ternary-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        curve-signaturep-forward)
           :use ((:instance crv-scalar-ternary-gadget-complete
                            (a ch1) (b ch2) (r ch))
                 (:instance crv-scalar-ternary-gadget-complete
                            (a rsp1) (b rsp2) (r rsp))
                 (:instance crv-compute-key-ternary-gadget-complete
                            (ck1 (third sig1)) (ck2 (third sig2)))))))
