;AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey and Signature is_equal / is_not_equal soundness without
; hypotheses on the internal wires.  The theorems in crv-account.lisp assume
; that the is_not_equal result wires and the and-outputs are bits.  snarkVM
; emits no boolean check on them; the two Field::is_not_equal constraints
; already force the result to be 0 or 1, and products of such bits are bits.

(in-package "ALEOVM")

(include-book "crv-account")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acct-neq-values-bitp
  (implies (and (primep p)
                (pfield::fep d p)
                (pfield::fep r p)
                (equal (pfield::mul d m p) r)
                (equal (pfield::mul d (pfield::sub 1 r p) p) 0))
           (bitp r))
  :hints (("Goal"
           :cases ((equal d 0))
           :in-theory (e/d (bitp) ((:definition pfield::sub)
                                   pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x d) (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub (x 1) (y r))))))

(defruled acct-neq-r-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (crv-field-is-not-equal-gadget x y m r p) asg p)
                (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (bitp (lookup-equal r asg)))
  :hints (("Goal"
           :use (crv-field-is-not-equal-gadget-to-spec
                 (:instance acct-neq-values-bitp
                            (d (pfield::sub (lookup-equal x asg)
                                            (lookup-equal y asg) p))
                            (m (lookup-equal m asg))
                            (r (lookup-equal r asg)))))))

(defruled acct-bit-product-cases
  (implies (and (primep p) (bitp a) (bitp b))
           (and (bitp (pfield::mul a b p))
                (bitp (pfield::mul a (pfield::sub 1 b p) p))
                (bitp (pfield::mul (pfield::sub 1 a p)
                                   (pfield::sub 1 b p) p))))
  :hints (("Goal" :in-theory (enable bitp))))

(defruled acct-and-not-out-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (crv-and-not-gadget rx ry out p) asg p)
                (bitp (lookup-equal rx asg))
                (bitp (lookup-equal ry asg))
                (symbolp rx) (symbolp ry) (symbolp out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg out))
           (bitp (lookup-equal out asg)))
  :hints (("Goal"
           :use (crv-and-not-gadget-to-mul
                 (:instance acct-bit-product-cases
                            (a (lookup-equal rx asg))
                            (b (lookup-equal ry asg)))))))

(defruled acct-and-var-not-out-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (crv-and-var-not-gadget x r out p) asg p)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal r asg))
                (symbolp x) (symbolp r) (symbolp out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg out))
           (bitp (lookup-equal out asg)))
  :hints (("Goal"
           :use (crv-and-var-not-gadget-to-mul
                 (:instance acct-bit-product-cases
                            (a (lookup-equal x asg))
                            (b (lookup-equal r asg)))))))

(defruled acct-boolean-and-out-bitp
  (implies (and (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget x y z) asg p)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (bitp (lookup-equal z asg)))
  :hints (("Goal"
           :use (boolean-and-gadget-to-bitand
                 (:instance bitp-of-bitand
                            (x (lookup-equal x asg))
                            (y (lookup-equal y asg))))
           :in-theory (disable bitp-of-bitand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acct-compute-key-is-equal-sound
  (implies (and (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pkmx) (symbolp pkrx) (symbolp pkmy) (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp prmx) (symbolp prrx) (symbolp prmy) (symbolp prry)
                (symbolp prout)
                (symbolp s1) (symbolp s2) (symbolp sm) (symbolp sr)
                (symbolp t1) (symbolp out)
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
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal s2 asg) (third ck2))
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-is-equal-gadget
                  pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
                  pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
                  s1 s2 sm sr t1 out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (compute-key-is-equal-funspec ck1 ck2)))
  :hints (("Goal" :use ((:instance crv-compute-key-is-equal-gadget-sound))
           :in-theory '(crv-compute-key-is-equal-gadget crv-compute-key-is-not-equal-gadget
                        crv-group-is-equal-gadget crv-scalar-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        acct-neq-r-bitp acct-and-not-out-bitp
                        acct-boolean-and-out-bitp acct-and-var-not-out-bitp
                        primep-of-base-prime))))

(defruled acct-compute-key-is-not-equal-sound
  (implies (and (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pkmx) (symbolp pkrx) (symbolp pkmy) (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp prmx) (symbolp prrx) (symbolp prmy) (symbolp prry)
                (symbolp prout)
                (symbolp s1) (symbolp s2) (symbolp sm) (symbolp sr)
                (symbolp t1) (symbolp out)
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
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first ck1)))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first ck1)))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first ck2)))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first ck2)))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second ck1)))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second ck1)))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second ck2)))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second ck2)))
                (equal (lookup-equal s1 asg) (third ck1))
                (equal (lookup-equal s2 asg) (third ck2))
                (r1cs::r1cs-constraints-holdp
                 (crv-compute-key-is-not-equal-gadget
                  pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
                  pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
                  s1 s2 sm sr t1 out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (compute-key-is-not-equal-funspec ck1 ck2)))
  :hints (("Goal" :use ((:instance crv-compute-key-is-not-equal-gadget-sound))
           :in-theory '(crv-compute-key-is-equal-gadget crv-compute-key-is-not-equal-gadget
                        crv-group-is-equal-gadget crv-scalar-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        acct-neq-r-bitp acct-and-not-out-bitp
                        acct-boolean-and-out-bitp acct-and-var-not-out-bitp
                        primep-of-base-prime))))

(defruled acct-signature-is-equal-sound
  (implies (and (symbolp c1) (symbolp c2) (symbolp cm) (symbolp cr)
                (symbolp r1) (symbolp r2) (symbolp rm) (symbolp rr)
                (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pkmx) (symbolp pkrx) (symbolp pkmy) (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp prmx) (symbolp prrx) (symbolp prmy) (symbolp prry)
                (symbolp prout)
                (symbolp s1) (symbolp s2) (symbolp sm) (symbolp sr)
                (symbolp tck) (symbolp ckout)
                (symbolp ts) (symbolp out)
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
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr
                  pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
                  pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
                  s1 s2 sm sr tck ckout ts out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (signature-is-equal-funspec sig1 sig2)))
  :hints (("Goal" :use ((:instance crv-signature-is-equal-gadget-sound))
           :in-theory '(crv-signature-is-equal-gadget crv-signature-is-not-equal-gadget crv-compute-key-is-equal-gadget crv-compute-key-is-not-equal-gadget
                        crv-group-is-equal-gadget crv-scalar-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        acct-neq-r-bitp acct-and-not-out-bitp
                        acct-boolean-and-out-bitp acct-and-var-not-out-bitp
                        primep-of-base-prime))))

(defruled acct-signature-is-not-equal-sound
  (implies (and (symbolp c1) (symbolp c2) (symbolp cm) (symbolp cr)
                (symbolp r1) (symbolp r2) (symbolp rm) (symbolp rr)
                (symbolp pk1x) (symbolp pk1y) (symbolp pk2x) (symbolp pk2y)
                (symbolp pkmx) (symbolp pkrx) (symbolp pkmy) (symbolp pkry)
                (symbolp pkout)
                (symbolp pr1x) (symbolp pr1y) (symbolp pr2x) (symbolp pr2y)
                (symbolp prmx) (symbolp prrx) (symbolp prmy) (symbolp prry)
                (symbolp prout)
                (symbolp s1) (symbolp s2) (symbolp sm) (symbolp sr)
                (symbolp tck) (symbolp ckout)
                (symbolp ts) (symbolp out)
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
                (equal (lookup-equal pk1x asg)
                       (ecurve::point-finite->x (first (third sig1))))
                (equal (lookup-equal pk1y asg)
                       (ecurve::point-finite->y (first (third sig1))))
                (equal (lookup-equal pk2x asg)
                       (ecurve::point-finite->x (first (third sig2))))
                (equal (lookup-equal pk2y asg)
                       (ecurve::point-finite->y (first (third sig2))))
                (equal (lookup-equal pr1x asg)
                       (ecurve::point-finite->x (second (third sig1))))
                (equal (lookup-equal pr1y asg)
                       (ecurve::point-finite->y (second (third sig1))))
                (equal (lookup-equal pr2x asg)
                       (ecurve::point-finite->x (second (third sig2))))
                (equal (lookup-equal pr2y asg)
                       (ecurve::point-finite->y (second (third sig2))))
                (equal (lookup-equal s1 asg) (third (third sig1)))
                (equal (lookup-equal s2 asg) (third (third sig2)))
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-not-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr
                  pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout
                  pr1x pr1y pr2x pr2y prmx prrx prmy prry prout
                  s1 s2 sm sr tck ckout ts out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (signature-is-not-equal-funspec sig1 sig2)))
  :hints (("Goal" :use ((:instance crv-signature-is-not-equal-gadget-sound))
           :in-theory '(crv-signature-is-equal-gadget crv-signature-is-not-equal-gadget crv-compute-key-is-equal-gadget crv-compute-key-is-not-equal-gadget
                        crv-group-is-equal-gadget crv-scalar-is-equal-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        acct-neq-r-bitp acct-and-not-out-bitp
                        acct-boolean-and-out-bitp acct-and-var-not-out-bitp
                        primep-of-base-prime))))
