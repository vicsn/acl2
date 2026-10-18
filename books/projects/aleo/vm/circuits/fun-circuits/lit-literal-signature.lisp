;AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature arm of Literal::is_equal, Literal::is_not_equal,
; Literal::write_bits_le and Literal::write_bits_be over the wires.  The
; account Signature circuits (lit-signature.lisp, acct-equal-sound.lisp) are
; stated on the curve-list model of a signature; the bridges below relate it
; to the program value model (fty signature) that the Literal funspecs use.
; The wires carry the challenge, response, pk_sig, pr_sig and sk_prf of each
; operand; their types come from the signature arm of Literal::new.

(in-package "ALEOVM")

(include-book "lit-signature")
(include-book "../fun-specs/values-literal")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lit-sig-curve ((sig signaturep))
  :short "The curve-list model of a program signature value."
  (b* ((ck (signature->compute-key sig)))
    (list (signature->challenge sig)
          (signature->response sig)
          (list (compute-key->pk-sig ck)
                (compute-key->pr-sig ck)
                (compute-key->sk-prf ck)))))

(defruled lit-curve-signaturep-of-lit-sig-curve
  (curve-signaturep (lit-sig-curve sig))
  :enable (lit-sig-curve curve-signaturep curve-compute-keyp))

(defruled lit-equal-of-lit-sig-curve
  (implies (and (signaturep a) (signaturep b))
           (equal (equal (lit-sig-curve a) (lit-sig-curve b))
                  (equal a b)))
  :enable lit-sig-curve
  :use ((:instance signature-of-fields (x a))
        (:instance signature-of-fields (x b))
        (:instance compute-key-of-fields (x (signature->compute-key a)))
        (:instance compute-key-of-fields (x (signature->compute-key b))))
  :disable (signature-of-fields compute-key-of-fields
            equal-of-signature equal-of-compute-key))

(defruled lit-literal-is-equal-signature
  (implies (and (signaturep a) (signaturep b))
           (equal (literal-is-equal (literal-signature a) (literal-signature b))
                  (signature-is-equal-funspec (lit-sig-curve a) (lit-sig-curve b))))
  :enable (literal-is-equal values-literal-equalp values-signature-equalp
           signature-is-equal-funspec values-bool-to-bit
           lit-equal-of-lit-sig-curve))

(defruled lit-literal-is-not-equal-signature
  (implies (and (signaturep a) (signaturep b))
           (equal (literal-is-not-equal (literal-signature a) (literal-signature b))
                  (signature-is-not-equal-funspec (lit-sig-curve a) (lit-sig-curve b))))
  :enable (literal-is-not-equal values-literal-equalp values-signature-equalp
           signature-is-not-equal-funspec values-bool-to-bit
           lit-equal-of-lit-sig-curve))

(defruled lit-values-scalar-bits-le-is-curve
  (implies (scalarp s)
           (equal (values-scalar-to-bits-le s) (curve-scalar-to-bits-le s)))
  :enable (values-scalar-to-bits-le curve-scalar-to-bits-le
           values-nat-to-lebits scalarp pfield::fep scalar-field-size-in-bits)
  :prep-lemmas
  ((defrule lit-scalar-prime-below
     (< (scalar-prime) (expt 2 251))
     :enable ((:e scalar-prime) (:e expt)))))

(defruled lit-values-group-bits-le-is-curve
  (implies (groupp g)
           (equal (values-group-to-bits-le g) (group-write-bits-le-funspec g)))
  :enable (values-group-to-bits-le group-write-bits-le-funspec
           values-group-x curve-field-to-bits-le values-field-to-bits-le
           values-nat-to-lebits values-field-fix base-field-size-in-bits
           ecurve::edwards-bls12-point->u)
  :use ((:instance lit-fep-x-of-group (g g))
        (:instance lit-mod-253-when-field (x (ecurve::point-finite->x g))))
  :prep-lemmas
  ((defrule lit-base-prime-below
     (< (base-prime) (expt 2 253))
     :enable ((:e base-prime) (:e expt) (:e ecurve::edwards-bls12-q)))
   (defruled lit-mod-253-when-field
     (implies (and (natp x) (< x (base-prime)))
              (equal (mod x (expt 2 253)) x))
     :disable ((:e base-prime) base-prime))
   (defruled lit-fep-x-of-group
     (implies (groupp g)
              (and (natp (ecurve::point-finite->x g))
                   (< (ecurve::point-finite->x g) (base-prime))))
     :in-theory '(pfield::fep curve-edwards-bls12-pointp-when-groupp)
     :use (:instance crv-fep-x-of-edwards-bls12-point
                     (p (base-prime)) (pt g)))))

(defruled lit-values-group-bits-be-is-rev
  (equal (values-group-to-bits-be g) (rev (values-group-to-bits-le g)))
  :enable (values-group-to-bits-be values-group-to-bits-le
           values-field-to-bits-be))

(defruled lit-literal-to-bits-le-signature
  (implies (signaturep sig)
           (equal (literal-to-bits-le (literal-signature sig))
                  (signature-write-bits-le-funspec (lit-sig-curve sig))))
  :enable (literal-to-bits-le values-signature-to-bits-le
           signature-write-bits-le-funspec compute-key-write-bits-le-funspec
           lit-sig-curve lit-values-scalar-bits-le-is-curve
           lit-values-group-bits-le-is-curve))

(defruled lit-literal-to-bits-be-signature
  (implies (signaturep sig)
           (equal (literal-to-bits-be (literal-signature sig))
                  (signature-write-bits-be-funspec (lit-sig-curve sig))))
  :enable (literal-to-bits-be values-signature-to-bits-be
           signature-write-bits-be-funspec compute-key-write-bits-be-funspec
           values-scalar-to-bits-be lit-values-group-bits-be-is-rev
           lit-sig-curve lit-values-scalar-bits-le-is-curve
           lit-rev-curve-scalar-bits-le)
  :use ((:instance lit-values-group-bits-le-is-curve
                   (g (compute-key->pk-sig (signature->compute-key sig))))
        (:instance lit-values-group-bits-le-is-curve
                   (g (compute-key->pr-sig (signature->compute-key sig))))
        (:instance crv-group-write-bits-be-is-rev-le
                   (pt (compute-key->pk-sig (signature->compute-key sig))))
        (:instance crv-group-write-bits-be-is-rev-le
                   (pt (compute-key->pr-sig (signature->compute-key sig))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wire-level theorems.  The literal of each operand is built from the wire
; values of its challenge, response, pk_sig and pr_sig coordinates, and
; sk_prf.  The type hypotheses are what the signature arm of Literal::new
; establishes (literal-signature-new-sound-unconditional).

(define lit-sig-of-wires (c r pkx pky prx pry s)
  :returns (sig signaturep)
  :verify-guards nil
  (signature c r (compute-key (ecurve::point-finite pkx pky)
                              (ecurve::point-finite prx pry)
                              s)))

(defruled lit-sig-of-wires-curve
  (implies (and (scalarp c) (scalarp r) (scalarp s)
                (groupp (ecurve::point-finite pkx pky))
                (groupp (ecurve::point-finite prx pry)))
           (and (equal (lit-sig-curve (lit-sig-of-wires c r pkx pky prx pry s))
                       (list c r (list (ecurve::point-finite pkx pky)
                                       (ecurve::point-finite prx pry)
                                       s)))
                (curve-signaturep
                 (list c r (list (ecurve::point-finite pkx pky)
                                 (ecurve::point-finite prx pry)
                                 s)))))
  :enable (lit-sig-curve lit-sig-of-wires))

(defruled lit-fieldp-of-lookup-wire
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :enable fieldp)

(defruled lit-coords-of-point-finite
  (implies (and (fieldp x) (fieldp y))
           (and (equal (ecurve::point-finite->x (ecurve::point-finite x y)) x)
                (equal (ecurve::point-finite->y (ecurve::point-finite x y)) y)))
  :enable (fieldp pfield::fep))

(defruled lit-literal-is-equal-signature-sound
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
                (scalarp (lookup-equal c1 asg))
                (scalarp (lookup-equal r1 asg))
                (scalarp (lookup-equal s1 asg))
                (groupp (ecurve::point-finite (lookup-equal pk1x asg) (lookup-equal pk1y asg)))
                (groupp (ecurve::point-finite (lookup-equal pr1x asg) (lookup-equal pr1y asg)))
                (scalarp (lookup-equal c2 asg))
                (scalarp (lookup-equal r2 asg))
                (scalarp (lookup-equal s2 asg))
                (groupp (ecurve::point-finite (lookup-equal pk2x asg) (lookup-equal pk2y asg)))
                (groupp (ecurve::point-finite (lookup-equal pr2x asg) (lookup-equal pr2y asg)))
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr tck ckout ts out p)
                 asg p))
           (equal (lookup-equal out asg)
                  (literal-is-equal (literal-signature (lit-sig-of-wires (lookup-equal c1 asg) (lookup-equal r1 asg) (lookup-equal pk1x asg) (lookup-equal pk1y asg) (lookup-equal pr1x asg) (lookup-equal pr1y asg) (lookup-equal s1 asg)))
                         (literal-signature (lit-sig-of-wires (lookup-equal c2 asg) (lookup-equal r2 asg) (lookup-equal pk2x asg) (lookup-equal pk2y asg) (lookup-equal pr2x asg) (lookup-equal pr2y asg) (lookup-equal s2 asg))))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(signaturep-of-lit-sig-of-wires lit-fieldp-of-lookup-wire car-cons cdr-cons
                        primep-of-base-prime)
           :use ((:instance acct-signature-is-equal-sound
                            (sig1 (list (lookup-equal c1 asg) (lookup-equal r1 asg) (list (ecurve::point-finite (lookup-equal pk1x asg) (lookup-equal pk1y asg)) (ecurve::point-finite (lookup-equal pr1x asg) (lookup-equal pr1y asg)) (lookup-equal s1 asg))))
                            (sig2 (list (lookup-equal c2 asg) (lookup-equal r2 asg) (list (ecurve::point-finite (lookup-equal pk2x asg) (lookup-equal pk2y asg)) (ecurve::point-finite (lookup-equal pr2x asg) (lookup-equal pr2y asg)) (lookup-equal s2 asg)))))
                 (:instance lit-literal-is-equal-signature
                            (a (lit-sig-of-wires (lookup-equal c1 asg) (lookup-equal r1 asg) (lookup-equal pk1x asg) (lookup-equal pk1y asg) (lookup-equal pr1x asg) (lookup-equal pr1y asg) (lookup-equal s1 asg))) (b (lit-sig-of-wires (lookup-equal c2 asg) (lookup-equal r2 asg) (lookup-equal pk2x asg) (lookup-equal pk2y asg) (lookup-equal pr2x asg) (lookup-equal pr2y asg) (lookup-equal s2 asg))))
                 (:instance lit-sig-of-wires-curve
                            (c (lookup-equal c1 asg)) (r (lookup-equal r1 asg)) (pkx (lookup-equal pk1x asg)) (pky (lookup-equal pk1y asg))
                            (prx (lookup-equal pr1x asg)) (pry (lookup-equal pr1y asg)) (s (lookup-equal s1 asg)))
                 (:instance lit-sig-of-wires-curve
                            (c (lookup-equal c2 asg)) (r (lookup-equal r2 asg)) (pkx (lookup-equal pk2x asg)) (pky (lookup-equal pk2y asg))
                            (prx (lookup-equal pr2x asg)) (pry (lookup-equal pr2y asg)) (s (lookup-equal s2 asg)))
                 (:instance lit-coords-of-point-finite (x (lookup-equal pk1x asg)) (y (lookup-equal pk1y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pk2x asg)) (y (lookup-equal pk2y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pr1x asg)) (y (lookup-equal pr1y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pr2x asg)) (y (lookup-equal pr2y asg)))))))

(defruled lit-literal-is-not-equal-signature-sound
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
                (scalarp (lookup-equal c1 asg))
                (scalarp (lookup-equal r1 asg))
                (scalarp (lookup-equal s1 asg))
                (groupp (ecurve::point-finite (lookup-equal pk1x asg) (lookup-equal pk1y asg)))
                (groupp (ecurve::point-finite (lookup-equal pr1x asg) (lookup-equal pr1y asg)))
                (scalarp (lookup-equal c2 asg))
                (scalarp (lookup-equal r2 asg))
                (scalarp (lookup-equal s2 asg))
                (groupp (ecurve::point-finite (lookup-equal pk2x asg) (lookup-equal pk2y asg)))
                (groupp (ecurve::point-finite (lookup-equal pr2x asg) (lookup-equal pr2y asg)))
                (r1cs::r1cs-constraints-holdp
                 (crv-signature-is-not-equal-gadget
                  c1 c2 cm cr r1 r2 rm rr pk1x pk1y pk2x pk2y pkmx pkrx pkmy pkry pkout pr1x pr1y pr2x pr2y prmx prrx prmy prry prout s1 s2 sm sr tck ckout ts out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (literal-is-not-equal (literal-signature (lit-sig-of-wires (lookup-equal c1 asg) (lookup-equal r1 asg) (lookup-equal pk1x asg) (lookup-equal pk1y asg) (lookup-equal pr1x asg) (lookup-equal pr1y asg) (lookup-equal s1 asg)))
                         (literal-signature (lit-sig-of-wires (lookup-equal c2 asg) (lookup-equal r2 asg) (lookup-equal pk2x asg) (lookup-equal pk2y asg) (lookup-equal pr2x asg) (lookup-equal pr2y asg) (lookup-equal s2 asg))))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(signaturep-of-lit-sig-of-wires lit-fieldp-of-lookup-wire car-cons cdr-cons
                        primep-of-base-prime)
           :use ((:instance acct-signature-is-not-equal-sound
                            (sig1 (list (lookup-equal c1 asg) (lookup-equal r1 asg) (list (ecurve::point-finite (lookup-equal pk1x asg) (lookup-equal pk1y asg)) (ecurve::point-finite (lookup-equal pr1x asg) (lookup-equal pr1y asg)) (lookup-equal s1 asg))))
                            (sig2 (list (lookup-equal c2 asg) (lookup-equal r2 asg) (list (ecurve::point-finite (lookup-equal pk2x asg) (lookup-equal pk2y asg)) (ecurve::point-finite (lookup-equal pr2x asg) (lookup-equal pr2y asg)) (lookup-equal s2 asg)))))
                 (:instance lit-literal-is-not-equal-signature
                            (a (lit-sig-of-wires (lookup-equal c1 asg) (lookup-equal r1 asg) (lookup-equal pk1x asg) (lookup-equal pk1y asg) (lookup-equal pr1x asg) (lookup-equal pr1y asg) (lookup-equal s1 asg))) (b (lit-sig-of-wires (lookup-equal c2 asg) (lookup-equal r2 asg) (lookup-equal pk2x asg) (lookup-equal pk2y asg) (lookup-equal pr2x asg) (lookup-equal pr2y asg) (lookup-equal s2 asg))))
                 (:instance lit-sig-of-wires-curve
                            (c (lookup-equal c1 asg)) (r (lookup-equal r1 asg)) (pkx (lookup-equal pk1x asg)) (pky (lookup-equal pk1y asg))
                            (prx (lookup-equal pr1x asg)) (pry (lookup-equal pr1y asg)) (s (lookup-equal s1 asg)))
                 (:instance lit-sig-of-wires-curve
                            (c (lookup-equal c2 asg)) (r (lookup-equal r2 asg)) (pkx (lookup-equal pk2x asg)) (pky (lookup-equal pk2y asg))
                            (prx (lookup-equal pr2x asg)) (pry (lookup-equal pr2y asg)) (s (lookup-equal s2 asg)))
                 (:instance lit-coords-of-point-finite (x (lookup-equal pk1x asg)) (y (lookup-equal pk1y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pk2x asg)) (y (lookup-equal pk2y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pr1x asg)) (y (lookup-equal pr1y asg))) (:instance lit-coords-of-point-finite (x (lookup-equal pr2x asg)) (y (lookup-equal pr2y asg)))))))

(defmacro lit-literal-sig-bits-hyps ()
  '(and (symbolp c) (symbol-listp cxs) (symbol-listp crs)
        (symbolp r) (symbol-listp rxs) (symbol-listp rrs)
        (symbolp pkx) (symbol-listp pkxs) (symbol-listp pkrs)
        (symbolp prx) (symbol-listp prxs) (symbol-listp prrs)
        (symbolp u) (symbolp pky) (symbolp pry) (symbolp s)
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
        (r1cs::valuation-bindsp asg pky)
        (r1cs::valuation-bindsp asg pry)
        (r1cs::valuation-bindsp asg s)
        (scalarp (lookup-equal c asg))
        (scalarp (lookup-equal r asg))
        (scalarp (lookup-equal s asg))
        (groupp (ecurve::point-finite (lookup-equal pkx asg)
                                      (lookup-equal pky asg)))
        (groupp (ecurve::point-finite (lookup-equal prx asg)
                                      (lookup-equal pry asg)))
        (equal (lookup-equal u asg) 1)))

(defruled lit-literal-write-bits-signature-sound
  (b* ((sig (lit-sig-of-wires (lookup-equal c asg) (lookup-equal r asg)
                              (lookup-equal pkx asg) (lookup-equal pky asg)
                              (lookup-equal prx asg) (lookup-equal pry asg)
                              (lookup-equal s asg))))
    (implies (and (lit-literal-sig-bits-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (lit-signature-write-bits-le-gadget
                    c cxs crs r rxs rrs pkx pkxs pkrs prx prxs prrs u p)
                   asg p))
             (and (equal (append (lookup-equal-list cxs asg)
                                 (lookup-equal-list rxs asg)
                                 (lookup-equal-list pkxs asg)
                                 (lookup-equal-list prxs asg))
                         (literal-to-bits-le (literal-signature sig)))
                  (equal (append (rev (lookup-equal-list cxs asg))
                                 (rev (lookup-equal-list rxs asg))
                                 (rev (lookup-equal-list pkxs asg))
                                 (rev (lookup-equal-list prxs asg)))
                         (literal-to-bits-be (literal-signature sig))))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory '(signaturep-of-lit-sig-of-wires lit-fieldp-of-lookup-wire
                        car-cons cdr-cons primep-of-base-prime)
           :use ((:instance lit-signature-write-bits-le-sound
                            (sig (list (lookup-equal c asg) (lookup-equal r asg)
                                       (list (ecurve::point-finite (lookup-equal pkx asg)
                                                                   (lookup-equal pky asg))
                                             (ecurve::point-finite (lookup-equal prx asg)
                                                                   (lookup-equal pry asg))
                                             (lookup-equal s asg)))))
                 (:instance lit-signature-write-bits-be-sound
                            (sig (list (lookup-equal c asg) (lookup-equal r asg)
                                       (list (ecurve::point-finite (lookup-equal pkx asg)
                                                                   (lookup-equal pky asg))
                                             (ecurve::point-finite (lookup-equal prx asg)
                                                                   (lookup-equal pry asg))
                                             (lookup-equal s asg)))))
                 (:instance lit-literal-to-bits-le-signature
                            (sig (lit-sig-of-wires (lookup-equal c asg) (lookup-equal r asg)
                                                   (lookup-equal pkx asg) (lookup-equal pky asg)
                                                   (lookup-equal prx asg) (lookup-equal pry asg)
                                                   (lookup-equal s asg))))
                 (:instance lit-literal-to-bits-be-signature
                            (sig (lit-sig-of-wires (lookup-equal c asg) (lookup-equal r asg)
                                                   (lookup-equal pkx asg) (lookup-equal pky asg)
                                                   (lookup-equal prx asg) (lookup-equal pry asg)
                                                   (lookup-equal s asg))))
                 (:instance lit-sig-of-wires-curve
                            (c (lookup-equal c asg)) (r (lookup-equal r asg))
                            (pkx (lookup-equal pkx asg)) (pky (lookup-equal pky asg))
                            (prx (lookup-equal prx asg)) (pry (lookup-equal pry asg))
                            (s (lookup-equal s asg)))
                 (:instance lit-coords-of-point-finite
                            (x (lookup-equal pkx asg)) (y (lookup-equal pky asg)))
                 (:instance lit-coords-of-point-finite
                            (x (lookup-equal prx asg)) (y (lookup-equal pry asg)))))))
