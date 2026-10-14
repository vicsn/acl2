; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inject::new  (circuit/types/integers/src/lib.rs)
;
; snarkVM builds the little-endian bits with Boolean::new, which is the
; boolean-check gadget, then calls from_bits_le.  For a list of exactly
; I::BITS bits, from_bits_le adds nothing.  The injected value is the
; two's-complement reading of those bits, which is int-new-spec.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/boolean-check")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-new-gadget ((xs symbol-listp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Boolean-check of every bit.  This is @('Integer::new')."
  (boolean-check-gadget-list xs p))

(defruled int-new-gadget-sound
  (implies (and (symbol-listp xs)
                (primep p)
                (equal n (len xs))
                (posp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::r1cs-constraints-holdp
                 (int-new-gadget xs p) asg p))
           (b* ((bits (lookup-equal-list xs asg))
                (x (lebits->int bits signedp)))
             (and (bit-listp bits)
                  (int-valuep x signedp n)
                  (equal x (int-new-spec x signedp n)))))
  :enable (int-new-gadget
           boolean-check-gadget-list-to-bit-listp
           int-new-spec
           int-valuep-of-lebits->int
           len-of-lookup-equal-list))

(defruled int-new-gadget-complete
  (implies (and (symbol-listp xs)
                (primep p)
                (equal n (len xs))
                (posp n)
                (integer-widthp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (int-valuep x signedp n)
                (equal (lookup-equal-list xs asg)
                       (int->lebits x n)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-new-gadget xs p) asg p)
                (equal (lebits->int (lookup-equal-list xs asg) signedp)
                       (int-new-spec x signedp n))))
  :enable (int-new-gadget
           boolean-check-gadget-list-to-bit-listp
           bit-listp-of-int->lebits-explicit
           int-new-spec
           lebits->int-of-int->lebits))

(defconst *int-new-sample*
  '((b0 . 1) (b1 . 0)))

(defruled int-new-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-new-gadget '(b0 b1) (base-prime))
   *int-new-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-new-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-new-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Integer::new') at width 8, the boolean checks."
  (pfcs::parse-def
   "int_new(b0, b1, b2, b3, b4, b5, b6, b7) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (1 - b2) * (b2) == (0),
    (1 - b3) * (b3) == (0),
    (1 - b4) * (b4) == (0),
    (1 - b5) * (b5) == (0),
    (1 - b6) * (b6) == (0),
    (1 - b7) * (b7) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-new-circuit)
            :pred int-new-pred
            :prime prime)

(defruled bitp-iff-boolean-check-mul
  (implies (and (equal p (base-prime))
                (pfield::fep b p))
           (equal (equal (pfield::mul (pfield::sub 1 b p) b p) 0)
                  (bitp b)))
  :hints (("Goal"
           :cases ((equal b 0) (equal b 1))
           :in-theory (e/d (bitp fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled int-new-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep b3 prime)
                (pfield::fep b4 prime)
                (pfield::fep b5 prime)
                (pfield::fep b6 prime)
                (pfield::fep b7 prime))
           (b* ((bits (list b0 b1 b2 b3 b4 b5 b6 b7))
                (x (lebits->int bits signedp)))
             (equal (int-new-pred b0 b1 b2 b3 b4 b5 b6 b7 prime)
                    (and (bit-listp bits)
                         (int-valuep x signedp 8)
                         (equal x (int-new-spec x signedp 8))))))
  :enable (int-new-pred
           bitp-iff-boolean-check-mul
           bit-listp
           int-new-spec
           int-valuep-of-lebits->int))
