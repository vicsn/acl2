; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pow, PowChecked, PowWrapped.
;
; Pow is pow_checked.  The variable case is square-and-multiply.
; pow_checked multiplies with overflow flags (mul_with_flags) and rejects
; a set flag on a one-bit of the exponent.  pow_wrapped uses mul_wrapped.
; Both inherit the gaps of multiplication: no 128-bit field product, and
; signed mul_checked is a different circuit.  Soundness and completeness
; are not claimed for every width.
;
; The funspecs agree with iterated wrapping or checked multiplication.
; One squaring step is formalized as the mul gadget.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "int-mul")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-pow-checked-step-gadget ((xs symbol-listp)
                                     (ys symbol-listp)
                                     (zs symbol-listp)
                                     (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "One unsigned checked multiplication inside square-and-multiply."
  (int-mul-checked-unsigned-gadget xs ys zs p))

(define int-pow-unsigned-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (+ (len xs) (len ys)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-pow-checked-step-gadget xs ys zs p))

(define int-pow-wrapped-step-gadget ((xs symbol-listp)
                                     (ys symbol-listp)
                                     (lowlow symbolp)
                                     (highlow symbolp)
                                     (lowhigh symbolp)
                                     (zs symbol-listp)
                                     (zs-high symbol-listp)
                                     (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-high) (1+ (floor (len xs) 2)))
              (< (len (append zs zs-high)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-mul-wrapped-gadget xs ys lowlow highlow lowhigh zs zs-high p))

(defruled int-pow-checked-zero-exponent
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (equal (nfix e) 0))
           (equal (int-pow-checked-spec x e signedp n) 1))
  :enable (int-pow-checked-spec int-valuep int-min int-max integer-widthp))

(defruled int-pow-wrapped-zero-exponent
  (implies (and (int-valuep x signedp n)
                (integer-widthp n)
                (posp n)
                (equal (nfix e) 0))
           (equal (int-pow-wrapped-spec x e signedp n) 1))
  :enable (int-pow-wrapped-spec int-wrap integer-widthp))

(defconst *int-pow-sample* *int-mul-and-check-sample*)

(defruled int-pow-checked-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-pow-checked-step-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-pow-sample*
   (base-prime))
  :enable (int-pow-checked-step-gadget int-mul-checked-sample-holds))

(defruled int-pow-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-pow-unsigned-gadget '(x0 x1) '(y0 y1) '(z0 z1) (base-prime))
   *int-pow-sample*
   (base-prime))
  :enable (int-pow-unsigned-gadget int-pow-checked-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-pow-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "The exponent-zero base case @($x^0 = 1$)."
  (pfcs::parse-def
   "int_pow_zero(one) := {
    (one) * (1) == (1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-pow-circuit) :pred int-pow-pred :prime prime)

(defruled int-pow-pred-to-one
  (implies (and (equal prime (base-prime))
                (fieldp one))
           (equal (int-pow-pred one prime)
                  (equal one 1)))
  :enable (int-pow-pred fieldp pfield::fep acl2::mod-when-<))
