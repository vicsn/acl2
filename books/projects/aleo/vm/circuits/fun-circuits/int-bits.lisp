; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FromBits::from_bits_le and from_bits_be.
;
; from_bits_le of at most n bits only pads with constant false and adds
; no constraint.  Extra bits are checked by Boolean::assert_bits_are_zero,
; which is one constraint: the sum of the excess linear combinations is 0.
; For bits, that sum is 0 iff every excess bit is 0, which is exactly
; int-from-bits-le-spec's error case.
;
; from_bits_be reverses the list and calls from_bits_le.  Reversal is not
; a constraint.  The funspecs agree via lebits=>nat of rev = bebits=>nat.

(in-package "ALEOVM")

(include-book "int-support")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/lists/rev" :dir :system)

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-excess-sum-vector ((xs symbol-listp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (if (endp xs)
      nil
    (cons (list 1 (car xs))
          (int-excess-sum-vector (cdr xs)))))

(define int-from-bits-le-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The single @('assert_bits_are_zero') constraint, or none."
  (if (endp excess)
      nil
    (list (r1cs::make-r1cs-constraint
           :a (int-excess-sum-vector excess)
           :b (list (list 1 1))
           :c nil))))

(define int-from-bits-be-gadget ((excess symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraint, applied to the leading bits after reversal."
  (int-from-bits-le-gadget excess))

(defruled int-from-bits-be-gadget-is-le
  (equal (int-from-bits-be-gadget excess)
         (int-from-bits-le-gadget excess))
  :enable (int-from-bits-be-gadget int-from-bits-le-gadget))

(defruled int-from-bits-be-spec-is-le-of-rev
  (equal (int-from-bits-be-spec bits signedp n)
         (int-from-bits-le-spec (rev bits) signedp n))
  :enable (int-from-bits-be-spec
           int-from-bits-le-spec
           acl2::lebits=>nat-of-rev))

(defruled int-from-bits-le-gadget-empty-sound
  (implies (and (bit-listp bits)
                (<= (len bits) n)
                (integer-widthp n)
                (posp n))
           (and (not (equal (int-from-bits-le-spec bits signedp n)
                            (spec-error)))
                (equal (int-from-bits-le-spec bits signedp n)
                       (int-wrap (lebits=>nat bits) signedp n))
                (r1cs::r1cs-constraints-holdp
                 (int-from-bits-le-gadget nil) asg p)))
  :enable (int-from-bits-le-gadget
           int-from-bits-le-spec
           r1cs::r1cs-constraints-holdp))

(defruled int-from-bits-le-gadget-empty-complete
  (implies (and (bit-listp bits)
                (<= (len bits) n)
                (posp n))
           (r1cs::r1cs-constraints-holdp
            (int-from-bits-le-gadget nil) asg p))
  :enable (int-from-bits-le-gadget r1cs::r1cs-constraints-holdp))

(defconst *int-from-bits-le-sample*
  '((e0 . 0) (e1 . 0)))

(defruled int-from-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-from-bits-le-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-from-bits-le-gadget
                                     int-excess-sum-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-from-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-from-bits-be-gadget '(e0 e1))
   *int-from-bits-le-sample*
   (base-prime))
  :enable (int-from-bits-be-gadget-is-le
           int-from-bits-le-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-from-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_from_bits_le(e0, e1) := {
    (e0 + e1) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-from-bits-le-circuit)
            :pred int-from-bits-le-pred
            :prime prime)

(defruled int-from-bits-le-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp e0)
                (bitp e1)
                (bit-listp low)
                (equal (len low) 8)
                (integer-widthp 8))
           (equal (int-from-bits-le-pred e0 e1 prime)
                  (not (equal (int-from-bits-le-spec
                               (append low (list e0 e1)) nil 8)
                              (spec-error)))))
  :enable (int-from-bits-le-pred
           int-from-bits-le-spec))

(define int-from-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "int_from_bits_be(e0, e1) := {
    (e0 + e1) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-from-bits-be-circuit)
            :pred int-from-bits-be-pred
            :prime prime)

(defruled int-from-bits-be-pred-is-le-pred
  (equal (int-from-bits-be-pred e0 e1 prime)
         (int-from-bits-le-pred e0 e1 prime))
  :enable (int-from-bits-be-pred int-from-bits-le-pred))
