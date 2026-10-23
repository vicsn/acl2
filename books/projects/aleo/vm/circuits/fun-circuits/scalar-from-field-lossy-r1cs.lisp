; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::from_field_lossy (circuit/types/scalar/src/helpers/from_field_lossy.rs).
;
; The body is Scalar::from_bits_le of the first size_in_data_bits (250) bits
; of Field::to_bits_le.  A list of 250 bits is not longer than the scalar,
; so from_bits_le only pads with constant false and rebuilds the linear
; combination.  It emits no constraint of its own.  The constraints are
; Field::to_bits_le: boolean checks, the power-of-two sum, the bits-below-prime
; comparator, and the final zero check against the public unit wire.
;
; field-to-bits-soundness reads that unit wire as 1.  zero-unit-gadget does
; not force the wire; snarkVM's public one is that input.  The hypothesis
; (lookup-equal u asg) = 1 is that public input.

(in-package "ALEOVM")

(include-book "../r1cs/field-to-bits")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule scalar-lossy-base-prime-oddp
  (and (primep (base-prime))
       (oddp (base-prime))
       (equal (integer-length (base-prime)) 253))
  :in-theory '((:e base-prime) (:e primep) (:e oddp) (:e integer-length)))

(defrule scalar-lossy-two-250-below-scalar-prime
  (< (expt 2 250) (scalar-prime))
  :in-theory '((:e expt) (:e scalar-prime) (:e <)))

(define scalar-from-field-lossy-gadget ((x symbolp)
                                        (xs symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Scalar::from_field_lossy'): @('Field::to_bits_le')."
  (field-to-bits-gadget x xs rs u p))

(defruledl scalar-lossy-take-250-below-prime
  (implies (and (bit-listp xs)
                (equal (len xs) 253))
           (< (lebits=>nat (take 250 xs)) (scalar-prime)))
  :hints (("Goal"
           :use ((:instance acl2::lebits=>nat-upper-bound
                            (digits (take 250 xs)))
                 scalar-lossy-two-250-below-scalar-prime)
           :in-theory (e/d (acl2::len-of-take)
                           (acl2::lebits=>nat-upper-bound
                            scalar-lossy-two-250-below-scalar-prime)))))

(defruled scalar-lossy-low-bits-are-funspec
  :short "The low 250 canonical field bits are @('scalar-from-field-lossy-funspec')."
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bit-listp xs)
                (equal (len xs) 253)
                (equal (lebits=>nat xs) x))
           (b* ((low (take 250 xs))
                (s (lebits=>nat low)))
             (and (equal (len low) 250)
                  (bit-listp low)
                  (< s (scalar-prime))
                  (scalarp s)
                  (equal s (scalar-from-field-lossy-funspec x)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits xs))
           :in-theory (e/d (scalar-from-field-lossy-funspec
                            scalar-from-bits-le-funspec
                            field-bits-le
                            fieldp
                            scalarp
                            pfield::fep
                            scalar-field-size-in-bits
                            base-field-size-in-bits
                            acl2::lebits=>nat-upper-bound
                            scalar-lossy-take-250-below-prime
                            acl2::bit-list-fix-when-bit-listp
                            scalar-lossy-two-250-below-scalar-prime)
                           (acl2::nat=>lebits-of-lebits=>nat)
                           ((:e expt)
                            (:e scalar-prime)
                            (:e base-prime))))))

(defruled scalar-from-field-lossy-gadget-sound
  :short "Wire soundness of @('Scalar::from_field_lossy').  The unit wire is
          the public one.  The scalar is the value of the low 250 bit wires."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (scalar-from-field-lossy-gadget x xs rs u p) asg p))
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg))
                (low (take 250 xs$))
                (s (lebits=>nat low)))
             (and (bit-listp xs$)
                  (equal x$ (lebits=>nat xs$))
                  (fieldp x$)
                  (scalarp s)
                  (equal s (scalar-from-field-lossy-funspec x$)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance field-to-bits-soundness
                            (x x) (xs xs) (rs rs) (u u) (p p))
                 (:instance scalar-lossy-low-bits-are-funspec
                            (x (lookup-equal x asg))
                            (xs (lookup-equal-list xs asg))
                            (p p)))
           :in-theory (e/d (scalar-from-field-lossy-gadget
                            scalar-lossy-base-prime-oddp
                            r1cs::fep-of-lookup-equal
                            fieldp
                            pfield::fep)
                           (field-to-bits-soundness
                            scalar-lossy-low-bits-are-funspec
                            (:e base-prime)
                            (:e scalar-prime))))))
