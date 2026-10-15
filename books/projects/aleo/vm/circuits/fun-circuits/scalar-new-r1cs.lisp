; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS for snarkVM Scalar::new (circuit/types/scalar/src/lib.rs), public or
; private mode.
;
; At snarkVM 7dc117d45 a variable Scalar::new is Field::new of the value
; and emits no constraint.  The base field (about 2^253) is larger than
; the scalar field (about 2^251), so a witness in [r, p) satisfies that
; empty constraint list without being a scalar.
; scalar-new-unpatched-accepts-non-scalar below is that witness.
;
; snarkVM-scalar-new-range-check.patch makes variable Scalar::new call
; to_bits_le, which caches the bits and emits:
;   251 boolean checks of the bits b_i      (Field::to_lower_bits_le),
;   (s) * (1) = (sum 2^i b_i)               (assert_eq),
;   assert_less_than_or_equal_constant(bits, r-1): constant false folded
;     over the bits of r-1, AND on a 1 bit and OR on a 0 bit.  Bit 0 of
;     r-1 is 0, so the first OR folds to b_0, and 250 gates remain,
;   (1 - r_last) * (1) = (1)                (assert of the negation).
; That is 503 constraints.  scalar-new-gadget is that list, and
; scalar-new-gadget-sound says a satisfying assignment carries a scalar.

(in-package "ALEOVM")

(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")
(include-book "../r1cs/bits-lte-const")
(include-book "../fun-specs/base")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "../library-extensions/r1cses"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-modulus-minus-one-bits ()
  :returns (cs bit-listp)
  :short "Little-endian bits of @($r - 1$), the constant of
          @('assert_less_than_or_equal_constant') in @('Scalar::new')."
  (nat=>lebits* (1- (scalar-prime))))

(defruled scalar-modulus-minus-one-bits-len
  (equal (len (scalar-modulus-minus-one-bits)) 251)
  :in-theory '((:e scalar-modulus-minus-one-bits) (:e len)))

(defruled scalar-modulus-minus-one-bits-has-0
  (iff (member-equal 0 (scalar-modulus-minus-one-bits)) t)
  :in-theory '((:e scalar-modulus-minus-one-bits) (:e member-equal) (:e iff)))

(defruled scalar-modulus-minus-one-bits-msb
  (equal (car (last (scalar-modulus-minus-one-bits))) 1)
  :in-theory '((:e scalar-modulus-minus-one-bits) (:e last) (:e car)))

(defruled scalar-modulus-minus-one-bits-value
  (equal (lebits=>nat (scalar-modulus-minus-one-bits))
         (1- (scalar-prime)))
  :in-theory '((:e scalar-modulus-minus-one-bits)
               (:e lebits=>nat)
               (:e scalar-prime)
               (:e binary-+)
               (:e unary--)))

(defruled scalar-modulus-minus-one-bits-rlen
  (equal (bits-lte-const-rlen (scalar-modulus-minus-one-bits)) 250)
  :in-theory '((:e scalar-modulus-minus-one-bits) (:e bits-lte-const-rlen)))

(defruled scalar-prime-less-than-base-prime
  (< (scalar-prime) (base-prime))
  :in-theory '((:e scalar-prime) (:e base-prime) (:e <)))

(in-theory (disable (:e scalar-modulus-minus-one-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1 - r) * (1) = (1), i.e. r = 0.  The constant one is the term (1 1).

(define scalar-new-assert-gadget ((r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1)
                  (list (1- p) r))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

(defruled scalar-new-assert-gadget-to-zero
  (implies (and (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraints-holdp
                   (scalar-new-assert-gadget r p) asg p)
                  (equal (lookup-equal r asg) 0)))
  :enable (scalar-new-assert-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-new-gadget ((s symbolp)
                           (xs symbol-listp)
                           (rs symbol-listp)
                           (p primep))
  :guard (and (equal (len xs) 251)
              (equal (len rs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory (enable scalar-modulus-minus-one-bits-len
                                                scalar-modulus-minus-one-bits-has-0
                                                scalar-modulus-minus-one-bits-msb
                                                scalar-modulus-minus-one-bits-rlen))))
  :short "Variable-mode constraints of the patched @('Scalar::new')."
  :guard-hints (("Goal"
                 :in-theory (enable scalar-modulus-minus-one-bits-len
                                    scalar-modulus-minus-one-bits-has-0
                                    scalar-modulus-minus-one-bits-msb
                                    scalar-modulus-minus-one-bits-rlen)))
  (append (boolean-check-gadget-list xs p)
          (pow2sum-gadget s xs)
          (bits-lte-const-gadget xs (scalar-modulus-minus-one-bits) rs p)
          (scalar-new-assert-gadget (car (last rs)) p)))

(defruledl scalar-new-last-var
  (implies (and (symbol-listp rs)
                (consp rs)
                (r1cs::valuation-binds-allp asg rs))
           (and (symbolp (car (last rs)))
                (r1cs::valuation-bindsp asg (car (last rs)))))
  :induct (len rs)
  :enable (last len r1cs::valuation-binds-allp))

(defruled scalar-new-gadget-sound
  :short "R1CS-SOUND of the patched @('Scalar::new'): the wire is a scalar,
          and the bit wires are its little-endian bits."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (scalar-new-gadget s xs rs p) asg p))
           (b* ((s$ (lookup-equal s asg))
                (xs$ (lookup-equal-list xs asg)))
             (and (bit-listp xs$)
                  (equal s$ (lebits=>nat xs$))
                  (scalarp s$))))
  :do-not-induct t
  :use ((:instance bits-lte-const-soundness
                   (cs (scalar-modulus-minus-one-bits)))
        scalar-prime-less-than-base-prime
        scalar-modulus-minus-one-bits-value
        scalar-new-last-var)
  :cases ((consp rs))
  :enable (scalar-new-gadget
           scalarp
           pfield::fep
           primep-of-base-prime
           scalar-modulus-minus-one-bits-len
           scalar-modulus-minus-one-bits-has-0
           scalar-modulus-minus-one-bits-msb
           scalar-modulus-minus-one-bits-rlen
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           scalar-new-assert-gadget-to-zero
           last-of-lookup-equal-list
           car-of-lookup-equal-list)
  :disable ((:e scalar-prime) (:e base-prime)))

(defruled scalar-new-gadget-rejects-non-scalar
  :short "The patched gadget has no satisfying assignment whose
          @('Scalar::new') wire is outside the scalar field."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (not (scalarp (lookup-equal s asg))))
           (not (r1cs::r1cs-constraints-holdp
                 (scalar-new-gadget s xs rs p) asg p)))
  :use scalar-new-gadget-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unpatched snarkVM: Field::new only.

(define scalar-new-unpatched-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Variable-mode constraints of @('Scalar::new') at snarkVM 7dc117d45."
  nil)

(defruled scalar-new-unpatched-accepts-non-scalar
  :short "The unpatched circuit accepts the wire value @($r$),
          which is a base field element but not a scalar."
  (b* ((asg (list (cons 's (scalar-prime)))))
    (and (r1cs::r1cs-valuationp asg (base-prime))
         (r1cs::valuation-bindsp asg 's)
         (r1cs::r1cs-constraints-holdp
          (scalar-new-unpatched-gadget) asg (base-prime))
         (not (scalarp (lookup-equal 's asg)))))
  :in-theory '((:e scalar-new-unpatched-gadget)
               (:e scalar-prime)
               (:e base-prime)
               (:e r1cs::r1cs-valuationp)
               (:e r1cs::valuation-bindsp)
               (:e r1cs::r1cs-constraints-holdp)
               (:e lookup-equal)
               (:e scalarp)
               (:e cons)
               (:e not)))
