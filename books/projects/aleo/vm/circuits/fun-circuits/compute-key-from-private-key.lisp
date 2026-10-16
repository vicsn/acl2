; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ComputeKey::from_private_key, at the level of the group funspecs.
;
; snarkVM (circuit/account/src/compute_key/from_private_key.rs) is
;   pk_sig = Aleo::g_scalar_multiply(sk_sig)
;   pr_sig = Aleo::g_scalar_multiply(r_sig)
;   sk_prf = Aleo::hash_to_scalar_psd4([pk_sig.x, pr_sig.x])
; and g_scalar_multiply (circuit/network/src/v0.rs) is
;   bits = scalar.to_bits_le()          ; 251 little-endian bits
;   output = Group::zero()
;   for (base, bit) in zip(g_powers(), bits):
;       output = Group::ternary(bit, output + base, output)
; with g_powers()[i] = 2^i G.
;
; g-scalar-window is that fold.  g-scalar-window-of-scalar-from-zero
; equates it to edwards-bls12-mul under twisted-edwards-add-associativity.
; compute-key-from-private-key-is-scalar-windows applies the fold to both
; scalars and then compute-key-from-funspec, whose third component is the
; abstract Poseidon hash of the two x coordinates.
;
; This is not an R1CS theorem, so the CSV flags stay 0.
; Variable mode emits 4353 constraints: two Scalar::to_bits_le (503 each),
; two 250-step folds (a variable/constant Group::add is 3 constraints and
; the following Group::ternary is 2; the first step adds constant zero to
; constant G and emits nothing), and hash_to_scalar_psd4 of two field
; elements (847).  The variable/variable addition gadget is a different
; circuit.  Poseidon stays abstract.  Associativity is not a prior circuit,
; so R1CS-SOUND-IF stays empty.

(in-package "ALEOVM")

(include-book "../fun-specs/curve-account")
(include-book "../fun-specs/primitives-scalar")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (in-theory (disable (:e curve-generator-g)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::twisted-edwards-zero)
                           bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled generator-on-edwards-bls12
  (and (ecurve::pointp (curve-generator-g))
       (ecurve::point-on-twisted-edwards-p
        (curve-generator-g)
        (ecurve::edwards-bls12-curve)))
  :hints (("Goal"
           :in-theory (e/d (ecurve::edwards-bls12-pointp)
                           (edwards-bls12-pointp-of-curve-generator-g
                            curve-generator-g))
           :use edwards-bls12-pointp-of-curve-generator-g)))

(defruled integerp-of-expt-2
  (implies (natp i)
           (integerp (expt 2 i)))
  :enable expt)

(defruled edwards-bls12-pointp-of-group-ternary
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2))
           (ecurve::edwards-bls12-pointp (group-ternary-funspec c p1 p2)))
  :enable group-ternary-funspec)

(define g-scalar-window ((bits bit-listp)
                         (i natp)
                         (acc ecurve::edwards-bls12-pointp))
  :returns (p ecurve::edwards-bls12-pointp
              :hyp (and (bit-listp bits)
                        (ecurve::edwards-bls12-pointp acc))
              :hints (("Goal"
                       :in-theory (enable edwards-bls12-pointp-of-group-ternary
                                          group-add-funspec))))
  :short "One step of Aleo::g_scalar_multiply: @('bit ? acc + 2^i G : acc'),
          then the same on the remaining little-endian bits."
  :measure (len bits)
  :verify-guards nil
  (if (endp bits)
      acc
    (g-scalar-window
     (cdr bits)
     (+ 1 (nfix i))
     (group-ternary-funspec
      (car bits)
      (group-add-funspec
       acc
       (ecurve::edwards-bls12-mul (expt 2 (nfix i))
                                  (curve-generator-g)))
      acc))))

(defruled g-scalar-window-step-acc
  :short "One ternary of @('acc + 2^i G') against @('acc') is multiplication
          by @('a + bit * 2^i'), using associativity only when the bit is 1."
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (bitp b)
                (natp a)
                (natp i))
           (equal (group-ternary-funspec
                   b
                   (group-add-funspec
                    (ecurve::edwards-bls12-mul a (curve-generator-g))
                    (ecurve::edwards-bls12-mul (expt 2 i)
                                              (curve-generator-g)))
                   (ecurve::edwards-bls12-mul a (curve-generator-g)))
                  (ecurve::edwards-bls12-mul
                   (+ a (* (bfix b) (expt 2 i)))
                   (curve-generator-g))))
  :disable curve-generator-g
  :enable (group-ternary-funspec
           group-add-funspec
           ecurve::edwards-bls12-add
           ecurve::edwards-bls12-mul
           ecurve::twisted-edwards-mul-of-scalar-addition-converse
           generator-on-edwards-bls12
           integerp-of-expt-2
           bfix)
  :cases ((equal b 1)))

(local
 (defun g-scalar-window-induct (bits i a)
   (if (atom bits)
       (list i a)
     (g-scalar-window-induct
      (cdr bits)
      (+ 1 (nfix i))
      (+ (nfix a)
         (* (bfix (car bits))
            (expt 2 (nfix i))))))))

(defruled expt-2-of-1+
  (implies (natp i)
           (equal (expt 2 (+ 1 i))
                  (* 2 (expt 2 i))))
  :enable expt)

(defruled lebits=>nat-of-bit-consp
  (implies (and (consp bits)
                (bitp (car bits)))
           (equal (acl2::lebits=>nat bits)
                  (+ (car bits)
                     (* 2 (acl2::lebits=>nat (cdr bits))))))
  :hints (("Goal"
           :in-theory (enable acl2::bfix-bitp)
           :use (:instance acl2::lebits=>nat-of-cons
                 (acl2::lodigit (car bits))
                 (acl2::hidigits (cdr bits))))))

(defruled window-scalar-step
  (equal (+ a (* (expt 2 i) (+ b (* 2 rest))))
         (+ a (* b (expt 2 i)) (* 2 (expt 2 i) rest))))

(defruled g-scalar-window-is-mul
  :short "The little-endian window, started at @('a G'), is
          @('(a + value(bits) * 2^i) G')."
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (bit-listp bits)
                (natp a)
                (natp i))
           (equal (g-scalar-window
                   bits i
                   (ecurve::edwards-bls12-mul a (curve-generator-g)))
                  (ecurve::edwards-bls12-mul
                   (+ a (* (acl2::lebits=>nat bits) (expt 2 i)))
                   (curve-generator-g))))
  :induct (g-scalar-window-induct bits i a)
  :disable (curve-generator-g acl2::lebits=>nat)
  :enable (g-scalar-window
           g-scalar-window-step-acc
           lebits=>nat-of-bit-consp
           window-scalar-step
           expt-2-of-1+
           nfix
           bfix))

(defruled zero-is-g-times-zero
  (equal (ecurve::twisted-edwards-zero)
         (ecurve::edwards-bls12-mul 0 (curve-generator-g)))
  :enable ecurve::edwards-bls12-mul
  :disable curve-generator-g
  :use (:instance ecurve::twisted-edwards-mul-of-0
        (point (curve-generator-g))
        (curve (ecurve::edwards-bls12-curve))))

(defruled lebits=>nat-of-scalar-bits-le
  (implies (scalarp s)
           (equal (acl2::lebits=>nat (scalar-bits-le s))
                  (nfix s)))
  :hints (("Goal"
           :in-theory (e/d (scalar-bits-le
                            scalarp
                            scalar-field-size-in-bits)
                           ((:definition pfield::fep)
                            (:definition pfield::fep-fix)
                            (:e scalar-prime)
                            (:e expt)))
           :use ((:instance acl2::lebits=>nat-of-nat=>lebits
                  (acl2::nat (pfield::fep-fix s (scalar-prime)))
                  (acl2::width 251))
                 curve-scalar-prime-bounds))))

(defruled g-scalar-window-of-scalar-from-zero
  :short "Aleo::g_scalar_multiply's fold of a scalar's own bits, from
          @('Group::zero()'), is @('s G').  Associativity is the only
          hypothesis beyond @('scalarp')."
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (scalarp s))
           (equal (g-scalar-window (scalar-bits-le s)
                                   0
                                   (ecurve::twisted-edwards-zero))
                  (aleo-g-scalar-multiply-funspec s)))
  :enable (aleo-g-scalar-multiply-funspec
           zero-is-g-times-zero
           g-scalar-window-is-mul
           lebits=>nat-of-scalar-bits-le
           scalarp
           pfield::fep
           nfix
           lnfix))

(defruled compute-key-from-private-key-is-scalar-windows
  :short "The two windows, then @('compute-key-from-funspec'), are
          @(tsee compute-key-from-private-key-funspec)."
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (scalarp sk-sig)
                (scalarp r-sig))
           (equal (compute-key-from-funspec
                   (g-scalar-window (scalar-bits-le sk-sig)
                                    0
                                    (ecurve::twisted-edwards-zero))
                   (g-scalar-window (scalar-bits-le r-sig)
                                    0
                                    (ecurve::twisted-edwards-zero)))
                  (compute-key-from-private-key-funspec sk-sig r-sig)))
  :enable (compute-key-from-private-key-funspec
           g-scalar-window-of-scalar-from-zero))
