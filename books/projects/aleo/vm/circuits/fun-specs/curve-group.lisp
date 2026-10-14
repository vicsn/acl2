; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/types/group crate.
;
; Conventions specific to the curve-* books:
;   - Spec names end in -funspec (as in the primitives-* books),
;     to avoid clashing with the pfcs/ and r1cs/ books;
;     helper names start with curve-.
;   - A group circuit value is the Edwards-BLS12 point (x, y)
;     of its two field coordinates.
;     Group values built by snarkVM are in the prime-order subgroup (groupp);
;     the operations are specified on all curve points
;     (ecurve::edwards-bls12-pointp), on which their formulas are complete.
;     Functions that also see pairs of coordinates that may be off the curve
;     take a curve-coordinatesp.
;   - Functions that return () in Rust and only add constraints
;     return nil on success and (spec-error) otherwise.
;   - The field and scalar helpers needed here are defined in this book
;     (curve-field-..., curve-scalar-...), independently of the primitives-* books.

(in-package "ALEOVM")

(include-book "base")
(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (e/d (spec-error) (bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic facts.

(defruled curve-not-reserrp-when-pointp
  (implies (ecurve::pointp x)
           (not (reserrp x)))
  :enable (ecurve::pointp reserrp))

(defrule curve-pointp-when-edwards-bls12-pointp
  (implies (ecurve::edwards-bls12-pointp p)
           (and (ecurve::pointp p)
                (equal (ecurve::point-kind p) :finite)))
  :rule-classes (:rewrite :forward-chaining)
  :enable (ecurve::pointp-when-edwards-bls12-pointp
           ecurve::point-finite-when-edwards-bls12-pointp))

(local (in-theory (enable curve-not-reserrp-when-pointp)))

(local (in-theory (disable (:e base-prime) (:e scalar-prime))))

(defruled curve-base-prime-is-edwards-bls12-q
  (equal (base-prime) (ecurve::edwards-bls12-q))
  :in-theory '((:e base-prime) (:e ecurve::edwards-bls12-q)))

(defrule curve-natp-of-base-prime
  (natp (base-prime))
  :rule-classes :type-prescription
  :in-theory '((:e base-prime) (:e natp)))

(defrule curve-base-prime-lower-bound
  (< 2 (base-prime))
  :rule-classes (:rewrite (:linear :trigger-terms ((base-prime))))
  :in-theory '((:e base-prime) (:e <)))

(defrule curve-base-prime-upper-bound
  (< (base-prime) (expt 2 253))
  :rule-classes (:rewrite (:linear :trigger-terms ((base-prime))))
  :in-theory '((:e base-prime) (:e <) (:e expt)))

(defrule curve-natp-of-scalar-prime
  (natp (scalar-prime))
  :rule-classes :type-prescription
  :in-theory '((:e scalar-prime) (:e natp)))

(defrule curve-scalar-prime-bounds
  (and (< (expt 2 250) (scalar-prime))
       (< (scalar-prime) (expt 2 251))
       (< (scalar-prime) (base-prime)))
  :rule-classes (:rewrite (:linear :trigger-terms ((scalar-prime))))
  :in-theory '((:e scalar-prime) (:e base-prime) (:e <) (:e expt)))

(defrule curve-fep-of-edwards-bls12-a
  (pfield::fep (ecurve::edwards-bls12-a) (base-prime))
  :enable curve-base-prime-is-edwards-bls12-q)

(defrule curve-fep-of-edwards-bls12-d
  (pfield::fep (ecurve::edwards-bls12-d) (base-prime))
  :enable curve-base-prime-is-edwards-bls12-q)

(defrule curve-fep-when-fieldp
  (implies (fieldp x)
           (pfield::fep x (base-prime)))
  :rule-classes :forward-chaining
  :enable fieldp)

(defrule curve-fieldp-when-fep
  (implies (pfield::fep x (base-prime))
           (fieldp x))
  :enable fieldp)

(defrule curve-fep-when-scalarp
  (implies (scalarp x)
           (pfield::fep x (scalar-prime)))
  :rule-classes :forward-chaining
  :enable scalarp)

(defrule curve-scalarp-when-fep
  (implies (pfield::fep x (scalar-prime))
           (scalarp x))
  :enable scalarp)

(defrule curve-fieldp-upper-bound
  (implies (fieldp x)
           (< x (base-prime)))
  :rule-classes :linear
  :enable (fieldp pfield::fep))

(defrule curve-scalarp-upper-bound
  (implies (scalarp x)
           (< x (scalar-prime)))
  :rule-classes :linear
  :enable (scalarp pfield::fep))

(defrule curve-natp-when-scalarp
  (implies (scalarp x) (natp x))
  :rule-classes :forward-chaining
  :enable (scalarp pfield::fep))

(defrule curve-edwards-bls12-pointp-of-zero
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero))
  :in-theory '((:e ecurve::edwards-bls12-pointp)
               (:e ecurve::twisted-edwards-zero)))

(defrule curve-edwards-bls12-pointp-when-groupp
  (implies (groupp p)
           (ecurve::edwards-bls12-pointp p))
  :rule-classes (:rewrite :forward-chaining)
  :enable groupp)

(defrule curve-edwards-bls12-coordinates-are-fields
  (implies (ecurve::edwards-bls12-pointp p)
           (and (pfield::fep (ecurve::point-finite->x p) (base-prime))
                (pfield::fep (ecurve::point-finite->y p) (base-prime))))
  :enable (ecurve::edwards-bls12-point->u
           ecurve::edwards-bls12-point->v
           curve-base-prime-is-edwards-bls12-q
           pfield::fep)
  :use ((:instance ecurve::edwards-bls12-point->u-upper-bound (point p))
        (:instance ecurve::edwards-bls12-point->v-upper-bound (point p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Coordinate pairs (possibly off the curve).

(define curve-coordinatesp (p)
  :returns (yes/no booleanp)
  :short "A pair of field coordinates @($(x, y)$), not necessarily on the curve."
  (and (ecurve::pointp p)
       (equal (ecurve::point-kind p) :finite)
       (fieldp (ecurve::point-finite->x p))
       (fieldp (ecurve::point-finite->y p)))
  ///
  (defrule curve-coordinatesp-when-edwards-bls12-pointp
    (implies (ecurve::edwards-bls12-pointp p)
             (curve-coordinatesp p)))
  (defrule curve-coordinatesp-of-point-finite
    (implies (and (fieldp x) (fieldp y))
             (curve-coordinatesp (ecurve::point-finite x y)))
    :enable (pfield::fep))
  (defrule curve-coordinatesp-forward
    (implies (curve-coordinatesp p)
             (and (ecurve::pointp p)
                  (equal (ecurve::point-kind p) :finite)
                  (fieldp (ecurve::point-finite->x p))
                  (fieldp (ecurve::point-finite->y p))))
    :rule-classes :forward-chaining))

(defrule curve-natp-when-fieldp
  (implies (fieldp x) (natp x))
  :rule-classes :forward-chaining
  :enable (fieldp pfield::fep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field and scalar helpers.

; snarkVM circuit/types/field/src/helpers/from_bits.rs: FromBits::from_bits_le
(define curve-field-from-bits-le ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (fieldp res))
                :hints (("Goal" :in-theory (enable pfield::fep))))
  :short "Field from little-endian bits:
          excess bits (beyond 253) must be 0 and the value must be below
          the modulus; equivalently the value of all the bits is below it."
  (b* ((v (acl2::lebits=>nat bits)))
    (if (< v (base-prime))
        v
      (spec-error))))

; snarkVM circuit/types/field/src/helpers/from_bits.rs: FromBits::from_bits_be
(define curve-field-from-bits-be ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (fieldp res)))
  (curve-field-from-bits-le (rev bits)))

; snarkVM circuit/types/field/src/helpers/to_bits.rs: ToBits::write_bits_le
(define curve-field-to-bits-le ((x fieldp))
  :returns (bits bit-listp)
  :short "The 253 little-endian bits of a field element."
  (acl2::nat=>lebits (base-field-size-in-bits) (lnfix x)))

; snarkVM circuit/types/field/src/helpers/to_bits.rs: ToBits::write_bits_be
(define curve-field-to-bits-be ((x fieldp))
  :returns (bits bit-listp)
  :short "The 253 big-endian bits of a field element."
  (acl2::nat=>bebits (base-field-size-in-bits) (lnfix x)))

; snarkVM circuit/types/scalar/src/helpers/from_bits.rs: FromBits::from_bits_le
(define curve-scalar-from-bits-le ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (scalarp res))
                :hints (("Goal" :in-theory (enable pfield::fep))))
  :short "Scalar from little-endian bits:
          excess bits (beyond 251) must be 0 and the value must be below
          the scalar modulus; equivalently the value of all the bits is below it."
  (b* ((v (acl2::lebits=>nat bits)))
    (if (< v (scalar-prime))
        v
      (spec-error))))

; snarkVM circuit/types/scalar/src/helpers/from_bits.rs: FromBits::from_bits_be
(define curve-scalar-from-bits-be ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (scalarp res)))
  (curve-scalar-from-bits-le (rev bits)))

; snarkVM circuit/types/scalar/src/helpers/to_bits.rs: ToBits::write_bits_le
(define curve-scalar-to-bits-le ((s scalarp))
  :returns (bits bit-listp)
  :short "The 251 little-endian bits of a scalar."
  (acl2::nat=>lebits (scalar-field-size-in-bits) (lnfix s)))

; snarkVM circuit/types/scalar/src/helpers/to_bits.rs: ToBits::write_bits_be
(define curve-scalar-to-bits-be ((s scalarp))
  :returns (bits bit-listp)
  :short "The 251 big-endian bits of a scalar."
  (acl2::nat=>bebits (scalar-field-size-in-bits) (lnfix s)))

; snarkVM circuit/types/scalar/src/helpers/from_field_lossy.rs: Scalar::from_field_lossy
(define curve-scalar-from-field-lossy ((x fieldp))
  :returns (s scalarp
              :hints (("Goal"
                       :in-theory (enable pfield::fep)
                       :use (:instance curve-mod-expt-2-250-bounds (n (nfix x))))))
  :short "The low 250 bits (the scalar data bits) of a field element."
  (mod (lnfix x) (expt 2 250))
  :prepwork
  ((defrule curve-mod-expt-2-250-bounds
     (implies (natp n)
              (and (natp (mod n (expt 2 250)))
                   (< (mod n (expt 2 250)) (expt 2 250))))
     :rule-classes ((:rewrite)
                    (:linear :corollary
                     (implies (natp n)
                              (< (mod n (expt 2 250)) (expt 2 250)))))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The circuit's affine formulas on arbitrary coordinates.
;; Their witnesses divide by the denominators,
;; and console field division by zero halts.
;; On curve points the denominators are never zero (the curve is complete)
;; and the formulas compute the group law.

; snarkVM circuit/types/group/src/double.rs: Double::double
(define curve-raw-double ((p curve-coordinatesp))
  :returns (res (implies (not (reserrp res)) (curve-coordinatesp res)))
  :short "Doubling formulas: @($x_3 = 2xy / (ax^2 + y^2)$),
          @($y_3 = (y^2 - ax^2) / (2 - ax^2 - y^2)$)."
  (b* ((q (base-prime))
       (a (ecurve::edwards-bls12-a))
       (x (ecurve::point-finite->x p))
       (y (ecurve::point-finite->y p))
       (xy (pfield::mul x y q))
       (x2 (pfield::mul x x q))
       (y2 (pfield::mul y y q))
       (ax2 (pfield::mul x2 a q))
       (den-x (pfield::add ax2 y2 q))
       (den-y (pfield::sub 2 den-x q))
       ((when (or (equal den-x 0) (equal den-y 0))) (spec-error)))
    (ecurve::point-finite (pfield::div (pfield::add xy xy q) den-x q)
                          (pfield::div (pfield::sub y2 ax2 q) den-y q)))
  :guard-hints (("Goal" :in-theory (enable pfield::fep)))
  :hooks nil)

; snarkVM circuit/types/group/src/add.rs: Add::add
(define curve-raw-add ((p1 curve-coordinatesp) (p2 curve-coordinatesp))
  :returns (res (implies (not (reserrp res)) (curve-coordinatesp res)))
  :short "Addition formulas: with @($v_0 = x_1 y_2$), @($v_1 = x_2 y_1$),
          @($v_2 = d v_0 v_1$), @($U = (-a x_1 + y_1)(x_2 + y_2)$),
          @($x_3 = (v_0 + v_1) / (v_2 + 1)$),
          @($y_3 = (U + a v_0 - v_1) / (1 - v_2)$)."
  (b* ((q (base-prime))
       (a (ecurve::edwards-bls12-a))
       (d (ecurve::edwards-bls12-d))
       (x1 (ecurve::point-finite->x p1))
       (y1 (ecurve::point-finite->y p1))
       (x2 (ecurve::point-finite->x p2))
       (y2 (ecurve::point-finite->y p2))
       (u (pfield::mul (pfield::add (pfield::mul x1 (pfield::neg a q) q) y1 q)
                       (pfield::add x2 y2 q)
                       q))
       (v0 (pfield::mul x1 y2 q))
       (v1 (pfield::mul x2 y1 q))
       (v2 (pfield::mul (pfield::mul v0 v1 q) d q))
       (den-x (pfield::add v2 1 q))
       (den-y (pfield::sub 1 v2 q))
       ((when (or (equal den-x 0) (equal den-y 0))) (spec-error)))
    (ecurve::point-finite
     (pfield::div (pfield::add v0 v1 q) den-x q)
     (pfield::div (pfield::sub (pfield::add u (pfield::mul v0 a q) q) v1 q) den-y q)))
  :guard-hints (("Goal" :in-theory (enable pfield::fep)))
  :hooks nil)

; snarkVM circuit/types/group/src/mul.rs: MulAssign<&[Boolean]>::mul_assign
(define curve-raw-mul-bits-be ((bits bit-listp)
                               (base curve-coordinatesp)
                               (acc curve-coordinatesp))
  :returns (res (implies (not (reserrp res)) (curve-coordinatesp res))
                :hyp (curve-coordinatesp acc))
  :short "Double-and-add on the big-endian bits:
          for each bit, @('acc := 2 acc'), then @('acc := base + acc') if the bit is set;
          the sum is computed (and may halt) also when the bit is not set."
  (b* (((when (endp bits)) acc)
       (dbl (curve-raw-double acc))
       ((when (reserrp dbl)) dbl)
       (sum (curve-raw-add base dbl))
       ((when (reserrp sum)) sum))
    (curve-raw-mul-bits-be (cdr bits) base (if (equal (car bits) 1) sum dbl)))
  :hooks nil)

; snarkVM circuit/types/group/src/lib.rs: Group::is_in_group (on arbitrary coordinates)
(define curve-raw-is-in-group ((p curve-coordinatesp))
  :returns (res (implies (not (reserrp res)) (bitp res)))
  :short "Multiply by the subgroup order with the circuit's formulas
          and test the result for zero (@($x = 0$, $y = 1$))."
  (b* ((prod (curve-raw-mul-bits-be (acl2::nat=>bebits (scalar-field-size-in-bits)
                                                      (scalar-prime))
                                    p
                                    (ecurve::twisted-edwards-zero)))
       ((when (reserrp prod)) prod))
    (if (equal prod (ecurve::twisted-edwards-zero)) 1 0))
  :guard-hints (("Goal" :in-theory (enable ecurve::twisted-edwards-zero pfield::fep)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Construction and checks.

; snarkVM circuit/types/group/src/lib.rs: Inject::new
(define group-new-funspec (p)
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "Injection enforces that the point is in the subgroup."
  (if (groupp p) p (spec-error)))

; snarkVM circuit/types/group/src/helpers/from_xy_coordinates.rs: Group::from_xy_coordinates
(define group-from-xy-coordinates-funspec ((x fieldp) (y fieldp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "The point @($(x, y)$), enforced to be in the subgroup."
  (b* ((p (ecurve::point-finite x y)))
    (if (groupp p) p (spec-error)))
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/group/src/lib.rs: Group::enforce_on_curve
(define group-enforce-on-curve-funspec ((p curve-coordinatesp))
  :short "The constraint @($y^2 (d x^2 - 1) = a x^2 - 1$),
          a rearrangement of the curve equation @($a x^2 + y^2 = 1 + d x^2 y^2$)."
  (if (ecurve::edwards-bls12-pointp p) nil (spec-error)))

; snarkVM circuit/types/group/src/lib.rs: Group::enforce_in_group
(define group-enforce-in-group-funspec ((p curve-coordinatesp))
  :short "The constraints require a curve point @($Q$) with @($4 Q = P$);
          the points @($4 Q$) are exactly the subgroup,
          and the witness @($Q = P / 4$) exists for subgroup points."
  (if (groupp p) nil (spec-error)))

; snarkVM circuit/types/group/src/double.rs: Group::enforce_double
(define group-enforce-double-funspec ((p ecurve::edwards-bls12-pointp)
                                      (dbl curve-coordinatesp))
  :short "The doubling constraints of @(tsee curve-raw-double) on @('dbl');
          for a curve point @('p') their denominators are non-zero,
          so they hold exactly when @('dbl') is @($2 p$)."
  (if (equal dbl (ecurve::edwards-bls12-add p p)) nil (spec-error))
  :guard-hints (("Goal" :in-theory (enable ecurve::edwards-bls12-pointp))))

; snarkVM circuit/types/group/src/lib.rs: Group::is_in_group
(define group-is-in-group-funspec ((p curve-coordinatesp))
  :returns (res (implies (not (reserrp res)) (bitp res)))
  :short "On curve points, whether the point is in the subgroup
          (@($r P = 0$) with @($r$) prime); snarkVM documents the curve point
          assumption, and off the curve the circuit's formulas are evaluated as is."
  (if (ecurve::edwards-bls12-pointp p)
      (if (groupp p) 1 0)
    (curve-raw-is-in-group p)))

(define-sk curve-x-coordinate-in-group-p ((x fieldp))
  :short "Whether some subgroup point has abscissa @('x').
          There is at most one: if @($(x, y)$) is in the subgroup,
          @($(x, -y) = (x, y) + (0, -1)$) has order @($2r$)."
  (exists (y)
          (and (fieldp y)
               (groupp (ecurve::point-finite x y))))
  :guard-hints (("Goal" :in-theory (enable pfield::fep)))
  :skolem-name curve-x-coordinate-in-group-witness)

(define curve-x-coordinate-to-group ((x fieldp))
  :returns (p ecurve::pointp)
  :short "The subgroup point with abscissa @('x'), if any."
  (ecurve::point-finite x (nfix (curve-x-coordinate-in-group-witness x)))
  :guard-hints (("Goal" :in-theory (enable pfield::fep)))
  ///
  (defrule groupp-of-curve-x-coordinate-to-group
    (implies (curve-x-coordinate-in-group-p x)
             (groupp (curve-x-coordinate-to-group x)))
    :enable (curve-x-coordinate-in-group-p pfield::fep)
    :disable groupp))

; snarkVM circuit/types/group/src/helpers/from_x_coordinate.rs: Group::from_x_coordinate
(define group-from-x-coordinate-funspec ((x fieldp))
  :returns (res (implies (not (reserrp res)) (groupp res))
                :hints (("Goal" :in-theory (disable groupp))))
  :short "The subgroup point with abscissa @('x');
          the witnessed ordinate is enforced to give a subgroup point,
          which fails when there is none."
  (if (curve-x-coordinate-in-group-p x)
      (curve-x-coordinate-to-group x)
    (spec-error)))

; snarkVM circuit/types/group/src/helpers/from_x_coordinate.rs: Group::from_x_coordinate_flagged
(define group-from-x-coordinate-flagged-funspec ((x fieldp))
  :returns (res (implies (not (reserrp res))
                    (and (true-listp res)
                         (equal (len res) 2)
                         (ecurve::pointp (first res))
                         (bitp (second res)))))
  :short "The pair (point, error flag):
          the subgroup point with abscissa @('x') and flag 0 if there is one,
          otherwise @($(x, 0)$) (off the subgroup) and flag 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "The circuit computes @($y^2 = (a x^2 - 1)/(d x^2 - 1)$),
     both square roots (0 and 0 if @($y^2$) is not a square),
     and runs @('is_in_group') on both candidate points.
     If @($y^2$) is a square the candidates are on the curve
     and the formulas do not halt.
     If it is not, both candidates are @($(x, 0)$), off the curve,
     and @('is_in_group') evaluates the formulas on it,
     which halts if a denominator is zero; we model that precisely."))
  (b* ((q (base-prime))
       (xx (pfield::mul x x q))
       (num (pfield::sub (pfield::mul (ecurve::edwards-bls12-a) xx q) 1 q))
       (den (pfield::sub (pfield::mul (ecurve::edwards-bls12-d) xx q) 1 q))
       ((when (equal den 0)) (spec-error))
       (yy (pfield::div num den q))
       ((when (and (not (ecurve::pfield-squarep yy q))
                   (reserrp (curve-raw-is-in-group (ecurve::point-finite x 0)))))
        (spec-error))
       ((when (curve-x-coordinate-in-group-p x))
        (list (curve-x-coordinate-to-group x) 0)))
    (list (ecurve::point-finite x 0) 1))
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

; snarkVM circuit/types/group/src/helpers/from_bits.rs: FromBits::from_bits_le
(define group-from-bits-le-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "The x-coordinate from little-endian bits, then @('from_x_coordinate')."
  (b* ((x (curve-field-from-bits-le bits))
       ((when (reserrp x)) x))
    (group-from-x-coordinate-funspec x)))

; snarkVM circuit/types/group/src/helpers/from_bits.rs: FromBits::from_bits_be
(define group-from-bits-be-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (groupp res)))
  :short "The x-coordinate from big-endian bits, then @('from_x_coordinate')."
  (b* ((x (curve-field-from-bits-be bits))
       ((when (reserrp x)) x))
    (group-from-x-coordinate-funspec x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Projections.

; snarkVM circuit/types/group/src/helpers/to_x_coordinate.rs: Group::to_x_coordinate
(define group-to-x-coordinate-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (x fieldp :hyp :guard)
  (ecurve::point-finite->x p))

(defrule curve-fep-of-group-to-x-coordinate-funspec
  (implies (ecurve::edwards-bls12-pointp p)
           (pfield::fep (group-to-x-coordinate-funspec p) (base-prime)))
  :enable group-to-x-coordinate-funspec)

; snarkVM circuit/types/group/src/helpers/to_bits.rs: ToBits::write_bits_le
(define group-write-bits-le-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (bits bit-listp)
  :short "The 253 little-endian bits of the x-coordinate."
  (curve-field-to-bits-le (ecurve::point-finite->x p)))

; snarkVM circuit/types/group/src/helpers/to_bits.rs: ToBits::write_bits_be
(define group-write-bits-be-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (bits bit-listp)
  :short "The 253 big-endian bits of the x-coordinate."
  (curve-field-to-bits-be (ecurve::point-finite->x p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Arithmetic.

; snarkVM circuit/types/group/src/add.rs: Add::add
(define group-add-funspec ((p1 ecurve::edwards-bls12-pointp)
                           (p2 ecurve::edwards-bls12-pointp))
  :returns (p ecurve::edwards-bls12-pointp :hyp :guard)
  (ecurve::edwards-bls12-add p1 p2))

; snarkVM circuit/types/group/src/add.rs: AddAssign::add_assign
(define group-add-assign-funspec ((p1 ecurve::edwards-bls12-pointp)
                                  (p2 ecurve::edwards-bls12-pointp))
  :returns (p ecurve::edwards-bls12-pointp :hyp :guard)
  (group-add-funspec p1 p2))

; snarkVM circuit/types/group/src/sub.rs: Sub::sub
(define group-sub-funspec ((p1 ecurve::edwards-bls12-pointp)
                           (p2 ecurve::edwards-bls12-pointp))
  :returns (p ecurve::edwards-bls12-pointp :hyp :guard)
  :short "@($P_1 + (-P_2)$), with negation @($(x, y) \\mapsto (-x, y)$)."
  (ecurve::edwards-bls12-add p1 (ecurve::edwards-bls12-neg p2)))

; snarkVM circuit/types/group/src/sub.rs: SubAssign::sub_assign
(define group-sub-assign-funspec ((p1 ecurve::edwards-bls12-pointp)
                                  (p2 ecurve::edwards-bls12-pointp))
  :returns (p ecurve::edwards-bls12-pointp :hyp :guard)
  (group-sub-funspec p1 p2))

; snarkVM circuit/types/group/src/double.rs: Double::double
(define group-double-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (p2 ecurve::edwards-bls12-pointp :hyp :guard)
  (ecurve::edwards-bls12-add p p))

; snarkVM circuit/types/group/src/mul.rs: Mul<Scalar>::mul
(define group-mul-funspec ((p ecurve::edwards-bls12-pointp) (s scalarp))
  :returns (p2 ecurve::edwards-bls12-pointp :hyp (ecurve::edwards-bls12-pointp p))
  :short "Scalar multiplication @($s P$)
          (double-and-add on the 251 big-endian bits of @($s$))."
  (ecurve::edwards-bls12-mul (lnfix s) p))

; snarkVM circuit/types/group/src/mul.rs: MulAssign<Scalar>::mul_assign
(define group-mul-assign-funspec ((p ecurve::edwards-bls12-pointp) (s scalarp))
  :returns (p2 ecurve::edwards-bls12-pointp :hyp (ecurve::edwards-bls12-pointp p))
  (group-mul-funspec p s))

; snarkVM circuit/types/group/src/helpers/mul_by_cofactor.rs: Group::mul_by_cofactor
(define group-mul-by-cofactor-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (p4 ecurve::edwards-bls12-pointp :hyp :guard)
  :short "@($4 P$), computed as two doublings."
  (ecurve::edwards-bls12-mul (ecurve::edwards-bls12-h) p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Selection and comparison.

; snarkVM circuit/types/group/src/ternary.rs: Ternary::ternary
(define group-ternary-funspec ((c bitp) p1 p2)
  :short "@('p1') if the condition is 1, else @('p2')."
  (if (equal c 1) p1 p2))

; snarkVM circuit/types/group/src/equal.rs: Equal::is_equal
(define group-is-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "Both coordinates are equal."
  (if (equal p1 p2) 1 0))

; snarkVM circuit/types/group/src/equal.rs: Equal::is_not_equal
(define group-is-not-equal-funspec ((p1 ecurve::edwards-bls12-pointp)
                                    (p2 ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  (if (equal p1 p2) 0 1))

; snarkVM circuit/types/group/src/helpers/zero.rs: Zero::is_zero
(define group-is-zero-funspec ((p ecurve::edwards-bls12-pointp))
  :returns (b bitp)
  :short "The point is the neutral element @($(0, 1)$)."
  (if (equal p (ecurve::twisted-edwards-zero)) 1 0))
