; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Square-root circuits.
;
; square_root
;   field-square-root-gadget is the square constraint plus a bit
;   decomposition of the root and bits-lte-const-check against (p-1)/2.
;   That is what snarkVM emits: r * r = x, then is_less_than_or_equal
;   against the constant (p-1)/2, then assert.  The tighter bound makes
;   a separate comparison with p redundant.
;   field-square-root-soundness concludes r * r = x and r <= (p-1)/2.
;   Equating r with field-square-root-funspec needs uniqueness of the
;   lesser root.  That is not proved here, so R1CS-SOUND stays 0.
;
; even_square_root
;   The same square constraint, the full to-bits gadget (so the canonical
;   bits, including the range check), and assert that the least
;   significant bit is 0.  The LSB is the first little-endian bit, which
;   is the last big-endian bit.  Assert of its negation is the
;   constraint (1 - lsb) * (1) = (1).  Soundness to
;   field-even-square-root-funspec is not proved.
;
; square_roots_flagged_nondeterministic
;   Constant-exponent pow of (p-1)/2 (Euler), is_one of that power,
;   a ternary that substitutes 0 for a non-square, a square constraint,
;   negation of the first root as a linear combination, is_zero, and
;   the error flag as an and.  The constraints do not order the two
;   roots, so a swapped pair satisfies the gadget while the funspec
;   returns the lesser root first.  See bugs-fb.txt.  Completeness of
;   the ordered snarkVM witness needs the constant-pow witnesses and is
;   not proved.

(in-package "ALEOVM")

(include-book "../library-extensions/digits")
(include-book "../r1cs/field-square-root")
(include-book "../r1cs/field-square")
(include-book "../r1cs/field-to-bits")
(include-book "../r1cs/field-pow-const")
(include-book "fb-field-zero")
(include-book "fb-field-eq")
(include-book "../r1cs/boolean-and")
(include-book "../fun-specs/primitives-field")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb-field-square-root-gadget-bound
  (implies (and (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (field-square-root-gadget x y ys rs p) asg p))
           (and (equal (pfield::mul (lookup-equal y asg)
                                    (lookup-equal y asg)
                                    p)
                       (lookup-equal x asg))
                (<= (lookup-equal y asg)
                    (field-modulus-minus-one-div-two))))
  :do-not-induct t
  :enable (field-modulus-minus-one-div-two
           field-square-root-bound)
  :use field-square-root-soundness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-even-square-root-gadget ((x symbolp)
                                          (y symbolp)
                                          (ys symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (p primep))
  :guard (and (oddp p)
              (consp ys)
              (equal (len ys) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::even_square_root').
          @('(car ys)') is the little-endian LSB."
  (append (field-square-gadget y x)
          (field-to-bits-gadget y ys rs u p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 1)
                          (list (1- p) (car ys)))
                 :b (list (list 1 1))
                 :c (list (list 1 1))))))

; Prime 5.  4^2 = 1, and 4 = bits (0 0 1), whose LSB is 0.
; Range-check witnesses for 4 are z0 = 0, z1 = 0.

(defconst *fb-field-even-square-root-asg*
  '((x . 1) (y . 4)
    (b0 . 0) (b1 . 0) (b2 . 1)
    (z0 . 0) (z1 . 0)
    (u . 1)))

(defconst *fb-field-even-square-root-prime* 5)

(defrule fb-field-even-square-root-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-even-square-root-gadget 'x 'y '(b0 b1 b2) '(z0 z1) 'u
                                     *fb-field-even-square-root-prime*)
   *fb-field-even-square-root-asg*
   *fb-field-even-square-root-prime*)
  :enable (fb-field-even-square-root-gadget
           field-square-gadget
           field-to-bits-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           bits-lt-prime-gadget
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-unit-gadget
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-square-roots-flagged-gadget
  ((x symbolp)
   (e posp)
   (ss symbol-listp)
   (pow-rs symbol-listp)
   (one-m symbolp)
   (one-r symbolp)
   (square symbolp)
   (root symbolp)
   (zero-m symbolp)
   (zero-r symbolp)
   (err symbolp)
   (p primep))
  :guard (and (not (equal e 1))
              (consp pow-rs)
              (equal (len ss) (field-pow-const-slen e))
              (equal (len pow-rs) (field-pow-const-rlen e)))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::square_roots_flagged_nondeterministic').
          The second root is the linear combination @('-(root)').
          @('e') is @('(p-1)/2').  @('one-r') is the is_not_equal bit of
          the Euler power against 1, so the is_one bit is @('1 - one-r').
          @('zero-r') is the is_not_equal bit of @('x') against 0, which
          is already the is_nonzero bit."
  (append (field-pow-const-gadget x e ss pow-rs p)
          (field-is-one-gadget (car pow-rs) one-m one-r p)
          ;; square = (1 - one-r) * x, i.e. x if the Euler power is 1, else 0
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 1)
                          (list (1- p) one-r))
                 :b (list (list 1 x))
                 :c (list (list 1 square))))
          (field-square-gadget root square)
          (field-is-zero-gadget x zero-m zero-r p)
          ;; err = is_nonzero AND NOT is_nonzero_square = zero-r AND one-r
          (boolean-and-gadget zero-r one-r err)))
