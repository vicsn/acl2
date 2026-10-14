; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS specifications of the field conversions and zero/one tests that
; do not already have a gadget in r1cs/.
;
;   Field::from              wraps a linear combination.  No constraint.
;   Field::from_boolean      same linear combination as the boolean.
;   Field::is_zero           is_equal against the constant 0.
;   Field::is_one            is_equal against the constant 1.
;
; is_equal is boolean negation of is_not_equal, and negation is the linear
; combination 1 - r, not a constraint.  is_not_equal against a constant still
; emits its two variable-side constraints (snarkVM only skips them when both
; operands are constant).  Subtraction of a constant is itself a linear
; combination, so it adds no constraint either.
;
;   is_not_equal(x, 0):  (x) * (m) = (r)  and  (x) * (1 - r) = (0)
;   is_zero output   :   1 - r
;   is_not_equal(x, 1):  (x - 1) * (m) = (r)  and  (x - 1) * (1 - r) = (0)
;   is_one output    :   1 - r

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-field")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-from-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: the field is the linear combination itself."
  nil)

(defruled field-from-gadget-to-funspec
  (implies (fieldp x)
           (equal (field-from-funspec x) x))
  :enable field-from-funspec)

(defruled field-from-gadget-sound
  (implies (and (symbolp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::r1cs-constraints-holdp (field-from-gadget) asg p))
           (equal (lookup-equal x asg)
                  (field-from-funspec (lookup-equal x asg))))
  :enable (field-from-gadget field-from-funspec))

(defruled field-from-gadget-complete
  (implies (and (symbolp x)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (equal (lookup-equal x asg)
                       (field-from-funspec (lookup-equal x asg))))
           (r1cs::r1cs-constraints-holdp (field-from-gadget) asg p))
  :enable field-from-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-from-boolean-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints: the field reuses the boolean's linear combination."
  nil)

(defruled field-from-boolean-gadget-sound
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (field-from-boolean-gadget) asg p))
           (equal (lookup-equal b asg)
                  (field-from-boolean-funspec (lookup-equal b asg))))
  :enable (field-from-boolean-gadget field-from-boolean-funspec))

(defruled field-from-boolean-gadget-complete
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg))
                (equal (lookup-equal b asg)
                       (field-from-boolean-funspec (lookup-equal b asg))))
           (r1cs::r1cs-constraints-holdp
            (field-from-boolean-gadget) asg p))
  :enable field-from-boolean-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; r is the is_not_equal witness bit.  The is_zero boolean is 1 - r.

(define field-is-zero-gadget ((x symbolp) (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::is_zero') on a non-constant field."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c nil)))

(defruled field-is-zero-gadget-to-spec
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (field-is-zero-gadget x m r p) asg p)
                    (and (equal (pfield::mul x$ m$ p) r$)
                         (equal (pfield::mul x$
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (field-is-zero-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled field-is-zero-bit-when-constraints
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp r)
                (pfield::fep m p)
                (equal (pfield::mul x m p) r)
                (equal (pfield::mul x (pfield::sub 1 r p) p) 0))
           (equal (pfield::sub 1 r p)
                  (field-is-zero-funspec x)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (field-is-zero-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::equal-of-0-and-mul
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-1-arg2)))))

(defruled field-is-zero-gadget-sound
  :short "R1CS-SOUND: the output linear combination @($1 - r$) is @('is_zero')."
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (field-is-zero-gadget x m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (field-is-zero-funspec (lookup-equal x asg))))
  :hints (("Goal"
           :in-theory (e/d (field-is-zero-gadget-to-spec
                            field-is-zero-bit-when-constraints
                            field-is-zero-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled field-is-zero-constraints-when-witness
  (implies (and (equal p (base-prime))
                (fieldp x)
                (equal r (if (equal x 0) 0 1))
                (equal m (if (equal x 0)
                             0
                           (pfield::inv x p))))
           (and (equal (pfield::mul x m p) r)
                (equal (pfield::mul x (pfield::sub 1 r p) p) 0)
                (equal (pfield::sub 1 r p)
                       (field-is-zero-funspec x))))
  :hints (("Goal"
           :cases ((equal x 0))
           :in-theory (e/d (field-is-zero-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::mul-of-inv-arg2)
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-0-arg2)))))

(defruled field-is-zero-gadget-complete
  :short "R1CS-COMPLETE for @('Field::is_zero').
          @('m') is @($x^{-1}$) when @($x \\neq 0$), and 0 when @($x = 0$).
          @('r') is 0 when @($x = 0$) and 1 otherwise, so the output
          @($1 - r$) is the funspec bit."
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg) 0) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal x asg) 0)
                           0
                         (pfield::inv (lookup-equal x asg) p))))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-zero-gadget x m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-zero-funspec (lookup-equal x asg)))))
  :hints (("Goal"
           :in-theory (e/d (field-is-zero-gadget-to-spec
                            field-is-zero-constraints-when-witness
                            field-is-zero-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-is-one-gadget ((x symbolp) (m symbolp) (r symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::is_one') on a non-constant field."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) 1))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) 1))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c nil)))

(defruled field-is-one-gadget-to-spec
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg))
                (delta (pfield::sub x$ 1 p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (field-is-one-gadget x m r p) asg p)
                    (and (equal (pfield::mul delta m$ p) r$)
                         (equal (pfield::mul delta
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (field-is-one-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled field-is-one-bit-when-constraints
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp r)
                (pfield::fep m p)
                (equal (pfield::mul (pfield::sub x 1 p) m p) r)
                (equal (pfield::mul (pfield::sub x 1 p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (equal (pfield::sub 1 r p)
                  (field-is-one-funspec x)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (field-is-one-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x 1 p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub (y 1))
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub x 1 p)))))))

(defruled field-is-one-gadget-sound
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (field-is-one-gadget x m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (field-is-one-funspec (lookup-equal x asg))))
  :hints (("Goal"
           :in-theory (e/d (field-is-one-gadget-to-spec
                            field-is-one-bit-when-constraints
                            field-is-one-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled field-is-one-constraints-when-witness
  (implies (and (equal p (base-prime))
                (fieldp x)
                (equal r (if (equal x 1) 0 1))
                (equal m (if (equal x 1)
                             0
                           (pfield::inv (pfield::sub x 1 p) p))))
           (and (equal (pfield::mul (pfield::sub x 1 p) m p) r)
                (equal (pfield::mul (pfield::sub x 1 p)
                                    (pfield::sub 1 r p)
                                    p)
                       0)
                (equal (pfield::sub 1 r p)
                       (field-is-one-funspec x))))
  :hints (("Goal"
           :cases ((equal x 1))
           :in-theory (e/d (field-is-one-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub x 1 p)))
                 (:instance pfield::equal-of-0-and-sub (y 1))
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub x 1 p)))))))

(defruled field-is-one-gadget-complete
  (implies (and (symbolp x) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg) 1) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal x asg) 1)
                           0
                         (pfield::inv (pfield::sub (lookup-equal x asg) 1 p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-one-gadget x m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-one-funspec (lookup-equal x asg)))))
  :hints (("Goal"
           :in-theory (e/d (field-is-one-gadget-to-spec
                            field-is-one-constraints-when-witness
                            field-is-one-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))
