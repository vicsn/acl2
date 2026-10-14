; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Local field constraints used by the group, scalar, address, and account
; circuit specifications.  These are the constraints snarkVM emits when the
; operands are not both constant:
;
;   is_not_equal(x, y):  (x - y) * (m) = (r)  and  (x - y) * (1 - r) = (0)
;   is_equal output:     the linear combination 1 - r (no extra constraint)
;   ternary:             (c) * (a - b) = (r - b)
;   mul / square:        (x) * (y) = (z)
;   and of two negated bits, as in Group::is_equal:
;                        (1 - rx) * (1 - ry) = (out)

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-field")
(include-book "../fun-specs/primitives-boolean")
(include-book "../r1cs/field-ternary")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-field-is-not-equal-gadget ((x symbolp)
                                       (y symbolp)
                                       (m symbolp)
                                       (r symbolp)
                                       (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The two enforces of @('Field::is_not_equal') on non-constant fields."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) y))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) y))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c nil)))

(defruled crv-field-is-not-equal-gadget-to-spec
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg))
                (delta (pfield::sub x$ y$ p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (crv-field-is-not-equal-gadget x y m r p) asg p)
                    (and (equal (pfield::mul delta m$ p) r$)
                         (equal (pfield::mul delta
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (crv-field-is-not-equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled crv-field-is-not-equal-when-constraints
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp r)
                (pfield::fep m p)
                (equal (pfield::mul (pfield::sub x y p) m p) r)
                (equal (pfield::mul (pfield::sub x y p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (and (equal r (field-is-not-equal-funspec x y))
                (equal (pfield::sub 1 r p)
                       (field-is-equal-funspec x y))))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (field-is-not-equal-funspec
                            field-is-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x y p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x x) (y y))
                 (:instance pfield::equal-of-0-and-sub
                            (x 1) (y r))
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub x y p)))))))

(defruled crv-field-is-not-equal-gadget-sound
  :short "R1CS-SOUND for @('Field::is_not_equal') and for the @('is_equal')
          linear combination @($1 - r$)."
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-field-is-not-equal-gadget x y m r p) asg p))
           (and (equal (lookup-equal r asg)
                       (field-is-not-equal-funspec (lookup-equal x asg)
                                                   (lookup-equal y asg)))
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-equal-funspec (lookup-equal x asg)
                                               (lookup-equal y asg)))))
  :hints (("Goal"
           :in-theory (e/d (crv-field-is-not-equal-gadget-to-spec
                            crv-field-is-not-equal-when-constraints
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled crv-field-is-not-equal-constraints-when-witness
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (equal r (if (equal x y) 0 1))
                (equal m (if (equal x y)
                             0
                           (pfield::inv (pfield::sub x y p) p))))
           (and (equal (pfield::mul (pfield::sub x y p) m p) r)
                (equal (pfield::mul (pfield::sub x y p)
                                    (pfield::sub 1 r p)
                                    p)
                       0)
                (equal r (field-is-not-equal-funspec x y))
                (equal (pfield::sub 1 r p)
                       (field-is-equal-funspec x y))))
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d (field-is-not-equal-funspec
                            field-is-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub x y p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x x) (y y))
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub x y p)))))))

(defruled crv-field-is-not-equal-gadget-complete
  :short "R1CS-COMPLETE.  @('m') is 0 when @($x = y$) and
          @($(x-y)^{-1}$) otherwise; @('r') is 0 when equal and 1 otherwise."
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal x asg)
                                  (lookup-equal y asg))
                           0
                         1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal x asg)
                                  (lookup-equal y asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal x asg)
                                                   (lookup-equal y asg)
                                                   p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (crv-field-is-not-equal-gadget x y m r p) asg p)
                (equal (lookup-equal r asg)
                       (field-is-not-equal-funspec (lookup-equal x asg)
                                                   (lookup-equal y asg)))
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-equal-funspec (lookup-equal x asg)
                                               (lookup-equal y asg)))))
  :hints (("Goal"
           :in-theory (e/d (crv-field-is-not-equal-gadget-to-spec
                            crv-field-is-not-equal-constraints-when-witness
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defconst *crv-field-is-not-equal-sample*
  '((x . 1) (y . 1) (m . 0) (r . 0)))

(defruled crv-field-is-not-equal-sample-holds
  :short "R1CS-SAMPLES: equal fields, witness @('m = 0'), @('r = 0')."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-field-is-not-equal-sample* p)
                (r1cs::valuation-bindsp *crv-field-is-not-equal-sample* 'x)
                (r1cs::valuation-bindsp *crv-field-is-not-equal-sample* 'y)
                (r1cs::valuation-bindsp *crv-field-is-not-equal-sample* 'm)
                (r1cs::valuation-bindsp *crv-field-is-not-equal-sample* 'r)
                (fieldp (lookup-equal 'x *crv-field-is-not-equal-sample*))
                (fieldp (lookup-equal 'y *crv-field-is-not-equal-sample*)))
           (r1cs::r1cs-constraints-holdp
            (crv-field-is-not-equal-gadget 'x 'y 'm 'r p)
            *crv-field-is-not-equal-sample*
            p))
  :enable (crv-field-is-not-equal-gadget-complete
           lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-field-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::is_not_equal').  @('m') and @('r') are parameters
          so the lifted predicate is the two enforces, as in
          @('env_assert_neq')."
  (pfcs::parse-def
   "crv_field_is_not_equal(x, y, m, r) := {
    (x - y) * (m) == (r),
    (x - y) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-field-is-not-equal-circuit)
            :pred crv-field-is-not-equal-pred
            :prime prime)

(defruled crv-field-is-not-equal-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep x prime)
                (pfield::fep y prime)
                (pfield::fep m prime)
                (pfield::fep r prime))
           (equal (crv-field-is-not-equal-pred x y m r prime)
                  (and (equal (pfield::mul (pfield::sub x y prime) m prime)
                              r)
                       (equal (pfield::mul (pfield::sub x y prime)
                                           (pfield::sub 1 r prime)
                                           prime)
                              0))))
  :enable crv-field-is-not-equal-pred)

(defruled crv-field-is-not-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp r)
                (pfield::fep m prime)
                (crv-field-is-not-equal-pred x y m r prime))
           (and (equal r (field-is-not-equal-funspec x y))
                (equal (pfield::sub 1 r prime)
                       (field-is-equal-funspec x y))))
  :enable (crv-field-is-not-equal-pred-to-mul
           crv-field-is-not-equal-when-constraints
           fieldp))

(defruled crv-field-is-not-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (fieldp y)
                (equal r (if (equal x y) 0 1))
                (equal m (if (equal x y)
                             0
                           (pfield::inv (pfield::sub x y prime) prime))))
           (crv-field-is-not-equal-pred x y m r prime))
  :enable (crv-field-is-not-equal-pred-to-mul
           crv-field-is-not-equal-constraints-when-witness
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-field-mul-gadget ((x symbolp) (y symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint of a non-constant field multiplication."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 z)))))

(defruled crv-field-mul-gadget-to-mul
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (crv-field-mul-gadget x y z) asg p)
                  (equal (pfield::mul (lookup-equal x asg)
                                      (lookup-equal y asg)
                                      p)
                         (lookup-equal z asg))))
  :enable (crv-field-mul-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(define crv-field-square-gadget ((x symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint of a non-constant field square."
  (crv-field-mul-gadget x x z))

(defruled crv-field-square-gadget-to-mul
  (implies (and (symbolp x) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp
                   (crv-field-square-gadget x z) asg p)
                  (equal (pfield::mul (lookup-equal x asg)
                                      (lookup-equal x asg)
                                      p)
                         (lookup-equal z asg))))
  :enable (crv-field-square-gadget
           crv-field-mul-gadget-to-mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-field-ternary-gadget ((c symbolp)
                                  (a symbolp)
                                  (b symbolp)
                                  (r symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The variable-case constraint of @('Field::ternary'):
          @($(a - b) \\cdot c = (r - b)$)."
  (field-ternary-gadget c a b r p))

(defruled crv-ternary-function-is-funspec
  (implies (bitp c)
           (equal (ternary-function c a b)
                  (field-ternary-funspec c a b)))
  :enable (ternary-function field-ternary-funspec bitp))

(defruled crv-field-ternary-gadget-sound
  (implies (and (symbolp c) (symbolp a) (symbolp b) (symbolp r)
                (primep p)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal c asg))
                (r1cs::r1cs-constraints-holdp
                 (crv-field-ternary-gadget c a b r p) asg p))
           (equal (lookup-equal r asg)
                  (field-ternary-funspec (lookup-equal c asg)
                                         (lookup-equal a asg)
                                         (lookup-equal b asg))))
  :enable (crv-field-ternary-gadget
           crv-ternary-function-is-funspec)
  :use (:instance field-ternary-gadget-soundness
                  (x c) (y a) (z b)))

(defruled crv-field-ternary-gadget-to-mul
  (implies (and (symbolp c) (symbolp a) (symbolp b) (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::r1cs-constraints-holdp
                   (crv-field-ternary-gadget c a b r p) asg p)
                  (equal (pfield::mul (lookup-equal c asg)
                                      (pfield::sub (lookup-equal a asg)
                                                   (lookup-equal b asg)
                                                   p)
                                      p)
                         (pfield::sub (lookup-equal r asg)
                                      (lookup-equal b asg)
                                      p))))
  :enable (crv-field-ternary-gadget
           field-ternary-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled crv-field-ternary-constraints-when-witness
  (implies (and (equal p (base-prime))
                (bitp c)
                (fieldp a)
                (fieldp b)
                (equal r (field-ternary-funspec c a b)))
           (equal (pfield::mul c (pfield::sub a b p) p)
                  (pfield::sub r b p)))
  :hints (("Goal"
           :cases ((equal c 1))
           :in-theory (e/d (field-ternary-funspec fieldp bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::mul-of-0-arg1
                            (y (pfield::sub a b p)))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub a b p)))))))

(defruled crv-field-ternary-gadget-complete
  (implies (and (symbolp c) (symbolp a) (symbolp b) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal c asg))
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (equal (lookup-equal r asg)
                       (field-ternary-funspec (lookup-equal c asg)
                                              (lookup-equal a asg)
                                              (lookup-equal b asg))))
           (r1cs::r1cs-constraints-holdp
            (crv-field-ternary-gadget c a b r p) asg p))
  :hints (("Goal"
           :in-theory (e/d (crv-field-ternary-gadget-to-mul
                            crv-field-ternary-constraints-when-witness
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defconst *crv-field-ternary-sample*
  '((c . 1) (a . 4) (b . 2) (r . 4)))

(defruled crv-field-ternary-sample-holds
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp *crv-field-ternary-sample* p)
                (r1cs::valuation-bindsp *crv-field-ternary-sample* 'c)
                (r1cs::valuation-bindsp *crv-field-ternary-sample* 'a)
                (r1cs::valuation-bindsp *crv-field-ternary-sample* 'b)
                (r1cs::valuation-bindsp *crv-field-ternary-sample* 'r)
                (bitp (lookup-equal 'c *crv-field-ternary-sample*))
                (fieldp (lookup-equal 'a *crv-field-ternary-sample*))
                (fieldp (lookup-equal 'b *crv-field-ternary-sample*))
                (equal (lookup-equal 'r *crv-field-ternary-sample*)
                       (field-ternary-funspec
                        (lookup-equal 'c *crv-field-ternary-sample*)
                        (lookup-equal 'a *crv-field-ternary-sample*)
                        (lookup-equal 'b *crv-field-ternary-sample*))))
           (r1cs::r1cs-constraints-holdp
            (crv-field-ternary-gadget 'c 'a 'b 'r p)
            *crv-field-ternary-sample*
            p))
  :enable crv-field-ternary-gadget-complete)

(define crv-field-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_field_ternary(c, a, b, r) := {
    (c) * (a - b) == (r - b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-field-ternary-circuit)
            :pred crv-field-ternary-pred
            :prime prime)

(defruled crv-field-ternary-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep c prime)
                (pfield::fep a prime)
                (pfield::fep b prime)
                (pfield::fep r prime))
           (equal (crv-field-ternary-pred c a b r prime)
                  (equal (pfield::mul c (pfield::sub a b prime) prime)
                         (pfield::sub r b prime))))
  :enable crv-field-ternary-pred)

(defruled crv-field-ternary-when-bit
  (implies (and (equal p (base-prime))
                (bitp c)
                (fieldp a)
                (fieldp b)
                (fieldp r)
                (equal (pfield::mul c (pfield::sub a b p) p)
                       (pfield::sub r b p)))
           (equal r (field-ternary-funspec c a b)))
  :hints (("Goal"
           :cases ((equal c 0))
           :in-theory (e/d (field-ternary-funspec fieldp bitp)
                           (pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled crv-field-ternary-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp c)
                (fieldp a)
                (fieldp b)
                (fieldp r)
                (crv-field-ternary-pred c a b r prime))
           (equal r (field-ternary-funspec c a b)))
  :enable (crv-field-ternary-pred-to-mul
           crv-field-ternary-when-bit
           fieldp))

(defruled crv-field-ternary-pred-complete
  (implies (and (equal prime (base-prime))
                (bitp c)
                (fieldp a)
                (fieldp b)
                (equal r (field-ternary-funspec c a b)))
           (crv-field-ternary-pred c a b r prime))
  :enable (crv-field-ternary-pred-to-mul
           crv-field-ternary-constraints-when-witness
           fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1 - rx) * (1 - ry) = out.  Boolean not is the linear combination, so
; Group::is_equal's boolean and does not allocate variables for the nots.

(define crv-and-not-gadget ((rx symbolp)
                            (ry symbolp)
                            (out symbolp)
                            (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1)
                  (list (1- p) rx))
         :b (list (list 1 1)
                  (list (1- p) ry))
         :c (list (list 1 out)))))

(defruled crv-and-not-gadget-to-mul
  (implies (and (symbolp rx) (symbolp ry) (symbolp out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg out))
           (equal (r1cs::r1cs-constraints-holdp
                   (crv-and-not-gadget rx ry out p) asg p)
                  (equal (pfield::mul (pfield::sub 1 (lookup-equal rx asg) p)
                                      (pfield::sub 1 (lookup-equal ry asg) p)
                                      p)
                         (lookup-equal out asg))))
  :enable (crv-and-not-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled crv-mul-of-bits-is-and
  (implies (and (equal p (base-prime))
                (bitp a)
                (bitp b))
           (equal (pfield::mul a b p)
                  (boolean-and-funspec a b)))
  :hints (("Goal"
           :cases ((equal a 0) (equal b 0))
           :in-theory (e/d (boolean-and-funspec bitp)
                           ((:definition pfield::mul)))
           :use ((:instance pfield::mul-of-0-arg1 (y b))
                 (:instance pfield::mul-of-0-arg2 (x a))
                 (:instance pfield::mul-of-1-arg1 (y b))
                 (:instance pfield::mul-of-1-arg2 (x a))))))

(defruled crv-and-not-is-and-of-equals
  (implies (and (equal p (base-prime))
                (bitp rx)
                (bitp ry)
                (equal (pfield::mul (pfield::sub 1 rx p)
                                    (pfield::sub 1 ry p)
                                    p)
                       out))
           (equal out
                  (boolean-and-funspec (boolean-not-funspec rx)
                                       (boolean-not-funspec ry))))
  :hints (("Goal"
           :in-theory (e/d (boolean-not-funspec bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use (:instance crv-mul-of-bits-is-and
                           (a (pfield::sub 1 rx p))
                           (b (pfield::sub 1 ry p))))))

(define crv-and-not-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "crv_and_not(rx, ry, out) := {
    (1 - rx) * (1 - ry) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-and-not-circuit)
            :pred crv-and-not-pred
            :prime prime)

(defruled crv-and-not-pred-to-mul
  (implies (and (primep prime)
                (pfield::fep rx prime)
                (pfield::fep ry prime)
                (pfield::fep out prime))
           (equal (crv-and-not-pred rx ry out prime)
                  (equal (pfield::mul (pfield::sub 1 rx prime)
                                      (pfield::sub 1 ry prime)
                                      prime)
                         out)))
  :enable crv-and-not-pred)

(defruled crv-and-not-pred-sound
  (implies (and (equal prime (base-prime))
                (bitp rx)
                (bitp ry)
                (pfield::fep out prime)
                (crv-and-not-pred rx ry out prime))
           (equal out
                  (boolean-and-funspec (boolean-not-funspec rx)
                                       (boolean-not-funspec ry))))
  :enable (crv-and-not-pred-to-mul
           crv-and-not-is-and-of-equals))
