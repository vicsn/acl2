; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::is_equal, non-constant case.
;
; snarkVM circuit/types/field/src/equal.rs emits exactly
;   (x - y) * (m) = (r)
;   (x - y) * (1 - r) = (0)
; and returns the linear combination 1 - r.  Boolean::from_variable does
; not add a separate boolean check: the two constraints force r in {0,1}.
; This is not field-neq-gadget, which also boolean-checks r and uses a
; public one in place of the constant 1.
;
; m is 1 when x = y (the inverse does not exist) and (x - y)^(-1)
; otherwise.  r is 0 when x = y and 1 otherwise.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-field")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-is-equal-gadget ((x symbolp)
                               (y symbolp)
                               (m symbolp)
                               (r symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The two constraints of @('Field::is_equal') / @('is_not_equal').
          The equal bit is the linear combination @($1 - r$)."
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

(defruled field-is-equal-gadget-to-spec
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
                     (field-is-equal-gadget x y m r p) asg p)
                    (and (equal (pfield::mul delta m$ p) r$)
                         (equal (pfield::mul delta
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (field-is-equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled field-is-equal-bit-when-constraints
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
           (equal (pfield::sub 1 r p)
                  (field-is-equal-funspec x y)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x y p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub)
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub x y p)))))))

(defruled field-is-equal-gadget-sound
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
                 (field-is-equal-gadget x y m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (field-is-equal-funspec (lookup-equal x asg)
                                          (lookup-equal y asg))))
  :hints (("Goal"
           :in-theory (e/d (field-is-equal-gadget-to-spec
                            field-is-equal-bit-when-constraints
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled field-is-equal-constraints-when-witness
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (equal r (if (equal x y) 0 1))
                (equal m (if (equal x y)
                             1
                           (pfield::inv (pfield::sub x y p) p))))
           (and (equal (pfield::mul (pfield::sub x y p) m p) r)
                (equal (pfield::mul (pfield::sub x y p)
                                    (pfield::sub 1 r p)
                                    p)
                       0)
                (equal (pfield::sub 1 r p)
                       (field-is-equal-funspec x y))))
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d (field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub x y p)))
                 (:instance pfield::equal-of-0-and-sub)
                 (:instance pfield::mul-of-0-arg1 (y m))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub x y p)))))))

(defruled field-is-equal-gadget-complete
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
                           1
                         (pfield::inv (pfield::sub (lookup-equal x asg)
                                                   (lookup-equal y asg)
                                                   p)
                                      p))))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-equal-gadget x y m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-equal-funspec (lookup-equal x asg)
                                               (lookup-equal y asg)))))
  :hints (("Goal"
           :in-theory (e/d (field-is-equal-gadget-to-spec
                            field-is-equal-constraints-when-witness
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('Field::is_equal').  @('z') is @($1 - r$)."
  (pfcs::parse-def
   "field_is_equal(x, y, z) := {
    (x - y) * (m) == (1 - z),
    (x - y) * (z) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-is-equal-circuit)
            :pred fb-field-is-equal-pred
            :prime prime)

(defruled fb-field-is-equal-pred-sound
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep z prime)
                (fb-field-is-equal-pred x y z prime))
           (equal (field-is-equal-funspec x y) z))
  :enable (fb-field-is-equal-pred
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2))

(defruled fb-field-is-equal-pred-complete
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep z prime)
                (equal z (field-is-equal-funspec x y))
                (equal m (if (equal x y)
                             1
                           (pfield::inv (pfield::sub x y prime) prime))))
           (fb-field-is-equal-pred x y z prime))
  :enable (field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec
           fieldp
           bitp)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance fb-field-is-equal-pred-suff (m m)))

(defruled fb-field-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep z prime))
           (equal (fb-field-is-equal-pred x y z prime)
                  (equal z (field-is-equal-funspec x y))))
  :use (fb-field-is-equal-pred-sound
        (:instance fb-field-is-equal-pred-complete
                   (m (if (equal x y)
                          1
                        (pfield::inv (pfield::sub x y prime) prime))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 3 = 1 in the prime 5 is false.  delta = 2, inverse is 3, r = 1,
; output 1 - r = 0.

(defconst *fb-field-is-equal-asg*
  '((x . 3) (y . 1) (m . 3) (r . 1)))

(defconst *fb-field-is-equal-prime* 5)

(defrule fb-field-is-equal-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-equal-gadget 'x 'y 'm 'r *fb-field-is-equal-prime*)
   *fb-field-is-equal-asg*
   *fb-field-is-equal-prime*)
  :enable (field-is-equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
