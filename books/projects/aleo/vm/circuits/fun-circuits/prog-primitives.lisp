; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Local R1CS primitives for the program crate.
;
; These are the constraints snarkVM emits for non-constant operands.
; Field addition and subtraction, and boolean negation, are linear
; combinations: they do not add a constraint.
;
;   Field::is_not_equal   (x - y) * m = r,  (x - y) * (1 - r) = 0
;   Field::is_equal       the same constraints; the result is 1 - r
;   Boolean::and          (x) * (y) = (z)
;   Boolean::or           (1 - x) * (1 - y) = (1 - z)
;   Boolean::xor          (x + x) * (y) = (x + y - z)
;   Field::mul            (x) * (y) = (z)
;   E::assert_eq          (a) * (1) = (b)     (see environment-r1cs)

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-field")
(include-book "../fun-specs/primitives-boolean")
(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (x - y) * (m) = (r)    and    (x - y) * (1 - r) = (0)
;
; snarkVM's witness: r = 0 and m = 1 when x = y (no inverse);
; r = 1 and m = (x - y)^(-1) otherwise.

(define prog-field-neq-gadget ((x symbolp)
                               (y symbolp)
                               (m symbolp)
                               (r symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::is_not_equal') on non-constant operands."
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

(defruled prog-field-neq-gadget-to-spec
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
                     (prog-field-neq-gadget x y m r p) asg p)
                    (and (equal (pfield::mul delta m$ p) r$)
                         (equal (pfield::mul delta
                                             (pfield::sub 1 r$ p)
                                             p)
                                0)))))
  :enable (prog-field-neq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-field-neq-bit-when-constraints
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
           (equal r (field-is-not-equal-funspec x y)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (field-is-not-equal-funspec
                            fieldp
                            bitp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x y p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x x)
                            (y y)
                            (p p))
                 (:instance pfield::mul-of-1-arg2
                            (x (pfield::sub x y p)))
                 (:instance pfield::mul-of-0-arg1
                            (x (pfield::sub x y p))
                            (y m))))))

(defruled prog-field-neq-gadget-sound
  :short "R1CS-SOUND: the witness bit @('r') is @('Field::is_not_equal')."
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
                 (prog-field-neq-gadget x y m r p) asg p))
           (equal (lookup-equal r asg)
                  (field-is-not-equal-funspec (lookup-equal x asg)
                                              (lookup-equal y asg))))
  :hints (("Goal"
           :in-theory (e/d (prog-field-neq-gadget-to-spec
                            prog-field-neq-bit-when-constraints
                            field-is-not-equal-funspec
                            fieldp
                            bitp
                            r1cs::fep-of-lookup-equal)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled prog-field-neq-constraints-when-witness
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
                (equal r (field-is-not-equal-funspec x y))))
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d (field-is-not-equal-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::mul-of-inv-arg2
                            (x (pfield::sub x y p)))
                 (:instance pfield::equal-of-0-and-sub
                            (x x) (y y) (p p))
                 (:instance pfield::mul-of-0-arg1
                            (x (pfield::sub x y p))
                            (y m))
                 (:instance pfield::mul-of-0-arg2
                            (x (pfield::sub x y p)))))))

(defruled prog-field-neq-gadget-complete
  :short "R1CS-COMPLETE for snarkVM's witness of @('Field::is_not_equal')."
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
                 (prog-field-neq-gadget x y m r p) asg p)
                (equal (lookup-equal r asg)
                       (field-is-not-equal-funspec (lookup-equal x asg)
                                                   (lookup-equal y asg)))))
  :hints (("Goal"
           :in-theory (e/d (prog-field-neq-gadget-to-spec
                            prog-field-neq-constraints-when-witness
                            field-is-not-equal-funspec
                            fieldp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled prog-bit-not-is-sub
  (implies (and (equal p (base-prime))
                (bitp r))
           (equal (pfield::sub 1 r p)
                  (boolean-not-funspec r)))
  :hints (("Goal"
           :cases ((equal r 0))
           :in-theory (e/d (boolean-not-funspec bitp pfield::sub)
                           ()))))

(defruled prog-field-eq-gadget-sound
  :short "R1CS-SOUND: @($1 - r$) is @('Field::is_equal').
          Negation adds no constraint."
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
                 (prog-field-neq-gadget x y m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (field-is-equal-funspec (lookup-equal x asg)
                                          (lookup-equal y asg))))
  :enable (prog-field-neq-gadget-sound
           prog-bit-not-is-sub
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec))

(defruled prog-field-eq-gadget-complete
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
                 (prog-field-neq-gadget x y m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (field-is-equal-funspec (lookup-equal x asg)
                                               (lookup-equal y asg)))))
  :enable (prog-field-neq-gadget-complete
           prog-bit-not-is-sub
           field-is-equal-funspec
           field-is-not-equal-funspec
           boolean-not-funspec))

(defconst *prog-field-neq-sample-asg*
  '((x . 3) (y . 1) (m . 3) (r . 1)))

(defruled prog-field-neq-sample-holds
  :short "Sample @($3 \\neq 1$) over the prime 5: @($m = 3 = 2^{-1}$), @('r = 1')."
  (r1cs::r1cs-constraints-holdp
   (prog-field-neq-gadget 'x 'y 'm 'r 5)
   *prog-field-neq-sample-asg*
   5)
  :enable (prog-field-neq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           r1cs::r1cs-constraint->a
           r1cs::r1cs-constraint->b
           r1cs::r1cs-constraint->c
           lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1 - ra) * (1 - rb) = (z)
; ra, rb are is_not_equal bits, so 1 - ra and 1 - rb are the equal bits.
; snarkVM folds boolean AND directly on those linear combinations.

(define prog-eq-and-gadget ((ra symbolp)
                            (rb symbolp)
                            (z symbolp)
                            (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Boolean AND of two @('is_equal') bits, each the negation of an
          @('is_not_equal') witness."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1)
                  (list (1- p) ra))
         :b (list (list 1 1)
                  (list (1- p) rb))
         :c (list (list 1 z)))))

(defruled prog-eq-and-gadget-to-mul
  (implies (and (symbolp ra) (symbolp rb) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg ra)
                (r1cs::valuation-bindsp asg rb)
                (r1cs::valuation-bindsp asg z))
           (b* ((ra$ (lookup-equal ra asg))
                (rb$ (lookup-equal rb asg))
                (z$ (lookup-equal z asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (prog-eq-and-gadget ra rb z p) asg p)
                    (equal (pfield::mul (pfield::sub 1 ra$ p)
                                        (pfield::sub 1 rb$ p)
                                        p)
                           z$))))
  :enable (prog-eq-and-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-eq-and-bit-when-mul
  (implies (and (equal p (base-prime))
                (bitp ra)
                (bitp rb)
                (equal (pfield::mul (pfield::sub 1 ra p)
                                    (pfield::sub 1 rb p)
                                    p)
                       z))
           (and (bitp z)
                (equal z (boolean-and-funspec (boolean-not-funspec ra)
                                              (boolean-not-funspec rb)))))
  :hints (("Goal"
           :cases ((equal ra 0) (equal rb 0))
           :in-theory (e/d (boolean-and-funspec
                            boolean-not-funspec
                            bitp
                            pfield::sub
                            pfield::mul)
                           ()))))

; (z) * (1 - r) = (w)   AND of a boolean variable with an is_equal bit.

(define prog-and-var-eq-gadget ((z symbolp)
                                (r symbolp)
                                (w symbolp)
                                (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 z))
         :b (list (list 1 1)
                  (list (1- p) r))
         :c (list (list 1 w)))))

(defruled prog-and-var-eq-gadget-to-mul
  (implies (and (symbolp z) (symbolp r) (symbolp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg w))
           (equal (r1cs::r1cs-constraints-holdp
                   (prog-and-var-eq-gadget z r w p) asg p)
                  (equal (pfield::mul (lookup-equal z asg)
                                      (pfield::sub 1 (lookup-equal r asg) p)
                                      p)
                         (lookup-equal w asg))))
  :enable (prog-and-var-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-and-var-eq-bit-when-mul
  (implies (and (equal p (base-prime))
                (bitp z)
                (bitp r)
                (equal (pfield::mul z (pfield::sub 1 r p) p) w))
           (and (bitp w)
                (equal w (boolean-and-funspec z (boolean-not-funspec r)))))
  :hints (("Goal"
           :cases ((equal z 0) (equal r 0))
           :in-theory (e/d (boolean-and-funspec
                            boolean-not-funspec
                            bitp
                            pfield::sub
                            pfield::mul)
                           ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1 - x) * (1 - y) = (1 - z)

(define prog-bool-or-gadget ((x symbolp)
                             (y symbolp)
                             (z symbolp)
                             (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Boolean::or') on two non-constant booleans."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1)
                  (list (1- p) x))
         :b (list (list 1 1)
                  (list (1- p) y))
         :c (list (list 1 1)
                  (list (1- p) z)))))

(defruled prog-bool-or-gadget-to-mul
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (prog-bool-or-gadget x y z p) asg p)
                    (equal (pfield::mul (pfield::sub 1 x$ p)
                                        (pfield::sub 1 y$ p)
                                        p)
                           (pfield::sub 1 z$ p)))))
  :enable (prog-bool-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-bool-or-bit-when-mul
  (implies (and (equal p (base-prime))
                (bitp x)
                (bitp y)
                (bitp z)
                (equal (pfield::mul (pfield::sub 1 x p)
                                    (pfield::sub 1 y p)
                                    p)
                       (pfield::sub 1 z p)))
           (equal z (boolean-or-funspec x y)))
  :hints (("Goal"
           :cases ((equal x 0) (equal y 0))
           :in-theory (e/d (boolean-or-funspec bitp pfield::sub pfield::mul)
                           ()))))

(defruled prog-bool-or-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (bitp (lookup-equal z asg))
                (r1cs::r1cs-constraints-holdp
                 (prog-bool-or-gadget x y z p) asg p))
           (equal (lookup-equal z asg)
                  (boolean-or-funspec (lookup-equal x asg)
                                      (lookup-equal y asg))))
  :enable (prog-bool-or-gadget-to-mul
           prog-bool-or-bit-when-mul
           boolean-or-funspec
           bitp))

(defruled prog-bool-or-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (equal (lookup-equal z asg)
                       (boolean-or-funspec (lookup-equal x asg)
                                           (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (prog-bool-or-gadget x y z p) asg p))
  :enable (prog-bool-or-gadget-to-mul
           boolean-or-funspec
           bitp
           pfield::sub
           pfield::mul))

(defconst *prog-bool-or-sample-asg*
  '((x . 0) (y . 1) (z . 1)))

(defruled prog-bool-or-sample-holds
  (r1cs::r1cs-constraints-holdp
   (prog-bool-or-gadget 'x 'y 'z 5)
   *prog-bool-or-sample-asg*
   5)
  :enable (prog-bool-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (x + x) * (y) = (x + y - z)

(define prog-bool-xor-gadget ((x symbolp)
                              (y symbolp)
                              (z symbolp)
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraint of @('Boolean::xor') on two non-constant booleans."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 x)
                  (list 1 y)
                  (list (1- p) z)))))

(defruled prog-bool-xor-gadget-to-mul
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (prog-bool-xor-gadget x y z p) asg p)
                    (equal (pfield::mul (pfield::add x$ x$ p) y$ p)
                           (pfield::add x$
                                        (pfield::sub y$ z$ p)
                                        p)))))
  :enable (prog-bool-xor-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (x) * (y) = (z)

(define prog-field-mul-gadget ((x symbolp) (y symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint of a non-constant field multiplication."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 z)))))

(defruled prog-field-mul-gadget-to-funspec
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (prog-field-mul-gadget x y z) asg p)
                  (equal (lookup-equal z asg)
                         (field-mul-funspec (lookup-equal x asg)
                                            (lookup-equal y asg)))))
  :enable (prog-field-mul-gadget
           field-mul-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-field-mul-gadget-sound
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (prog-field-mul-gadget x y z) asg p))
           (equal (lookup-equal z asg)
                  (field-mul-funspec (lookup-equal x asg)
                                     (lookup-equal y asg))))
  :enable prog-field-mul-gadget-to-funspec)

(defruled prog-field-mul-gadget-complete
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal z asg)
                       (field-mul-funspec (lookup-equal x asg)
                                          (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (prog-field-mul-gadget x y z) asg p))
  :enable prog-field-mul-gadget-to-funspec)

(defconst *prog-field-mul-sample-asg*
  '((x . 3) (y . 4) (z . 2)))

(defruled prog-field-mul-sample-holds
  :short "Sample @($3 \\cdot 4 = 2$) over the prime 5."
  (r1cs::r1cs-constraints-holdp
   (prog-field-mul-gadget 'x 'y 'z)
   *prog-field-mul-sample-asg*
   5)
  :enable (prog-field-mul-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (a) * (1) = (b)

(define prog-assert-eq-gadget ((a symbolp) (b symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The constraint of @('E::assert_eq') on non-constant operands."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 a))
         :b (list (list 1 1))
         :c (list (list 1 b)))))

(defruled prog-assert-eq-gadget-to-equal
  (implies (and (symbolp a) (symbolp b)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (prog-assert-eq-gadget a b) asg p)
                  (equal (lookup-equal a asg)
                         (lookup-equal b asg))))
  :enable (prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-assert-eq-gadget-sound
  (implies (and (symbolp a) (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (prog-assert-eq-gadget a b) asg p))
           (assert-eq-funspec (lookup-equal a asg)
                              (lookup-equal b asg)))
  :enable (prog-assert-eq-gadget-to-equal
           assert-eq-funspec
           enforce-funspec))

(defruled prog-assert-eq-gadget-complete
  (implies (and (symbolp a) (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (fieldp (lookup-equal a asg))
                (fieldp (lookup-equal b asg))
                (assert-eq-funspec (lookup-equal a asg)
                                   (lookup-equal b asg)))
           (r1cs::r1cs-constraints-holdp
            (prog-assert-eq-gadget a b) asg p))
  :enable (prog-assert-eq-gadget-to-equal
           assert-eq-funspec
           enforce-funspec))

(defconst *prog-assert-eq-sample-asg*
  '((a . 4) (b . 4)))

(defruled prog-assert-eq-sample-holds
  (r1cs::r1cs-constraints-holdp
   (prog-assert-eq-gadget 'a 'b)
   *prog-assert-eq-sample-asg*
   5)
  :enable (prog-assert-eq-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (b) * (1) = (1)

(define prog-assert-gadget ((b symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

(defruled prog-assert-gadget-to-funspec
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (prog-assert-gadget b) asg p)
                  (assert-funspec (lookup-equal b asg))))
  :enable (prog-assert-gadget
           assert-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled prog-assert-gadget-sound
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (r1cs::r1cs-constraints-holdp
                 (prog-assert-gadget b) asg p))
           (assert-funspec (lookup-equal b asg)))
  :enable prog-assert-gadget-to-funspec)

(defruled prog-assert-gadget-complete
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (assert-funspec (lookup-equal b asg)))
           (r1cs::r1cs-constraints-holdp
            (prog-assert-gadget b) asg p))
  :enable prog-assert-gadget-to-funspec)
