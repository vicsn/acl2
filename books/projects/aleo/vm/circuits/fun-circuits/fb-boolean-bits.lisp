; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::assert_bits_are_zero sums the bits as one linear combination
; and emits assert_eq of that sum with 0.  It does not constrain each
; bit separately.  Bits are booleans because they were injected earlier.
;
; Boolean::is_less_than_or_equal_constant is bits-lte-const-gadget.
; The fold bit r is 0 iff the comparison holds, and the boolean snarkVM
; returns is the linear combination 1 - r.
; Boolean::assert_less_than_or_equal_constant asserts that boolean, which
; is bits-lte-const-check-gadget (it zeros r).
;
; Completeness of the comparison gadgets needs the fold witnesses for an
; arbitrary constant.  Those witnesses are not constructed here.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-boolean")
(include-book "../r1cs/bits-lte-const")
(include-book "../r1cs/bits-lte-const-check")
(include-book "../library-extensions/lookup-equal-list")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-bits-one-vector ((bits symbol-listp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (if (endp bits)
      nil
    (cons (list 1 (car bits))
          (fb-bits-one-vector (cdr bits)))))

(defruled fb-dot-product-of-bits-one-vector
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::dot-product (fb-bits-one-vector bits) asg p)
                  (bits-field-sum (lookup-equal-list bits asg))))
  :hints (("Goal"
           :in-theory (enable fb-bits-one-vector
                              r1cs::dot-product
                              bits-field-sum
                              lookup-equal-list
                              bitp
                              pfield::add
                              pfield::mul
                              acl2::bfix))))

(define fb-boolean-assert-bits-are-zero-gadget ((bits symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "The one constraint of @('Boolean::assert_bits_are_zero')."
  (list (r1cs::make-r1cs-constraint
         :a (fb-bits-one-vector bits)
         :b (list (list 1 1))
         :c nil)))

(defruled fb-boolean-assert-bits-are-zero-gadget-to-funspec
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::r1cs-constraints-holdp
                   (fb-boolean-assert-bits-are-zero-gadget bits) asg p)
                  (boolean-assert-bits-are-zero-funspec
                   (lookup-equal-list bits asg))))
  :enable (fb-boolean-assert-bits-are-zero-gadget
           fb-dot-product-of-bits-one-vector
           boolean-assert-bits-are-zero-funspec
           assert-eq-funspec
           enforce-funspec
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled fb-boolean-assert-bits-are-zero-gadget-sound
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-boolean-assert-bits-are-zero-gadget bits) asg p))
           (boolean-assert-bits-are-zero-funspec
            (lookup-equal-list bits asg)))
  :enable fb-boolean-assert-bits-are-zero-gadget-to-funspec)

(defruled fb-boolean-assert-bits-are-zero-gadget-complete
  (implies (and (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg))
                (boolean-assert-bits-are-zero-funspec
                 (lookup-equal-list bits asg)))
           (r1cs::r1cs-constraints-holdp
            (fb-boolean-assert-bits-are-zero-gadget bits) asg p))
  :enable fb-boolean-assert-bits-are-zero-gadget-to-funspec)

(define fb-boolean-assert-bits-are-zero-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for a two-bit @('assert_bits_are_zero').
          The R1CS gadget is the same sum for any length."
  (pfcs::parse-def
   "boolean_assert_bits_are_zero(b0, b1) := {
    (b0 + b1) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-boolean-assert-bits-are-zero-circuit)
            :pred fb-boolean-assert-bits-are-zero-pred
            :prime prime)

(defruled fb-boolean-assert-bits-are-zero-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1))
           (equal (fb-boolean-assert-bits-are-zero-pred b0 b1 prime)
                  (boolean-assert-bits-are-zero-funspec (list b0 b1))))
  :enable (fb-boolean-assert-bits-are-zero-pred
           boolean-assert-bits-are-zero-funspec
           bits-field-sum
           assert-eq-funspec
           enforce-funspec
           bitp))

(defconst *fb-boolean-assert-bits-are-zero-asg*
  '((b0 . 0) (b1 . 0)))

(defconst *fb-boolean-assert-bits-are-zero-prime* 5)

(defrule fb-boolean-assert-bits-are-zero-sample
  (r1cs::r1cs-constraints-holdp
   (fb-boolean-assert-bits-are-zero-gadget '(b0 b1))
   *fb-boolean-assert-bits-are-zero-asg*
   *fb-boolean-assert-bits-are-zero-prime*)
  :enable (fb-boolean-assert-bits-are-zero-gadget
           fb-bits-one-vector
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Constant bits (0 1), value 2.  The optimized fold keeps one result bit r
; with constraint (b1) * (b0) = (r).  r = 0 iff the value is <= 2.

(define fb-boolean-is-lte-const-gadget ((xs symbol-listp)
                                        (cs bit-listp)
                                        (rs symbol-listp)
                                        (p primep))
  :guard (and (member-equal 0 cs)
              (equal (car (last cs)) 1)
              (equal (len xs) (len cs))
              (equal (len rs) (bits-lte-const-rlen cs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (bits-lte-const-gadget xs cs rs p))

(defruled fb-boolean-is-lte-const-gadget-sound
  (implies (and (symbol-listp xs)
                (bit-listp cs)
                (symbol-listp rs)
                (equal (len xs) (len cs))
                (equal (len rs) (bits-lte-const-rlen cs))
                (member-equal 0 cs)
                (equal (car (last cs)) 1)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (bitp (car (last (lookup-equal-list rs asg))))
                (r1cs::r1cs-constraints-holdp
                 (fb-boolean-is-lte-const-gadget xs cs rs p) asg p))
           (equal (pfield::sub 1
                               (car (last (lookup-equal-list rs asg)))
                               p)
                  (boolean-is-less-than-or-equal-constant-funspec
                   (lookup-equal-list xs asg) cs)))
  :cases ((equal (car (last (lookup-equal-list rs asg))) 0))
  :enable (fb-boolean-is-lte-const-gadget
           boolean-is-less-than-or-equal-constant-funspec
           bitp)
  :disable ((:definition pfield::sub))
  :use bits-lte-const-soundness)

(define fb-boolean-assert-lte-const-gadget ((xs symbol-listp)
                                            (cs bit-listp)
                                            (rs symbol-listp)
                                            (p primep))
  :guard (and (or (endp cs) (equal (car (last cs)) 1))
              (equal (len rs) (bits-lte-const-check-rlen cs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (bits-lte-const-check-gadget xs cs rs p))

(defruled fb-boolean-assert-lte-const-gadget-sound
  (implies (and (symbol-listp xs)
                (bit-listp cs)
                (symbol-listp rs)
                (equal (len xs) (len cs))
                (or (endp cs) (equal (car (last cs)) 1))
                (equal (len rs) (bits-lte-const-check-rlen cs))
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-boolean-assert-lte-const-gadget xs cs rs p) asg p))
           (boolean-assert-less-than-or-equal-constant-funspec
            (lookup-equal-list xs asg) cs))
  :enable (fb-boolean-assert-lte-const-gadget
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           assert-funspec
           enforce-funspec)
  :use bits-lte-const-check-soundness)

(define fb-boolean-is-lte-const-01-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS of @('is_less_than_or_equal_constant') against bits (0 1)."
  (pfcs::parse-def
   "boolean_is_lte_const_01(b0, b1, r) := {
    (b1) * (b0) == (r)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-boolean-is-lte-const-01-circuit)
            :pred fb-boolean-is-lte-const-01-pred
            :prime prime)

(defruled fb-boolean-is-lte-const-01-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1)
                (bitp r))
           (equal (fb-boolean-is-lte-const-01-pred b0 b1 r prime)
                  (equal (pfield::sub 1 r prime)
                         (boolean-is-less-than-or-equal-constant-funspec
                          (list b0 b1) '(0 1)))))
  :enable (fb-boolean-is-lte-const-01-pred
           boolean-is-less-than-or-equal-constant-funspec
           bitp))

(define fb-boolean-assert-lte-const-01-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "boolean_assert_lte_const_01(b0, b1, r) := {
    (b1) * (b0) == (r),
    (r) * (1) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-boolean-assert-lte-const-01-circuit)
            :pred fb-boolean-assert-lte-const-01-pred
            :prime prime)

(defruled fb-boolean-assert-lte-const-01-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1)
                (bitp r))
           (equal (fb-boolean-assert-lte-const-01-pred b0 b1 r prime)
                  (boolean-assert-less-than-or-equal-constant-funspec
                   (list b0 b1) '(0 1))))
  :enable (fb-boolean-assert-lte-const-01-pred
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           assert-funspec
           enforce-funspec
           bitp))

; Value 1 = bits (1 0) <= 2 = bits (0 1).  r = b1 AND b0 = 0.

(defconst *fb-boolean-is-lte-const-asg*
  '((b0 . 1) (b1 . 0) (r . 0)))

(defconst *fb-boolean-is-lte-const-prime* 5)

(defrule fb-boolean-is-lte-const-sample
  (r1cs::r1cs-constraints-holdp
   (fb-boolean-is-lte-const-gadget '(b0 b1) '(0 1) '(r)
                                   *fb-boolean-is-lte-const-prime*)
   *fb-boolean-is-lte-const-asg*
   *fb-boolean-is-lte-const-prime*)
  :enable (fb-boolean-is-lte-const-gadget
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb-boolean-assert-lte-const-sample
  (r1cs::r1cs-constraints-holdp
   (fb-boolean-assert-lte-const-gadget '(b0 b1) '(0 1) '(r)
                                       *fb-boolean-is-lte-const-prime*)
   *fb-boolean-is-lte-const-asg*
   *fb-boolean-is-lte-const-prime*)
  :enable (fb-boolean-assert-lte-const-gadget
           bits-lte-const-check-gadget
           bits-lte-const-check-rlen
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))
