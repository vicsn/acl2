; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Collections circuits.
;
; BHP / Keccak / Poseidon hash internals are not expanded.  hash_children
; and hash_empty are exactly the funspec's call of the abstract hash on
; the prepended input (a constant true bit, or 1field, or VARIANT output
; bits).  Those functions add no constraint besides the hash.
;
; BooleanHash::new is a boolean check per bit.
; is_equal is xor per bit (boolean not of the xor is the equality bit,
; a linear combination) folded with AND.
; ternary is the boolean if-gadget per bit.
; MerklePath::new / KaryMerklePath::new host-check lengths.
; MerklePath::verify orders children with boolean not of the index bit
; (a linear combination) and Field::ternary, hashes (abstract), then
; Field::is_equal.

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "../fun-specs/crypto-merkle")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/if")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *val-collections-empty-sample* nil)

(defruled val-collections-empty-sample-holds
  (r1cs::r1cs-constraints-holdp nil *val-collections-empty-sample* (base-prime))
  :enable r1cs::r1cs-constraints-holdp)

(define bhp-hash-children-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "BHP PathHash::hash_children prepends a constant true bit and hashes.
          The hash constraints are the abstract BHP hash."
  nil)

(defruled bhp-hash-children-gadget-sound
  (implies (and (crypto-hasher-p ph)
                (equal (car ph) :bhp)
                (crypto-merkle-hash-list-p ph children)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (bhp-hash-children-gadget) asg p))
           (equal (crypto-merkle-hash-children ph children)
                  (crypto-hash-bhp (cdr ph)
                                  (cons 1 (crypto-merkle-hash-list-bits ph children)))))
  :enable (bhp-hash-children-gadget
           crypto-merkle-hash-children
           r1cs::r1cs-constraints-holdp))

(defruled bhp-hash-children-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (bhp-hash-children-gadget) asg p))
  :enable bhp-hash-children-gadget)

(defconst *bhp-hash-children-sample* *val-collections-empty-sample*)

(defruled bhp-hash-children-sample-holds
  (r1cs::r1cs-constraints-holdp (bhp-hash-children-gadget)
                                *bhp-hash-children-sample*
                                (base-prime))
  :enable (bhp-hash-children-gadget val-collections-empty-sample-holds))

(define bhp-hash-children-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "bhp_hash_children() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (bhp-hash-children-circuit)
            :pred bhp-hash-children-pred
            :prime prime)

(defruled bhp-hash-children-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (crypto-hasher-p ph)
                (equal (car ph) :bhp)
                (bhp-hash-children-pred prime))
           (equal (crypto-merkle-hash-children ph children)
                  (crypto-hash-bhp (cdr ph)
                                  (cons 1 (crypto-merkle-hash-list-bits ph children)))))
  :enable (bhp-hash-children-pred crypto-merkle-hash-children))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keccak-hash-children-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Keccak PathHash::hash_children prepends true and keeps VARIANT bits.
          Keccak itself is abstract."
  nil)

(defruled keccak-hash-children-gadget-sound
  (implies (and (crypto-hasher-p ph)
                (equal (car ph) :keccak)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (keccak-hash-children-gadget) asg p))
           (equal (crypto-merkle-hash-children ph children)
                  (crypto-keccak-truncate
                   (crypto-hash-keccak (cadr ph)
                                      (cons 1 (crypto-merkle-hash-list-bits ph children)))
                   (crypto-keccak-variant ph))))
  :enable (keccak-hash-children-gadget
           crypto-merkle-hash-children
           r1cs::r1cs-constraints-holdp))

(defruled keccak-hash-children-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (keccak-hash-children-gadget) asg p))
  :enable keccak-hash-children-gadget)

(defconst *keccak-hash-children-sample* *val-collections-empty-sample*)

(defruled keccak-hash-children-sample-holds
  (r1cs::r1cs-constraints-holdp (keccak-hash-children-gadget)
                                *keccak-hash-children-sample*
                                (base-prime))
  :enable (keccak-hash-children-gadget val-collections-empty-sample-holds))

(define keccak-hash-children-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "keccak_hash_children() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (keccak-hash-children-circuit)
            :pred keccak-hash-children-pred
            :prime prime)

(defruled keccak-hash-children-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (crypto-hasher-p ph)
                (equal (car ph) :keccak)
                (keccak-hash-children-pred prime))
           (equal (crypto-merkle-hash-children ph children)
                  (crypto-keccak-truncate
                   (crypto-hash-keccak (cadr ph)
                                      (cons 1 (crypto-merkle-hash-list-bits ph children)))
                   (crypto-keccak-variant ph))))
  :enable (keccak-hash-children-pred crypto-merkle-hash-children))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kary-hash-empty-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "PathHash::hash_empty hashes ARITY default hashes.  No local constraint."
  nil)

(defruled kary-hash-empty-gadget-sound
  (implies (and (crypto-hasher-p ph)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (kary-hash-empty-gadget) asg p))
           (equal (crypto-kary-merkle-hash-empty ph arity)
                  (crypto-merkle-hash-children
                   ph (repeat arity (crypto-merkle-hash-default ph)))))
  :enable (kary-hash-empty-gadget
           crypto-kary-merkle-hash-empty
           r1cs::r1cs-constraints-holdp))

(defruled kary-hash-empty-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (kary-hash-empty-gadget) asg p))
  :enable kary-hash-empty-gadget)

(defconst *kary-hash-empty-sample* *val-collections-empty-sample*)

(defruled kary-hash-empty-sample-holds
  (r1cs::r1cs-constraints-holdp (kary-hash-empty-gadget)
                                *kary-hash-empty-sample*
                                (base-prime))
  :enable (kary-hash-empty-gadget val-collections-empty-sample-holds))

(define kary-hash-empty-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "kary_hash_empty() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (kary-hash-empty-circuit)
            :pred kary-hash-empty-pred
            :prime prime)

(defruled kary-hash-empty-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (crypto-hasher-p ph)
                (kary-hash-empty-pred prime))
           (equal (crypto-kary-merkle-hash-empty ph arity)
                  (crypto-merkle-hash-children
                   ph (repeat arity (crypto-merkle-hash-default ph)))))
  :enable (kary-hash-empty-pred crypto-kary-merkle-hash-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-hash-new-gadget ((xs symbol-listp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "BooleanHash::new checks each bit with (1 - x) * x = 0."
  (boolean-check-gadget-list xs p))

(defruled boolean-hash-new-gadget-sound
  (implies (and (symbol-listp xs)
                (natp variant)
                (equal (len xs) variant)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::r1cs-constraints-holdp
                 (boolean-hash-new-gadget xs p) asg p))
           (equal (crypto-boolean-hash-new variant (lookup-equal-list xs asg))
                  (lookup-equal-list xs asg)))
  :enable (boolean-hash-new-gadget
           boolean-check-gadget-list-to-bit-listp
           crypto-boolean-hash-new))

(defruled boolean-hash-new-gadget-complete
  (implies (and (symbol-listp xs)
                (natp variant)
                (equal (len xs) variant)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg)))
           (r1cs::r1cs-constraints-holdp
            (boolean-hash-new-gadget xs p) asg p))
  :enable (boolean-hash-new-gadget
           boolean-check-gadget-list-to-bit-listp))

(defconst *boolean-hash-new-sample* '((b . 1)))

(defruled boolean-hash-new-sample-holds
  (r1cs::r1cs-constraints-holdp
   (boolean-hash-new-gadget '(b) (base-prime))
   *boolean-hash-new-sample*
   (base-prime))
  :enable (boolean-hash-new-gadget
           boolean-check-gadget-list
           boolean-check-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define boolean-hash-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "boolean_hash_new(b) := {
    (1 - b) * (b) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (boolean-hash-new-circuit)
            :pred boolean-hash-new-pred
            :prime prime)

(defruled boolean-hash-new-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b)
                (boolean-hash-new-pred b prime))
           (equal (crypto-boolean-hash-new 1 (list b))
                  (list b)))
  :enable (boolean-hash-new-pred crypto-boolean-hash-new))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two-bit BooleanHash::is_equal.  Each xor witness z, equality bits are
; 1 - z (linear combinations), folded by one AND.

(define boolean-hash-is-equal-gadget ((a0 symbolp) (a1 symbolp)
                                     (b0 symbolp) (b1 symbolp)
                                     (z0 symbolp) (z1 symbolp)
                                     (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-xor-gadget a0 b0 z0 p)
          (boolean-xor-gadget a1 b1 z1 p)
          (val-and-nots-gadget z0 z1 out p)))

(defruled boolean-hash-is-equal-gadget-sound
  (implies (and (symbolp a0) (symbolp a1) (symbolp b0) (symbolp b1)
                (symbolp z0) (symbolp z1) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal a0 asg))
                (bitp (lookup-equal a1 asg))
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-hash-is-equal-gadget a0 a1 b0 b1 z0 z1 out p) asg p))
           (equal (lookup-equal out asg)
                  (crypto-boolean-hash-is-equal
                   (list (lookup-equal a0 asg) (lookup-equal a1 asg))
                   (list (lookup-equal b0 asg) (lookup-equal b1 asg)))))
  :enable (boolean-hash-is-equal-gadget
           boolean-xor-gadget-to-bitxor
           val-and-nots-gadget-to-spec
           crypto-boolean-hash-is-equal
           values-b-not
           bitxor))

(defruled boolean-hash-is-equal-gadget-complete
  (implies (and (symbolp a0) (symbolp a1) (symbolp b0) (symbolp b1)
                (symbolp z0) (symbolp z1) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal a0 asg))
                (bitp (lookup-equal a1 asg))
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (equal (lookup-equal z0 asg)
                       (bitxor (lookup-equal a0 asg) (lookup-equal b0 asg)))
                (equal (lookup-equal z1 asg)
                       (bitxor (lookup-equal a1 asg) (lookup-equal b1 asg)))
                (equal (lookup-equal out asg)
                       (pfield::mul (pfield::sub 1 (lookup-equal z0 asg) p)
                                    (pfield::sub 1 (lookup-equal z1 asg) p)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (boolean-hash-is-equal-gadget a0 a1 b0 b1 z0 z1 out p) asg p))
  :enable (boolean-hash-is-equal-gadget
           boolean-xor-gadget-to-bitxor
           val-and-nots-gadget-to-spec))

(defconst *boolean-hash-is-equal-sample*
  '((a0 . 1) (a1 . 0) (b0 . 1) (b1 . 0) (z0 . 0) (z1 . 0) (out . 1)))

(defruled boolean-hash-is-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (boolean-hash-is-equal-gadget 'a0 'a1 'b0 'b1 'z0 'z1 'out (base-prime))
   *boolean-hash-is-equal-sample*
   (base-prime))
  :enable (boolean-hash-is-equal-gadget
           boolean-xor-gadget
           val-and-nots-gadget
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define boolean-hash-is-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "boolean_hash_is_equal(a0, a1, b0, b1, z0, z1, out) := {
    (2 * a0) * (b0) == (a0 + b0 - z0),
    (2 * a1) * (b1) == (a1 + b1 - z1),
    (1 - z0) * (1 - z1) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (boolean-hash-is-equal-circuit)
            :pred boolean-hash-is-equal-pred
            :prime prime)

(defruled boolean-hash-is-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp a0) (bitp a1) (bitp b0) (bitp b1)
                (bitp z0) (bitp z1) (bitp out)
                (equal z0 (bitxor a0 b0))
                (equal z1 (bitxor a1 b1))
                (boolean-hash-is-equal-pred a0 a1 b0 b1 z0 z1 out prime))
           (equal out (crypto-boolean-hash-is-equal (list a0 a1) (list b0 b1))))
  :enable (boolean-hash-is-equal-pred
           crypto-boolean-hash-is-equal
           bitxor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-hash-is-not-equal-gadget ((a0 symbolp) (a1 symbolp)
                                         (b0 symbolp) (b1 symbolp)
                                         (z0 symbolp) (z1 symbolp)
                                         (out symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "is_not_equal is boolean not of is_equal, the linear combination 1 - out."
  (boolean-hash-is-equal-gadget a0 a1 b0 b1 z0 z1 out p))

(defruled boolean-hash-is-not-equal-gadget-sound
  (implies (and (symbolp a0) (symbolp a1) (symbolp b0) (symbolp b1)
                (symbolp z0) (symbolp z1) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal a0 asg))
                (bitp (lookup-equal a1 asg))
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (bitp (lookup-equal out asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-hash-is-not-equal-gadget a0 a1 b0 b1 z0 z1 out p)
                 asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (crypto-boolean-hash-is-not-equal
                   (list (lookup-equal a0 asg) (lookup-equal a1 asg))
                   (list (lookup-equal b0 asg) (lookup-equal b1 asg)))))
  :enable (boolean-hash-is-not-equal-gadget
           boolean-hash-is-equal-gadget-sound
           crypto-boolean-hash-is-not-equal))

(defruled boolean-hash-is-not-equal-gadget-complete
  (implies (and (symbolp a0) (symbolp a1) (symbolp b0) (symbolp b1)
                (symbolp z0) (symbolp z1) (symbolp out)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg z0)
                (r1cs::valuation-bindsp asg z1)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal a0 asg))
                (bitp (lookup-equal a1 asg))
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal b1 asg))
                (equal (lookup-equal z0 asg)
                       (bitxor (lookup-equal a0 asg) (lookup-equal b0 asg)))
                (equal (lookup-equal z1 asg)
                       (bitxor (lookup-equal a1 asg) (lookup-equal b1 asg)))
                (equal (lookup-equal out asg)
                       (pfield::mul (pfield::sub 1 (lookup-equal z0 asg) p)
                                    (pfield::sub 1 (lookup-equal z1 asg) p)
                                    p)))
           (r1cs::r1cs-constraints-holdp
            (boolean-hash-is-not-equal-gadget a0 a1 b0 b1 z0 z1 out p) asg p))
  :enable (boolean-hash-is-not-equal-gadget
           boolean-hash-is-equal-gadget-complete))

(defconst *boolean-hash-is-not-equal-sample* *boolean-hash-is-equal-sample*)

(defruled boolean-hash-is-not-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (boolean-hash-is-not-equal-gadget 'a0 'a1 'b0 'b1 'z0 'z1 'out (base-prime))
   *boolean-hash-is-not-equal-sample*
   (base-prime))
  :enable (boolean-hash-is-not-equal-gadget
           boolean-hash-is-equal-sample-holds))

(define boolean-hash-is-not-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "boolean_hash_is_not_equal(a0, a1, b0, b1, z0, z1, out) := {
    (2 * a0) * (b0) == (a0 + b0 - z0),
    (2 * a1) * (b1) == (a1 + b1 - z1),
    (1 - z0) * (1 - z1) == (out)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (boolean-hash-is-not-equal-circuit)
            :pred boolean-hash-is-not-equal-pred
            :prime prime)

(defruled boolean-hash-is-not-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp a0) (bitp a1) (bitp b0) (bitp b1)
                (bitp z0) (bitp z1) (bitp out)
                (equal z0 (bitxor a0 b0))
                (equal z1 (bitxor a1 b1))
                (boolean-hash-is-not-equal-pred a0 a1 b0 b1 z0 z1 out prime))
           (equal (pfield::sub 1 out prime)
                  (crypto-boolean-hash-is-not-equal (list a0 a1) (list b0 b1))))
  :enable (boolean-hash-is-not-equal-pred
           crypto-boolean-hash-is-not-equal
           crypto-boolean-hash-is-equal
           bitxor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-hash-ternary-gadget ((c symbolp)
                                    (a0 symbolp) (b0 symbolp) (w0 symbolp)
                                    (a1 symbolp) (b1 symbolp) (w1 symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (if-gadget c a0 b0 w0 p)
          (if-gadget c a1 b1 w1 p)))

(defruled boolean-hash-ternary-gadget-sound
  (implies (and (symbolp c) (symbolp a0) (symbolp b0) (symbolp w0)
                (symbolp a1) (symbolp b1) (symbolp w1)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg w0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg w1)
                (bitp (lookup-equal c asg))
                (bitp (lookup-equal a0 asg))
                (bitp (lookup-equal b0 asg))
                (bitp (lookup-equal a1 asg))
                (bitp (lookup-equal b1 asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-hash-ternary-gadget c a0 b0 w0 a1 b1 w1 p) asg p))
           (equal (list (lookup-equal w0 asg) (lookup-equal w1 asg))
                  (crypto-boolean-hash-ternary
                   (lookup-equal c asg)
                   (list (lookup-equal a0 asg) (lookup-equal a1 asg))
                   (list (lookup-equal b0 asg) (lookup-equal b1 asg)))))
  :enable (boolean-hash-ternary-gadget
           if-gadget-to-if
           crypto-boolean-hash-ternary))

(defruled boolean-hash-ternary-gadget-complete
  (implies (and (symbolp c) (symbolp a0) (symbolp b0) (symbolp w0)
                (symbolp a1) (symbolp b1) (symbolp w1)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-bindsp asg a0)
                (r1cs::valuation-bindsp asg b0)
                (r1cs::valuation-bindsp asg w0)
                (r1cs::valuation-bindsp asg a1)
                (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg w1)
                (bitp (lookup-equal c asg))
                (equal (lookup-equal w0 asg)
                       (if (equal (lookup-equal c asg) 1)
                           (lookup-equal a0 asg)
                         (lookup-equal b0 asg)))
                (equal (lookup-equal w1 asg)
                       (if (equal (lookup-equal c asg) 1)
                           (lookup-equal a1 asg)
                         (lookup-equal b1 asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-hash-ternary-gadget c a0 b0 w0 a1 b1 w1 p) asg p))
  :enable (boolean-hash-ternary-gadget if-gadget-to-if))

(defconst *boolean-hash-ternary-sample*
  '((c . 1) (a0 . 1) (b0 . 0) (w0 . 1) (a1 . 0) (b1 . 1) (w1 . 0)))

(defruled boolean-hash-ternary-sample-holds
  (r1cs::r1cs-constraints-holdp
   (boolean-hash-ternary-gadget 'c 'a0 'b0 'w0 'a1 'b1 'w1 (base-prime))
   *boolean-hash-ternary-sample*
   (base-prime))
  :enable (boolean-hash-ternary-gadget
           if-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define boolean-hash-ternary-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "boolean_hash_ternary(c, a0, b0, w0, a1, b1, w1) := {
    (c) * (a0 - b0) == (w0 - b0),
    (c) * (a1 - b1) == (w1 - b1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (boolean-hash-ternary-circuit)
            :pred boolean-hash-ternary-pred
            :prime prime)

(defruled boolean-hash-ternary-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp c) (bitp a0) (bitp b0) (bitp a1) (bitp b1)
                (pfield::fep w0 prime) (pfield::fep w1 prime)
                (boolean-hash-ternary-pred c a0 b0 w0 a1 b1 w1 prime))
           (equal (list w0 w1)
                  (crypto-boolean-hash-ternary c (list a0 a1) (list b0 b1))))
  :enable (boolean-hash-ternary-pred crypto-boolean-hash-ternary))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define merkle-path-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "MerklePath::new host-checks the sibling count.  No R1CS constraint."
  nil)

(defruled merkle-path-new-gadget-sound
  (implies (and (natp depth)
                (natp leaf-index)
                (crypto-field-listp siblings)
                (equal (len siblings) depth)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (merkle-path-new-gadget) asg p))
           (equal (crypto-merkle-path-new depth leaf-index siblings)
                  (list leaf-index siblings)))
  :enable (merkle-path-new-gadget
           crypto-merkle-path-new
           r1cs::r1cs-constraints-holdp))

(defruled merkle-path-new-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (merkle-path-new-gadget) asg p))
  :enable merkle-path-new-gadget)

(defconst *merkle-path-new-sample* *val-collections-empty-sample*)

(defruled merkle-path-new-sample-holds
  (r1cs::r1cs-constraints-holdp (merkle-path-new-gadget)
                                *merkle-path-new-sample*
                                (base-prime))
  :enable (merkle-path-new-gadget val-collections-empty-sample-holds))

(define merkle-path-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "merkle_path_new() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (merkle-path-new-circuit)
            :pred merkle-path-new-pred
            :prime prime)

(defruled merkle-path-new-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (natp depth)
                (equal (len siblings) depth)
                (merkle-path-new-pred prime))
           (equal (crypto-merkle-path-new depth leaf-index siblings)
                  (list leaf-index siblings)))
  :enable (merkle-path-new-pred crypto-merkle-path-new))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kary-merkle-path-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled kary-merkle-path-new-gadget-sound
  (implies (and (natp depth) (natp arity) (natp leaf-index)
                (true-listp siblings)
                (crypto-kary-levels-have-len (nfix (- (nfix arity) 1)) siblings)
                (equal (len siblings) depth)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp
                 (kary-merkle-path-new-gadget) asg p))
           (equal (crypto-kary-merkle-path-new depth arity leaf-index siblings)
                  (list leaf-index siblings)))
  :enable (kary-merkle-path-new-gadget
           crypto-kary-merkle-path-new
           r1cs::r1cs-constraints-holdp))

(defruled kary-merkle-path-new-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (kary-merkle-path-new-gadget) asg p))
  :enable kary-merkle-path-new-gadget)

(defconst *kary-merkle-path-new-sample* *val-collections-empty-sample*)

(defruled kary-merkle-path-new-sample-holds
  (r1cs::r1cs-constraints-holdp (kary-merkle-path-new-gadget)
                                *kary-merkle-path-new-sample*
                                (base-prime))
  :enable (kary-merkle-path-new-gadget val-collections-empty-sample-holds))

(define kary-merkle-path-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "kary_merkle_path_new() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (kary-merkle-path-new-circuit)
            :pred kary-merkle-path-new-pred
            :prime prime)

(defruled kary-merkle-path-new-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (natp depth) (natp arity)
                (crypto-kary-levels-have-len (nfix (- (nfix arity) 1)) siblings)
                (equal (len siblings) depth)
                (kary-merkle-path-new-pred prime))
           (equal (crypto-kary-merkle-path-new depth arity leaf-index siblings)
                  (list leaf-index siblings)))
  :enable (kary-merkle-path-new-pred crypto-kary-merkle-path-new))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One level of MerklePath::verify, plus the final is_equal of root and
; the hash of the ordered children.  The hash is an assumption.

(define merkle-path-verify-gadget ((bit symbolp) (cur symbolp) (sib symbolp)
                                  (left symbolp) (right symbolp)
                                  (root symbolp) (m symbolp) (r symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (merkle-path-left-gadget bit cur sib left p)
          (merkle-path-right-gadget bit cur sib right p)
          (field-var-is-equal-gadget root 'hashed m r p)))

(defruled merkle-path-verify-gadget-sound
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib)
                (symbolp left) (symbolp right)
                (symbolp root) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg left)
                (r1cs::valuation-bindsp asg right)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg 'hashed)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal bit asg))
                (fieldp (lookup-equal cur asg))
                (fieldp (lookup-equal sib asg))
                (fieldp (lookup-equal left asg))
                (fieldp (lookup-equal right asg))
                (fieldp (lookup-equal root asg))
                (fieldp (lookup-equal 'hashed asg))
                (bitp (lookup-equal r asg))
                (crypto-field-hasher-p ph)
                (equal (lookup-equal 'hashed asg)
                       (crypto-merkle-hash-children
                        ph
                        (list (lookup-equal left asg)
                              (lookup-equal right asg))))
                (r1cs::r1cs-constraints-holdp
                 (merkle-path-verify-gadget bit cur sib left right root m r p)
                 asg p))
           (and (equal (lookup-equal left asg)
                       (if (equal (lookup-equal bit asg) 0)
                           (lookup-equal cur asg)
                         (lookup-equal sib asg)))
                (equal (lookup-equal right asg)
                       (if (equal (lookup-equal bit asg) 0)
                           (lookup-equal sib asg)
                         (lookup-equal cur asg)))
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           1
                         0))))
  :enable (merkle-path-verify-gadget
           merkle-path-left-gadget-to-spec
           merkle-path-right-gadget-to-spec
           merkle-path-order-when-bit
           field-var-is-equal-gadget-sound))

(defruled merkle-path-verify-gadget-complete
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib)
                (symbolp left) (symbolp right)
                (symbolp root) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg left)
                (r1cs::valuation-bindsp asg right)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg 'hashed)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal bit asg))
                (fieldp (lookup-equal cur asg))
                (fieldp (lookup-equal sib asg))
                (equal (lookup-equal left asg)
                       (if (equal (lookup-equal bit asg) 0)
                           (lookup-equal cur asg)
                         (lookup-equal sib asg)))
                (equal (lookup-equal right asg)
                       (if (equal (lookup-equal bit asg) 0)
                           (lookup-equal sib asg)
                         (lookup-equal cur asg)))
                (fieldp (lookup-equal root asg))
                (fieldp (lookup-equal 'hashed asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal root asg)
                                                   (lookup-equal 'hashed asg)
                                                   p)
                                      p))))
           (r1cs::r1cs-constraints-holdp
            (merkle-path-verify-gadget bit cur sib left right root m r p)
            asg p))
  :enable (merkle-path-verify-gadget
           merkle-path-left-gadget-to-spec
           merkle-path-right-gadget-to-spec
           field-var-is-equal-gadget-complete))

(defconst *merkle-path-verify-sample*
  ;; index bit 0: left = current = 5, right = sibling = 7.
  ;; hashed = 5, root = 5, so equal, r = 0, m = 0.
  '((bit . 0) (cur . 5) (sib . 7) (left . 5) (right . 7)
    (root . 5) (hashed . 5) (m . 0) (r . 0)))

(defruled merkle-path-verify-sample-holds
  (r1cs::r1cs-constraints-holdp
   (merkle-path-verify-gadget 'bit 'cur 'sib 'left 'right 'root 'm 'r
                             (base-prime))
   *merkle-path-verify-sample*
   (base-prime))
  :enable (merkle-path-verify-gadget
           merkle-path-left-gadget
           merkle-path-right-gadget
           field-var-is-equal-gadget
           val-not-lc
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define merkle-path-verify-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "merkle_path_verify(bit, cur, sib, left, right, root, hashed, m, r) := {
    (cur - sib) * (1 - bit) == (left - sib),
    (sib - cur) * (1 - bit) == (right - cur),
    (root - hashed) * (m) == (r),
    (root - hashed) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (merkle-path-verify-circuit)
            :pred merkle-path-verify-pred
            :prime prime)

(defruled merkle-path-verify-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp bit)
                (fieldp cur) (fieldp sib) (fieldp left) (fieldp right)
                (fieldp root) (fieldp hashed) (bitp r)
                (pfield::fep m prime)
                (merkle-path-verify-pred bit cur sib left right root hashed m r prime))
           (and (equal left (if (equal bit 0) cur sib))
                (equal right (if (equal bit 0) sib cur))
                (equal (pfield::sub 1 r prime)
                       (if (equal root hashed) 1 0))))
  :enable (merkle-path-verify-pred
           field-var-is-equal-bit-when-constraints))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; KaryMerklePath::verify uses the same is_equal finish and abstract hash.
; Child placement is crypto-kary-children; the integer index arithmetic
; (div/mod by the constant arity) is the integer gadget, not re-derived here.
; One ternary places the running hash when the indicator matches.

(define kary-merkle-path-verify-gadget ((bit symbolp)
                                       (cur symbolp) (sib symbolp) (w symbolp)
                                       (root symbolp) (m symbolp) (r symbolp)
                                       (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "One child ternary of KaryMerklePath::verify, plus the root is_equal."
  (append (if-gadget bit cur sib w p)
          (field-var-is-equal-gadget root 'hashed m r p)))

(defruled kary-merkle-path-verify-gadget-sound
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib) (symbolp w)
                (symbolp root) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg 'hashed)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal bit asg))
                (fieldp (lookup-equal root asg))
                (fieldp (lookup-equal 'hashed asg))
                (bitp (lookup-equal r asg))
                (r1cs::r1cs-constraints-holdp
                 (kary-merkle-path-verify-gadget bit cur sib w root m r p)
                 asg p))
           (and (equal (lookup-equal w asg)
                       (if (equal (lookup-equal bit asg) 1)
                           (lookup-equal cur asg)
                         (lookup-equal sib asg)))
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           1 0))))
  :enable (kary-merkle-path-verify-gadget
           if-gadget-to-if
           field-var-is-equal-gadget-sound))

(defruled kary-merkle-path-verify-gadget-complete
  (implies (and (symbolp bit) (symbolp cur) (symbolp sib) (symbolp w)
                (symbolp root) (symbolp m) (symbolp r)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg sib)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg root)
                (r1cs::valuation-bindsp asg 'hashed)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (bitp (lookup-equal bit asg))
                (equal (lookup-equal w asg)
                       (if (equal (lookup-equal bit asg) 1)
                           (lookup-equal cur asg)
                         (lookup-equal sib asg)))
                (fieldp (lookup-equal root asg))
                (fieldp (lookup-equal 'hashed asg))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal root asg)
                                  (lookup-equal 'hashed asg))
                           0
                         (pfield::inv (pfield::sub (lookup-equal root asg)
                                                   (lookup-equal 'hashed asg)
                                                   p)
                                      p))))
           (r1cs::r1cs-constraints-holdp
            (kary-merkle-path-verify-gadget bit cur sib w root m r p) asg p))
  :enable (kary-merkle-path-verify-gadget
           if-gadget-to-if
           field-var-is-equal-gadget-complete))

(defconst *kary-merkle-path-verify-sample*
  '((bit . 1) (cur . 4) (sib . 8) (w . 4)
    (root . 4) (hashed . 4) (m . 0) (r . 0)))

(defruled kary-merkle-path-verify-sample-holds
  (r1cs::r1cs-constraints-holdp
   (kary-merkle-path-verify-gadget 'bit 'cur 'sib 'w 'root 'm 'r (base-prime))
   *kary-merkle-path-verify-sample*
   (base-prime))
  :enable (kary-merkle-path-verify-gadget
           if-gadget
           field-var-is-equal-gadget
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::mul
           pfield::add
           base-prime
           ecurve::edwards-bls12-q
           (:e primes::bls12-377-scalar-field-prime)))

(define kary-merkle-path-verify-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "kary_merkle_path_verify(bit, cur, sib, w, root, hashed, m, r) := {
    (bit) * (cur - sib) == (w - sib),
    (root - hashed) * (m) == (r),
    (root - hashed) * (1 - r) == (0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (kary-merkle-path-verify-circuit)
            :pred kary-merkle-path-verify-pred
            :prime prime)

(defruled kary-merkle-path-verify-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp bit) (fieldp cur) (fieldp sib) (fieldp w)
                (fieldp root) (fieldp hashed) (bitp r)
                (pfield::fep m prime)
                (kary-merkle-path-verify-pred bit cur sib w root hashed m r prime))
           (and (equal w (if (equal bit 1) cur sib))
                (equal (pfield::sub 1 r prime)
                       (if (equal root hashed) 1 0))))
  :enable (kary-merkle-path-verify-pred
           field-var-is-equal-bit-when-constraints))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define merkle-tree-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "MerkleTree::new's constraints are the leaf and path hashes, which
          are abstract.  The tree shape is the funspec."
  nil)

(defruled merkle-tree-new-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (merkle-tree-new-gadget) asg p))
           (equal (crypto-merkle-tree-new lh ph depth leaves)
                  (crypto-merkle-tree-new lh ph depth leaves)))
  :hints (("Goal" :in-theory (enable merkle-tree-new-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled merkle-tree-new-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p))
           (r1cs::r1cs-constraints-holdp (merkle-tree-new-gadget) asg p))
  :enable merkle-tree-new-gadget)

(defconst *merkle-tree-new-sample* *val-collections-empty-sample*)

(defruled merkle-tree-new-sample-holds
  (r1cs::r1cs-constraints-holdp (merkle-tree-new-gadget)
                                *merkle-tree-new-sample*
                                (base-prime))
  :enable (merkle-tree-new-gadget val-collections-empty-sample-holds))

(define merkle-tree-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "merkle_tree_new() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (merkle-tree-new-circuit)
            :pred merkle-tree-new-pred
            :prime prime)

(defruled merkle-tree-new-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (merkle-tree-new-pred prime)
                  (r1cs::r1cs-constraints-holdp (merkle-tree-new-gadget)
                                               nil prime)))
  :enable (merkle-tree-new-pred
           merkle-tree-new-gadget
           r1cs::r1cs-constraints-holdp))
