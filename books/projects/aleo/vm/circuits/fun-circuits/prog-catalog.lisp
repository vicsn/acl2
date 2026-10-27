; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remaining program-crate circuit functions, smallest wrappers first.
; A gadget whose body is nil and whose :short says the constraints are not
; expanded is intentionally incomplete: its R1CS-SPEC flag is 0.
; Funspec-match lemmas are unconditional equalities of the specifications.

(in-package "ALEOVM")

(include-book "prog-primitives")
(include-book "prog-equal")
(include-book "field-zero-r1cs")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/values-value")
(include-book "../fun-specs/values-cast")
(include-book "../fun-specs/values-plaintext")
(include-book "../fun-specs/crypto-record")
(include-book "../fun-specs/crypto-request")
(include-book "../fun-specs/crypto-response")
(include-book "../fun-specs/crypto-state-path")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compute-function-id-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "to_bits_le of the tuple, then BHP1024. Hash abstracted; bit constraints not expanded."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled argument-is-not-equal-funspecs-match
  (implies (and (bitp (argument-is-equal x y)))
           (equal (argument-is-not-equal x y)
                  (boolean-not-funspec (argument-is-equal x y))))
  :hints (("Goal"
           :cases ((values-argument-equalp x y))
           :in-theory (enable argument-is-not-equal argument-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define argument-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean::cast is cast_lossy, except IdentifierLiteral which casts through Field and always fails."
  nil)

(defruled boolean-cast-funspecs-match
  (equal (boolean-cast b to) (if (literal-type-case to :identifier) (field-cast (bfix b) to) (boolean-cast-lossy b to)))
  :enable boolean-cast)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean::cast_lossy is a ternary between generator/one and zero. No range assert."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define crypto-ciphertext-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-ciphertext-is-not-equal-funspecs-match
  (equal (crypto-ciphertext-is-not-equal a b) (boolean-not-funspec (crypto-ciphertext-is-equal a b)))
  :hints (("Goal"
           :cases ((equal (crypto-ciphertext-is-equal a b) 0))
           :in-theory (enable crypto-ciphertext-is-not-equal
                              crypto-bit-not
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-ciphertext-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-future-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-from-record-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-merkleize-data-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled dynamic-record-is-not-equal-funspecs-match
  (equal (dynamic-record-is-not-equal x y) (boolean-not-funspec (dynamic-record-is-equal x y)))
  :hints (("Goal"
           :cases ((equal (dynamic-record-is-equal x y) 0))
           :in-theory (enable dynamic-record-is-not-equal
                              values-b-not
                              boolean-not-funspec
                              bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dynamic-record-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-fields-with-visibility-as-mode-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-write-bits-le-with-visibility-as-mode-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled entry-is-not-equal-funspecs-match
  (implies (and (bitp (entry-is-equal x y)))
           (equal (entry-is-not-equal x y)
                  (boolean-not-funspec (entry-is-equal x y))))
  :hints (("Goal"
           :cases ((values-entry-equalp x y))
           :in-theory (enable entry-is-not-equal entry-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::cast to Boolean: is_zero, is_one, OR, assert.
; The is_one boolean is the result (linear combination 1 - r-o).
; Other destinations of Field::cast are not this gadget; field-cast-gadget
; stays nil and the catalog row stays at 0.

(define field-cast-to-boolean-gadget ((x symbolp)
                                      (m-z symbolp)
                                      (r-z symbolp)
                                      (m-o symbolp)
                                      (r-o symbolp)
                                      (or-bit symbolp)
                                      (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::cast') to @('Boolean'): @('is_zero'),
          @('is_one'), the OR of those bits, and assert of the OR."
  (append (field-is-zero-gadget x m-z r-z p)
          (field-is-one-gadget x m-o r-o p)
          (prog-demorgan-or-gadget r-z r-o or-bit p)
          (prog-assert-gadget or-bit)))

(defruled field-cast-boolean-of-bit
  (implies (and (fieldp x)
                (bitp x))
           (equal (field-cast x (literal-type-boolean))
                  (literal-boolean x)))
  :hints (("Goal"
           :in-theory (enable field-cast
                              values-field-fix-when-fieldp
                              values-literal-type-integerp
                              bitp))))

(defruled field-cast-to-boolean-from-checks
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp rz)
                (bitp ro)
                (bitp orb)
                (equal (pfield::sub 1 rz p) (field-is-zero-funspec x))
                (equal (pfield::sub 1 ro p) (field-is-one-funspec x))
                (equal (pfield::mul rz ro p) (pfield::sub 1 orb p))
                (equal orb 1))
           (equal (field-cast x (literal-type-boolean))
                  (literal-boolean (pfield::sub 1 ro p))))
  :hints (("Goal"
           :cases ((equal x 0)
                   (equal x 1)
                   (equal rz 0)
                   (equal ro 0))
           :in-theory (e/d (field-is-zero-funspec
                            field-is-one-funspec
                            field-is-equal-funspec
                            field-is-not-equal-funspec
                            boolean-not-funspec
                            field-cast-boolean-of-bit
                            bitp
                            pfield::sub
                            pfield::mul
                            crypto-fieldp-of-0
                            crypto-fieldp-of-1)
                           ()))))

(defruled field-cast-to-boolean-gadget-sound
  (implies (and (symbolp x) (symbolp m-z) (symbolp r-z)
                (symbolp m-o) (symbolp r-o) (symbolp or-bit)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m-z)
                (r1cs::valuation-bindsp asg r-z)
                (r1cs::valuation-bindsp asg m-o)
                (r1cs::valuation-bindsp asg r-o)
                (r1cs::valuation-bindsp asg or-bit)
                (fieldp (lookup-equal x asg))
                (bitp (lookup-equal r-z asg))
                (bitp (lookup-equal r-o asg))
                (bitp (lookup-equal or-bit asg))
                (r1cs::r1cs-constraints-holdp
                 (field-cast-to-boolean-gadget
                  x m-z r-z m-o r-o or-bit p)
                 asg p))
           (equal (field-cast (lookup-equal x asg) (literal-type-boolean))
                  (literal-boolean
                   (pfield::sub 1 (lookup-equal r-o asg) p))))
  :hints (("Goal"
           :use ((:instance field-is-zero-gadget-sound (m m-z) (r r-z))
                 (:instance field-is-one-gadget-sound (m m-o) (r r-o))
                 (:instance prog-demorgan-or-gadget-to-mul
                            (x r-z) (y r-o) (z or-bit))
                 (:instance prog-assert-gadget-to-funspec (b or-bit))
                 (:instance field-cast-to-boolean-from-checks
                            (x (lookup-equal x asg))
                            (rz (lookup-equal r-z asg))
                            (ro (lookup-equal r-o asg))
                            (orb (lookup-equal or-bit asg))))
           :in-theory '(field-cast-to-boolean-gadget
                        r1cs::r1cs-constraints-holdp-of-append
                        assert-funspec
                        enforce-funspec
                        bitp
                        (:e base-prime)
                        (:e pfield::mul)
                        (:e pfield::sub)
                        primes::primep-of-bls12-377-scalar-field-prime-constant))))

(defruled field-cast-to-boolean-or-product
  (implies (and (equal p (base-prime))
                (bitp x)
                (equal rz (if (equal x 0) 0 1))
                (equal ro (if (equal x 1) 0 1))
                (equal orb 1))
           (equal (pfield::mul rz ro p)
                  (pfield::sub 1 orb p)))
  :hints (("Goal"
           :cases ((equal x 0))
           :in-theory (e/d (bitp pfield::mul pfield::sub) ()))))

(defruled field-cast-to-boolean-gadget-complete
  :short "Completeness for a field that is already 0 or 1.
          Multipliers are snarkVM's: 1 when the difference has no inverse."
  (implies (and (symbolp x) (symbolp m-z) (symbolp r-z)
                (symbolp m-o) (symbolp r-o) (symbolp or-bit)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg m-z)
                (r1cs::valuation-bindsp asg r-z)
                (r1cs::valuation-bindsp asg m-o)
                (r1cs::valuation-bindsp asg r-o)
                (r1cs::valuation-bindsp asg or-bit)
                (fieldp (lookup-equal x asg))
                (bitp (lookup-equal x asg))
                (equal (lookup-equal r-z asg)
                       (if (equal (lookup-equal x asg) 0) 0 1))
                (equal (lookup-equal m-z asg)
                       (if (equal (lookup-equal x asg) 0)
                           1
                         (pfield::inv (lookup-equal x asg) p)))
                (equal (lookup-equal r-o asg)
                       (if (equal (lookup-equal x asg) 1) 0 1))
                (equal (lookup-equal m-o asg)
                       (if (equal (lookup-equal x asg) 1)
                           1
                         (pfield::inv (pfield::sub (lookup-equal x asg) 1 p)
                                      p)))
                (equal (lookup-equal or-bit asg) 1))
           (and (r1cs::r1cs-constraints-holdp
                 (field-cast-to-boolean-gadget
                  x m-z r-z m-o r-o or-bit p)
                 asg p)
                (equal (field-cast (lookup-equal x asg) (literal-type-boolean))
                       (literal-boolean (lookup-equal x asg)))))
  :hints (("Goal"
           :in-theory (e/d (field-cast-to-boolean-gadget
                            field-is-zero-gadget-to-spec
                            field-is-one-gadget-to-spec
                            prog-demorgan-or-gadget-to-mul
                            prog-assert-gadget-to-funspec
                            assert-funspec
                            enforce-funspec
                            field-cast-boolean-of-bit
                            field-is-not-equal-funspec
                            crypto-fieldp-of-1
                            bitp
                            fieldp
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance prog-field-zero-neq-constraints-when-witness
                            (x (lookup-equal x asg))
                            (m (lookup-equal m-z asg))
                            (r (lookup-equal r-z asg))
                            (p p))
                 (:instance prog-field-neq-constraints-when-witness
                            (x (lookup-equal x asg))
                            (y 1)
                            (m (lookup-equal m-o asg))
                            (r (lookup-equal r-o asg))
                            (p p))
                 (:instance field-cast-to-boolean-or-product
                            (x (lookup-equal x asg))
                            (rz (lookup-equal r-z asg))
                            (ro (lookup-equal r-o asg))
                            (orb (lookup-equal or-bit asg))
                            (p p))))))

(defconst *field-cast-to-boolean-sample-asg*
  '((x . 1) (m-z . 1) (r-z . 1) (m-o . 1) (r-o . 0) (or-bit . 1)))

(defruled field-cast-to-boolean-sample-holds
  :short "Sample cast of @('1') to boolean over the prime 5."
  (r1cs::r1cs-constraints-holdp
   (field-cast-to-boolean-gadget 'x 'm-z 'r-z 'm-o 'r-o 'or-bit 5)
   *field-cast-to-boolean-sample-asg*
   5)
  :enable (field-cast-to-boolean-gadget
           field-is-zero-gadget
           field-is-one-gadget
           prog-demorgan-or-gadget
           prog-assert-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal))

(define field-cast-to-boolean-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "field_cast_to_boolean(x, mz, rz, mo, ro, orbit) := {
    (x) * (mz) == (rz),
    (x) * (1 - rz) == (0),
    (x - 1) * (mo) == (ro),
    (x - 1) * (1 - ro) == (0),
    (rz) * (ro) == (1 - orbit),
    (orbit) * (1) == (1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (field-cast-to-boolean-circuit)
            :pred field-cast-to-boolean-pred
            :prime prime)

(defruled field-cast-to-boolean-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (pfield::fep mz prime)
                (bitp rz)
                (pfield::fep mo prime)
                (bitp ro)
                (bitp orbit)
                (field-cast-to-boolean-pred x mz rz mo ro orbit prime))
           (equal (field-cast x (literal-type-boolean))
                  (literal-boolean (pfield::sub 1 ro prime))))
  :enable (field-cast-to-boolean-pred
           field-is-zero-bit-when-constraints
           field-is-one-bit-when-constraints
           field-cast-to-boolean-from-checks))

(define field-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Field::cast dispatches on the destination. The Boolean destination
          is @('field-cast-to-boolean-gadget'). Integer, scalar, address,
          group, and identifier destinations are not expanded, so this body
          stays nil and the catalog row stays at 0."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Field::cast_lossy takes the low bits, the LSB, or Elligator2 / the subgroup point. No ordering constraint beyond the unique subgroup point."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled future-is-not-equal-funspecs-match
  (implies (and (bitp (future-is-equal x y)))
           (equal (future-is-not-equal x y)
                  (boolean-not-funspec (future-is-equal x y))))
  :hints (("Goal"
           :cases ((values-future-equalp x y))
           :in-theory (enable future-is-not-equal future-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define future-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define header-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define header-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled identifier-from-bits-be-funspecs-match
  (equal (identifier-from-bits-be bits) (identifier-from-bits-le (rev bits)))
  :enable identifier-from-bits-be)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-from-field-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled identifier-from-field-funspecs-match
  (equal (identifier-from-field x) (identifier-from-bits-le (values-field-to-bits-le x)))
  :enable identifier-from-field)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-literal-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "IdentifierLiteral::cast is to_field then Field::cast."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-input-id-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Integer::cast goes through to_field, which asserts the value is in range, then Field::cast."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Integer::cast_lossy truncates or sign-extends, then Field::cast_lossy for address and group."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-from-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-from-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled literal-is-not-equal-funspecs-match
  (implies (and (bitp (literal-is-equal x y)))
           (equal (literal-is-not-equal x y)
                  (boolean-not-funspec (literal-is-equal x y))))
  :hints (("Goal"
           :cases ((values-literal-equalp x y))
           :in-theory (enable literal-is-not-equal literal-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define crypto-owner-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-to-entry-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-owner-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-symmetric-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-encrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-from-bit-array-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define plaintext-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Forwards to size_in_fields."
  nil)

(defruled plaintext-num-randomizers-funspecs-match
  (equal (plaintext-num-randomizers pt) (plaintext-size-in-fields pt))
  :enable plaintext-num-randomizers)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled plaintext-is-not-equal-funspecs-match
  (implies (and (bitp (plaintext-is-equal x y)))
           (equal (plaintext-is-not-equal x y)
                  (boolean-not-funspec (plaintext-is-equal x y))))
  :hints (("Goal"
           :cases ((values-plaintext-equalp x y))
           :in-theory (enable plaintext-is-not-equal plaintext-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define plaintext-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Returns the OnceCell cache when the plaintext was built by from_bits; otherwise recomputes. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Returns the OnceCell cache when the plaintext was built by from_bits; otherwise recomputes. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Packs to_bits_le, so a cached raw bitstring is packed instead of the recomputed encoding."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-to-fields-raw-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Packs raw literal bits. Does not use the from_bits cache."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plaintext-size-in-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Host u16, ceiling of (len(to_bits_le)+1)/252. The length follows the cache."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-id-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define crypto-record-encrypt-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-record-encrypt-funspecs-match
  (equal (crypto-record-encrypt r randomizer) (b* (((fty::ok res) (crypto-record-encrypt-symmetric r randomizer))) (crypto-ciphertext-record-fix (first res))))
  :enable crypto-record-encrypt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-symmetric-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-symmetric-unchecked-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-encrypt-with-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-num-randomizers-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-serial-number-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-serial-number-from-gamma-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-to-commitment-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled crypto-record-is-not-equal-funspecs-match
  (equal (crypto-record-is-not-equal a b) (boolean-not-funspec (crypto-record-is-equal a b)))
  :hints (("Goal"
           :cases ((equal (crypto-record-is-equal a b) 0))
           :in-theory (enable crypto-record-is-not-equal
                              crypto-bit-not
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-record-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-check-input-ids-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Per-input equality and hash checks. Hash and encryption abstracted."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-to-tpk-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Group scalar multiplication and addition. Edwards formulas are not expanded here."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-verify-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Boolean conjunction of input-id, root, and checksum checks. Hashes abstracted."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-request-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-response-from-outputs-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Per-output hash (abstract) and OutputID constructors, including the record disjunction."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-response-process-outputs-from-callback-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Same family as from_outputs, with the callback record id."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-cast-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Scalar::cast asserts 0 or 1 for boolean and a bit-width bound for integers."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scalar-cast-lossy-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Scalar::cast_lossy takes the low bits. Address and group use Field::cast_lossy."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crypto-state-path-verify-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Merkle path checks (BHP/PSD abstracted) conjoined with boolean ANDs."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transaction-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transaction-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transition-leaf-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transition-leaf-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-find-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-is-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-is-not-equal-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

(defruled value-is-not-equal-funspecs-match
  (implies (and (bitp (value-is-equal x y)))
           (equal (value-is-not-equal x y)
                  (boolean-not-funspec (value-is-equal x y))))
  :hints (("Goal"
           :cases ((values-value-equalp x y))
           :in-theory (enable value-is-not-equal value-is-equal
                              values-bool-to-bit
                              boolean-not-funspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-fields-raw-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of this program-crate function are not fully expanded in this book. See bugs-prog.txt."
  nil)
