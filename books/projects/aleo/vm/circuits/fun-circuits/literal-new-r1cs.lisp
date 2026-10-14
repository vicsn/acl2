; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS for snarkVM Literal::new (circuit/program/src/data/literal/mod.rs).
;
; The function is a match.  Each arm is the Inject::new of that variant,
; in variable mode (the mode that emits constraints; constant mode is the
; same predicate, checked by the host):
;
;   Address     Group::new, i.e. enforce_in_group
;   Boolean     one boolean check
;   Field       no constraint
;   Group       enforce_in_group
;   I8..U128    one boolean check per bit; from_bits_le at exact width
;               adds nothing
;   Scalar      Field::new of the scalar, no constraint
;   Signature   two Scalar::new, then ComputeKey::new:
;               Group::new of pk_sig and of pr_sig, then
;               hash_to_scalar_psd4 of the two x-coordinates.
;               The hash is the excluded Poseidon circuit.  Satisfaction
;               uses the abstract values-hash-to-scalar-psd4 equality,
;               the same abstraction as the funspec.  The Poseidon
;               constraints are not expanded.
;   String      assert_eq of the length (a constant) with a private size
;               witness, then U8::new of each byte (8 boolean checks).
;               If the length does not fit in u32 the host halts before
;               any constraint; that is not an unsatisfiable R1CS.
;   Identifier  31 times U8::new, then validate_identifier_bits.
;
; literal-new is the identity on address, boolean, field, group, integer
; and scalar literals (a literalp value is already well formed).  It
; recomputes a signature's compute-key scalar, and it returns (spec-error)
; when string-type-new or identifier-literal-new does.

(in-package "ALEOVM")

(include-book "group-inject-r1cs")
(include-book "identifier-new-r1cs")
(include-book "../r1cs/boolean-check")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/integers")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (in-theory (disable (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean::new

(define literal-boolean-new-gadget ((b symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (boolean-check-gadget b p))

(defruled literal-boolean-new-gadget-to-bitp
  (implies (and (symbolp b)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b))
           (equal (r1cs::r1cs-constraints-holdp
                   (literal-boolean-new-gadget b p) asg p)
                  (bitp (lookup-equal b asg))))
  :enable (literal-boolean-new-gadget
           boolean-check-gadget-to-bitp))

(defruled literal-new-of-boolean
  (implies (and (literalp x)
                (literal-case x :boolean))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new)

(defruled literal-boolean-new-sound
  :short "R1CS-SOUND for the boolean arm of @('Literal::new')."
  (implies (and (literalp x)
                (literal-case x :boolean)
                (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (equal (lookup-equal b asg) (literal-boolean->get x))
                (r1cs::r1cs-constraints-holdp
                 (literal-boolean-new-gadget b p) asg p))
           (equal (literal-new x) (literal-fix x)))
  :enable (literal-new-of-boolean))

(defruled literal-boolean-new-complete
  :short "R1CS-COMPLETE for the boolean arm of @('Literal::new')."
  (implies (and (literalp x)
                (literal-case x :boolean)
                (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (equal (lookup-equal b asg) (literal-boolean->get x)))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-boolean-new-gadget b p) asg p)
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-boolean-new-gadget-to-bitp
           literal-new-of-boolean))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::new and Scalar::new allocate a variable and emit nothing.

(define literal-field-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(define literal-scalar-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled literal-new-of-field
  (implies (and (literalp x) (literal-case x :field))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new)

(defruled literal-new-of-scalar
  (implies (and (literalp x) (literal-case x :scalar))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new)

(defruled literal-field-new-sound
  (implies (and (literalp x)
                (literal-case x :field)
                (r1cs::r1cs-constraints-holdp
                 (literal-field-new-gadget) asg p))
           (equal (literal-new x) (literal-fix x)))
  :enable (literal-field-new-gadget literal-new-of-field))

(defruled literal-field-new-complete
  (implies (and (literalp x)
                (literal-case x :field)
                (r1cs::r1cs-valuationp asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-field-new-gadget) asg p)
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-field-new-gadget literal-new-of-field))

(defruled literal-scalar-new-sound
  (implies (and (literalp x)
                (literal-case x :scalar)
                (r1cs::r1cs-constraints-holdp
                 (literal-scalar-new-gadget) asg p))
           (equal (literal-new x) (literal-fix x)))
  :enable (literal-scalar-new-gadget literal-new-of-scalar))

(defruled literal-scalar-new-complete
  (implies (and (literalp x)
                (literal-case x :scalar)
                (r1cs::r1cs-valuationp asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-scalar-new-gadget) asg p)
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-scalar-new-gadget literal-new-of-scalar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Integer::new is a boolean check per bit.  from_bits_le of exactly
; I::BITS bits adds no further constraint.

(define literal-integer-new-gadget ((bits symbol-listp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (boolean-check-gadget-list bits p))

(defruled literal-integer-new-gadget-to-bit-listp
  (implies (and (symbol-listp bits)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits))
           (equal (r1cs::r1cs-constraints-holdp
                   (literal-integer-new-gadget bits p) asg p)
                  (bit-listp (lookup-equal-list bits asg))))
  :enable (literal-integer-new-gadget
           boolean-check-gadget-list-to-bit-listp))

(define literal-integer-kindp ((x literalp))
  :returns (yes/no booleanp)
  ;; literal-case of a quoted list is member-eq, whose tail is not a boolean.
  (and (literal-case x '(:i8 :i16 :i32 :i64 :i128
                         :u8 :u16 :u32 :u64 :u128))
       t))

(defruled literal-new-of-integer
  (implies (and (literalp x)
                (literal-integer-kindp x))
           (equal (literal-new x) (literal-fix x)))
  :hints (("Goal"
           :in-theory (enable literal-new literal-integer-kindp)
           :cases ((equal (literal-kind x) :i8)
                   (equal (literal-kind x) :i16)
                   (equal (literal-kind x) :i32)
                   (equal (literal-kind x) :i64)
                   (equal (literal-kind x) :i128)
                   (equal (literal-kind x) :u8)
                   (equal (literal-kind x) :u16)
                   (equal (literal-kind x) :u32)
                   (equal (literal-kind x) :u64)
                   (equal (literal-kind x) :u128)))))

(defruled literal-integer-new-sound
  :short "R1CS-SOUND for an integer arm of @('Literal::new')."
  (implies (and (literalp x)
                (literal-integer-kindp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::r1cs-constraints-holdp
                 (literal-integer-new-gadget bits p) asg p))
           (and (bit-listp (lookup-equal-list bits asg))
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-integer-new-gadget-to-bit-listp
           literal-new-of-integer))

(defruled literal-integer-new-complete
  :short "R1CS-COMPLETE for an integer arm.  The wires are a bit list,
          which they are for the two's-complement bits of any integer literal."
  (implies (and (literalp x)
                (literal-integer-kindp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-integer-new-gadget bits p) asg p)
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-integer-new-gadget-to-bit-listp
           literal-new-of-integer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; StringType::new.  The length is a constant linear combination on the
; left of assert_eq, and a private field on the right.  Each byte is
; U8::new.  n is the byte length; the host only builds this when
; n < 2^32, and n is far below the base prime.

(define literal-string-size-gadget ((size symbolp) (n natp) (p primep))
  :guard (< n p)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "assert_eq of the constant length with the private size witness."
  (declare (ignorable p))
  (list (r1cs::make-r1cs-constraint
         :a (list (list n 1))
         :b (list (list 1 1))
         :c (list (list 1 size)))))

(defruled literal-string-size-gadget-to-len
  (implies (and (symbolp size)
                (natp n)
                (equal p (base-prime))
                (< n p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size))
           (equal (r1cs::r1cs-constraints-holdp
                   (literal-string-size-gadget size n p) asg p)
                  (equal (lookup-equal size asg) n)))
  :hints (("Goal"
           :in-theory (e/d (literal-string-size-gadget
                            r1cs::r1cs-constraint-holdsp
                            r1cs::dot-product)
                           (pfield::mul-commutative)))))

(define literal-string-new-gadget ((size symbolp)
                                   (n natp)
                                   (bits symbol-listp)
                                   (p primep))
  :guard (< n p)
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (literal-string-size-gadget size n p)
          (boolean-check-gadget-list bits p)))

(defruled literal-new-string-when-short
  (implies (and (literalp x)
                (literal-case x :string)
                (< (len (string-type->bytes (literal-string->get x)))
                   (expt 2 32)))
           (equal (literal-new x)
                  (literal-string (literal-string->get x))))
  :enable (literal-new string-type-new))

(defruled literal-new-string-errors-when-long
  :short "The host halts before emitting constraints when the length
          does not fit in u32.  This is (spec-error), not an unsatisfiable
          R1CS: the size assert_eq of that length with itself would hold."
  (implies (and (literalp x)
                (literal-case x :string)
                (>= (len (string-type->bytes (literal-string->get x)))
                    (expt 2 32)))
           (reserrp (literal-new x)))
  :enable (literal-new string-type-new spec-error))

(defruled literal-string-new-sound
  (implies (and (literalp x)
                (literal-case x :string)
                (symbolp size)
                (symbol-listp bits)
                (natp n)
                (equal n (len (string-type->bytes (literal-string->get x))))
                (< n (expt 2 32))
                (equal p (base-prime))
                (< n p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::valuation-binds-allp asg bits)
                (equal (lookup-equal size asg) n)
                (r1cs::r1cs-constraints-holdp
                 (literal-string-new-gadget size n bits p) asg p))
           (equal (literal-new x)
                  (literal-string (literal-string->get x))))
  :enable literal-new-string-when-short)

(defruled literal-string-new-complete
  :short "R1CS-COMPLETE for a string the host actually injects (length fits in u32)."
  (implies (and (literalp x)
                (literal-case x :string)
                (symbolp size)
                (symbol-listp bits)
                (natp n)
                (equal n (len (string-type->bytes (literal-string->get x))))
                (< n (expt 2 32))
                (equal p (base-prime))
                (< n p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::valuation-binds-allp asg bits)
                (equal (lookup-equal size asg) n)
                (bit-listp (lookup-equal-list bits asg)))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-string-new-gadget size n bits p) asg p)
                (equal (literal-new x)
                       (literal-string (literal-string->get x)))))
  :enable (literal-string-new-gadget
           literal-string-size-gadget-to-len
           boolean-check-gadget-list-to-bit-listp
           literal-new-string-when-short))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::new and Address::new.  literal-new does not re-check subgroup
; membership: a literal's group is already a groupp.  The circuit still
; emits enforce_in_group.  Soundness of the identity therefore only needs
; the wires to be the point.  Completeness needs a cofactor witness; that
; witness is not constructed here.

(define literal-group-new-gadget ((x symbolp) (y symbolp)
                                  (qx symbolp) (qy symbolp)
                                  (cx2 symbolp) (cy2 symbolp)
                                  (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                  (x3 symbolp) (y3 symbolp)
                                  (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                  (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (group-enforce-in-group-gadget
   x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p))

(defruled literal-new-of-group
  (implies (and (literalp x) (literal-case x :group))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new)

(defruled literal-new-of-address
  (implies (and (literalp x) (literal-case x :address))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new)

(defruled literal-group-new-sound
  :short "R1CS-SOUND for the group arm.  The funspec is the identity on a
          literal, which is already in the subgroup.  The cofactor
          constraints are part of the hyp, so a satisfying assignment still
          has to meet enforce_in_group."
  (implies (and (literalp x)
                (literal-case x :group)
                (symbolp xcoord) (symbolp ycoord)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xcoord)
                (r1cs::valuation-bindsp asg ycoord)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (equal (lookup-equal xcoord asg)
                       (ecurve::edwards-bls12-point->u (literal-group->get x)))
                (equal (lookup-equal ycoord asg)
                       (ecurve::edwards-bls12-point->v (literal-group->get x)))
                (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new-of-group)

(defruled literal-address-new-sound
  (implies (and (literalp x)
                (literal-case x :address)
                (symbolp xcoord) (symbolp ycoord)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xcoord)
                (r1cs::valuation-bindsp asg ycoord)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (equal (lookup-equal xcoord asg)
                       (ecurve::edwards-bls12-point->u (literal-address->get x)))
                (equal (lookup-equal ycoord asg)
                       (ecurve::edwards-bls12-point->v (literal-address->get x)))
                (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p))
           (equal (literal-new x) (literal-fix x)))
  :enable literal-new-of-address)

(defruled literal-group-new-complete-when-witness
  :short "R1CS-COMPLETE for the group arm, given a cofactor witness whose
          wires satisfy the enforce_in_group equations.  Constructing that
          witness for every groupp point is an open TODO."
  (implies (and (literalp x)
                (or (literal-case x :group)
                    (literal-case x :address))
                (symbolp xcoord) (symbolp ycoord)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xcoord)
                (r1cs::valuation-bindsp asg ycoord)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (group-enforce-in-group-equations
                 (lookup-equal xcoord asg) (lookup-equal ycoord asg)
                 (lookup-equal qx asg) (lookup-equal qy asg)
                 (lookup-equal cx2 asg) (lookup-equal cy2 asg)
                 (lookup-equal dxy asg) (lookup-equal dx2 asg)
                 (lookup-equal dy2 asg)
                 (lookup-equal x3 asg) (lookup-equal y3 asg)
                 (lookup-equal exy asg) (lookup-equal ex2 asg)
                 (lookup-equal ey2 asg)
                 p))
           (r1cs::r1cs-constraints-holdp
            (literal-group-new-gadget
             xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
            asg p))
  :enable (literal-group-new-gadget
           group-enforce-in-group-gadget-to-equations))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signature::new.  The two scalars emit nothing.  Each group emits
; enforce_in_group.  sk_prf is hash_to_scalar_psd4 of the two x-coordinates;
; that hash is abstract, matching values-signature-new.

(define literal-signature-new-gadget
  ((pkx symbolp) (pky symbolp)
   (pk-qx symbolp) (pk-qy symbolp)
   (pk-cx2 symbolp) (pk-cy2 symbolp)
   (pk-dxy symbolp) (pk-dx2 symbolp) (pk-dy2 symbolp)
   (pk-x3 symbolp) (pk-y3 symbolp)
   (pk-exy symbolp) (pk-ex2 symbolp) (pk-ey2 symbolp)
   (prx symbolp) (pry symbolp)
   (pr-qx symbolp) (pr-qy symbolp)
   (pr-cx2 symbolp) (pr-cy2 symbolp)
   (pr-dxy symbolp) (pr-dx2 symbolp) (pr-dy2 symbolp)
   (pr-x3 symbolp) (pr-y3 symbolp)
   (pr-exy symbolp) (pr-ex2 symbolp) (pr-ey2 symbolp)
   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Signature::new') aside from the excluded hash."
  (append (literal-group-new-gadget
           pkx pky pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2
           pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 p)
          (literal-group-new-gadget
           prx pry pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2
           pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 p)))

(defruled literal-signature-new-sound
  :short "R1CS-SOUND for the signature arm.  The hash conjunct is the
          specification of hash_to_scalar_psd4, not a constraint snarkVM
          emits in place of Poseidon."
  (b* ((sig (literal-signature->get x))
       (ck (signature->compute-key sig))
       (pk (compute-key->pk-sig ck))
       (pr (compute-key->pr-sig ck)))
    (implies (and (literalp x)
                  (literal-case x :signature)
                  (equal p (base-prime))
                  (symbolp challenge) (symbolp response) (symbolp sk)
                  (symbolp pkx) (symbolp prx)
                  (r1cs::r1cs-valuationp asg p)
                  (r1cs::valuation-bindsp asg challenge)
                  (r1cs::valuation-bindsp asg response)
                  (r1cs::valuation-bindsp asg sk)
                  (r1cs::valuation-bindsp asg pkx)
                  (r1cs::valuation-bindsp asg prx)
                  (equal (lookup-equal challenge asg) (signature->challenge sig))
                  (equal (lookup-equal response asg) (signature->response sig))
                  (equal (lookup-equal pkx asg) (ecurve::edwards-bls12-point->u pk))
                  ;; Both hash inputs are x-coordinates (Group::to_x_coordinate).
                  (equal (lookup-equal prx asg) (ecurve::edwards-bls12-point->u pr))
                  (equal (lookup-equal sk asg)
                         (values-hash-to-scalar-psd4
                          (list (values-group-x pk) (values-group-x pr)))))
             (equal (literal-signature
                     (make-signature
                      :challenge (lookup-equal challenge asg)
                      :response (lookup-equal response asg)
                      :compute-key
                      (make-compute-key
                       :pk-sig pk
                       :pr-sig pr
                       :sk-prf (lookup-equal sk asg))))
                    (literal-new x))))
  :enable (literal-new
           values-signature-new
           values-compute-key-from
           values-group-x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::new.  The constraint list is identifier-new-gadget.
; R1CS-SOUND is identifier-literal-new-sound in identifier-list-sound.lisp.
; The PFCS for these constraints is literal-new-pfcs.lisp.

(define literal-identifier-new-gadget ((bitrows true-listp)
                                       (witrows true-listp)
                                       (partial symbolp)
                                       (uscore symbolp)
                                       (islet symbolp)
                                       (p primep))
  :guard (and (consp bitrows)
              (consp witrows)
              (id-bitrows-p bitrows)
              (id-witrows-p witrows))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (consp bitrows)
                              (consp witrows)
                              (id-bitrows-p bitrows)
                              (id-witrows-p witrows)
                              (primep p)
                              (symbolp partial)
                              (symbolp uscore)
                              (symbolp islet))
                    :hints (("Goal" :in-theory (enable literal-identifier-new-gadget))))
  (identifier-new-gadget bitrows witrows partial uscore islet p))
