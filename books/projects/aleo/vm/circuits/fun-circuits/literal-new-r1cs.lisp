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
;   Scalar      Field::new and the range check of
;               snarkVM-scalar-new-range-check.patch (scalar-new-r1cs.lisp)
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
; R1CS-SOUND is stated over the wire values: from a satisfying assignment
; each theorem builds the literal the wires denote, shows that the value
; type holds of the wires (so the fty constructor does not fix them), and
; shows literal-new returns that literal.  The theorems do not take the
; literal as an input.  The group, address and signature arms are
; conditional on edwards-bls12-cofactor-clears (group-inject-sound.lisp).
; The identifier arm is in identifier-list-sound.lisp.

(in-package "ALEOVM")

(include-book "group-inject-r1cs")
(include-book "group-inject-sound")
(include-book "scalar-new-r1cs")
(include-book "identifier-new-r1cs")
(include-book "../r1cs/boolean-check")
(include-book "../fun-specs/values-literal")
(include-book "../fun-specs/integers")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (in-theory (disable (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled literal-new-when-not-recomputed
  :short "@('literal-new') is the identity on a literal that is not a
          signature, string or identifier."
  (implies (and (literalp x)
                (not (member-equal (literal-kind x)
                                   '(:signature :string :identifier))))
           (equal (literal-new x) x))
  :enable literal-new)

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

(defruled literal-boolean-new-sound
  :short "R1CS-SOUND for the boolean arm of @('Literal::new')."
  (implies (and (symbolp b)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg b)
                (r1cs::r1cs-constraints-holdp
                 (literal-boolean-new-gadget b p) asg p))
           (b* ((b$ (lookup-equal b asg))
                (lit (literal-boolean b$)))
             (and (bitp b$)
                  (equal (literal-boolean->get lit) b$)
                  (equal (literal-new lit) lit))))
  :enable (literal-boolean-new-gadget-to-bitp
           literal-new-when-not-recomputed
           primep-of-base-prime))

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
           literal-new-when-not-recomputed
           primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::new allocates a variable and emits nothing.  Every wire is a
; base field element, which is what a field literal holds.

(define literal-field-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled literal-field-new-sound
  (implies (and (symbolp f)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::r1cs-constraints-holdp
                 (literal-field-new-gadget) asg p))
           (b* ((f$ (lookup-equal f asg))
                (lit (literal-field f$)))
             (and (fieldp f$)
                  (equal (literal-field->get lit) f$)
                  (equal (literal-new lit) lit))))
  :enable (fieldp
           r1cs::fep-of-lookup-equal
           literal-new-when-not-recomputed))

(defruled literal-field-new-complete
  (implies (and (literalp x)
                (literal-case x :field)
                (r1cs::r1cs-valuationp asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-field-new-gadget) asg p)
                (equal (literal-new x) (literal-fix x))))
  :enable (literal-field-new-gadget
           literal-new-when-not-recomputed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar::new: Field::new, then the range check below r.

(define literal-scalar-new-gadget ((s symbolp)
                                   (xs symbol-listp)
                                   (rs symbol-listp)
                                   (p primep))
  :guard (and (equal (len xs) 251)
              (equal (len rs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (scalar-new-gadget s xs rs p))

(defruled literal-scalar-new-sound
  :short "R1CS-SOUND for the scalar arm.  This needs the range check: the
          unpatched gadget accepts the wire @($r$)
          (@(tsee scalar-new-unpatched-accepts-non-scalar))."
  (implies (and (symbolp s)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) 251)
                (equal (len rs) 250)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg s)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (literal-scalar-new-gadget s xs rs p) asg p))
           (b* ((s$ (lookup-equal s asg))
                (lit (literal-scalar s$)))
             (and (scalarp s$)
                  (equal (literal-scalar->get lit) s$)
                  (equal (literal-new lit) lit))))
  :use scalar-new-gadget-sound
  :enable (literal-scalar-new-gadget
           literal-new-when-not-recomputed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Integer::new is a boolean check per bit.  from_bits_le of exactly
; I::BITS bits adds no further constraint.  The literal the wires denote
; is literal-from-bits-le of the bit values; the variant numbers 4..13
; are I8..I128, U8..U128.

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

(define literal-integer-variant-width ((variant natp))
  :returns (n natp)
  :short "Bit width of the integer literal variant (4..13)."
  (case variant
    ((4 9) 8)
    ((5 10) 16)
    ((6 11) 32)
    ((7 12) 64)
    ((8 13) 128)
    (t 0)))

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

(defruled literal-from-bits-le-of-integer-bits
  :short "Bits of the exact width of an integer variant decode to an
          integer literal of that variant."
  (implies (and (member-equal variant '(4 5 6 7 8 9 10 11 12 13))
                (bit-listp bits)
                (equal (len bits) (literal-integer-variant-width variant)))
           (b* ((lit (literal-from-bits-le variant bits)))
             (and (literalp lit)
                  (literal-integer-kindp lit))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal variant 4) (equal variant 5) (equal variant 6)
                   (equal variant 7) (equal variant 8) (equal variant 9)
                   (equal variant 10) (equal variant 11) (equal variant 12)
                   (equal variant 13))
           :in-theory (enable literal-from-bits-le
                              values-literal-from-bits
                              values-int-from-bits-le
                              literal-integer-variant-width
                              literal-integer-kindp
                              values-lebits=>nat-upper-bound))))

(defruled literal-integer-new-sound
  :short "R1CS-SOUND for an integer arm of @('Literal::new')."
  (implies (and (member-equal variant '(4 5 6 7 8 9 10 11 12 13))
                (symbol-listp bits)
                (equal (len bits) (literal-integer-variant-width variant))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::r1cs-constraints-holdp
                 (literal-integer-new-gadget bits p) asg p))
           (b* ((bits$ (lookup-equal-list bits asg))
                (lit (literal-from-bits-le variant bits$)))
             (and (bit-listp bits$)
                  (literalp lit)
                  (literal-integer-kindp lit)
                  (equal (literal-new lit) lit))))
  :use (:instance literal-from-bits-le-of-integer-bits
                  (bits (lookup-equal-list bits asg)))
  :enable (literal-integer-new-gadget-to-bit-listp
           literal-new-of-integer
           primep-of-base-prime))

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
           literal-new-of-integer
           primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; StringType::new.  The length is a constant linear combination on the
; left of assert_eq, and a private field on the right.  Each byte is
; U8::new.  n is the byte length; the host only builds this when
; n < 2^32, and n is far below the base prime.  The literal the wires
; denote is literal-from-bits-le (variant 16) of the bit values.

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

(defruled literal-string-u32-below-base-prime
  (< (expt 2 32) (base-prime))
  :in-theory '((:e base-prime) (:e expt) (:e <)))

(defun literal-bytes-induct (bits n)
  (declare (xargs :measure (len bits)))
  (if (or (endp bits) (zp n))
      nil
    (literal-bytes-induct (nthcdr 8 bits) (1- n))))

(defruled len-of-values-lebits-to-bytes-of-bytes
  (implies (and (natp n)
                (equal (len bits) (* 8 n)))
           (equal (len (values-lebits-to-bytes bits)) n))
  :induct (literal-bytes-induct bits n)
  :enable values-lebits-to-bytes)

(defruled literal-string-new-sound
  :short "R1CS-SOUND for the string arm: the size wire is the length, and
          the bit wires decode to a string of that many bytes."
  (implies (and (symbolp size)
                (symbol-listp bits)
                (natp n)
                (< n (expt 2 32))
                (equal (len bits) (* 8 n))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg size)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::r1cs-constraints-holdp
                 (literal-string-new-gadget size n bits p) asg p))
           (b* ((bits$ (lookup-equal-list bits asg))
                (lit (literal-from-bits-le 16 bits$)))
             (and (bit-listp bits$)
                  (equal (lookup-equal size asg) n)
                  (literalp lit)
                  (literal-case lit :string)
                  (equal (string-type->bytes (literal-string->get lit))
                         (values-lebits-to-bytes bits$))
                  (equal (len (string-type->bytes (literal-string->get lit)))
                         n)
                  (equal (literal-new lit) lit))))
  :do-not-induct t
  :use (literal-string-u32-below-base-prime
        (:instance len-of-values-lebits-to-bytes-of-bytes
                   (bits (lookup-equal-list bits asg))))
  :enable (literal-string-new-gadget
           literal-string-size-gadget-to-len
           boolean-check-gadget-list-to-bit-listp
           literal-new-string-when-short
           literal-from-bits-le
           values-literal-from-bits
           string-type-from-bits-le
           string-type-inject-size-in-bytes
           primep-of-base-prime))

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

; Group::new and Address::new.  The output wires (x, y) are 4Q for the
; cofactor witness Q (group-enforce-in-group-sound).  They are a group
; element, and literal-new returns the literal of that point, given
; edwards-bls12-cofactor-clears.  Completeness needs a cofactor witness;
; that witness is not constructed here.

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

(defruled literal-group-new-sound
  :short "R1CS-SOUND for the group arm, conditional on
          @(tsee edwards-bls12-cofactor-clears)."
  (implies (and (symbolp xcoord) (symbolp ycoord)
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
                (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p)
                (edwards-bls12-cofactor-clears))
           (b* ((pt (ecurve::point-finite (lookup-equal xcoord asg)
                                          (lookup-equal ycoord asg)))
                (lit (literal-group pt)))
             (and (groupp pt)
                  (equal (literal-group->get lit) pt)
                  (equal (literal-new lit) lit))))
  :use (:instance group-enforce-in-group-sound (x xcoord) (y ycoord))
  :enable (literal-group-new-gadget
           literal-new-when-not-recomputed))

(defruled literal-address-new-sound
  :short "R1CS-SOUND for the address arm, conditional on
          @(tsee edwards-bls12-cofactor-clears)."
  (implies (and (symbolp xcoord) (symbolp ycoord)
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
                (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p)
                (edwards-bls12-cofactor-clears))
           (b* ((pt (ecurve::point-finite (lookup-equal xcoord asg)
                                          (lookup-equal ycoord asg)))
                (lit (literal-address pt)))
             (and (groupp pt)
                  (equal (literal-address->get lit) pt)
                  (equal (literal-new lit) lit))))
  :use (:instance group-enforce-in-group-sound (x xcoord) (y ycoord))
  :enable (literal-group-new-gadget
           literal-new-when-not-recomputed))

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

; Signature::new.  The challenge and the response are Scalar::new, each
; with the range check.  Each group emits enforce_in_group.  sk_prf is
; hash_to_scalar_psd4 of the two x-coordinates; that hash is abstract,
; matching values-signature-new.

(define literal-signature-new-gadget
  ((c symbolp) (cxs symbol-listp) (crs symbol-listp)
   (r symbolp) (rxs symbol-listp) (rrs symbol-listp)
   (pkx symbolp) (pky symbolp)
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
  :guard (and (equal (len cxs) 251) (equal (len crs) 250)
              (equal (len rxs) 251) (equal (len rrs) 250))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Signature::new') aside from the excluded hash."
  (append (literal-scalar-new-gadget c cxs crs p)
          (literal-scalar-new-gadget r rxs rrs p)
          (literal-group-new-gadget
           pkx pky pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2
           pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2 p)
          (literal-group-new-gadget
           prx pry pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2
           pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 p)))

(defruled literal-signature-new-sound
  :short "R1CS-SOUND for the signature arm, conditional on
          @(tsee edwards-bls12-cofactor-clears).  The hash conjunct is the
          specification of hash_to_scalar_psd4 on the x-coordinate wires,
          not a constraint snarkVM emits in place of Poseidon."
  (implies (and (symbolp c) (symbol-listp cxs) (symbol-listp crs)
                (symbolp r) (symbol-listp rxs) (symbol-listp rrs)
                (equal (len cxs) 251) (equal (len crs) 250)
                (equal (len rxs) 251) (equal (len rrs) 250)
                (symbolp pkx) (symbolp pky)
                (symbolp pk-qx) (symbolp pk-qy)
                (symbolp pk-cx2) (symbolp pk-cy2)
                (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2)
                (symbolp pk-x3) (symbolp pk-y3)
                (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
                (symbolp prx) (symbolp pry)
                (symbolp pr-qx) (symbolp pr-qy)
                (symbolp pr-cx2) (symbolp pr-cy2)
                (symbolp pr-dxy) (symbolp pr-dx2) (symbolp pr-dy2)
                (symbolp pr-x3) (symbolp pr-y3)
                (symbolp pr-exy) (symbolp pr-ex2) (symbolp pr-ey2)
                (symbolp sk)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg cxs)
                (r1cs::valuation-binds-allp asg crs)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-binds-allp asg rxs)
                (r1cs::valuation-binds-allp asg rrs)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg pk-qx)
                (r1cs::valuation-bindsp asg pk-qy)
                (r1cs::valuation-bindsp asg pk-cx2)
                (r1cs::valuation-bindsp asg pk-cy2)
                (r1cs::valuation-bindsp asg pk-dxy)
                (r1cs::valuation-bindsp asg pk-dx2)
                (r1cs::valuation-bindsp asg pk-dy2)
                (r1cs::valuation-bindsp asg pk-x3)
                (r1cs::valuation-bindsp asg pk-y3)
                (r1cs::valuation-bindsp asg pk-exy)
                (r1cs::valuation-bindsp asg pk-ex2)
                (r1cs::valuation-bindsp asg pk-ey2)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg pr-qx)
                (r1cs::valuation-bindsp asg pr-qy)
                (r1cs::valuation-bindsp asg pr-cx2)
                (r1cs::valuation-bindsp asg pr-cy2)
                (r1cs::valuation-bindsp asg pr-dxy)
                (r1cs::valuation-bindsp asg pr-dx2)
                (r1cs::valuation-bindsp asg pr-dy2)
                (r1cs::valuation-bindsp asg pr-x3)
                (r1cs::valuation-bindsp asg pr-y3)
                (r1cs::valuation-bindsp asg pr-exy)
                (r1cs::valuation-bindsp asg pr-ex2)
                (r1cs::valuation-bindsp asg pr-ey2)
                (r1cs::valuation-bindsp asg sk)
                (r1cs::r1cs-constraints-holdp
                 (literal-signature-new-gadget
                  c cxs crs r rxs rrs
                  pkx pky pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2
                  pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2
                  prx pry pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2
                  pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 p)
                 asg p)
                (equal (lookup-equal sk asg)
                       (values-hash-to-scalar-psd4
                        (list (lookup-equal pkx asg) (lookup-equal prx asg))))
                (edwards-bls12-cofactor-clears))
           (b* ((c$ (lookup-equal c asg))
                (r$ (lookup-equal r asg))
                (pk (ecurve::point-finite (lookup-equal pkx asg)
                                          (lookup-equal pky asg)))
                (pr (ecurve::point-finite (lookup-equal prx asg)
                                          (lookup-equal pry asg)))
                (sig (make-signature
                      :challenge c$
                      :response r$
                      :compute-key (make-compute-key
                                    :pk-sig pk
                                    :pr-sig pr
                                    :sk-prf (lookup-equal sk asg))))
                (lit (literal-signature sig)))
             (and (scalarp c$)
                  (scalarp r$)
                  (groupp pk)
                  (groupp pr)
                  (equal (signature->challenge sig) c$)
                  (equal (signature->response sig) r$)
                  (equal (compute-key->pk-sig (signature->compute-key sig)) pk)
                  (equal (compute-key->pr-sig (signature->compute-key sig)) pr)
                  (equal (literal-new lit) lit))))
  :do-not-induct t
  :use ((:instance literal-scalar-new-sound (s c) (xs cxs) (rs crs))
        (:instance literal-scalar-new-sound (s r) (xs rxs) (rs rrs))
        (:instance literal-group-new-sound
                   (xcoord pkx) (ycoord pky)
                   (qx pk-qx) (qy pk-qy) (cx2 pk-cx2) (cy2 pk-cy2)
                   (dxy pk-dxy) (dx2 pk-dx2) (dy2 pk-dy2)
                   (x3 pk-x3) (y3 pk-y3)
                   (exy pk-exy) (ex2 pk-ex2) (ey2 pk-ey2))
        (:instance literal-group-new-sound
                   (xcoord prx) (ycoord pry)
                   (qx pr-qx) (qy pr-qy) (cx2 pr-cx2) (cy2 pr-cy2)
                   (dxy pr-dxy) (dx2 pr-dx2) (dy2 pr-dy2)
                   (x3 pr-x3) (y3 pr-y3)
                   (exy pr-exy) (ex2 pr-ex2) (ey2 pr-ey2)))
  :enable (literal-signature-new-gadget
           literal-new
           values-signature-new
           values-compute-key-from
           values-group-x
           ecurve::edwards-bls12-point->u
           r1cs::fep-of-lookup-equal
           primep-of-base-prime)
  :disable (literal-scalar-new-gadget
            literal-group-new-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::new.  The constraint list is identifier-new-gadget.
; R1CS-SOUND is literal-identifier-new-sound in identifier-list-sound.lisp.
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
