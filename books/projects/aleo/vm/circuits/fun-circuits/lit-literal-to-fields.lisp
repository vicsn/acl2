; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Literal::to_fields (circuit/program/src/data/literal/to_fields.rs) over
; the wires.
;
; Literal::to_fields dispatches on the variant (a host match).  No arm
; emits a constraint:
;   Address::to_field and Group::to_x_coordinate are the x wire;
;   Field::from_boolean is the bit wire as a field;
;   Field is the wire itself;
;   Integer::to_field is Field::from_bits_le of the I::BITS bit wires
;     (fewer than 253, so the weighted sum, a linear combination);
;   Scalar::to_field is the scalar's field wire;
;   Signature::to_fields is the challenge and response field wires and
;     the x wires of pk_sig and pr_sig (sk_prf is not read, so no hash);
;   StringType::to_fields is Field::from_bits_le of each 252-bit chunk of
;     the byte bit wires (linear combinations);
;   IdentifierLiteral::to_field is Field::from_bits_le of the 248 byte bit
;     wires (a linear combination).
; So the gadget is empty, and each theorem below shows that the values of
; those linear combinations are literal-to-fields of the literal the wires
; denote.  The literal the wires denote, and the type facts about it, are
; what the matching arm of Literal::new establishes on the input
; (literal-new-r1cs.lisp, identifier-list-sound.lisp): bit wires are bits,
; scalar wires are below r, points are in the group, string and identifier
; bit wires decode to the literal's bytes.

(in-package "ALEOVM")

(include-book "literal-new-r1cs")
(include-book "fsa-identifier-literal-bits")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lit-literal-to-fields-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('Literal::to_fields'): none on any arm."
  nil)

(defruled lit-literal-to-fields-gadget-complete
  :short "R1CS-COMPLETE: the empty gadget holds on every valuation, and the
          funspec never errs."
  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p)
  :enable lit-literal-to-fields-gadget)

(defruledl lit-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :enable fieldp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defruled lit-literal-to-fields-address-sound
  :short "Address arm: the x wire.  The point is in the group by the
          address arm of @('Literal::new') (@('enforce_in_group'))."
  (b* ((pt (ecurve::point-finite (lookup-equal x asg) (lookup-equal y asg))))
    (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg x)
                  (groupp pt)
                  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
             (equal (list (lookup-equal x asg))
                    (literal-to-fields (literal-address pt)))))
  :enable (literal-to-fields values-group-x ecurve::edwards-bls12-point->u
           fieldp)
  :use ((:instance lit-fieldp-of-lookup (x x))))

(defruled lit-literal-to-fields-group-sound
  :short "Group arm: @('to_x_coordinate'), the x wire."
  (b* ((pt (ecurve::point-finite (lookup-equal x asg) (lookup-equal y asg))))
    (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg x)
                  (groupp pt)
                  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
             (equal (list (lookup-equal x asg))
                    (literal-to-fields (literal-group pt)))))
  :enable (literal-to-fields values-group-x ecurve::edwards-bls12-point->u
           fieldp)
  :use ((:instance lit-fieldp-of-lookup (x x))))

(defruled lit-literal-to-fields-boolean-sound
  :short "Boolean arm: @('Field::from_boolean'), the bit wire.  The wire is a
          bit by @('Boolean::new')."
  (implies (and (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
           (equal (list (lookup-equal b asg))
                  (literal-to-fields (literal-boolean (lookup-equal b asg)))))
  :enable literal-to-fields)

(defruled lit-literal-to-fields-field-sound
  :short "Field arm: the wire itself; no type hypothesis."
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg f)
                (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
           (and (literalp (literal-field (lookup-equal f asg)))
                (equal (literal-field->get (literal-field (lookup-equal f asg)))
                       (lookup-equal f asg))
                (equal (list (lookup-equal f asg))
                       (literal-to-fields (literal-field (lookup-equal f asg))))))
  :enable (literal-to-fields lit-fieldp-of-lookup))

(defruled lit-literal-to-fields-scalar-sound
  :short "Scalar arm: the scalar's field wire.  It is below r by the scalar
          arm of @('Literal::new') (@(tsee literal-scalar-new-sound))."
  (implies (and (scalarp (lookup-equal s asg))
                (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
           (equal (list (lookup-equal s asg))
                  (literal-to-fields (literal-scalar (lookup-equal s asg)))))
  :enable literal-to-fields)

(defruled lit-literal-to-fields-signature-sound
  :short "Signature arm: the challenge and response wires and the x wires of
          @('pk_sig') and @('pr_sig').  The types come from the signature arm
          of @('Literal::new'); @('sk_prf') is not read."
  (b* ((c$ (lookup-equal c asg))
       (r$ (lookup-equal r asg))
       (pk (ecurve::point-finite (lookup-equal pkx asg) (lookup-equal pky asg)))
       (pr (ecurve::point-finite (lookup-equal prx asg) (lookup-equal pry asg))))
    (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg pkx)
                  (r1cs::valuation-bindsp asg prx)
                  (scalarp c$)
                  (scalarp r$)
                  (groupp pk)
                  (groupp pr)
                  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
             (equal (list c$ r$ (lookup-equal pkx asg) (lookup-equal prx asg))
                    (literal-to-fields
                     (literal-signature
                      (signature c$ r$ (compute-key pk pr sk)))))))
  :enable (literal-to-fields values-signature-to-fields
           values-group-x ecurve::edwards-bls12-point->u fieldp)
  :use ((:instance lit-fieldp-of-lookup (x pkx))
        (:instance lit-fieldp-of-lookup (x prx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defruledl lit-mod-of-int-of-unsigned
  (implies (and (equal m (expt 2 n)) (natp u) (posp n) (< u m))
           (equal (mod (values-int-of-unsigned u signedp n) m) u))
  :enable values-int-of-unsigned)

(defruledl lit-signed-byte-p-of-int-of-unsigned
  (implies (and (natp u) (posp n) (< u (expt 2 n)))
           (signed-byte-p n (values-int-of-unsigned u t n)))
  :enable values-int-of-unsigned
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))

(defruledl lit-sbyte-of-int-of-unsigned
  (implies (natp u)
           (and (implies (< u (expt 2 8)) (acl2::sbyte8p (values-int-of-unsigned u t 8)))
                (implies (< u (expt 2 16)) (acl2::sbyte16p (values-int-of-unsigned u t 16)))
                (implies (< u (expt 2 32)) (acl2::sbyte32p (values-int-of-unsigned u t 32)))
                (implies (< u (expt 2 64)) (acl2::sbyte64p (values-int-of-unsigned u t 64)))
                (implies (< u (expt 2 128)) (acl2::sbyte128p (values-int-of-unsigned u t 128)))
                (implies (< u (expt 2 8)) (acl2::ubyte8p (values-int-of-unsigned u nil 8)))
                (implies (< u (expt 2 16)) (acl2::ubyte16p (values-int-of-unsigned u nil 16)))
                (implies (< u (expt 2 32)) (acl2::ubyte32p (values-int-of-unsigned u nil 32)))
                (implies (< u (expt 2 64)) (acl2::ubyte64p (values-int-of-unsigned u nil 64)))
                (implies (< u (expt 2 128)) (acl2::ubyte128p (values-int-of-unsigned u nil 128)))))
  :enable (acl2::sbyte8p acl2::sbyte16p acl2::sbyte32p acl2::sbyte64p acl2::sbyte128p
           acl2::ubyte8p acl2::ubyte16p acl2::ubyte32p acl2::ubyte64p acl2::ubyte128p
           values-int-of-unsigned)
  :use ((:instance lit-signed-byte-p-of-int-of-unsigned (n 8))
        (:instance lit-signed-byte-p-of-int-of-unsigned (n 16))
        (:instance lit-signed-byte-p-of-int-of-unsigned (n 32))
        (:instance lit-signed-byte-p-of-int-of-unsigned (n 64))
        (:instance lit-signed-byte-p-of-int-of-unsigned (n 128))))

(defruled lit-literal-to-fields-integer-sound
  :short "Integer arms (variants 4..13): @('Field::from_bits_le') of the
          @('I::BITS') bit wires, the weighted sum.  The wires are bits by
          the integer arm of @('Literal::new') (@(tsee literal-integer-new-sound)),
          which also names the literal they denote."
  (b* ((vals (lookup-equal-list bits asg)))
    (implies (and (member-equal variant '(4 5 6 7 8 9 10 11 12 13))
                  (bit-listp vals)
                  (equal (len bits) (literal-integer-variant-width variant))
                  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
             (equal (list (lebits=>nat vals))
                    (literal-to-fields (literal-from-bits-le variant vals)))))
  :do-not-induct t
  :cases ((equal variant 4) (equal variant 5) (equal variant 6)
          (equal variant 7) (equal variant 8) (equal variant 9)
          (equal variant 10) (equal variant 11) (equal variant 12)
          (equal variant 13))
  :in-theory (enable literal-to-fields
                     literal-from-bits-le
                     values-literal-from-bits
                     values-int-from-bits-le
                     values-int-to-field
                     literal-integer-variant-width
                     len-of-lookup-equal-list
                     lit-mod-of-int-of-unsigned
                     lit-sbyte-of-int-of-unsigned
                     acl2::sbyte8-fix acl2::sbyte16-fix acl2::sbyte32-fix
                     acl2::sbyte64-fix acl2::sbyte128-fix
                     acl2::ubyte8-fix acl2::ubyte16-fix acl2::ubyte32-fix
                     acl2::ubyte64-fix acl2::ubyte128-fix)
  :use ((:instance literal-from-bits-le-of-integer-bits
                   (bits (lookup-equal-list bits asg)))
        (:instance values-lebits=>nat-upper-bound
                   (bits (lookup-equal-list bits asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun lit-by8-induct (b k)
  (declare (xargs :measure (len b)))
  (if (endp b) k (lit-by8-induct (nthcdr 8 b) (1- k))))

(defruled lit-bytes-to-lebits-of-lebits-to-bytes
  (implies (and (bit-listp b) (natp k) (equal (len b) (* 8 k)))
           (equal (values-bytes-to-lebits (values-lebits-to-bytes b)) b))
  :induct (lit-by8-induct b k)
  :expand ((values-lebits-to-bytes b))
  :hints (("Subgoal *1/2" :cases ((zp k)) :expand ((values-lebits-to-bytes b))
           :use ((:instance lit-recombine (b b))
                 (:instance acl2::nat=>lebits-of-lebits=>nat (digits (take 8 b))))
           :in-theory (enable values-bytes-to-lebits values-nat-to-lebits
                              acl2::bit-list-fix-when-bit-listp)
           :do-not '(generalize)))
  :enable (values-bytes-to-lebits)
  :prep-lemmas
  ((defrule lit-nthcdr-8-of-8
     (implies (and (true-listp b) (equal (len b) 8)) (equal (nthcdr 8 b) nil))
     :expand ((nthcdr 8 b) (nthcdr 7 (cdr b)) (nthcdr 6 (cddr b))
              (nthcdr 5 (cdddr b)) (nthcdr 4 (cddddr b))
              (nthcdr 3 (cdr (cddddr b))) (nthcdr 2 (cddr (cddddr b)))
              (nthcdr 1 (cdddr (cddddr b)))))
   (defrule lit-recombine
     (implies (and (true-listp b) (<= 8 (len b)))
              (equal (append (take 8 b) (nthcdr 8 b)) b))
     :rule-classes nil)))

(defruled lit-literal-to-fields-string-sound
  :short "String arm: @('Field::from_bits_le') of each 252-bit chunk of the
          byte bit wires (@(tsee values-pack-bits)).  The string arm of
          @('Literal::new') (@(tsee literal-string-new-sound)) gives that the
          wires are bits, that there are 8 per byte, and that the literal they
          denote is a string whose bytes they encode."
  (b* ((vals (lookup-equal-list bits asg)))
    (implies (and (bit-listp vals)
                  (natp n)
                  (equal (len bits) (* 8 n))
                  (literalp lit)
                  (literal-case lit :string)
                  (equal (string-type->bytes (literal-string->get lit))
                         (values-lebits-to-bytes vals))
                  (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
             (equal (values-pack-bits vals)
                    (literal-to-fields lit))))
  :do-not-induct t
  :enable (literal-to-fields string-type-to-fields string-type-to-bits-le
           len-of-lookup-equal-list)
  :use (:instance lit-bytes-to-lebits-of-lebits-to-bytes
                  (b (lookup-equal-list bits asg)) (k n)))

(defruled lit-literal-to-fields-identifier-sound
  :short "Identifier arm: @('Field::from_bits_le') of the 248 byte bit wires.
          The identifier arm of @('Literal::new')
          (@(tsee literal-identifier-new-sound), @(tsee id-decode-rows-matchp))
          gives that the bit rows encode the literal's bytes."
  (implies (and (identifier-literalp x)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::r1cs-constraints-holdp (lit-literal-to-fields-gadget) asg p))
           (equal (list (values-lebits-to-field
                         (lookup-equal-list (fsa-id-flatten bitrows) asg)))
                  (literal-to-fields (literal-identifier x))))
  :enable literal-to-fields
  :use (:instance fsa-identifier-to-fields-wire-sound)
  :prep-lemmas
  ((defrule lit-identifier-to-fields-gadget-nil
     (equal (identifier-to-fields-gadget) nil)
     :enable identifier-to-fields-gadget)))
