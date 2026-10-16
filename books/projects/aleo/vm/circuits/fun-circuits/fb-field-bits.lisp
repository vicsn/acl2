; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bit decomposition circuits for Field.
;
; to_non_unique_bits_le
;   Boolean checks on the witnessed bits, plus assert_eq of the field
;   with their powers-of-two linear combination.  No range check.
;   The canonical bits satisfy the gadget.  Other bit vectors with the
;   same residue also satisfy it when 2^(bit length) > p, so soundness
;   to the canonical funspec is false.  See bugs-fb.txt.
;
; to_lower_bits_le / _be
;   The same boolean checks and assert_eq, on k bits (the be form only
;   reverses the list).  When 2^k < p the residue is unique and the
;   bits are the funspec.  At k = 253, 2^k > p and the same aliasing
;   bug as to_non_unique appears.  Completeness of the canonical
;   witness holds for every k <= 253, including 253.
;
; to_upper_bits_be / _le
;   Boolean checks plus assert_eq against the linear combination whose
;   coefficients start at 2^(253-k).  The funspec bridge (nthcdr of the
;   canonical bits) is not proved.
;
; write_bits_le / _be
;   field-to-bits-gadget: boolean checks, the weighted sum, and the
;   range check against p - 1.  That is to_non_unique_bits_le followed
;   by assert_less_than_or_equal_constant.  Soundness uses
;   field-to-bits-soundness.  write_bits_be reverses the list and adds
;   no constraint.  Completeness needs the range-check witnesses.
;
; from_bits_le / _be
;   The weighted sum is the output linear combination, not a constraint.
;   If the list is longer than the field, one assert_bits_are_zero is
;   emitted for the excess (a sum, not one zero-constraint per bit).
;   If the list is at least the field width, assert_less_than_or_equal
;   against p - 1 is emitted (bits-lte-const-check).  The existing
;   field-from-bits-gadget also forces a fresh variable to equal the
;   sum; snarkVM does not.  Soundness for lists shorter than the field
;   is proved.  The full-width funspec bridge is not.

(in-package "ALEOVM")

(include-book "fb-boolean-bits")
(include-book "../r1cs/field-to-bits")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")
(include-book "../r1cs/pow2sum-vectors")
(include-book "../r1cs/bits-lte-const-check")
(include-book "../fun-specs/primitives-field")
(include-book "../library-extensions/digits")
(include-book "../library-extensions/lookup-equal-list")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb-integer-length-of-base-prime
  (equal (integer-length (base-prime))
         (base-field-size-in-bits))
  :enable (base-prime base-field-size-in-bits)
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e integer-length)
                                     (:e base-field-size-in-bits)))))

(defruled fb-base-prime-below-2-253
  (< (base-prime) (expt 2 (base-field-size-in-bits)))
  :enable (base-prime base-field-size-in-bits)
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e expt)
                                     (:e base-field-size-in-bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-to-non-unique-bits-le-gadget ((x symbolp)
                                               (bits symbol-listp)
                                               (p primep))
  :guard (equal (len bits) (integer-length p))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Boolean checks and assert_eq of @('Field::to_non_unique_bits_le')."
  (append (boolean-check-gadget-list bits p)
          (pow2sum-gadget x bits)))

(defruled fb-field-to-non-unique-bits-le-gadget-to-mod
  (implies (and (symbolp x)
                (symbol-listp bits)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits))
           (b* ((x$ (lookup-equal x asg))
                (bits$ (lookup-equal-list bits asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (fb-field-to-non-unique-bits-le-gadget x bits p)
                     asg p)
                    (and (bit-listp bits$)
                         (equal x$ (mod (lebits=>nat bits$) p))))))
  :enable (fb-field-to-non-unique-bits-le-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat))

(defruled fb-mod-lebits=>nat-when-field-bits-le
  (implies (and (equal bs (field-bits-le x))
                (fieldp x))
           (equal (mod (lebits=>nat bs) (base-prime))
                  x))
  :enable (field-bits-le
           fb-integer-length-of-base-prime
           fb-base-prime-below-2-253
           fieldp
           acl2::lebits=>nat-of-nat=>lebits))

(defruled fb-field-to-non-unique-bits-le-gadget-complete
  :short "The canonical 253 bits satisfy the gadget.  They are not the
          only solution; see bugs-fb.txt."
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (equal (len bits) (base-field-size-in-bits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal-list bits asg)
                       (field-to-non-unique-bits-le-funspec
                        (lookup-equal x asg))))
           (r1cs::r1cs-constraints-holdp
            (fb-field-to-non-unique-bits-le-gadget x bits p) asg p))
  :do-not-induct t
  :enable (fb-field-to-non-unique-bits-le-gadget-to-mod
           field-to-non-unique-bits-le-funspec)
  :use (:instance fb-mod-lebits=>nat-when-field-bits-le
                  (bs (lookup-equal-list bits asg))
                  (x (lookup-equal x asg))))

; Prime 5, value 1, bits (1 0 0).  1 = 1 + 2*0 + 4*0.

(defconst *fb-field-to-non-unique-bits-asg*
  '((x . 1) (b0 . 1) (b1 . 0) (b2 . 0)))

(defconst *fb-field-to-non-unique-bits-prime* 5)

(defrule fb-field-to-non-unique-bits-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-to-non-unique-bits-le-gadget 'x '(b0 b1 b2)
                                          *fb-field-to-non-unique-bits-prime*)
   *fb-field-to-non-unique-bits-asg*
   *fb-field-to-non-unique-bits-prime*)
  :enable (fb-field-to-non-unique-bits-le-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-to-lower-bits-le-gadget ((x symbolp)
                                          (bits symbol-listp)
                                          (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::to_lower_bits_le') for @('k = (len bits)')."
  (append (boolean-check-gadget-list bits p)
          (pow2sum-gadget x bits)))

(defruled fb-field-to-lower-bits-le-gadget-to-mod
  (implies (and (symbolp x)
                (symbol-listp bits)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits))
           (b* ((x$ (lookup-equal x asg))
                (bits$ (lookup-equal-list bits asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (fb-field-to-lower-bits-le-gadget x bits p) asg p)
                    (and (bit-listp bits$)
                         (equal x$ (mod (lebits=>nat bits$) p))))))
  :enable (fb-field-to-lower-bits-le-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat))

(defruled fb-nat=>lebits-when-lebits=>nat
  (implies (and (equal v (lebits=>nat bs))
                (bit-listp bs))
           (equal (acl2::nat=>lebits (len bs) v) bs))
  :enable (acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix))

(defruled fb-nat=>lebits-when-mod-lebits=>nat
  (implies (and (equal v (mod (lebits=>nat bs) p))
                (bit-listp bs)
                (posp p)
                (< (expt 2 (len bs)) p))
           (and (< v (expt 2 (len bs)))
                (equal (acl2::nat=>lebits (len bs) v) bs)))
  :enable (acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix))

(defruled fb-field-to-lower-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k 252)
                (< (expt 2 k) p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (fieldp (lookup-equal x asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-to-lower-bits-le-gadget x bits p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-lower-bits-le-funspec (lookup-equal x asg) k)))
  :do-not-induct t
  :enable (fb-field-to-lower-bits-le-gadget-to-mod
           field-to-lower-bits-le-funspec
           base-field-size-in-bits
           fieldp
           pfield::fep-fix-when-fep)
  :use (:instance fb-nat=>lebits-when-mod-lebits=>nat
                  (v (lookup-equal x asg))
                  (bs (lookup-equal-list bits asg))))

(defruled fb-field-to-lower-bits-le-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-to-lower-bits-le-funspec
                               (lookup-equal x asg) k)))
                (equal (lookup-equal-list bits asg)
                       (field-to-lower-bits-le-funspec
                        (lookup-equal x asg) k)))
           (r1cs::r1cs-constraints-holdp
            (fb-field-to-lower-bits-le-gadget x bits p) asg p))
  :enable (fb-field-to-lower-bits-le-gadget-to-mod
           field-to-lower-bits-le-funspec
           base-field-size-in-bits
           fieldp
           pfield::fep-fix-when-fep
           acl2::lebits=>nat-of-nat=>lebits
           acl2::bit-listp-of-nat=>lebits))

(define fb-field-to-lower-bits-be-gadget ((x symbolp)
                                          (bits symbol-listp)
                                          (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as the little-endian form.
          @('bits') here are the big-endian output."
  (fb-field-to-lower-bits-le-gadget x (rev bits) p))

(defthm fb-equal-rev-when-rev-equal
  (implies (and (equal (rev a) b)
                (true-listp a))
           (equal a (rev b)))
  :rule-classes nil)

(defruled fb-not-reserrp-when-bit-listp
  (implies (bit-listp x)
           (not (reserrp x)))
  :enable (reserrp bit-listp))

(defruled fb-field-to-lower-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k 252)
                (< (expt 2 k) p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg (rev bits))
                (fieldp (lookup-equal x asg))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-to-lower-bits-be-gadget x bits p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-lower-bits-be-funspec (lookup-equal x asg) k)))
  :do-not-induct t
  :enable (fb-field-to-lower-bits-be-gadget
           field-to-lower-bits-be-funspec
           lookup-equal-list-of-rev
           fb-not-reserrp-when-bit-listp)
  :use ((:instance fb-field-to-lower-bits-le-gadget-sound
                   (bits (rev bits)))
        (:instance fb-field-to-lower-bits-le-gadget-to-mod
                   (bits (rev bits)))
        (:instance fb-equal-rev-when-rev-equal
                   (a (lookup-equal-list bits asg))
                   (b (field-to-lower-bits-le-funspec
                       (lookup-equal x asg) k)))))

(defruled fb-field-to-lower-bits-be-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg (rev bits))
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-to-lower-bits-be-funspec
                               (lookup-equal x asg) k)))
                (equal (lookup-equal-list bits asg)
                       (field-to-lower-bits-be-funspec
                        (lookup-equal x asg) k)))
           (r1cs::r1cs-constraints-holdp
            (fb-field-to-lower-bits-be-gadget x bits p) asg p))
  :do-not-induct t
  :enable (fb-field-to-lower-bits-be-gadget
           field-to-lower-bits-be-funspec
           lookup-equal-list-of-rev)
  :use (:instance fb-field-to-lower-bits-le-gadget-complete
                  (bits (rev bits))))

(define fb-field-to-lower-bits-le-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for @('to_lower_bits_le') at @('k = 2')."
  (pfcs::parse-def
   "field_to_lower_bits_le_2(x, b0, b1) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (x) * (1) == (b0 + 2 * b1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb-field-to-lower-bits-le-2-circuit)
            :pred fb-field-to-lower-bits-le-2-pred
            :prime prime)

(defruled fb-field-to-lower-bits-le-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime))
           (equal (fb-field-to-lower-bits-le-2-pred x b0 b1 prime)
                  (and (bitp b0)
                       (bitp b1)
                       (equal (list b0 b1)
                              (field-to-lower-bits-le-funspec x 2)))))
  :cases ((equal x 0) (equal x 1) (equal x 2) (equal x 3))
  :enable (fb-field-to-lower-bits-le-2-pred
           field-to-lower-bits-le-funspec
           base-field-size-in-bits
           fieldp
           bitp
           pfield::fep-fix-when-fep))

; 2 = bits (0 1) at prime 5, and 4 < 5.

(defconst *fb-field-to-lower-bits-asg*
  '((x . 2) (b0 . 0) (b1 . 1)))

(defconst *fb-field-to-lower-bits-prime* 5)

(defrule fb-field-to-lower-bits-le-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-to-lower-bits-le-gadget 'x '(b0 b1)
                                     *fb-field-to-lower-bits-prime*)
   *fb-field-to-lower-bits-asg*
   *fb-field-to-lower-bits-prime*)
  :enable (fb-field-to-lower-bits-le-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb-field-to-lower-bits-be-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-to-lower-bits-be-gadget 'x '(b1 b0)
                                     *fb-field-to-lower-bits-prime*)
   *fb-field-to-lower-bits-asg*
   *fb-field-to-lower-bits-prime*)
  :enable (fb-field-to-lower-bits-be-gadget
           fb-field-to-lower-bits-le-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           rev
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-to-upper-bits-be-gadget ((x symbolp)
                                          (bits symbol-listp)
                                          (k natp)
                                          (n natp)
                                          (p primep))
  :guard (<= k n)
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Boolean checks and assert_eq for @('Field::to_upper_bits_be').
          @('bits') is big-endian.  Coefficients start at @($2^{n-k}$)."
  (append (boolean-check-gadget-list bits p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 x))
                 :b (list (list 1 1))
                 :c (pow2sum-vector (rev bits) (- n k))))))

(define fb-field-to-upper-bits-le-gadget ((x symbolp)
                                          (bits symbol-listp)
                                          (k natp)
                                          (n natp)
                                          (p primep))
  :guard (<= k n)
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as the big-endian form, on the reversed bits."
  (fb-field-to-upper-bits-be-gadget x (rev bits) k n p))

(defruled fb-field-to-upper-bits-be-gadget-to-mod
  (implies (and (symbolp x)
                (symbol-listp bits)
                (natp k)
                (natp n)
                (<= k n)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits))
           (b* ((x$ (lookup-equal x asg))
                (le$ (lookup-equal-list (rev bits) asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (fb-field-to-upper-bits-be-gadget x bits k n p)
                     asg p)
                    (and (bit-listp (lookup-equal-list bits asg))
                         (equal x$
                                (mod (* (expt 2 (- n k))
                                        (lebits=>nat le$))
                                     p))))))
  :do-not-induct t
  :enable (fb-field-to-upper-bits-be-gadget
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           lookup-equal-list-of-rev)
  :use (:instance pow2sum-vector-to-mod-of-lebits=>nat
                  (xs (rev bits))
                  (i (- n k))))

; Prime 5 has bit length 3.  Upper 1 bit of 4 = 100b is 1.
; Coefficient 2^(3-1) = 4.

(defconst *fb-field-to-upper-bits-asg*
  '((x . 4) (b . 1)))

(defconst *fb-field-to-upper-bits-prime* 5)

(defrule fb-field-to-upper-bits-be-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-to-upper-bits-be-gadget 'x '(b) 1 3
                                     *fb-field-to-upper-bits-prime*)
   *fb-field-to-upper-bits-asg*
   *fb-field-to-upper-bits-prime*)
  :enable (fb-field-to-upper-bits-be-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-vector
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb-field-to-upper-bits-le-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-to-upper-bits-le-gadget 'x '(b) 1 3
                                     *fb-field-to-upper-bits-prime*)
   *fb-field-to-upper-bits-asg*
   *fb-field-to-upper-bits-prime*)
  :enable (fb-field-to-upper-bits-le-gadget
           fb-field-to-upper-bits-be-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-vector
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-write-bits-le-gadget ((x symbolp)
                                       (bits symbol-listp)
                                       (rs symbol-listp)
                                       (u symbolp)
                                       (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::write_bits_le').
          The accumulator is extended in the host; it adds no constraint."
  (field-to-bits-gadget x bits rs u p))

(defruled fb-field-write-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (bit-listp acc)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget x bits rs u p) asg p))
           (equal (append acc (lookup-equal-list bits asg))
                  (field-write-bits-le-funspec acc (lookup-equal x asg))))
  :do-not-induct t
  :enable (fb-field-write-bits-le-gadget
           field-write-bits-le-funspec
           field-bits-le
           fb-integer-length-of-base-prime
           pfield::fep-fix-when-fep
           r1cs::fep-of-lookup-equal
           acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix)
  :use ((:instance field-to-bits-soundness (xs bits))
        (:instance fb-nat=>lebits-when-lebits=>nat
                   (v (lookup-equal x asg))
                   (bs (lookup-equal-list bits asg)))))

(define fb-field-write-bits-be-gadget ((x symbolp)
                                       (bits symbol-listp)
                                       (rs symbol-listp)
                                       (u symbolp)
                                       (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::write_bits_be'): the little-endian
          gadget.  The written bits are that list reversed."
  (fb-field-write-bits-le-gadget x bits rs u p))

(defthm fb-append-rev-of-equal
  (implies (equal a b)
           (equal (append acc (rev a))
                  (append acc (rev b))))
  :rule-classes nil)

(defruled fb-field-write-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (symbolp u)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (equal (len bits) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (bit-listp acc)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-be-gadget x bits rs u p) asg p))
           (equal (append acc (rev (lookup-equal-list bits asg)))
                  (field-write-bits-be-funspec acc (lookup-equal x asg))))
  :do-not-induct t
  :enable (fb-field-write-bits-be-gadget
           field-write-bits-be-funspec
           field-write-bits-le-funspec)
  :use ((:instance fb-field-write-bits-le-gadget-sound (acc nil))
        (:instance fb-append-rev-of-equal
                   (a (lookup-equal-list bits asg))
                   (b (field-bits-le (lookup-equal x asg))))))

; Value 1 at prime 5.  Bits (1 0 0).  Range-check witnesses z0 = 1, z1 = 0.

(defconst *fb-field-write-bits-asg*
  '((x . 1) (b0 . 1) (b1 . 0) (b2 . 0) (z0 . 1) (z1 . 0) (u . 1)))

(defconst *fb-field-write-bits-prime* 5)

(defrule fb-field-write-bits-le-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-write-bits-le-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                  *fb-field-write-bits-prime*)
   *fb-field-write-bits-asg*
   *fb-field-write-bits-prime*)
  :enable (fb-field-write-bits-le-gadget
           field-to-bits-gadget
           boolean-check-gadget
           boolean-check-gadget-list
           pow2sum-gadget
           pow2sum-vector
           bits-lt-prime-gadget
           bits-lte-const-gadget
           bits-lte-const-gadget-aux
           bits-lte-const-rlen
           boolean-and-gadget
           boolean-or-gadget
           zero-unit-gadget
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb-field-write-bits-be-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-write-bits-be-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                  *fb-field-write-bits-prime*)
   *fb-field-write-bits-asg*
   *fb-field-write-bits-prime*)
  :enable (fb-field-write-bits-be-gadget
           fb-field-write-bits-le-sample))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-field-from-bits-le-gadget ((bits symbol-listp)
                                      (rs symbol-listp)
                                      (p primep))
  :guard (and (oddp p)
              (equal (len rs)
                     (if (>= (len bits) (integer-length p))
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
                       0)))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal" :do-not-induct t
                             :in-theory (enable nat=>lebits*-msb-is-1))))
  :short "Constraints of @('Field::from_bits_le').
          The weighted sum is the result linear combination."
  (b* ((size (integer-length p)))
    (append (and (> (len bits) size)
                 (fb-boolean-assert-bits-are-zero-gadget
                  (nthcdr size bits)))
            (and (>= (len bits) size)
                 (bits-lte-const-check-gadget
                  (take size bits)
                  (nat=>lebits* (1- p))
                  rs
                  p)))))

(defruled fb-field-from-bits-le-gadget-short
  (implies (and (symbol-listp bits)
                (primep p)
                (oddp p)
                (< (len bits) (integer-length p)))
           (equal (fb-field-from-bits-le-gadget bits nil p)
                  nil))
  :enable (fb-field-from-bits-le-gadget))

(defruled fb-field-from-bits-le-short-sound
  (implies (and (bit-listp bits)
                (equal p (base-prime))
                (< (len bits) (integer-length p)))
           (equal (lebits=>nat bits)
                  (field-from-bits-le-funspec bits)))
  :enable (field-from-bits-le-funspec
           base-field-size-in-bits
           fb-integer-length-of-base-prime
           lebits=>nat-less-when-len-less))

(define fb-field-from-bits-be-gadget ((bits symbol-listp)
                                      (rs symbol-listp)
                                      (p primep))
  :guard (and (oddp p)
              (equal (len rs)
                     (if (>= (len bits) (integer-length p))
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
                       0)))
  :verify-guards nil
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Field::from_bits_be'): little-endian on the
          reversed list."
  (fb-field-from-bits-le-gadget (rev bits) rs p))

(defruled fb-field-from-bits-be-short-sound
  (implies (and (bit-listp bits)
                (equal p (base-prime))
                (< (len bits) (integer-length p)))
           (equal (lebits=>nat (rev bits))
                  (field-from-bits-be-funspec bits)))
  :enable (field-from-bits-be-funspec)
  :use (:instance fb-field-from-bits-le-short-sound
                  (bits (rev bits))))

(defconst *fb-field-from-bits-asg*
  '((b0 . 1) (b1 . 0)))

(defconst *fb-field-from-bits-prime* 5)

(defrule fb-field-from-bits-le-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-from-bits-le-gadget '(b0 b1) nil *fb-field-from-bits-prime*)
   *fb-field-from-bits-asg*
   *fb-field-from-bits-prime*)
  :enable (fb-field-from-bits-le-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defrule fb-field-from-bits-be-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-from-bits-be-gadget '(b0 b1) nil *fb-field-from-bits-prime*)
   *fb-field-from-bits-asg*
   *fb-field-from-bits-prime*)
  :enable (fb-field-from-bits-be-gadget
           fb-field-from-bits-le-gadget
           rev
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
