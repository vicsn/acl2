; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remaining bit-decomposition proofs.
;
; to_lower_bits_be gets the PFCS that the little-endian form already has,
; at k = 2 (the R1CS gadget is the general one).
;
; to_upper_bits: a satisfying assignment whose shifted bit value lies
; below the prime is the funspec, and the canonical upper bits are a
; witness.  The k = 1 PFCS is the same constraint.
;
; from_bits_le / from_bits_be: the sum is the output linear combination.
; A long list adds the excess sum-to-zero constraint and the
; bits-lte-const-check against p - 1.  Soundness reads those checks.
; Completeness uses the fold witness from fb2-boolean-lte.lisp.
;
; write_bits_le / write_bits_be completeness is the canonical bits plus
; that same fold witness and the unit-zero on its last bit.

(in-package "ALEOVM")

(include-book "fb-field-bits")
(include-book "fb2-boolean-lte")
(include-book "../r1cs/field-to-bits")
(include-book "../r1cs/boolean-check")
(include-book "../r1cs/pow2sum")
(include-book "../r1cs/zero")
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; to_lower_bits_be PFCS at k = 2.
;; Big-endian bits (b0 b1) have value b1 + 2*b0.

(define fb2-field-to-lower-bits-be-2-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "field_to_lower_bits_be_2(x, b0, b1) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (x) * (1) == (b1 + 2 * b0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb2-field-to-lower-bits-be-2-circuit)
            :pred fb2-field-to-lower-bits-be-2-pred
            :prime prime)

(defruled fb2-field-to-lower-bits-be-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime))
           (equal (fb2-field-to-lower-bits-be-2-pred x b0 b1 prime)
                  (and (bitp b0)
                       (bitp b1)
                       (equal (list b0 b1)
                              (field-to-lower-bits-be-funspec x 2)))))
  :enable (fb2-field-to-lower-bits-be-2-pred
           field-to-lower-bits-be-funspec
           field-to-lower-bits-le-funspec
           base-field-size-in-bits
           fieldp
           bitp
           pfield::fep-fix-when-fep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Upper bits.  x = 2^s * v with v < 2^k has little-endian bits
;; (s low zeros, then the k bits of v).

(defruled fb2-pm1-lebits-have-a-zero
  (implies (and (equal p (base-prime))
                (oddp p)
                (> p 2))
           (member-equal 0 (nat=>lebits* (1- p))))
  :enable (nat=>lebits*
           acl2::nat=>lendian*))

(define fb2-shift-induct ((s natp))
  (if (zp s)
      nil
    (fb2-shift-induct (1- s))))

(defruled fb2-nat=>lendian*-of-mul-expt2
  (implies (and (posp v)
                (natp s))
           (equal (acl2::nat=>lendian* 2 (* (expt 2 s) v))
                  (append (repeat s 0)
                          (acl2::nat=>lendian* 2 v))))
  :hints (("Goal"
           :induct (fb2-shift-induct s)
           :in-theory (enable fb2-shift-induct
                              acl2::nat=>lendian*
                              repeat))))

(defruled fb2-nthcdr-of-nat=>lebits-of-shift
  (implies (and (natp v)
                (natp s)
                (natp k)
                (< v (expt 2 k)))
           (equal (nthcdr s (acl2::nat=>lebits (+ s k)
                                               (* (expt 2 s) v)))
                  (acl2::nat=>lebits k v)))
  :hints (("Goal"
           :cases ((zp v))
           :in-theory (enable acl2::nat=>lebits
                              acl2::nat=>lendian
                              fb2-nat=>lendian*-of-mul-expt2
                              repeat
                              nthcdr))))

(defruled fb2-field-to-upper-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (fieldp (lookup-equal x asg))
                (< (* (expt 2 (- n k))
                      (lebits=>nat (rev (lookup-equal-list bits asg))))
                   p)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-to-upper-bits-be-gadget x bits k n p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-upper-bits-be-funspec (lookup-equal x asg) k)))
  :enable (fb-field-to-upper-bits-be-gadget-to-mod
           field-to-upper-bits-be-funspec
           base-field-size-in-bits
           fieldp
           pfield::fep-fix-when-fep
           fb2-nthcdr-of-nat=>lebits-of-shift
           fb-base-prime-below-2-253
           acl2::nat=>lebits-of-lebits=>nat
           acl2::lebits=>nat-upper-bound
           acl2::bit-list-fix
           rev-of-rev))

(defruled fb2-field-to-upper-bits-be-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-to-upper-bits-be-funspec
                               (lookup-equal x asg) k)))
                (equal (lookup-equal-list bits asg)
                       (field-to-upper-bits-be-funspec
                        (lookup-equal x asg) k)))
           (r1cs::r1cs-constraints-holdp
            (fb-field-to-upper-bits-be-gadget x bits k n p) asg p))
  :enable (fb-field-to-upper-bits-be-gadget-to-mod
           field-to-upper-bits-be-funspec
           base-field-size-in-bits
           fieldp
           pfield::fep-fix-when-fep
           fb2-nthcdr-of-nat=>lebits-of-shift
           fb-base-prime-below-2-253
           acl2::lebits=>nat-of-nat=>lebits
           acl2::bit-listp-of-nat=>lebits
           rev-of-rev))

(defruled fb2-field-to-upper-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg (rev bits))
                (fieldp (lookup-equal x asg))
                (< (* (expt 2 (- n k))
                      (lebits=>nat (lookup-equal-list bits asg)))
                   p)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-to-upper-bits-le-gadget x bits k n p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-upper-bits-le-funspec (lookup-equal x asg) k)))
  :enable (fb-field-to-upper-bits-le-gadget
           field-to-upper-bits-le-funspec
           field-to-upper-bits-be-funspec
           lookup-equal-list-of-rev)
  :use (:instance fb2-field-to-upper-bits-be-gadget-sound
                  (bits (rev bits))))

(defruled fb2-field-to-upper-bits-le-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp bits)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg (rev bits))
                (fieldp (lookup-equal x asg))
                (not (reserrp (field-to-upper-bits-le-funspec
                               (lookup-equal x asg) k)))
                (equal (lookup-equal-list bits asg)
                       (field-to-upper-bits-le-funspec
                        (lookup-equal x asg) k)))
           (r1cs::r1cs-constraints-holdp
            (fb-field-to-upper-bits-le-gadget x bits k n p) asg p))
  :enable (fb-field-to-upper-bits-le-gadget
           field-to-upper-bits-le-funspec
           field-to-upper-bits-be-funspec
           lookup-equal-list-of-rev)
  :use (:instance fb2-field-to-upper-bits-be-gadget-complete
                  (bits (rev bits))))

(define fb2-field-to-upper-bits-1-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "PFCS for the top bit.  Little- and big-endian agree at k = 1."
  (pfcs::parse-def
   "field_to_upper_bits_1(x, b) := {
    (1 - b) * (b) == (0),
    (x) * (1) == (7237005577332262213973186563042994240829374041602535252466099000494570602496 * b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb2-field-to-upper-bits-1-circuit)
            :pred fb2-field-to-upper-bits-1-pred
            :prime prime)

(defruled fb2-field-to-upper-bits-1-pred-to-be-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (pfield::fep b prime))
           (equal (fb2-field-to-upper-bits-1-pred x b prime)
                  (and (bitp b)
                       (equal (list b)
                              (field-to-upper-bits-be-funspec x 1)))))
  :enable (fb2-field-to-upper-bits-1-pred
           field-to-upper-bits-be-funspec
           base-field-size-in-bits
           fieldp
           bitp
           pfield::fep-fix-when-fep
           fb-base-prime-below-2-253))

(defruled fb2-field-to-upper-bits-1-pred-to-le-funspec
  (implies (and (equal prime (base-prime))
                (fieldp x)
                (pfield::fep b prime))
           (equal (fb2-field-to-upper-bits-1-pred x b prime)
                  (and (bitp b)
                       (equal (list b)
                              (field-to-upper-bits-le-funspec x 1)))))
  :enable (field-to-upper-bits-le-funspec
           fb2-field-to-upper-bits-1-pred-to-be-funspec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-field-from-bits-le-sound
  (implies (and (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list bits asg))
                (equal (len rs)
                       (if (>= (len bits) (integer-length p))
                           (bits-lte-const-check-rlen
                            (nat=>lebits* (1- p)))
                         0))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-from-bits-le-gadget bits rs p) asg p))
           (equal (lebits=>nat
                   (take (min (len bits) (integer-length p))
                         (lookup-equal-list bits asg)))
                  (field-from-bits-le-funspec
                   (lookup-equal-list bits asg))))
  :do-not-induct t
  :enable (fb-field-from-bits-le-gadget
           fb-field-from-bits-le-short-sound
           fb-integer-length-of-base-prime
           fb-boolean-assert-bits-are-zero-gadget-to-funspec
           fb-boolean-assert-lte-const-gadget-sound
           field-from-bits-le-funspec
           base-field-size-in-bits
           boolean-assert-bits-are-zero-funspec
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           acl2::lebits=>nat-of-nat=>lebits
           nat=>lebits*
           acl2::nat=>lendian*
           acl2::nat=>lebits
           acl2::nat=>lendian)
  :use (:instance bits-lte-const-check-soundness
                  (xs (take (integer-length p) bits))
                  (cs (nat=>lebits* (1- p)))
                  (rs rs)))

(defruled fb2-field-from-bits-le-complete
  (implies (and (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list bits asg))
                (not (reserrp (field-from-bits-le-funspec
                               (lookup-equal-list bits asg))))
                (equal (len rs)
                       (if (>= (len bits) (integer-length p))
                           (bits-lte-const-check-rlen
                            (nat=>lebits* (1- p)))
                         0))
                (equal (lookup-equal-list rs asg)
                       (if (>= (len bits) (integer-length p))
                           (fb-bits-lte-const-witness
                            (take (integer-length p)
                                  (lookup-equal-list bits asg))
                            (nat=>lebits* (1- p)))
                         nil)))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-from-bits-le-gadget bits rs p) asg p)
                (equal (lebits=>nat
                        (take (min (len bits) (integer-length p))
                              (lookup-equal-list bits asg)))
                       (field-from-bits-le-funspec
                        (lookup-equal-list bits asg)))))
  :do-not-induct t
  :enable (fb-field-from-bits-le-gadget
           fb-field-from-bits-le-short-sound
           fb-integer-length-of-base-prime
           fb-boolean-assert-bits-are-zero-gadget-to-funspec
           fb-boolean-assert-lte-const-gadget-complete
           field-from-bits-le-funspec
           base-field-size-in-bits
           lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           nat=>lebits*-msb-is-1
           fb2-pm1-lebits-have-a-zero))

(defruled fb2-field-from-bits-be-sound
  (implies (and (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (rev bits))
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list (rev bits) asg))
                (equal (len rs)
                       (if (>= (len bits) (integer-length p))
                           (bits-lte-const-check-rlen
                            (nat=>lebits* (1- p)))
                         0))
                (r1cs::r1cs-constraints-holdp
                 (fb-field-from-bits-be-gadget bits rs p) asg p))
           (equal (lebits=>nat
                   (take (min (len bits) (integer-length p))
                         (lookup-equal-list (rev bits) asg)))
                  (field-from-bits-be-funspec
                   (lookup-equal-list bits asg))))
  :enable (fb-field-from-bits-be-gadget
           field-from-bits-be-funspec
           lookup-equal-list-of-rev)
  :use (:instance fb2-field-from-bits-le-sound
                  (bits (rev bits))))

(defruled fb2-field-from-bits-be-complete
  (implies (and (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg (rev bits))
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list (rev bits) asg))
                (not (reserrp (field-from-bits-be-funspec
                               (lookup-equal-list bits asg))))
                (equal (len rs)
                       (if (>= (len bits) (integer-length p))
                           (bits-lte-const-check-rlen
                            (nat=>lebits* (1- p)))
                         0))
                (equal (lookup-equal-list rs asg)
                       (if (>= (len bits) (integer-length p))
                           (fb-bits-lte-const-witness
                            (take (integer-length p)
                                  (lookup-equal-list (rev bits) asg))
                            (nat=>lebits* (1- p)))
                         nil)))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-from-bits-be-gadget bits rs p) asg p)
                (equal (lebits=>nat
                        (take (min (len bits) (integer-length p))
                              (lookup-equal-list (rev bits) asg)))
                       (field-from-bits-be-funspec
                        (lookup-equal-list bits asg)))))
  :enable (fb-field-from-bits-be-gadget
           field-from-bits-be-funspec
           lookup-equal-list-of-rev)
  :use (:instance fb2-field-from-bits-le-complete
                  (bits (rev bits))))

(define fb2-field-from-bits-le-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Two-bit @('from_bits_le') emits no constraint."
  (pfcs::parse-def
   "field_from_bits_le_2(b0, b1) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb2-field-from-bits-le-2-circuit)
            :pred fb2-field-from-bits-le-2-pred
            :prime prime)

(defruled fb2-field-from-bits-le-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1))
           (and (fb2-field-from-bits-le-2-pred b0 b1 prime)
                (equal (lebits=>nat (list b0 b1))
                       (field-from-bits-le-funspec (list b0 b1)))))
  :enable (fb2-field-from-bits-le-2-pred
           fb-field-from-bits-le-short-sound
           fb-integer-length-of-base-prime
           bitp))

(define fb2-field-from-bits-be-2-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "field_from_bits_be_2(b0, b1) := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb2-field-from-bits-be-2-circuit)
            :pred fb2-field-from-bits-be-2-pred
            :prime prime)

(defruled fb2-field-from-bits-be-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (bitp b0)
                (bitp b1))
           (and (fb2-field-from-bits-be-2-pred b0 b1 prime)
                (equal (lebits=>nat (list b1 b0))
                       (field-from-bits-be-funspec (list b0 b1)))))
  :enable (fb2-field-from-bits-be-2-pred
           field-from-bits-be-funspec
           fb-field-from-bits-le-short-sound
           fb-integer-length-of-base-prime
           bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb2-field-write-bits-le-gadget-complete
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
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list bits asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (fb-field-write-bits-le-gadget x bits rs u p) asg p))
  :do-not-induct t
  :enable (fb-field-write-bits-le-gadget
           field-to-bits-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           bits-lt-prime-gadget
           zero-unit-gadget-to-equal-0
           field-bits-le
           fb-integer-length-of-base-prime
           fb-bits-lte-const-witness-satisfies
           fb-boolean-is-lte-const-gadget-complete
           pfield::fep-fix-when-fep
           acl2::lebits=>nat-of-nat=>lebits
           acl2::bit-listp-of-nat=>lebits
           nat=>lebits*-msb-is-1
           fb2-pm1-lebits-have-a-zero
           last-of-lookup-equal-list
           car-of-lookup-equal-list))

(defruled fb2-field-write-bits-be-gadget-complete
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
                (fieldp (lookup-equal x asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list bits asg)
                        (nat=>lebits* (1- p)))))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-be-gadget x bits rs u p) asg p)
                (equal (append nil
                               (rev (lookup-equal-list bits asg)))
                       (field-write-bits-be-funspec
                        nil (lookup-equal x asg)))))
  :enable (fb-field-write-bits-be-gadget
           fb2-field-write-bits-le-gadget-complete
           field-write-bits-be-funspec
           field-bits-le))
