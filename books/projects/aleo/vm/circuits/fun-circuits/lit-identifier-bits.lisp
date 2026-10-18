; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier::write_bits_le / write_bits_be, ProgramID::write_bits_le /
; write_bits_be, and Identifier::from_bits_le / from_bits_be / from_field
; (circuit/program/src/data/identifier/{to_bits,from_bits,from_field}.rs,
; circuit/program/src/id/to_bits.rs).
;
; An Identifier is a Field plus a host-side size in bytes.  It is
; injected only as a constant or public field (Field::new), so its field
; has no bits cache when it reaches write_bits_le.
;
; write_bits_le is Field::write_bits_le of the field wire
; (fb-field-write-bits-le-gadget: 253 boolean bit wires, the weighted-sum
; constraint, and the bits < p check), then the host truncates the vector
; to 8 * size bits.  write_bits_be reverses that truncated vector.  An
; Identifier that came out of from_bits instead carries the input bits in
; the field's bits cache, and write_bits_le then emits nothing; that case
; is not modelled here.
;
; ProgramID::write_bits_le is the name's write_bits_le followed by the
; network's (two copies of the field gadget).  write_bits_be is the
; name's write_bits_be followed by the network's.
;
; from_bits_le is Field::from_bits_le of the input bits
; (fb-field-from-bits-le-gadget: the bits < p check only when there are
; 253 bits; the field is the weighted sum, a linear combination).  The
; size is computed on the host from the ejected bits by
; console::Identifier::from_bits_le, which halts (A::halt) on more than
; 253 bits or on an invalid identifier string.  Those are host halts,
; not unsatisfiable constraints.  from_bits_be runs from_bits_le on the
; reversed list.  from_field is Field::to_bits_le of the input
; (fb-field-write-bits-le-gadget on 253 fresh bit wires) followed by
; from_bits_le of those 253 bit wires, which emits the bits < p check a
; second time.

(in-package "ALEOVM")

(include-book "fb2-field-bits")
(include-book "../fun-specs/values-literal")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bridges between the primitive Field funspecs and the program-crate helpers.

(defruled lit-field-bits-le-is-values-field-to-bits-le
  (implies (fieldp x)
           (equal (field-bits-le x) (values-field-to-bits-le x)))
  :use fb-base-prime-below-2-253
  :enable (field-bits-le values-field-to-bits-le values-nat-to-lebits
           values-field-fix base-field-size-in-bits fieldp))
(defruled lit-values-field-from-bits-le-is-funspec
  (implies (and (bit-listp bits) (<= (len bits) 253))
           (equal (values-field-from-bits-le bits)
                  (field-from-bits-le-funspec bits)))
  :do-not-induct t
  :cases ((< (len bits) 253))
  :enable (values-field-from-bits-le field-from-bits-le-funspec
           base-field-size-in-bits
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           assert-funspec
           acl2::lebits=>nat-of-nat=>lebits
           fb-integer-length-of-base-prime)
  :use (fb-base-prime-below-2-253
        (:instance lebits=>nat-less-when-len-less (bs bits) (p (base-prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier::write_bits_le / write_bits_be.

(define lit-identifier-write-bits-le-gadget ((x symbolp)
                                             (bits symbol-listp)
                                             (rs symbol-listp)
                                             (u symbolp)
                                             (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Identifier::write_bits_le'): @('Field::write_bits_le')
          of the field wire.  The truncation to @('8 * size') bits is on the host."
  (fb-field-write-bits-le-gadget x bits rs u p))

(define lit-identifier-write-bits-be-gadget ((x symbolp)
                                             (bits symbol-listp)
                                             (rs symbol-listp)
                                             (u symbolp)
                                             (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Identifier::write_bits_be'): the little-endian
          gadget; the truncated bits are reversed on the host."
  (lit-identifier-write-bits-le-gadget x bits rs u p))

(defmacro lit-field-bits-hyps (x bits rs u)
  `(and (symbolp ,x)
        (symbol-listp ,bits)
        (symbol-listp ,rs)
        (symbolp ,u)
        (equal p (base-prime))
        (equal (len ,bits) (integer-length p))
        (equal (len ,rs) (bits-lt-prime-rlen p))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg ,x)
        (r1cs::valuation-binds-allp asg ,bits)
        (r1cs::valuation-binds-allp asg ,rs)
        (r1cs::valuation-bindsp asg ,u)
        (equal (lookup-equal ,u asg) 1)))

(defruledl lit-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :enable fieldp)

(defruled lit-identifier-write-bits-le-sound
  :short "Over the wires: the identifier built from the field wire and the
          constant size is well typed, and the truncated bit wires are its
          @('identifier-to-bits-le')."
  (implies (and (lit-field-bits-hyps x bits rs u)
                (acl2::ubyte5p s)
                (r1cs::r1cs-constraints-holdp
                 (lit-identifier-write-bits-le-gadget x bits rs u p) asg p))
           (b* ((id (identifier (lookup-equal x asg) s)))
             (and (identifierp id)
                  (equal (identifier->field id) (lookup-equal x asg))
                  (equal (identifier->size id) s)
                  (equal (take (* 8 s) (lookup-equal-list bits asg))
                         (identifier-to-bits-le id)))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-write-bits-le-gadget
                   identifier-to-bits-le
                   identifier-size-in-bits
                   field-write-bits-le-funspec
                   lit-fieldp-of-lookup
                   lit-field-bits-le-is-values-field-to-bits-le)
                  (fb-field-write-bits-le-gadget))
  :use ((:instance fb-field-write-bits-le-gadget-sound (acc nil))
        lit-fieldp-of-lookup))

(defruled lit-identifier-write-bits-le-complete
  :short "With the canonical bits of the field wire and the range-check
          witness, the constraints hold."
  (implies (and (lit-field-bits-hyps x bits rs u)
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list bits asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (lit-identifier-write-bits-le-gadget x bits rs u p) asg p))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-write-bits-le-gadget lit-fieldp-of-lookup)
                  (fb-field-write-bits-le-gadget))
  :use (fb2-field-write-bits-le-gadget-complete lit-fieldp-of-lookup))

(defruled lit-identifier-write-bits-be-sound
  (implies (and (lit-field-bits-hyps x bits rs u)
                (acl2::ubyte5p s)
                (r1cs::r1cs-constraints-holdp
                 (lit-identifier-write-bits-be-gadget x bits rs u p) asg p))
           (b* ((id (identifier (lookup-equal x asg) s)))
             (and (identifierp id)
                  (equal (identifier->field id) (lookup-equal x asg))
                  (equal (identifier->size id) s)
                  (equal (rev (take (* 8 s) (lookup-equal-list bits asg)))
                         (identifier-to-bits-be id)))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-write-bits-be-gadget identifier-to-bits-be)
                  (lit-identifier-write-bits-le-gadget identifier-to-bits-le))
  :use lit-identifier-write-bits-le-sound)

(defruled lit-identifier-write-bits-be-complete
  (implies (and (lit-field-bits-hyps x bits rs u)
                (equal (lookup-equal-list bits asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list bits asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (lit-identifier-write-bits-be-gadget x bits rs u p) asg p))
  :in-theory '(lit-identifier-write-bits-be-gadget)
  :use lit-identifier-write-bits-le-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ProgramID::write_bits_le / write_bits_be.

(define lit-program-id-write-bits-le-gadget ((xn symbolp) (bn symbol-listp) (rn symbol-listp)
                                             (xw symbolp) (bw symbol-listp) (rw symbol-listp)
                                             (u symbolp)
                                             (p primep))
  :guard (and (oddp p)
              (equal (len bn) (integer-length p))
              (equal (len rn) (bits-lt-prime-rlen p))
              (equal (len bw) (integer-length p))
              (equal (len rw) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('ProgramID::write_bits_le'): the name's
          @('write_bits_le') followed by the network's."
  (append (lit-identifier-write-bits-le-gadget xn bn rn u p)
          (lit-identifier-write-bits-le-gadget xw bw rw u p)))

(define lit-program-id-write-bits-be-gadget ((xn symbolp) (bn symbol-listp) (rn symbol-listp)
                                             (xw symbolp) (bw symbol-listp) (rw symbol-listp)
                                             (u symbolp)
                                             (p primep))
  :guard (and (oddp p)
              (equal (len bn) (integer-length p))
              (equal (len rn) (bits-lt-prime-rlen p))
              (equal (len bw) (integer-length p))
              (equal (len rw) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('ProgramID::write_bits_be'): the name's
          @('write_bits_be') followed by the network's."
  (append (lit-identifier-write-bits-be-gadget xn bn rn u p)
          (lit-identifier-write-bits-be-gadget xw bw rw u p)))

(defruled lit-program-id-write-bits-le-sound
  :short "Over the wires: the program ID built from the two field wires and
          the constant sizes is well typed, and the two truncated bit-wire
          lists, concatenated, are its @('program-id-to-bits-le')."
  (implies (and (lit-field-bits-hyps xn bn rn u)
                (lit-field-bits-hyps xw bw rw u)
                (acl2::ubyte5p sn)
                (acl2::ubyte5p sw)
                (r1cs::r1cs-constraints-holdp
                 (lit-program-id-write-bits-le-gadget xn bn rn xw bw rw u p)
                 asg p))
           (b* ((id (program-id (identifier (lookup-equal xn asg) sn)
                                (identifier (lookup-equal xw asg) sw))))
             (and (program-idp id)
                  (equal (append (take (* 8 sn) (lookup-equal-list bn asg))
                                 (take (* 8 sw) (lookup-equal-list bw asg)))
                         (program-id-to-bits-le id)))))
  :do-not-induct t
  :in-theory (e/d (lit-program-id-write-bits-le-gadget
                   program-id-to-bits-le
                   r1cs::r1cs-constraints-holdp-of-append)
                  (lit-identifier-write-bits-le-gadget identifier-to-bits-le))
  :use ((:instance lit-identifier-write-bits-le-sound (x xn) (bits bn) (rs rn) (s sn))
        (:instance lit-identifier-write-bits-le-sound (x xw) (bits bw) (rs rw) (s sw))))

(defruled lit-program-id-write-bits-be-sound
  (implies (and (lit-field-bits-hyps xn bn rn u)
                (lit-field-bits-hyps xw bw rw u)
                (acl2::ubyte5p sn)
                (acl2::ubyte5p sw)
                (r1cs::r1cs-constraints-holdp
                 (lit-program-id-write-bits-be-gadget xn bn rn xw bw rw u p)
                 asg p))
           (b* ((id (program-id (identifier (lookup-equal xn asg) sn)
                                (identifier (lookup-equal xw asg) sw))))
             (and (program-idp id)
                  (equal (append (rev (take (* 8 sn) (lookup-equal-list bn asg)))
                                 (rev (take (* 8 sw) (lookup-equal-list bw asg))))
                         (program-id-to-bits-be id)))))
  :do-not-induct t
  :in-theory (e/d (lit-program-id-write-bits-be-gadget
                   program-id-to-bits-be
                   r1cs::r1cs-constraints-holdp-of-append)
                  (lit-identifier-write-bits-be-gadget identifier-to-bits-be))
  :use ((:instance lit-identifier-write-bits-be-sound (x xn) (bits bn) (rs rn) (s sn))
        (:instance lit-identifier-write-bits-be-sound (x xw) (bits bw) (rs rw) (s sw))))

(defmacro lit-field-bits-witness (x bits rs)
  `(and (equal (lookup-equal-list ,bits asg)
               (field-bits-le (lookup-equal ,x asg)))
        (equal (lookup-equal-list ,rs asg)
               (fb-bits-lte-const-witness
                (lookup-equal-list ,bits asg)
                (nat=>lebits* (1- p))))))

(defruled lit-program-id-write-bits-le-complete
  (implies (and (lit-field-bits-hyps xn bn rn u)
                (lit-field-bits-hyps xw bw rw u)
                (lit-field-bits-witness xn bn rn)
                (lit-field-bits-witness xw bw rw))
           (r1cs::r1cs-constraints-holdp
            (lit-program-id-write-bits-le-gadget xn bn rn xw bw rw u p)
            asg p))
  :do-not-induct t
  :in-theory '(lit-program-id-write-bits-le-gadget
               r1cs::r1cs-constraints-holdp-of-append)
  :use ((:instance lit-identifier-write-bits-le-complete (x xn) (bits bn) (rs rn))
        (:instance lit-identifier-write-bits-le-complete (x xw) (bits bw) (rs rw))))

(defruled lit-program-id-write-bits-be-complete
  (implies (and (lit-field-bits-hyps xn bn rn u)
                (lit-field-bits-hyps xw bw rw u)
                (lit-field-bits-witness xn bn rn)
                (lit-field-bits-witness xw bw rw))
           (r1cs::r1cs-constraints-holdp
            (lit-program-id-write-bits-be-gadget xn bn rn xw bw rw u p)
            asg p))
  :do-not-induct t
  :in-theory '(lit-program-id-write-bits-be-gadget
               r1cs::r1cs-constraints-holdp-of-append)
  :use ((:instance lit-identifier-write-bits-be-complete (x xn) (bits bn) (rs rn))
        (:instance lit-identifier-write-bits-be-complete (x xw) (bits bw) (rs rw))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier::from_bits_le / from_bits_be.

(define lit-identifier-host-size ((bits bit-listp))
  :returns (n natp :rule-classes :type-prescription)
  :short "The size in bytes that @('console::Identifier::from_bits_le')
          computes on the host from the ejected bits."
  (values-index-of-first-zero (values-lebits-to-bytes bits)))

(define lit-identifier-host-ok ((bits bit-listp))
  :returns (yes/no booleanp)
  :short "@('console::Identifier::from_bits_le') succeeds on the ejected bits.
          Otherwise the host halts (@('A::halt')); that is not an
          unsatisfiable constraint system."
  :guard-hints (("Goal" :in-theory (enable lit-identifier-host-size)))
  (b* ((bytes (values-lebits-to-bytes bits)))
    (and (<= (len bits) 253)
         (values-valid-identifier-bytes-p
          (take (lit-identifier-host-size bits) bytes)))))

(define lit-identifier-from-bits-le-gadget ((bits symbol-listp)
                                            (rs symbol-listp)
                                            (p primep))
  :guard (and (oddp p)
              (equal (len rs)
                     (if (>= (len bits) (integer-length p))
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
                       0)))
  :verify-guards nil
  :short "Constraints of @('Identifier::from_bits_le'):
          @('Field::from_bits_le') of the input bits."
  (fb-field-from-bits-le-gadget bits rs p))

(define lit-identifier-from-bits-be-gadget ((bits symbol-listp)
                                            (rs symbol-listp)
                                            (p primep))
  :guard (and (oddp p)
              (equal (len rs)
                     (if (>= (len bits) (integer-length p))
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
                       0)))
  :verify-guards nil
  :short "Constraints of @('Identifier::from_bits_be'): the little-endian
          gadget on the reversed input."
  (lit-identifier-from-bits-le-gadget (rev bits) rs p))

(defruledl lit-ubyte5p-when-valid
  (implies (values-valid-identifier-bytes-p (take n bytes))
           (acl2::ubyte5p (nfix n)))
  :enable (values-valid-identifier-bytes-p acl2::ubyte5p unsigned-byte-p))

(defruledl lit-nat-not-reserrp
  (implies (natp n) (not (reserrp n)))
  :enable reserrp)

(defruled lit-identifier-from-bits-le-when-field-ok
  (implies (and (bit-listp vals)
                (lit-identifier-host-ok vals)
                (equal (field-from-bits-le-funspec vals) (lebits=>nat vals)))
           (b* ((id (identifier (lebits=>nat vals) (lit-identifier-host-size vals))))
             (and (identifierp id)
                  (equal (identifier->field id) (lebits=>nat vals))
                  (equal (identifier->size id) (lit-identifier-host-size vals))
                  (equal (identifier-from-bits-le vals) id))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-host-ok lit-identifier-host-size
                   identifier-from-bits-le values-field-from-bits-le
                   lit-nat-not-reserrp fieldp)
                  (values-valid-identifier-bytes-p))
  :use ((:instance lit-values-field-from-bits-le-is-funspec (bits vals))
        (:instance lit-ubyte5p-when-valid
                   (n (values-index-of-first-zero (values-lebits-to-bytes vals)))
                   (bytes (values-lebits-to-bytes vals)))))

(defmacro lit-from-bits-hyps (bits rs)
  `(and (symbol-listp ,bits)
        (symbol-listp ,rs)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg ,bits)
        (r1cs::valuation-binds-allp asg ,rs)
        (bit-listp (lookup-equal-list ,bits asg))
        (equal (len ,rs)
               (if (>= (len ,bits) (integer-length p))
                   (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
                 0))))

(defruledl lit-take-253-when-short
  (implies (and (true-listp x) (<= (len x) 253))
           (equal (take (min (len x) 253) x) x)))

(defruled lit-identifier-from-bits-le-sound
  :short "Over the wires, given @('Boolean::new') on each input bit and that
          the host did not halt: the identifier built from the weighted sum of
          the bit wires and the host size is well typed, and
          @('identifier-from-bits-le') of the bit values returns it.  So an
          input on which the funspec errs and the host does not halt has no
          satisfying assignment."
  (b* ((vals (lookup-equal-list bits asg)))
    (implies (and (lit-from-bits-hyps bits rs)
                  (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-bits-le-gadget bits rs p) asg p))
             (b* ((id (identifier (lebits=>nat vals)
                                  (lit-identifier-host-size vals))))
               (and (identifierp id)
                    (equal (identifier->field id) (lebits=>nat vals))
                    (equal (identifier->size id) (lit-identifier-host-size vals))
                    (equal (identifier-from-bits-le vals) id)))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-from-bits-le-gadget
                   len-of-lookup-equal-list
                   fb-integer-length-of-base-prime)
                  (identifier-from-bits-le lit-identifier-host-ok
                   lit-identifier-host-size fb-field-from-bits-le-gadget))
  :use ((:instance fb2-field-from-bits-le-sound)
        (:instance lit-identifier-from-bits-le-when-field-ok
                   (vals (lookup-equal-list bits asg)))
        (:instance lit-take-253-when-short (x (lookup-equal-list bits asg)))
        (:instance lit-host-ok-len (vals (lookup-equal-list bits asg))))
  :prep-lemmas
  ((defrule lit-host-ok-len
     (implies (lit-identifier-host-ok vals) (<= (len vals) 253))
     :rule-classes nil
     :enable lit-identifier-host-ok)))

(defruled lit-identifier-from-bits-le-unsat-on-error
  (b* ((vals (lookup-equal-list bits asg)))
    (implies (and (lit-from-bits-hyps bits rs)
                  (lit-identifier-host-ok vals)
                  (reserrp (identifier-from-bits-le vals)))
             (not (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-bits-le-gadget bits rs p) asg p))))
  :in-theory (disable identifier-from-bits-le lit-identifier-host-ok
                      lit-identifier-from-bits-le-gadget)
  :use lit-identifier-from-bits-le-sound)

(defruled lit-identifier-from-bits-le-ok-facts
  (implies (and (bit-listp vals)
                (not (reserrp (identifier-from-bits-le vals))))
           (and (lit-identifier-host-ok vals)
                (not (reserrp (field-from-bits-le-funspec vals)))))
  :do-not-induct t
  :in-theory (e/d (identifier-from-bits-le lit-identifier-host-ok
                   lit-identifier-host-size)
                  (values-valid-identifier-bytes-p))
  :use (:instance lit-values-field-from-bits-le-is-funspec (bits vals)))

(defruled lit-identifier-from-bits-le-complete
  :short "R1CS-COMPLETE: when the funspec returns an identifier, the host
          does not halt, and the bit wires with the range-check witness
          satisfy the constraints."
  (b* ((vals (lookup-equal-list bits asg)))
    (implies (and (lit-from-bits-hyps bits rs)
                  (not (reserrp (identifier-from-bits-le vals)))
                  (equal (lookup-equal-list rs asg)
                         (if (>= (len bits) (integer-length p))
                             (fb-bits-lte-const-witness
                              (take (integer-length p) vals)
                              (nat=>lebits* (1- p)))
                           nil)))
             (and (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-bits-le-gadget bits rs p) asg p))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-from-bits-le-gadget)
                  (identifier-from-bits-le lit-identifier-host-ok
                   fb-field-from-bits-le-gadget))
  :use ((:instance lit-identifier-from-bits-le-ok-facts
                   (vals (lookup-equal-list bits asg)))
        fb2-field-from-bits-le-complete))

;; from_bits_be: the little-endian gadget on the reversed bit wires.

(defrule lit-from-bits-hyps-of-rev
  (implies (lit-from-bits-hyps bits rs)
           (lit-from-bits-hyps (rev bits) rs))
  :rule-classes nil
  :enable (fb-symbol-listp-of-rev fb-valuation-binds-allp-of-rev
           lookup-equal-list-of-rev))

(defruled lit-identifier-from-bits-be-sound
  (b* ((vals (rev (lookup-equal-list bits asg))))
    (implies (and (lit-from-bits-hyps bits rs)
                  (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-bits-be-gadget bits rs p) asg p))
             (b* ((id (identifier (lebits=>nat vals)
                                  (lit-identifier-host-size vals))))
               (and (identifierp id)
                    (equal (identifier->field id) (lebits=>nat vals))
                    (equal (identifier->size id) (lit-identifier-host-size vals))
                    (equal (identifier-from-bits-be (lookup-equal-list bits asg))
                           id)))))
  :do-not-induct t
  :in-theory '(lit-identifier-from-bits-be-gadget identifier-from-bits-be
               lookup-equal-list-of-rev)
  :use (lit-from-bits-hyps-of-rev
        (:instance lit-identifier-from-bits-le-sound (bits (rev bits)))))

(defruled lit-identifier-from-bits-be-complete
  (b* ((vals (rev (lookup-equal-list bits asg))))
    (implies (and (lit-from-bits-hyps bits rs)
                  (not (reserrp (identifier-from-bits-be (lookup-equal-list bits asg))))
                  (equal (lookup-equal-list rs asg)
                         (if (>= (len bits) (integer-length p))
                             (fb-bits-lte-const-witness
                              (take (integer-length p) vals)
                              (nat=>lebits* (1- p)))
                           nil)))
             (and (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-bits-be-gadget bits rs p) asg p))))
  :do-not-induct t
  :in-theory '(lit-identifier-from-bits-be-gadget identifier-from-bits-be
               lookup-equal-list-of-rev acl2::len-of-rev)
  :use (lit-from-bits-hyps-of-rev
        (:instance lit-identifier-from-bits-le-complete (bits (rev bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Identifier::from_field.

(define lit-identifier-from-field-gadget ((x symbolp)
                                          (bits symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (rs2 symbol-listp)
                                          (p primep))
  :guard (and (oddp p)
              (equal (len bits) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p))
              (equal (len rs2)
                     (bits-lte-const-check-rlen (nat=>lebits* (1- p)))))
  :verify-guards nil
  :short "Constraints of @('Identifier::from_field'): @('Field::to_bits_le')
          of the input, then @('Identifier::from_bits_le') of those 253 bit
          wires (which checks bits < p a second time)."
  (append (fb-field-write-bits-le-gadget x bits rs u p)
          (lit-identifier-from-bits-le-gadget bits rs2 p)))

(defruledl lit-lebits-of-field-bits-le
  (implies (fieldp x)
           (equal (lebits=>nat (field-bits-le x)) x))
  :enable (field-bits-le fieldp base-field-size-in-bits
           acl2::lebits=>nat-of-nat=>lebits)
  :use fb-base-prime-below-2-253)

(defruledl lit-bit-listp-of-field-bits-le
  (bit-listp (field-bits-le x))
  :enable field-bits-le)

(defruled lit-identifier-from-field-sound
  :short "Over the wires, given that the host did not halt: the identifier
          built from the field wire and the host size is well typed, and
          @('identifier-from-field') of the field wire returns it."
  (b* ((xv (lookup-equal x asg))
       (vals (values-field-to-bits-le xv)))
    (implies (and (lit-field-bits-hyps x bits rs u)
                  (symbol-listp rs2)
                  (r1cs::valuation-binds-allp asg rs2)
                  (equal (len rs2)
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p))))
                  (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-field-gadget x bits rs u rs2 p) asg p))
             (b* ((id (identifier xv (lit-identifier-host-size vals))))
               (and (identifierp id)
                    (equal (identifier->field id) xv)
                    (equal (identifier->size id) (lit-identifier-host-size vals))
                    (equal (lookup-equal-list bits asg) vals)
                    (equal (identifier-from-field xv) id)))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-from-field-gadget
                   identifier-from-field
                   r1cs::r1cs-constraints-holdp-of-append
                   field-write-bits-le-funspec
                   lit-fieldp-of-lookup
                   lit-lebits-of-field-bits-le
                   lit-bit-listp-of-field-bits-le
                   fb-integer-length-of-base-prime)
                  (identifier-from-bits-le lit-identifier-host-ok
                   lit-identifier-host-size
                   lit-identifier-from-bits-le-gadget
                   fb-field-write-bits-le-gadget))
  :use ((:instance fb-field-write-bits-le-gadget-sound (acc nil))
        (:instance lit-field-bits-le-is-values-field-to-bits-le
                   (x (lookup-equal x asg)))
        lit-fieldp-of-lookup
        (:instance lit-identifier-from-bits-le-sound (rs rs2))))

(defruled lit-identifier-from-field-complete
  :short "R1CS-COMPLETE: when the funspec returns an identifier, the host
          does not halt, and the canonical bits of the field wire with the
          two range-check witnesses satisfy the constraints."
  (b* ((xv (lookup-equal x asg))
       (vals (values-field-to-bits-le xv)))
    (implies (and (lit-field-bits-hyps x bits rs u)
                  (symbol-listp rs2)
                  (r1cs::valuation-binds-allp asg rs2)
                  (equal (len rs2)
                         (bits-lte-const-check-rlen (nat=>lebits* (1- p))))
                  (not (reserrp (identifier-from-field xv)))
                  (lit-field-bits-witness x bits rs)
                  (equal (lookup-equal-list rs2 asg)
                         (fb-bits-lte-const-witness
                          (lookup-equal-list bits asg)
                          (nat=>lebits* (1- p)))))
             (and (lit-identifier-host-ok vals)
                  (r1cs::r1cs-constraints-holdp
                   (lit-identifier-from-field-gadget x bits rs u rs2 p) asg p))))
  :do-not-induct t
  :in-theory (e/d (lit-identifier-from-field-gadget
                   lit-identifier-write-bits-le-gadget
                   identifier-from-field
                   r1cs::r1cs-constraints-holdp-of-append
                   lit-fieldp-of-lookup
                   lit-bit-listp-of-field-bits-le
                   fb-integer-length-of-base-prime)
                  (identifier-from-bits-le lit-identifier-host-ok
                   lit-identifier-from-bits-le-gadget
                   fb-field-write-bits-le-gadget))
  :use (lit-identifier-write-bits-le-complete
        (:instance lit-field-bits-le-is-values-field-to-bits-le
                   (x (lookup-equal x asg)))
        lit-fieldp-of-lookup
        (:instance lit-identifier-from-bits-le-complete (rs rs2))))
