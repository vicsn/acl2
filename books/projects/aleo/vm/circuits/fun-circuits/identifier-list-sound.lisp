; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND for IdentifierLiteral::new and the identifier arm of Literal::new.
; identifier-new-sound.lisp turns one byte's field equations into validate-byte.
; This book derives the boolean witness bits from the gates, lifts that
; byte theorem across the list and the trailing-null constraints, and
; concludes identifier-literal-new.

(in-package "ALEOVM")

(include-book "identifier-new-sound")
(include-book "literal-new-r1cs")
(include-book "../fun-specs/values-literal")

(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable lookup-equal-of-nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-lookup-list-8
  (implies (equal (len keys) 8)
           (equal (lookup-equal-list keys asg)
                  (list (lookup-equal (nth 0 keys) asg)
                        (lookup-equal (nth 1 keys) asg)
                        (lookup-equal (nth 2 keys) asg)
                        (lookup-equal (nth 3 keys) asg)
                        (lookup-equal (nth 4 keys) asg)
                        (lookup-equal (nth 5 keys) asg)
                        (lookup-equal (nth 6 keys) asg)
                        (lookup-equal (nth 7 keys) asg))))
  :hints (("Goal"
           :in-theory (e/d (lookup-equal-list nth len)
                           (lookup-equal-of-nth))
           :expand ((lookup-equal-list keys asg)
                    (lookup-equal-list (cdr keys) asg)
                    (lookup-equal-list (cddr keys) asg)
                    (lookup-equal-list (cdddr keys) asg)
                    (lookup-equal-list (cddddr keys) asg)
                    (lookup-equal-list (cdr (cddddr keys)) asg)
                    (lookup-equal-list (cddr (cddddr keys)) asg)
                    (lookup-equal-list (cdddr (cddddr keys)) asg)
                    (nth 0 keys) (nth 1 keys) (nth 2 keys) (nth 3 keys)
                    (nth 4 keys) (nth 5 keys) (nth 6 keys) (nth 7 keys)))))

(defruled id-byte-gadget-sound-rest
  (implies (and (symbol-listp bits)
                (equal (len bits) 8)
                (symbol-listp wits)
                (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))
                (bitp (lookup-equal (nth 0 wits) asg))
                (bitp (lookup-equal (nth 1 wits) asg))
                (bitp (lookup-equal (nth 6 wits) asg))
                (bitp (lookup-equal (nth 8 wits) asg))
                (bitp (lookup-equal (nth 10 wits) asg))
                (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget bits wits p) asg p))
           (equal (validate-byte (lookup-equal-list bits asg) nil)
                  (values-b-and
                   (values-b-not (lookup-equal (nth 6 bits) asg))
                   (values-b-not (lookup-equal (nth 5 bits) asg)))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-byte-gadget-to-equations
                 (:instance id-equations-imply-validate-rest
                            (b0 (lookup-equal (nth 0 bits) asg))
                            (b1 (lookup-equal (nth 1 bits) asg))
                            (b2 (lookup-equal (nth 2 bits) asg))
                            (b3 (lookup-equal (nth 3 bits) asg))
                            (b4 (lookup-equal (nth 4 bits) asg))
                            (b5 (lookup-equal (nth 5 bits) asg))
                            (b6 (lookup-equal (nth 6 bits) asg))
                            (b7 (lookup-equal (nth 7 bits) asg))
                            (b4b3 (lookup-equal (nth 0 wits) asg))
                            (b1b0 (lookup-equal (nth 1 wits) asg))
                            (m (lookup-equal (nth 2 wits) asg))
                            (r (lookup-equal (nth 3 wits) asg))
                            (null (lookup-equal (nth 4 wits) asg))
                            (lower (lookup-equal (nth 5 wits) asg))
                            (dor (lookup-equal (nth 6 wits) asg))
                            (idig (lookup-equal (nth 7 wits) asg))
                            (xor (lookup-equal (nth 8 wits) asg))
                            (bu (lookup-equal (nth 9 wits) asg))
                            (lor (lookup-equal (nth 10 wits) asg))
                            (bl (lookup-equal (nth 11 wits) asg))
                            (p p))
                 (:instance id-lookup-list-8 (keys bits) (asg asg)))
           :in-theory (e/d (member-equal-of-nth
                            symbolp-of-nth
                            r1cs::fep-of-lookup-equal
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            primep-when-equal-base-prime)
                           (validate-byte
                            id-byte-gadget
                            id-byte-equations
                            lookup-equal-list
                            lookup-equal-of-nth
                            (:definition nth)
                            (:definition pfield::mul)
                            (:definition pfield::add)
                            (:definition pfield::sub)
                            (:definition pfield::neg)
                            pfield::mul-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-byte-gate-holds
  (implies (r1cs::r1cs-constraints-holdp
            (id-byte-gadget bits wits p) asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget (nth 4 bits) (nth 3 bits) (nth 0 wits))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget (nth 1 bits) (nth 0 bits) (nth 1 wits))
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-gadget (nth 2 bits) (nth 1 bits) (nth 6 wits) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (nth 2 bits) (nth 1 wits) (nth 8 wits) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-gadget (nth 2 bits) (nth 1 wits) (nth 10 wits) p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (id-byte-gadget
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition nth)
                            (:definition boolean-and-gadget)
                            (:definition boolean-or-gadget)
                            (:definition boolean-xor-gadget)
                            (:definition id-b7-zero-gadget)
                            (:definition id-low5-neq-gadget)
                            (:definition id-null-gadget)
                            (:definition id-zero-prod-gadget)
                            (:definition id-digit-enforce-gadget)
                            (:definition id-upper-lc-enforce-gadget)
                            (:definition id-category-enforce-gadget)
                            (:definition r1cs::r1cs-constraint-holdsp))))))

(defruled id-and-gadget-bitp
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget x y z) asg p))
           (bitp (lookup-equal z asg)))
  :do-not-induct t
  :hints (("Goal"
           :use boolean-and-gadget-to-bitand
           :in-theory (e/d (id-bitp-of-bitand)
                           (boolean-and-gadget)))))

(defruled id-or-gadget-bitp
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-gadget x y z p) asg p))
           (bitp (lookup-equal z asg)))
  :do-not-induct t
  :hints (("Goal"
           :use boolean-or-gadget-to-bitor
           :in-theory (e/d (id-bitp-of-bitor)
                           (boolean-or-gadget)))))

(defruled id-xor-gadget-bitp
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget x y z p) asg p))
           (bitp (lookup-equal z asg)))
  :do-not-induct t
  :hints (("Goal"
           :use boolean-xor-gadget-to-bitxor
           :in-theory (e/d (id-bitp-of-bitxor)
                           (boolean-xor-gadget)))))

(defruled id-byte-witness-bitps
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))
                (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget bits wits p) asg p))
           (and (bitp (lookup-equal (nth 0 wits) asg))
                (bitp (lookup-equal (nth 1 wits) asg))
                (bitp (lookup-equal (nth 6 wits) asg))
                (bitp (lookup-equal (nth 8 wits) asg))
                (bitp (lookup-equal (nth 10 wits) asg))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-byte-gate-holds
                 (:instance id-and-gadget-bitp
                            (x (nth 4 bits)) (y (nth 3 bits)) (z (nth 0 wits)))
                 (:instance id-and-gadget-bitp
                            (x (nth 1 bits)) (y (nth 0 bits)) (z (nth 1 wits)))
                 (:instance id-or-gadget-bitp
                            (x (nth 2 bits)) (y (nth 1 bits)) (z (nth 6 wits)))
                 (:instance id-xor-gadget-bitp
                            (x (nth 2 bits)) (y (nth 1 wits)) (z (nth 8 wits)))
                 (:instance id-or-gadget-bitp
                            (x (nth 2 bits)) (y (nth 1 wits)) (z (nth 10 wits))))
           :in-theory (e/d (symbolp-of-nth
                            member-equal-of-nth
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            primep-when-equal-base-prime)
                           (id-byte-gadget
                            boolean-and-gadget
                            boolean-or-gadget
                            boolean-xor-gadget
                            (:definition nth))))))

(defruled id-null-equals-validate-rest
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (id-byte-equations b0 b1 b2 b3 b4 b5 b6 b7
                                   b4b3 b1b0 m r null lower
                                   dor idig xor bu lor bl p))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) nil)
                  null))
  :do-not-induct t
  :hints (("Goal"
           :use (id-equations-imply-validate-rest
                 (:instance id-null-is-spec
                            (b5 b5) (b6 b6) (null null) (p p)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-byte-equations
                         bitp-of-values-b-and
                         bitp-of-values-b-not
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff)
                         (:executable-counterpart cons))))))

(defruled id-byte-null-rest
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))
                (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget bits wits p) asg p))
           (and (bitp (lookup-equal (nth 4 wits) asg))
                (equal (validate-byte (lookup-equal-list bits asg) nil)
                       (lookup-equal (nth 4 wits) asg))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-byte-witness-bitps
                 id-byte-gadget-to-equations
                 id-byte-gadget-sound-rest
                 (:instance id-null-equals-validate-rest
                            (b0 (lookup-equal (nth 0 bits) asg))
                            (b1 (lookup-equal (nth 1 bits) asg))
                            (b2 (lookup-equal (nth 2 bits) asg))
                            (b3 (lookup-equal (nth 3 bits) asg))
                            (b4 (lookup-equal (nth 4 bits) asg))
                            (b5 (lookup-equal (nth 5 bits) asg))
                            (b6 (lookup-equal (nth 6 bits) asg))
                            (b7 (lookup-equal (nth 7 bits) asg))
                            (b4b3 (lookup-equal (nth 0 wits) asg))
                            (b1b0 (lookup-equal (nth 1 wits) asg))
                            (m (lookup-equal (nth 2 wits) asg))
                            (r (lookup-equal (nth 3 wits) asg))
                            (null (lookup-equal (nth 4 wits) asg))
                            (lower (lookup-equal (nth 5 wits) asg))
                            (dor (lookup-equal (nth 6 wits) asg))
                            (idig (lookup-equal (nth 7 wits) asg))
                            (xor (lookup-equal (nth 8 wits) asg))
                            (bu (lookup-equal (nth 9 wits) asg))
                            (lor (lookup-equal (nth 10 wits) asg))
                            (bl (lookup-equal (nth 11 wits) asg))
                            (p p))
                 (:instance id-lookup-list-8 (keys bits) (asg asg)))
           :in-theory (e/d (member-equal-of-nth
                            symbolp-of-nth
                            r1cs::fep-of-lookup-equal
                            r1cs::valuation-bindsp-when-valuation-binds-allp
                            primep-when-equal-base-prime
                            bitp-of-values-b-and
                            bitp-of-values-b-not)
                           (validate-byte
                            id-byte-gadget
                            id-byte-equations
                            lookup-equal-list
                            lookup-equal-of-nth
                            (:definition nth)
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            pfield::mul-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-first-extra-gate-holds
  (implies (r1cs::r1cs-constraints-holdp
            (id-first-extra-gadget b4b3 b1b0 b2 b6
                                   partial uscore islet p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget b4b3 b1b0 partial) asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget partial b2 uscore) asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (id-first-extra-gadget
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition boolean-and-gadget)
                            (:definition id-letter-gadget)
                            (:definition assert-gadget)
                            (:definition r1cs::r1cs-constraint-holdsp))))))

(defruled id-null-equals-validate-first
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (bitp partial) (bitp uscore)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (id-byte-equations b0 b1 b2 b3 b4 b5 b6 b7
                                   b4b3 b1b0 m r null lower
                                   dor idig xor bu lor bl p)
                (id-first-extra-equations b4b3 b1b0 b2 b6
                                          partial uscore islet p))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) t)
                  null))
  :do-not-induct t
  :hints (("Goal"
           :use (id-equations-imply-validate-first
                 (:instance id-null-is-spec
                            (b5 b5) (b6 b6) (null null) (p p)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-byte-equations
                         id-first-extra-equations
                         bitp-of-values-b-and
                         bitp-of-values-b-not
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff)
                         (:executable-counterpart cons))))))

(defruled id-first-byte-null
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))
                (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget bits wits p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (id-first-extra-gadget (nth 0 wits) (nth 1 wits)
                                        (nth 2 bits) (nth 6 bits)
                                        partial uscore islet p)
                 asg p))
           (and (bitp (lookup-equal (nth 4 wits) asg))
                (equal (validate-byte (lookup-equal-list bits asg) t)
                       (lookup-equal (nth 4 wits) asg))))
  :do-not-induct t
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :use (id-byte-witness-bitps
                 (:instance id-first-extra-gate-holds
                            (b4b3 (nth 0 wits))
                            (b1b0 (nth 1 wits))
                            (b2 (nth 2 bits))
                            (b6 (nth 6 bits)))
                 (:instance id-and-gadget-bitp
                            (x (nth 0 wits)) (y (nth 1 wits)) (z partial))
                 (:instance id-and-gadget-bitp
                            (x partial) (y (nth 2 bits)) (z uscore))
                 id-byte-gadget-to-equations
                 (:instance id-first-extra-gadget-to-equations
                            (b4b3 (nth 0 wits))
                            (b1b0 (nth 1 wits))
                            (b2 (nth 2 bits))
                            (b6 (nth 6 bits)))
                 (:instance id-null-is-spec
                            (b5 (lookup-equal (nth 5 bits) asg))
                            (b6 (lookup-equal (nth 6 bits) asg))
                            (null (lookup-equal (nth 4 wits) asg))
                            (p p))
                 (:instance id-null-equals-validate-first
                            (b0 (lookup-equal (nth 0 bits) asg))
                            (b1 (lookup-equal (nth 1 bits) asg))
                            (b2 (lookup-equal (nth 2 bits) asg))
                            (b3 (lookup-equal (nth 3 bits) asg))
                            (b4 (lookup-equal (nth 4 bits) asg))
                            (b5 (lookup-equal (nth 5 bits) asg))
                            (b6 (lookup-equal (nth 6 bits) asg))
                            (b7 (lookup-equal (nth 7 bits) asg))
                            (b4b3 (lookup-equal (nth 0 wits) asg))
                            (b1b0 (lookup-equal (nth 1 wits) asg))
                            (m (lookup-equal (nth 2 wits) asg))
                            (r (lookup-equal (nth 3 wits) asg))
                            (null (lookup-equal (nth 4 wits) asg))
                            (lower (lookup-equal (nth 5 wits) asg))
                            (dor (lookup-equal (nth 6 wits) asg))
                            (idig (lookup-equal (nth 7 wits) asg))
                            (xor (lookup-equal (nth 8 wits) asg))
                            (bu (lookup-equal (nth 9 wits) asg))
                            (lor (lookup-equal (nth 10 wits) asg))
                            (bl (lookup-equal (nth 11 wits) asg))
                            (partial (lookup-equal partial asg))
                            (uscore (lookup-equal uscore asg))
                            (islet (lookup-equal islet asg))
                            (p p))
                 (:instance id-lookup-list-8 (keys bits) (asg asg)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(member-equal-of-nth
                         symbolp-of-nth
                         r1cs::fep-of-lookup-equal
                         r1cs::valuation-bindsp-when-valuation-binds-allp
                         primep-when-equal-base-prime
                         bitp-of-values-b-and
                         bitp-of-values-b-not
                         id-byte-equations
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff)
                         (:executable-counterpart cons)
                         (:executable-counterpart natp)
                         (:executable-counterpart <)
                         (:executable-counterpart len))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-trail-product-zero
  (implies (and (symbolp prev) (symbolp next)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-bindsp asg next)
                (bitp (lookup-equal prev asg))
                (bitp (lookup-equal next asg))
                (r1cs::r1cs-constraints-holdp
                 (id-trail-gadget prev next p) asg p))
           (equal (* (lookup-equal prev asg)
                     (values-b-not (lookup-equal next asg)))
                  0))
  :do-not-induct t
  :hints (("Goal"
           :use id-trail-gadget-to-mul
           :in-theory (e/d (id-sub1-of-bit
                            id-mul-of-bits
                            bitp-of-values-b-not
                            primep-when-equal-base-prime)
                           ((:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition id-trail-gadget)
                            pfield::mul-commutative)))))

(defruled id-trailing-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp nulls)
                (r1cs::valuation-binds-allp asg nulls)
                (bit-listp (lookup-equal-list nulls asg))
                (r1cs::r1cs-constraints-holdp
                 (id-trailing-gadget nulls p) asg p))
           (equal (validate-trailing-nulls (lookup-equal-list nulls asg))
                  t))
  :hints (("Goal"
           :induct (id-trailing-gadget nulls p)
           :in-theory (e/d (id-trailing-gadget
                            validate-trailing-nulls
                            lookup-equal-list
                            bit-listp
                            symbol-listp
                            acl2::bfix-when-bitp
                            id-trail-product-zero
                            (:definition r1cs::valuation-binds-allp)
                            r1cs::r1cs-constraints-holdp-of-append
                            primep-when-equal-base-prime)
                           ((:definition id-trail-gadget)
                            lookup-equal-of-nth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-lookup-nulls ((witrows true-listp) (asg alistp))
  :verify-guards nil
  (if (atom witrows)
      nil
    (cons (lookup-equal (nth 4 (car witrows)) asg)
          (id-lookup-nulls (cdr witrows) asg))))

(define id-rows-bitsp ((rows true-listp) (asg alistp))
  :verify-guards nil
  (if (atom rows)
      t
    (and (equal (len (car rows)) 8)
         (bit-listp (lookup-equal-list (car rows) asg))
         (id-rows-bitsp (cdr rows) asg))))

(define id-bitrows-all-boundp ((bitrows true-listp) (asg alistp))
  :verify-guards nil
  (if (atom bitrows)
      t
    (and (r1cs::valuation-binds-allp asg (car bitrows))
         (id-bitrows-all-boundp (cdr bitrows) asg))))

(defruled id-bit-checks-to-rows-bitsp
  (implies (and (id-bitrows-p bitrows)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-bitrows-all-boundp bitrows asg)
                (r1cs::r1cs-constraints-holdp
                 (id-bit-checks bitrows p) asg p))
           (id-rows-bitsp bitrows asg))
  :hints (("Goal"
           :in-theory (e/d (id-bit-checks
                            id-bitrows-p
                            id-bitrows-all-boundp
                            id-rows-bitsp
                            boolean-check-gadget-list-to-bit-listp
                            r1cs::r1cs-constraints-holdp-of-append
                            primep-when-equal-base-prime)
                           (lookup-equal-of-nth)))))

(defruled id-bitrows-bound-from-rows
  (implies (and (equal (len bitrows) (len witrows))
                (id-rows-boundp bitrows witrows asg))
           (id-bitrows-all-boundp bitrows asg))
  :hints (("Goal"
           :in-theory (enable id-rows-boundp
                              id-bitrows-all-boundp
                              len))))

(defruled id-row-8-bitps
  (implies (and (equal (len bits) 8)
                (bit-listp (lookup-equal-list bits asg)))
           (and (bitp (lookup-equal (nth 0 bits) asg))
                (bitp (lookup-equal (nth 1 bits) asg))
                (bitp (lookup-equal (nth 2 bits) asg))
                (bitp (lookup-equal (nth 3 bits) asg))
                (bitp (lookup-equal (nth 4 bits) asg))
                (bitp (lookup-equal (nth 5 bits) asg))
                (bitp (lookup-equal (nth 6 bits) asg))
                (bitp (lookup-equal (nth 7 bits) asg))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (lookup-equal-of-nth
                            bitp-of-nth-when-bit-listp
                            len-of-lookup-equal-list)
                           ((:definition nth))))))

(defun id-rest-induct (bytes bitrows witrows)
  (if (or (atom bytes) (atom bitrows) (atom witrows))
      nil
    (id-rest-induct (cdr bytes) (cdr bitrows) (cdr witrows))))

(defruled id-rest-nulls-sound
  (implies (and (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (acl2::ubyte8-listp bytes)
                (equal (len bytes) (len bitrows))
                (equal (len witrows) (len bitrows))
                (id-bits-matchp bytes bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg)
                (id-rows-bitsp bitrows asg)
                (r1cs::r1cs-constraints-holdp
                 (id-rest-bytes-gadget bitrows witrows p) asg p))
           (and (bit-listp (id-lookup-nulls witrows asg))
                (equal (values-validate-bytes-null-flags bytes nil)
                       (id-lookup-nulls witrows asg))))
  :hints (("Goal"
           :induct (id-rest-induct bytes bitrows witrows)
           :in-theory (e/d (id-rest-bytes-gadget
                            id-rest-induct
                            values-validate-bytes-null-flags
                            id-lookup-nulls
                            id-bits-matchp
                            id-rows-boundp
                            id-rows-bitsp
                            id-bitrows-p
                            id-witrows-p
                            lookup-equal-list
                            lookup-equal-of-nth
                            bit-listp
                            bitp-of-nth-when-bit-listp
                            len
                            acl2::ubyte8-listp
                            acl2::ubyte8-fix
                            not-reserrp-when-bitp
                            r1cs::r1cs-constraints-holdp-of-append)
                           (validate-byte
                            (:definition id-byte-gadget))))
          ("Subgoal *1/2"
           :do-not-induct t
           :use ((:instance id-row-8-bitps
                            (bits (car bitrows))
                            (asg asg))
                 (:instance id-byte-null-rest
                            (bits (car bitrows))
                            (wits (car witrows))
                            (p p)
                            (asg asg))))))

(defruled id-new-gadget-pieces
  (implies (r1cs::r1cs-constraints-holdp
            (identifier-new-gadget bitrows witrows partial uscore islet p)
            asg p)
           (and (r1cs::r1cs-constraints-holdp
                 (id-bit-checks bitrows p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget (car bitrows) (car witrows) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (id-first-extra-gadget (nth 0 (car witrows))
                                        (nth 1 (car witrows))
                                        (nth 2 (car bitrows))
                                        (nth 6 (car bitrows))
                                        partial uscore islet p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (id-trailing-gadget (id-null-symbols witrows) p) asg p)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (identifier-new-gadget
                            r1cs::r1cs-constraints-holdp-of-append)
                           ((:definition id-bit-checks)
                            (:definition id-byte-gadget)
                            (:definition id-first-extra-gadget)
                            (:definition id-rest-bytes-gadget)
                            (:definition id-trailing-gadget)
                            (:definition id-null-symbols)
                            (:definition nth))))))

(defruled id-null-symbols-lookup
  (implies (id-witrows-p witrows)
           (equal (lookup-equal-list (id-null-symbols witrows) asg)
                  (id-lookup-nulls witrows asg)))
  :hints (("Goal"
           :in-theory (enable id-null-symbols
                              id-lookup-nulls
                              id-witrows-p
                              lookup-equal-list
                              nth))))

(defruled id-null-symbols-boundp
  (implies (and (id-witrows-p witrows)
                (id-bitrows-p bitrows)
                (equal (len bitrows) (len witrows))
                (id-rows-boundp bitrows witrows asg))
           (r1cs::valuation-binds-allp asg (id-null-symbols witrows)))
  :hints (("Goal"
           :in-theory (e/d (id-null-symbols
                            id-rows-boundp
                            id-witrows-p
                            id-bitrows-p
                            len
                            member-equal-of-nth
                            symbolp-of-nth
                            (:definition r1cs::valuation-binds-allp))
                           ((:definition nth))))))

(defruled id-flags-sound
  (implies (and (consp bytes)
                (acl2::ubyte8-listp bytes)
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (consp bitrows)
                (consp witrows)
                (equal (len bytes) (len bitrows))
                (equal (len witrows) (len bitrows))
                (id-bits-matchp bytes bitrows asg)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (r1cs::r1cs-constraints-holdp
                 (identifier-new-gadget bitrows witrows
                                        partial uscore islet p)
                 asg p))
           (and (bit-listp (id-lookup-nulls witrows asg))
                (equal (values-validate-bytes-null-flags bytes t)
                       (id-lookup-nulls witrows asg))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-new-gadget-pieces
                 (:instance id-bit-checks-to-rows-bitsp)
                 (:instance id-bitrows-bound-from-rows)
                 (:instance id-first-byte-null
                            (bits (car bitrows))
                            (wits (car witrows)))
                 (:instance id-rest-nulls-sound
                            (bytes (cdr bytes))
                            (bitrows (cdr bitrows))
                            (witrows (cdr witrows))))
           :in-theory (e/d (values-validate-bytes-null-flags
                            id-lookup-nulls
                            id-bits-matchp
                            id-rows-boundp
                            id-rows-bitsp
                            id-bitrows-p
                            id-witrows-p
                            lookup-equal-of-nth
                            bit-listp
                            bitp-of-nth-when-bit-listp
                            len
                            acl2::ubyte8-listp
                            acl2::ubyte8-fix
                            not-reserrp-when-bitp
                            symbolp-of-nth
                            member-equal-of-nth)
                           (validate-byte
                            identifier-new-gadget
                            (:definition id-byte-gadget)
                            (:definition id-first-extra-gadget)
                            (:definition nth))))))

(defruled identifier-literal-new-when-valid
  (implies (and (identifier-literalp x)
                (equal (validate-identifier-bytes
                        (identifier-literal->bytes x))
                       t))
           (equal (identifier-literal-new x)
                  (identifier-literal-fix x)))
  :hints (("Goal"
           :in-theory (enable identifier-literal-new
                              validate-identifier-bytes))))

(defruled identifier-literal-new-sound-empty
  (implies (and (identifier-literalp x)
                (endp (identifier-literal->bytes x)))
           (equal (identifier-literal-new x)
                  (identifier-literal-fix x)))
  :hints (("Goal"
           :in-theory (enable identifier-literal-new
                              validate-identifier-bytes
                              values-validate-bytes-null-flags
                              validate-trailing-nulls))))

(defruled identifier-literal-new-sound
  (implies (and (identifier-literalp x)
                (consp (identifier-literal->bytes x))
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (consp bitrows)
                (consp witrows)
                (equal (len bitrows)
                       (len (identifier-literal->bytes x)))
                (equal (len witrows) (len bitrows))
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (id-rows-boundp bitrows witrows asg)
                (id-bits-matchp (identifier-literal->bytes x) bitrows asg)
                (r1cs::r1cs-constraints-holdp
                 (identifier-new-gadget bitrows witrows
                                        partial uscore islet p)
                 asg p))
           (equal (identifier-literal-new x)
                  (identifier-literal-fix x)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-flags-sound
                            (bytes (identifier-literal->bytes x)))
                 id-new-gadget-pieces
                 (:instance id-null-symbols-lookup)
                 (:instance id-null-symbols-boundp)
                 (:instance id-trailing-sound
                            (nulls (id-null-symbols witrows))))
           :in-theory (e/d (identifier-literal-new
                            validate-identifier-bytes
                            not-reserrp-when-bit-listp
                            bit-listp
                            reserrp)
                           (identifier-new-gadget
                            values-validate-bytes-null-flags
                            validate-trailing-nulls)))))

(defruled literal-identifier-new-sound-empty
  (implies (and (literalp x)
                (literal-case x :identifier)
                (endp (identifier-literal->bytes
                       (literal-identifier->get x))))
           (equal (literal-new x)
                  (literal-identifier
                   (identifier-literal-fix
                    (literal-identifier->get x)))))
  :hints (("Goal"
           :use (:instance identifier-literal-new-sound-empty
                           (x (literal-identifier->get x)))
           :in-theory (enable literal-new))))

(defruled literal-identifier-new-sound
  (implies (and (literalp x)
                (literal-case x :identifier)
                (consp (identifier-literal->bytes
                        (literal-identifier->get x)))
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (consp bitrows)
                (consp witrows)
                (equal (len bitrows)
                       (len (identifier-literal->bytes
                             (literal-identifier->get x))))
                (equal (len witrows) (len bitrows))
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (id-rows-boundp bitrows witrows asg)
                (id-bits-matchp (identifier-literal->bytes
                                 (literal-identifier->get x))
                                bitrows asg)
                (r1cs::r1cs-constraints-holdp
                 (literal-identifier-new-gadget
                  bitrows witrows partial uscore islet p)
                 asg p))
           (equal (literal-new x)
                  (literal-identifier
                   (identifier-literal-fix
                    (literal-identifier->get x)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance identifier-literal-new-sound
                           (x (literal-identifier->get x)))
           :in-theory (enable literal-new
                              literal-identifier-new-gadget))))
