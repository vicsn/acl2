; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group and address write_bits are the field bit decomposition of the
; x-coordinate (booleanity, power-of-two sum, and the range check), which
; is the gadget already verified as field-to-bits-gadget.  Big-endian is
; the reversal of those bits and adds no constraint.
;
; Completeness uses the canonical little-endian bits and the
; bits-lte-const fold witness (unit 1, final fold bit 0).
; A prime-5 assignment is the sample.  A 3-bit PFCS, the shape of that
; gadget at prime 5, is equivalent to the low three bits of the funspec
; for x-coordinates below 5.

(in-package "ALEOVM")

(include-book "../fun-specs/curve-group")
(include-book "../fun-specs/curve-address")
(include-book "../r1cs/field-to-bits")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-group-write-bits-le-gadget ((x symbolp)
                                        (xs symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-to-bits-gadget x xs rs u p))

(defruled crv-group-write-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-write-bits-le-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (lookup-equal-list xs asg)
                  (group-write-bits-le-funspec p0)))
  :do-not-induct t
  :enable (crv-group-write-bits-le-gadget
           group-write-bits-le-funspec
           curve-field-to-bits-le
           acl2::nat=>lebits-of-lebits=>nat
           acl2::bit-list-fix-when-bit-listp
           len-of-lookup-equal-list)
  :disable (acl2::nat=>lebits
            (:e acl2::nat=>lebits)
            acl2::bit-list-fix
            base-prime
            (:e base-prime)
            ecurve::edwards-bls12-q
            (:e ecurve::edwards-bls12-q)
            integer-length)
  :use (field-to-bits-soundness
        (:instance acl2::nat=>lebits-of-lebits=>nat
                   (digits (lookup-equal-list xs asg)))))

(defruled crv-group-write-bits-be-is-rev-le
  (implies (ecurve::edwards-bls12-pointp pt)
           (equal (group-write-bits-be-funspec pt)
                  (rev (group-write-bits-le-funspec pt))))
  :enable (group-write-bits-be-funspec
           group-write-bits-le-funspec
           curve-field-to-bits-be
           curve-field-to-bits-le
           acl2::nat=>bebits
           acl2::nat=>bendian
           acl2::nat=>lebits)
  :disable (acl2::nat=>lendian
            (:e acl2::nat=>lendian)
            (:e acl2::nat=>lebits)
            (:e acl2::nat=>bebits)
            (:e acl2::nat=>bendian)))

(define crv-group-write-bits-be-gadget ((x symbolp)
                                        (xs symbol-listp)
                                        (rs symbol-listp)
                                        (u symbolp)
                                        (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as little-endian.  The written list is reversed."
  (crv-group-write-bits-le-gadget x xs rs u p))

(defruled crv-group-write-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-group-write-bits-be-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (rev (lookup-equal-list xs asg))
                  (group-write-bits-be-funspec p0)))
  :do-not-induct t
  :enable (crv-group-write-bits-be-gadget
           crv-group-write-bits-be-is-rev-le)
  :disable (acl2::nat=>lebits
            (:e acl2::nat=>lebits)
            acl2::nat=>bebits
            acl2::nat=>lendian
            group-write-bits-le-funspec
            group-write-bits-be-funspec
            base-prime
            (:e base-prime)
            ecurve::edwards-bls12-q
            (:e ecurve::edwards-bls12-q)
            integer-length)
  :use crv-group-write-bits-le-gadget-sound)

(define crv-address-write-bits-le-gadget ((x symbolp)
                                          (xs symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-write-bits-le-gadget x xs rs u p))

(defruled crv-address-write-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-write-bits-le-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (lookup-equal-list xs asg)
                  (address-write-bits-le-funspec p0)))
  :do-not-induct t
  :enable (crv-address-write-bits-le-gadget
           address-write-bits-le-funspec)
  :disable (acl2::nat=>lebits
            (:e acl2::nat=>lebits)
            group-write-bits-le-funspec
            base-prime
            (:e base-prime)
            integer-length)
  :use crv-group-write-bits-le-gadget-sound)

(define crv-address-write-bits-be-gadget ((x symbolp)
                                          (xs symbol-listp)
                                          (rs symbol-listp)
                                          (u symbolp)
                                          (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (crv-group-write-bits-be-gadget x xs rs u p))

(defruled crv-address-write-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (equal (len xs) (base-field-size-in-bits))
                (primep p)
                (oddp p)
                (equal p (base-prime))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp p0)
                (equal (lookup-equal x asg) (ecurve::point-finite->x p0))
                (r1cs::r1cs-constraints-holdp
                 (crv-address-write-bits-be-gadget x xs rs u p) asg p)
                (equal (lookup-equal u asg) 1))
           (equal (rev (lookup-equal-list xs asg))
                  (address-write-bits-be-funspec p0)))
  :do-not-induct t
  :enable (crv-address-write-bits-be-gadget
           address-write-bits-be-funspec)
  :disable (acl2::nat=>lebits
            (:e acl2::nat=>lebits)
            acl2::nat=>bebits
            group-write-bits-be-funspec
            base-prime
            (:e base-prime)
            integer-length)
  :use crv-group-write-bits-be-gadget-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fold witness for bits-lte-const, in the same order as
; bits-lte-const-gadget-aux.  Each step is one and or one or.

(include-book "../library-extensions/digits")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../library-extensions/r1cses")
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/lists/take" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(define crv-lte-aux-witness ((xs bit-listp) (cs bit-listp))
  :guard (and (consp cs)
              (equal (len xs) (1+ (len cs))))
  :returns (rs bit-listp
               :hyp (and (bit-listp xs)
                         (bit-listp cs)
                         (consp cs)
                         (equal (len xs) (1+ (len cs))))
               :hints (("Goal" :in-theory (enable bitand bitor bitp))))
  (cond ((endp (cdr cs))
         (list (if (equal (car cs) 0)
                   (bitor (car xs) (cadr xs))
                 (bitand (car xs) (cadr xs)))))
        (t (b* ((cdr-rs (crv-lte-aux-witness (cdr xs) (cdr cs)))
                (car-rs (if (equal (car cs) 0)
                            (bitor (car xs) (car cdr-rs))
                          (bitand (car xs) (car cdr-rs)))))
             (cons car-rs cdr-rs))))
  ///
  (defret len-of-crv-lte-aux-witness
    (implies (and (consp cs)
                  (equal (len xs) (1+ (len cs))))
             (equal (len rs) (len cs)))
    :hints (("Goal" :in-theory (enable crv-lte-aux-witness))))

  (defret bit-listp-of-crv-lte-aux-witness-forward
    (implies (and (bit-listp xs)
                  (bit-listp cs)
                  (consp cs)
                  (equal (len xs) (1+ (len cs))))
             (bit-listp rs))
    :rule-classes ((:forward-chaining
                    :trigger-terms ((crv-lte-aux-witness xs cs))))
    :hints (("Goal" :in-theory (enable crv-lte-aux-witness bitand bitor bitp)))))

(define crv-lte-aux-induct ((xs true-listp)
                            (cs true-listp)
                            (rs true-listp))
  (cond ((or (endp xs) (endp (cdr xs)) (endp (cddr xs))
             (endp cs) (endp (cdr cs))
             (endp rs) (endp (cdr rs)))
         nil)
        (t (crv-lte-aux-induct (cdr xs) (cdr cs) (cdr rs)))))

(defruled crv-lookup-equal-list-of-cdr
  (implies (consp keys)
           (equal (lookup-equal-list (cdr keys) alist)
                  (cdr (lookup-equal-list keys alist))))
  :enable lookup-equal-list)

(defrule crv-bitp-of-lookup-car
  (implies (and (consp xs)
                (bit-listp (lookup-equal-list xs asg)))
           (bitp (lookup-equal (car xs) asg)))
  :enable (lookup-equal-of-car bit-listp)
  :disable lookup-equal-list)

(defrule crv-bit-listp-of-cdr-lookup
  (implies (and (consp xs)
                (bit-listp (lookup-equal-list xs asg)))
           (bit-listp (lookup-equal-list (cdr xs) asg)))
  :hints (("Goal"
           :in-theory (e/d (crv-lookup-equal-list-of-cdr bit-listp)
                           (lookup-equal-list)))))

(defrule crv-bitp-of-lookup-cadr
  (implies (and (consp (cdr xs))
                (bit-listp (lookup-equal-list xs asg)))
           (bitp (lookup-equal (cadr xs) asg)))
  :use ((:instance crv-bitp-of-lookup-car (xs (cdr xs)))
        crv-bit-listp-of-cdr-lookup)
  :disable crv-bitp-of-lookup-car)

(defrule crv-valuation-bindsp-of-cadr
  (implies (and (r1cs::valuation-binds-allp asg xs)
                (consp (cdr xs)))
           (r1cs::valuation-bindsp asg (cadr xs)))
  :hints (("Goal" :in-theory (enable r1cs::valuation-binds-allp))))

(defruled crv-or-step-holds
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (equal (lookup-equal z asg)
                       (bitor (lookup-equal x asg)
                              (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-or-gadget x y z p) asg p))
  :use boolean-or-gadget-to-bitor
  :disable (boolean-or-gadget-to-bitor bitor bitand))

(defrule crv-car-of-lookup-list
  (implies (consp xs)
           (equal (car (lookup-equal-list xs asg))
                  (lookup-equal (car xs) asg)))
  :hints (("Goal" :in-theory (enable lookup-equal-list))))

(defrule crv-consp-implies-pos-len
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear)

(defrule crv-witness-is-bit-listp
  (implies (and (bit-listp xs)
                (bit-listp cs)
                (consp cs)
                (equal (len xs) (1+ (len cs))))
           (bit-listp (crv-lte-aux-witness xs cs)))
  :enable (crv-lte-aux-witness bitand bitor bitp))

(defruled crv-and-step-holds
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (equal (lookup-equal z asg)
                       (bitand (lookup-equal x asg)
                               (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-and-gadget x y z) asg p))
  :use boolean-and-gadget-to-bitand
  :disable (boolean-and-gadget-to-bitand bitor bitand))

(defruled crv-lte-aux-witness-satisfies
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (bit-listp cs)
                (consp cs)
                (equal (len xs) (1+ (len cs)))
                (equal (len rs) (len cs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list rs asg)
                       (crv-lte-aux-witness (lookup-equal-list xs asg) cs)))
           (r1cs::r1cs-constraints-holdp
            (bits-lte-const-gadget-aux xs cs rs p) asg p))
  :hints (("Goal"
           :induct (crv-lte-aux-induct xs cs rs)
           :in-theory (e/d (crv-lte-aux-induct
                            crv-lte-aux-witness
                            bits-lte-const-gadget-aux
                            boolean-or-gadget-to-bitor
                            boolean-and-gadget-to-bitand
                            lookup-equal-list
                            crv-car-of-lookup-list
                            len-of-lookup-equal-list
                            crv-bitp-of-lookup-car
                            crv-witness-is-bit-listp
                            r1cs::valuation-binds-allp)
                           (bitp
                            lookup-equal-of-car
                            crv-lookup-equal-list-of-cdr
                            crv-bitp-of-lookup-cadr
                            (:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal *1/2"
           :use ((:instance crv-witness-is-bit-listp
                            (xs (cons (lookup-equal (cadr xs) asg)
                                      (lookup-equal-list (cddr xs) asg)))
                            (cs (cdr cs)))
                 (:instance crv-bitp-of-lookup-car
                            (xs (cdr rs)))))))

(defruled crv-r1cs-holdp-of-rev
  (equal (r1cs::r1cs-constraints-holdp (rev constrs) asg p)
         (r1cs::r1cs-constraints-holdp constrs asg p))
  :hints (("Goal" :in-theory (enable rev r1cs::r1cs-constraints-holdp))))

(define crv-bits-lte-const-witness ((xs bit-listp) (cs bit-listp))
  :guard (and (equal (len xs) (len cs))
              (member-equal 0 cs)
              (equal (car (last cs)) 1))
  :returns (rs bit-listp :hyp :guard)
  :short "Little-endian fold bits for @('bits-lte-const-gadget')."
  (b* ((rlen (bits-lte-const-rlen cs))
       (trimmed-xs (nthcdr (- (len xs) (1+ rlen)) xs))
       (trimmed-cs (nthcdr (- (len cs) rlen) cs)))
    (rev (crv-lte-aux-witness (rev trimmed-xs) (rev trimmed-cs))))
  ///
  (defret len-of-crv-bits-lte-const-witness
    (implies (and (equal (len xs) (len cs))
                  (member-equal 0 cs)
                  (equal (car (last cs)) 1))
             (equal (len rs) (bits-lte-const-rlen cs)))
    :hints (("Goal"
             :in-theory (enable crv-bits-lte-const-witness
                                crv-lte-aux-witness
                                bits-lte-const-rlen
                                rev)))))

(defruled crv-valuation-binds-allp-of-rev
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (rev xs)))
  :hints (("Goal" :in-theory (enable rev r1cs::valuation-binds-allp))))

(defruled crv-valuation-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr r1cs::valuation-binds-allp))))

(defruled crv-symbol-listp-of-rev
  (implies (symbol-listp xs)
           (symbol-listp (rev xs)))
  :hints (("Goal" :in-theory (enable rev symbol-listp))))

(defruled crv-symbol-listp-of-nthcdr
  (implies (symbol-listp xs)
           (symbol-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr symbol-listp))))

(defruled crv-bit-listp-of-rev
  (implies (bit-listp xs)
           (bit-listp (rev xs)))
  :hints (("Goal" :in-theory (enable rev bit-listp))))

(defruled crv-bit-listp-of-nthcdr
  (implies (bit-listp xs)
           (bit-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr bit-listp))))

(defruled crv-bits-lte-const-witness-satisfies
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (bit-listp cs)
                (equal (len xs) (len cs))
                (equal (len rs) (bits-lte-const-rlen cs))
                (member-equal 0 cs)
                (equal (car (last cs)) 1)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg) cs)))
           (r1cs::r1cs-constraints-holdp
            (bits-lte-const-gadget xs cs rs p) asg p))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (bits-lte-const-gadget
                            crv-bits-lte-const-witness
                            crv-r1cs-holdp-of-rev
                            lookup-equal-list-of-rev
                            lookup-equal-list-of-nthcdr
                            acl2::rev-of-rev
                            crv-valuation-binds-allp-of-rev
                            crv-valuation-binds-allp-of-nthcdr
                            crv-symbol-listp-of-rev
                            crv-symbol-listp-of-nthcdr
                            crv-bit-listp-of-rev
                            crv-bit-listp-of-nthcdr)
                           nil)
           :use (:instance crv-lte-aux-witness-satisfies
                           (xs (rev (nthcdr (- (len xs)
                                               (1+ (bits-lte-const-rlen cs)))
                                            xs)))
                           (cs (rev (nthcdr (- (len cs)
                                               (bits-lte-const-rlen cs))
                                            cs)))
                           (rs (rev rs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule crv-base-prime-integer-length
  (equal (integer-length (base-prime)) 253)
  :in-theory '((:e base-prime)
               (:e ecurve::edwards-bls12-q)
               (:e integer-length)))

(local
 (defthmd crv-base-prime-below-2-253-exec
   (< (base-prime) (expt 2 253))
   :hints (("Goal" :in-theory (enable (:e base-prime)
                                      (:e ecurve::edwards-bls12-q)
                                      (:e <)
                                      (:e expt))))))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q))))

(defrule crv-base-prime-below-2-253
  (< (base-prime) (expt 2 253))
  :rule-classes ((:linear :trigger-terms ((base-prime))))
  :hints (("Goal" :use crv-base-prime-below-2-253-exec
                  :in-theory (disable (:e base-prime)
                                      (:e ecurve::edwards-bls12-q)))))

(defrule crv-pm1-has-zero-bit
  (member-equal 0 (nat=>lebits* (1- (base-prime))))
  :hints (("Goal" :in-theory (enable (:e base-prime)
                                     (:e ecurve::edwards-bls12-q)
                                     (:e nat=>lebits*)
                                     (:e acl2::nat=>lendian*)))))

(defrule crv-pm1-msb-is-one
  (equal (car (last (nat=>lebits* (1- (base-prime))))) 1)
  :hints (("Goal" :in-theory (enable (:e base-prime)
                                     (:e ecurve::edwards-bls12-q)
                                     (:e nat=>lebits*)
                                     (:e acl2::nat=>lendian*)))))

(defrule crv-pm1-len-is-253
  (equal (len (nat=>lebits* (1- (base-prime)))) 253)
  :hints (("Goal" :in-theory (enable (:e base-prime)
                                     (:e ecurve::edwards-bls12-q)
                                     (:e nat=>lebits*)
                                     (:e acl2::nat=>lendian*)))))

(defrule crv-bits-lt-prime-rlen-is-252
  (equal (bits-lt-prime-rlen (base-prime)) 252)
  :hints (("Goal" :in-theory (enable bits-lt-prime-rlen
                                     bits-lte-const-rlen
                                     (:e base-prime)
                                     (:e ecurve::edwards-bls12-q)
                                     (:e nat=>lebits*)
                                     (:e acl2::nat=>lendian*)))))

(defrule crv-consp-when-len-252
  (implies (equal (len x) 252)
           (consp x)))

(defrule crv-bindsp-of-car-of-last
  (implies (and (r1cs::valuation-binds-allp asg rs)
                (consp rs))
           (r1cs::valuation-bindsp asg (car (last rs))))
  :hints (("Goal" :in-theory (enable last r1cs::valuation-binds-allp))))

(defruled crv-lebits=>nat-of-canonical
  (implies (and (natp x)
                (< x (base-prime)))
           (equal (lebits=>nat (acl2::nat=>lebits 253 x))
                  x))
  :enable acl2::lebits=>nat-of-nat=>lebits
  :disable ((:e base-prime) base-prime)
  :use crv-base-prime-below-2-253)

(defruled crv-bit-listp-of-canonical
  (implies (natp x)
           (bit-listp (acl2::nat=>lebits 253 x)))
  :enable acl2::bit-listp-of-nat=>lebits)

(defruled crv-symbolp-of-car-of-last
  (implies (and (symbol-listp rs)
                (consp rs))
           (symbolp (car (last rs))))
  :hints (("Goal" :in-theory (enable last symbol-listp))))

(defruled crv-lookup-of-car-of-last
  (implies (and (symbol-listp rs)
                (consp rs))
           (equal (lookup-equal (car (last rs)) asg)
                  (car (last (lookup-equal-list rs asg)))))
  :hints (("Goal"
           :in-theory (enable last
                              lookup-equal-list
                              car-of-lookup-equal-list
                              last-of-lookup-equal-list))))

(defruled crv-bits-lt-prime-when-witness
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p)))))
           (r1cs::r1cs-constraints-holdp
            (bits-lt-prime-gadget xs rs p) asg p))
  :do-not-induct t
  :enable (bits-lt-prime-gadget
           bits-lt-prime-rlen
           crv-bits-lte-const-witness-satisfies
           crv-pm1-has-zero-bit
           crv-pm1-msb-is-one
           crv-pm1-len-is-253
           crv-base-prime-integer-length)
  :disable (base-prime (:e base-prime)
            integer-length))

(defruled crv-field-to-bits-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (natp (lookup-equal x asg))
                (< (lookup-equal x asg) p)
                (equal (lookup-equal-list xs asg)
                       (acl2::nat=>lebits (integer-length p)
                                          (lookup-equal x asg)))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (field-to-bits-gadget x xs rs u p) asg p))
  :do-not-induct t
  :enable (field-to-bits-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           zero-unit-gadget-to-equal-0
           crv-lebits=>nat-of-canonical
           crv-bit-listp-of-canonical
           crv-base-prime-integer-length
           crv-pm1-len-is-253
           crv-symbolp-of-car-of-last
           crv-lookup-of-car-of-last
           crv-bindsp-of-car-of-last
           crv-consp-when-len-252
           crv-bits-lt-prime-rlen-is-252
           acl2::len-of-nat=>lebits
           acl2::mod-when-<
           r1cs::fep-of-lookup-equal)
  :disable (base-prime (:e base-prime)
            integer-length
            (:e integer-length)
            (:e nat=>lebits*)
            (:e bits-lt-prime-rlen)
            bits-lt-prime-rlen
            (:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            crv-bits-lt-prime-when-witness)
  :use ((:instance crv-bits-lt-prime-when-witness)
        (:instance bits-lt-prime-soundness (x x))
        (:instance crv-lebits=>nat-of-canonical
                   (x (lookup-equal x asg)))))

(defruled crv-group-write-bits-are-canonical
  (implies (ecurve::edwards-bls12-pointp pt)
           (equal (group-write-bits-le-funspec pt)
                  (acl2::nat=>lebits 253 (ecurve::point-finite->x pt))))
  :enable (group-write-bits-le-funspec
           curve-field-to-bits-le
           base-field-size-in-bits))

(defruled crv-group-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg)
                       (ecurve::point-finite->x pt))
                (equal (lookup-equal-list xs asg)
                       (group-write-bits-le-funspec pt))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-write-bits-le-gadget x xs rs u p) asg p))
  :do-not-induct t
  :enable (crv-group-write-bits-le-gadget
           crv-group-write-bits-are-canonical
           crv-field-to-bits-gadget-complete
           crv-base-prime-integer-length
           curve-edwards-bls12-coordinates-are-fields
           pfield::fep)
  :disable (base-prime (:e base-prime)
            integer-length bits-lt-prime-rlen))

(defruled crv-group-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg)
                       (ecurve::point-finite->x pt))
                (equal (lookup-equal-list xs asg)
                       (group-write-bits-le-funspec pt))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (crv-group-write-bits-be-gadget x xs rs u p) asg p))
  :enable (crv-group-write-bits-be-gadget
           crv-group-write-bits-le-gadget-complete))

(defruled crv-address-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg)
                       (ecurve::point-finite->x pt))
                (equal (lookup-equal-list xs asg)
                       (address-write-bits-le-funspec pt))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (crv-address-write-bits-le-gadget x xs rs u p) asg p))
  :enable (crv-address-write-bits-le-gadget
           address-write-bits-le-funspec
           crv-group-write-bits-le-gadget-complete))

(defruled crv-address-write-bits-be-gadget-is-le
  (equal (crv-address-write-bits-be-gadget x xs rs u p)
         (crv-address-write-bits-le-gadget x xs rs u p))
  :enable (crv-address-write-bits-be-gadget
           crv-group-write-bits-be-gadget
           crv-address-write-bits-le-gadget))

(defruled crv-address-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (ecurve::edwards-bls12-pointp pt)
                (equal (lookup-equal x asg)
                       (ecurve::point-finite->x pt))
                (equal (lookup-equal-list xs asg)
                       (address-write-bits-le-funspec pt))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal u asg) 1))
           (r1cs::r1cs-constraints-holdp
            (crv-address-write-bits-be-gadget x xs rs u p) asg p))
  :do-not-induct t
  :enable (crv-address-write-bits-be-gadget-is-le
           crv-address-write-bits-le-gadget-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value 1 at prime 5.  Little-endian bits (1 0 0).
; p - 1 = (0 0 1), so the fold is z0 = b1 OR b0 and z1 = b2 AND z0.

(defconst *crv-write-bits-sample*
  '((x . 1) (b0 . 1) (b1 . 0) (b2 . 0) (z0 . 1) (z1 . 0) (u . 1)))

(defconst *crv-write-bits-prime* 5)

(defruled crv-group-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crv-group-write-bits-le-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                   *crv-write-bits-prime*)
   *crv-write-bits-sample*
   *crv-write-bits-prime*)
  :hints (("Goal"
           :in-theory (enable crv-group-write-bits-le-gadget
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
                              r1cs::r1cs-constraints-holdp
                              r1cs::r1cs-constraint-holdsp
                              r1cs::dot-product
                              lookup-equal
                              pfield::add
                              pfield::mul))))

(defruled crv-group-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crv-group-write-bits-be-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                   *crv-write-bits-prime*)
   *crv-write-bits-sample*
   *crv-write-bits-prime*)
  :enable (crv-group-write-bits-be-gadget
           crv-group-write-bits-le-sample-holds))

(defruled crv-address-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crv-address-write-bits-le-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                     *crv-write-bits-prime*)
   *crv-write-bits-sample*
   *crv-write-bits-prime*)
  :enable (crv-address-write-bits-le-gadget
           crv-group-write-bits-le-sample-holds))

(defruled crv-address-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp
   (crv-address-write-bits-be-gadget 'x '(b0 b1 b2) '(z0 z1) 'u
                                     *crv-write-bits-prime*)
   *crv-write-bits-sample*
   *crv-write-bits-prime*)
  :enable (crv-address-write-bits-be-gadget
           crv-address-write-bits-le-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Three-bit PFCS.  At prime 5 the range fold is two constraints, and the
; accepted values are exactly the field elements below 5.  Those are the
; low three little-endian bits of the 253-bit funspec (the other 250 bits
; are zero).  Big-endian writes the reverse, so the same three bits are
; the last three of the 253-bit big-endian list.

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/bitp-idioms" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel" :dir :system))

(local
 (defthmd crv-wb3-base-prime-above-16-exec
   (< 16 (base-prime))
   :hints (("Goal" :in-theory (enable (:e base-prime)
                                      (:e ecurve::edwards-bls12-q))))))

(defrule crv-wb3-base-prime-above-16
  (< 16 (base-prime))
  :rule-classes ((:linear :trigger-terms ((base-prime))))
  :hints (("Goal" :use crv-wb3-base-prime-above-16-exec
                  :in-theory (disable (:e base-prime)
                                      (:e ecurve::edwards-bls12-q)))))

(defruled crv-wb3-bool-check-is-bitp
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep b p))
           (equal (equal (pfield::mul (pfield::sub (mod 1 p) b p) b p)
                         (mod 0 p))
                  (bitp b)))
  :enable (pfield::sub
           pfield::bitp-idiom-2-alt
           acl2::mod-of-0-arg1
           acl2::mod-of-1-arg1
           crv-wb3-base-prime-above-16)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            (:rewrite pfield::bitp-idiom-2)))

(defruled crv-wb3-neg-is-zero
  (implies (and (pfield::fep z p)
                (integerp p))
           (equal (equal (pfield::neg z p) 0)
                  (equal z 0)))
  :hints (("Goal"
           :cases ((equal z 0))
           :in-theory (e/d (pfield::neg pfield::neg-of-neg pfield::fep
                                        acl2::mod-of-0-arg1)
                           (pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled crv-wb3-sub1-iff-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep z p))
           (equal (equal (pfield::sub 1 z p) 1)
                  (equal z 0)))
  :enable (pfield::sub crv-wb3-neg-is-zero pfield::fep-holds
                       crv-wb3-base-prime-above-16)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance pfield::equal-of-add-cancel-1
                  (x 1)
                  (y (pfield::neg z (base-prime)))
                  (p (base-prime))))

(defruled crv-wb3-sub1-iff-one
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep z p))
           (equal (equal (pfield::sub 1 z p) 0)
                  (equal z 1)))
  :enable (pfield::sub
           pfield::fep-holds
           crv-wb3-base-prime-above-16
           pfield::equal-of-0-and-add-of-neg-arg1
           pfield::add-commutative)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance pfield::equal-of-0-and-add-of-neg-arg1
                  (x z)
                  (y 1)
                  (p (base-prime))))

(defruled crv-wb3-unit-is-one
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep u p))
           (equal (equal (pfield::mul u (mod 1 p) p)
                         (mod 1 p))
                  (equal u 1)))
  :enable (acl2::mod-of-1-arg1
           pfield::mul-of-1-arg2
           crv-wb3-base-prime-above-16))

(defruled crv-wb3-zero-unit-is-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (equal u 1)
                (pfield::fep z p))
           (equal (equal (pfield::mul (pfield::sub u z p) (mod 1 p) p)
                         (mod 1 p))
                  (equal z 0)))
  :enable (crv-wb3-unit-is-one crv-wb3-sub1-iff-zero pfield::mul-of-1-arg2
           acl2::mod-of-1-arg1))

(defruled crv-wb3-weighted-3
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (pfield::fep x p))
           (equal (equal (pfield::mul x (mod 1 p) p)
                         (pfield::add
                          (pfield::add b0
                                       (pfield::mul (mod 2 p) b1 p)
                                       p)
                          (pfield::mul (mod 4 p) b2 p)
                          p))
                  (equal x (+ b0 (* 2 b1) (* 4 b2)))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            acl2::mod-of-1-arg1
                            acl2::mod-when-<
                            pfield::mul-of-1-arg2
                            crv-wb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::add)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

(defruled crv-wb3-or-is-bitor
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp a)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul (pfield::sub (mod 1 p) a p)
                                      (pfield::sub (mod 1 p) b p)
                                      p)
                         (pfield::sub (mod 1 p) z p))
                  (equal z (bitor a b))))
  :hints (("Goal"
           :cases ((equal a 0) (equal a 1))
           :in-theory (e/d (bitp bitor
                            pfield::sub
                            acl2::mod-of-1-arg1
                            crv-wb3-sub1-iff-zero
                            crv-wb3-sub1-iff-one
                            crv-wb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e pfield::add)
                            (:e pfield::neg)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b 0) (equal b 1)))
          ("Subgoal 2" :cases ((equal b 0) (equal b 1)))))

(defruled crv-wb3-mul-is-bitand
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp a)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul a b p) z)
                  (equal z (bitand a b))))
  :hints (("Goal"
           :cases ((equal a 0) (equal a 1))
           :in-theory (e/d (bitp bitand
                            crv-wb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))
          ("Subgoal 1" :cases ((equal b 0) (equal b 1)))
          ("Subgoal 2" :cases ((equal b 0) (equal b 1)))))

(defruled crv-wb3-three-bits-below-5
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal x (+ b0 (* 2 b1) (* 4 b2))))
           (< x 5))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (enable bitp bitor bitand))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

(defruled crv-wb3-bits-match-le
  (implies (and (equal p (base-prime))
                (pfield::fep x p)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt))
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal x (+ b0 (* 2 b1) (* 4 b2))))
           (and (equal (list b0 b1 b2)
                       (take 3 (group-write-bits-le-funspec pt)))
                (equal (list b0 b1 b2)
                       (take 3 (address-write-bits-le-funspec pt)))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            group-write-bits-le-funspec
                            address-write-bits-le-funspec
                            curve-field-to-bits-le
                            base-field-size-in-bits
                            lnfix
                            pfield::fep
                            (:e acl2::nat=>lebits)
                            (:e take)
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q))
                           nil))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

(defruled crv-wb3-bits-match-be
  (implies (and (equal p (base-prime))
                (pfield::fep x p)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt))
                (bitp w0)
                (bitp w1)
                (bitp w2)
                (equal x (+ w2 (* 2 w1) (* 4 w0))))
           (and (equal (list w0 w1 w2)
                       (nthcdr 250 (group-write-bits-be-funspec pt)))
                (equal (list w0 w1 w2)
                       (nthcdr 250 (address-write-bits-be-funspec pt)))))
  :hints (("Goal"
           :cases ((equal w2 0) (equal w2 1))
           :in-theory (e/d (bitp
                            crv-group-write-bits-be-is-rev-le
                            address-write-bits-be-funspec
                            group-write-bits-le-funspec
                            curve-field-to-bits-le
                            base-field-size-in-bits
                            lnfix
                            pfield::fep
                            (:e acl2::nat=>lebits)
                            (:e rev)
                            (:e nthcdr)
                            (:e take)
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q))
                           (group-write-bits-be-funspec)))
          ("Subgoal 1" :cases ((equal w1 0) (equal w1 1)))
          ("Subgoal 2" :cases ((equal w1 0) (equal w1 1)))
          ("Subgoal 1.1" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 1.2" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 2.1" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 2.2" :cases ((equal w0 0) (equal w0 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crv-write-bits-le-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for group and address @('write_bits_le')."
  (pfcs::parse-def
   "crv_write_bits_le_3(x, b0, b1, b2, z0, z1, u) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (1 - b2) * (b2) == (0),
    (u) * (1) == (1),
    (u - z1) * (1) == (1),
    (x) * (1) == (b0 + 2 * b1 + 4 * b2),
    (1 - b1) * (1 - b0) == (1 - z0),
    (b2) * (z0) == (z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-write-bits-le-3-circuit)
            :pred crv-write-bits-le-3-pred
            :prime prime)

(defthm crv-write-bits-le-3-pred-to-arith
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (crv-write-bits-le-3-pred x b0 b1 b2 z0 z1 u prime))
           (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal u 1)
                (equal z1 0)
                (equal x (+ b0 (* 2 b1) (* 4 b2)))
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (crv-write-bits-le-3-pred
                            crv-wb3-bool-check-is-bitp
                            crv-wb3-unit-is-one
                            crv-wb3-zero-unit-is-zero
                            crv-wb3-weighted-3
                            crv-wb3-or-is-bitor
                            crv-wb3-mul-is-bitand)
                           (bitp)))))

(defruled crv-write-bits-le-3-arith-to-pred
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal u 1)
                (equal z1 0)
                (equal x (+ b0 (* 2 b1) (* 4 b2)))
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0)))
           (crv-write-bits-le-3-pred x b0 b1 b2 z0 z1 u prime))
  :enable (crv-write-bits-le-3-pred
           crv-wb3-bool-check-is-bitp
           crv-wb3-unit-is-one
           crv-wb3-zero-unit-is-zero
           crv-wb3-weighted-3
           crv-wb3-or-is-bitor
           crv-wb3-mul-is-bitand))

(defruled crv-group-write-bits-le-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt)))
           (iff (crv-write-bits-le-3-pred x b0 b1 b2 z0 z1 u prime)
                (and (bitp b0)
                       (bitp b1)
                       (bitp b2)
                       (equal u 1)
                       (equal z1 0)
                       (equal x (+ b0 (* 2 b1) (* 4 b2)))
                       (equal z0 (bitor b1 b0))
                       (equal z1 (bitand b2 z0))
                       (equal (list b0 b1 b2)
                              (take 3 (group-write-bits-le-funspec pt)))
                       (< x 5))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance crv-write-bits-le-3-pred-to-arith)
                 (:instance crv-write-bits-le-3-arith-to-pred)
                 (:instance crv-wb3-bits-match-le (p prime))
                 (:instance crv-wb3-three-bits-below-5))
           :in-theory (union-theories '(iff)
                                      (theory 'minimal-theory)))))

(defruled crv-address-write-bits-le-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt)))
           (iff (crv-write-bits-le-3-pred x b0 b1 b2 z0 z1 u prime)
                (and (bitp b0)
                     (bitp b1)
                     (bitp b2)
                     (equal u 1)
                     (equal z1 0)
                     (equal x (+ b0 (* 2 b1) (* 4 b2)))
                     (equal z0 (bitor b1 b0))
                     (equal z1 (bitand b2 z0))
                     (equal (list b0 b1 b2)
                            (take 3 (address-write-bits-le-funspec pt)))
                     (< x 5))))
  :hints (("Goal"
           :do-not-induct t
           :use crv-group-write-bits-le-3-pred-to-funspec
           :in-theory (union-theories '(iff address-write-bits-le-funspec)
                                      (theory 'minimal-theory)))))

(define crv-write-bits-be-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for group and address @('write_bits_be').
          @('w0') is the most significant of the three low bits."
  (pfcs::parse-def
   "crv_write_bits_be_3(x, w0, w1, w2, z0, z1, u) := {
    (1 - w2) * (w2) == (0),
    (1 - w1) * (w1) == (0),
    (1 - w0) * (w0) == (0),
    (u) * (1) == (1),
    (u - z1) * (1) == (1),
    (x) * (1) == (w2 + 2 * w1 + 4 * w0),
    (1 - w1) * (1 - w2) == (1 - z0),
    (w0) * (z0) == (z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (crv-write-bits-be-3-circuit)
            :pred crv-write-bits-be-3-pred
            :prime prime)

(defthm crv-write-bits-be-3-pred-to-arith
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep w0 prime)
                (pfield::fep w1 prime)
                (pfield::fep w2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (crv-write-bits-be-3-pred x w0 w1 w2 z0 z1 u prime))
           (and (bitp w2)
                (bitp w1)
                (bitp w0)
                (equal u 1)
                (equal z1 0)
                (equal x (+ w2 (* 2 w1) (* 4 w0)))
                (equal z0 (bitor w1 w2))
                (equal z1 (bitand w0 z0))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (crv-write-bits-be-3-pred
                            crv-wb3-bool-check-is-bitp
                            crv-wb3-unit-is-one
                            crv-wb3-zero-unit-is-zero
                            crv-wb3-weighted-3
                            crv-wb3-or-is-bitor
                            crv-wb3-mul-is-bitand)
                           (bitp)))))

(defruled crv-write-bits-be-3-arith-to-pred
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep w0 prime)
                (pfield::fep w1 prime)
                (pfield::fep w2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (bitp w2)
                (bitp w1)
                (bitp w0)
                (equal u 1)
                (equal z1 0)
                (equal x (+ w2 (* 2 w1) (* 4 w0)))
                (equal z0 (bitor w1 w2))
                (equal z1 (bitand w0 z0)))
           (crv-write-bits-be-3-pred x w0 w1 w2 z0 z1 u prime))
  :enable (crv-write-bits-be-3-pred
           crv-wb3-bool-check-is-bitp
           crv-wb3-unit-is-one
           crv-wb3-zero-unit-is-zero
           crv-wb3-weighted-3
           crv-wb3-or-is-bitor
           crv-wb3-mul-is-bitand))

(defruled crv-group-write-bits-be-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep w0 prime)
                (pfield::fep w1 prime)
                (pfield::fep w2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt)))
           (iff (crv-write-bits-be-3-pred x w0 w1 w2 z0 z1 u prime)
                (and (bitp w2)
                       (bitp w1)
                       (bitp w0)
                       (equal u 1)
                       (equal z1 0)
                       (equal x (+ w2 (* 2 w1) (* 4 w0)))
                       (equal z0 (bitor w1 w2))
                       (equal z1 (bitand w0 z0))
                       (equal (list w0 w1 w2)
                              (nthcdr 250 (group-write-bits-be-funspec pt)))
                       (< x 5))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance crv-write-bits-be-3-pred-to-arith)
                 (:instance crv-write-bits-be-3-arith-to-pred)
                 (:instance crv-wb3-bits-match-be (p prime))
                 (:instance crv-wb3-three-bits-below-5
                            (b0 w2) (b1 w1) (b2 w0)
                            (z0 z0) (z1 z1) (x x)))
           :in-theory (union-theories '(iff)
                                      (theory 'minimal-theory)))))

(defruled crv-address-write-bits-be-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (pfield::fep x prime)
                (pfield::fep w0 prime)
                (pfield::fep w1 prime)
                (pfield::fep w2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime)
                (ecurve::edwards-bls12-pointp pt)
                (equal x (ecurve::point-finite->x pt)))
           (iff (crv-write-bits-be-3-pred x w0 w1 w2 z0 z1 u prime)
                (and (bitp w2)
                     (bitp w1)
                     (bitp w0)
                     (equal u 1)
                     (equal z1 0)
                     (equal x (+ w2 (* 2 w1) (* 4 w0)))
                     (equal z0 (bitor w1 w2))
                     (equal z1 (bitand w0 z0))
                     (equal (list w0 w1 w2)
                            (nthcdr 250
                                    (address-write-bits-be-funspec pt)))
                     (< x 5))))
  :hints (("Goal"
           :do-not-induct t
           :use crv-group-write-bits-be-3-pred-to-funspec
           :in-theory (union-theories '(iff address-write-bits-be-funspec)
                                      (theory 'minimal-theory)))))
