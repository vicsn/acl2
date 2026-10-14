; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness for Boolean::is_less_than_or_equal_constant and
; Boolean::assert_less_than_or_equal_constant.
;
; bits-lte-const-soundness already says that a satisfying assignment
; makes the last fold bit 0 exactly when the little-endian value is at
; most the constant.  The missing direction is the witness: the fold
; bits snarkVM would compute, built the same way as
; bits-lte-const-gadget-aux.  Each step is one and or one or, whose
; gadgets are iffs.  Asserting the comparison zeros that last bit,
; which is 0 precisely when the funspec bit is 1.
;
; The constant must contain a 0 and end with 1, which is the guard of
; bits-lte-const-gadget.  An all-ones constant makes the comparison
; true with no constraints; that case is not this gadget.

(in-package "ALEOVM")

(include-book "fb-boolean-bits")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../library-extensions/r1cses")
(include-book "std/lists/rev" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb-lte-aux-witness ((xs bit-listp) (cs bit-listp))
  :guard (and (consp cs)
              (equal (len xs) (1+ (len cs))))
  :returns (rs bit-listp
               :hyp (and (bit-listp xs)
                         (bit-listp cs)
                         (consp cs)
                         (equal (len xs) (1+ (len cs))))
               :hints (("Goal" :in-theory (enable bitand bitor bitp))))
  :short "Fold bits for @('bits-lte-const-gadget-aux'), in that function's
          argument order."
  (cond ((endp (cdr cs))
         (list (if (equal (car cs) 0)
                   (bitor (car xs) (cadr xs))
                 (bitand (car xs) (cadr xs)))))
        (t (b* ((cdr-rs (fb-lte-aux-witness (cdr xs) (cdr cs)))
                (car-rs (if (equal (car cs) 0)
                            (bitor (car xs) (car cdr-rs))
                          (bitand (car xs) (car cdr-rs)))))
             (cons car-rs cdr-rs))))
  ///
  (defret len-of-fb-lte-aux-witness
    (implies (and (consp cs)
                  (equal (len xs) (1+ (len cs))))
             (equal (len rs) (len cs)))
    :hints (("Goal" :in-theory (enable fb-lte-aux-witness)))))

(define fb-lte-aux-induct ((xs true-listp)
                           (cs true-listp)
                           (rs true-listp))
  (if (or (endp cs) (endp (cdr cs)) (endp xs) (endp rs))
      nil
    (fb-lte-aux-induct (cdr xs) (cdr cs) (cdr rs))))

(defruled fb-lookup-equal-list-of-cdr
  (implies (consp keys)
           (equal (lookup-equal-list (cdr keys) alist)
                  (cdr (lookup-equal-list keys alist))))
  :enable lookup-equal-list)

(defruled fb-lte-aux-witness-satisfies
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
                       (fb-lte-aux-witness (lookup-equal-list xs asg) cs)))
           (r1cs::r1cs-constraints-holdp
            (bits-lte-const-gadget-aux xs cs rs p) asg p))
  :hints (("Goal"
           :induct (fb-lte-aux-induct xs cs rs)
           :in-theory (e/d (fb-lte-aux-induct
                            fb-lte-aux-witness
                            bits-lte-const-gadget-aux
                            fb-lookup-equal-list-of-cdr
                            lookup-equal-of-car
                            boolean-and-gadget-to-bitand
                            boolean-or-gadget-to-bitor
                            bitand
                            bitor
                            bitp
                            r1cs::valuation-binds-allp)
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb-r1cs-holdp-of-rev
  (equal (r1cs::r1cs-constraints-holdp (rev constrs) asg p)
         (r1cs::r1cs-constraints-holdp constrs asg p))
  :hints (("Goal" :in-theory (enable rev r1cs::r1cs-constraints-holdp))))

(define fb-bits-lte-const-witness ((xs bit-listp) (cs bit-listp))
  :guard (and (equal (len xs) (len cs))
              (member-equal 0 cs)
              (equal (car (last cs)) 1))
  :returns (rs bit-listp :hyp :guard)
  :short "Little-endian fold bits for @('bits-lte-const-gadget')."
  (b* ((rlen (bits-lte-const-rlen cs))
       (trimmed-xs (nthcdr (- (len xs) (1+ rlen)) xs))
       (trimmed-cs (nthcdr (- (len cs) rlen) cs)))
    (rev (fb-lte-aux-witness (rev trimmed-xs) (rev trimmed-cs))))
  ///
  (defret len-of-fb-bits-lte-const-witness
    (implies (and (equal (len xs) (len cs))
                  (member-equal 0 cs)
                  (equal (car (last cs)) 1))
             (equal (len rs) (bits-lte-const-rlen cs)))
    :hints (("Goal"
             :in-theory (enable fb-bits-lte-const-witness
                                fb-lte-aux-witness
                                bits-lte-const-rlen
                                rev)))))

(defruled fb-valuation-binds-allp-of-rev
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (rev xs)))
  :hints (("Goal" :in-theory (enable rev r1cs::valuation-binds-allp))))

(defruled fb-valuation-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp asg xs)
           (r1cs::valuation-binds-allp asg (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr r1cs::valuation-binds-allp))))

(defruled fb-symbol-listp-of-rev
  (implies (symbol-listp xs)
           (symbol-listp (rev xs)))
  :hints (("Goal" :in-theory (enable rev symbol-listp))))

(defruled fb-symbol-listp-of-nthcdr
  (implies (symbol-listp xs)
           (symbol-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr symbol-listp))))

(defruled fb-bit-listp-of-rev
  (implies (bit-listp xs)
           (bit-listp (rev xs)))
  :hints (("Goal" :in-theory (enable rev bit-listp))))

(defruled fb-bit-listp-of-nthcdr
  (implies (bit-listp xs)
           (bit-listp (nthcdr n xs)))
  :hints (("Goal" :in-theory (enable nthcdr bit-listp))))

(defruled fb-bits-lte-const-witness-satisfies
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
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg) cs)))
           (r1cs::r1cs-constraints-holdp
            (bits-lte-const-gadget xs cs rs p) asg p))
  :do-not-induct t
  :enable (bits-lte-const-gadget
           fb-bits-lte-const-witness
           fb-r1cs-holdp-of-rev
           lookup-equal-list-of-rev
           lookup-equal-list-of-nthcdr
           rev-of-rev
           fb-valuation-binds-allp-of-rev
           fb-valuation-binds-allp-of-nthcdr
           fb-symbol-listp-of-rev
           fb-symbol-listp-of-nthcdr
           fb-bit-listp-of-rev
           fb-bit-listp-of-nthcdr)
  :use (:instance fb-lte-aux-witness-satisfies
                  (xs (rev (nthcdr (- (len xs) (1+ (bits-lte-const-rlen cs)))
                                   xs)))
                  (cs (rev (nthcdr (- (len cs) (bits-lte-const-rlen cs)) cs)))
                  (rs (rev rs))))

(defruled fb-boolean-is-lte-const-gadget-complete
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (bit-listp cs)
                (equal (len xs) (len cs))
                (equal (len rs) (bits-lte-const-rlen cs))
                (member-equal 0 cs)
                (equal (car (last cs)) 1)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg) cs)))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-boolean-is-lte-const-gadget xs cs rs p) asg p)
                (equal (pfield::sub 1
                                    (car (last (lookup-equal-list rs asg)))
                                    p)
                       (boolean-is-less-than-or-equal-constant-funspec
                        (lookup-equal-list xs asg) cs))))
  :do-not-induct t
  :enable (fb-boolean-is-lte-const-gadget
           fb-bits-lte-const-witness-satisfies)
  :use fb-boolean-is-lte-const-gadget-sound)

(defruled fb-boolean-assert-lte-const-gadget-complete
  (implies (and (symbol-listp xs)
                (symbol-listp rs)
                (bit-listp cs)
                (equal (len xs) (len cs))
                (equal (len rs) (bits-lte-const-check-rlen cs))
                (member-equal 0 cs)
                (equal (car (last cs)) 1)
                (equal p (base-prime))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (equal (boolean-is-less-than-or-equal-constant-funspec
                        (lookup-equal-list xs asg) cs)
                       1)
                (equal (lookup-equal-list rs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg) cs)))
           (r1cs::r1cs-constraints-holdp
            (fb-boolean-assert-lte-const-gadget xs cs rs p) asg p))
  :do-not-induct t
  :enable (fb-boolean-assert-lte-const-gadget
           bits-lte-const-check-gadget
           bits-lte-const-check-rlen
           zero-gadget-list
           zero-gadget-to-equal-0
           last-of-lookup-equal-list
           car-of-lookup-equal-list
           fb-boolean-is-lte-const-gadget-complete
           bitp)
  :disable ((:definition pfield::sub)))
