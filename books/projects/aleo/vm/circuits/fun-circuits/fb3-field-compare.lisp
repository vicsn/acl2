; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Completeness, samples, and PFCS for the field comparisons.
;
; is_less_than is field-lt-gadget.  The canonical witness is the
; little-endian bits of each operand, the write_bits fold against
; p - 1, and the bits-lt fold.  is_greater_than swaps the operands.
; The or-equal forms are the same constraints; the result boolean is
; the linear combination 1 - r.
;
; The PFCSs are the same comparison at two bits.  Both operands are
; then below 4, so the range check is redundant, as it is for
; to_lower_bits at k = 2.  The result bit is not free.

(in-package "ALEOVM")

(include-book "fb-field-compare")
(include-book "fb3-field-write-bits")
(include-book "../r1cs/bits-lt")
(include-book "../library-extensions/bit-lists")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-bits-lt-r ((ds bit-listp) (ys bit-listp) (p primep))
  :guard (equal (len ys) (len ds))
  :returns (rs bit-listp
               :hyp (and (bit-listp ds)
                         (bit-listp ys)
                         (equal (len ys) (len ds)))
               :hints (("Goal" :in-theory (enable if0 bitp))))
  :short "Big-endian fold of @('bits-lt-gadget-aux')."
  (cond ((endp ds) nil)
        ((endp (cdr ds)) (list (if0 (car ds) (car ys) p)))
        (t (b* ((cdr-rs (fb3-bits-lt-r (cdr ds) (cdr ys) p)))
             (cons (if (= (car ds) 1)
                       (car ys)
                     (car cdr-rs))
                   cdr-rs))))
  ///
  (defret len-of-fb3-bits-lt-r
    (equal (len rs) (len ds))
    :hints (("Goal" :in-theory (enable fb3-bits-lt-r)))))

(define fb3-bits-lt-rs ((xs bit-listp) (ys bit-listp) (p primep))
  :guard (equal (len xs) (len ys))
  :returns (rs bit-listp :hyp :guard)
  :short "Little-endian result bits of @('bits-lt-gadget')."
  (rev (fb3-bits-lt-r (rev (bitxor-list xs ys)) (rev ys) p)))

(define fb3-bits-lt-induct ((xs true-listp)
                            (ys true-listp)
                            (ds true-listp)
                            (rs true-listp))
  (if (or (endp xs) (endp (cdr xs))
          (endp ys) (endp ds) (endp rs))
      nil
    (fb3-bits-lt-induct (cdr xs) (cdr ys) (cdr ds) (cdr rs))))

(defruled fb3-consp-of-fb3-bits-lt-r
  (equal (consp (fb3-bits-lt-r ds ys p))
         (consp ds))
  :expand ((fb3-bits-lt-r ds ys p)))

(defruled fb3-consp-of-fb3-bits-lt-r-type
  (implies (consp ds)
           (consp (fb3-bits-lt-r ds ys p)))
  :rule-classes :type-prescription
  :enable fb3-consp-of-fb3-bits-lt-r)

(defruled fb3-bits-lt-lookup-car-rs
  (implies (and (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-r ds ys p))
                (consp ds))
           (equal (lookup-equal (car rs) asg)
                  (if (consp (cdr ds))
                      (if (= (car ds) 1)
                          (car ys)
                        (lookup-equal (cadr rs) asg))
                    (if0 (car ds) (car ys) p))))
  :do-not-induct t
  :cases ((consp (cdr rs)))
  :expand ((fb3-bits-lt-r ds ys p))
  :enable (lookup-equal-list fb3-consp-of-fb3-bits-lt-r
                             fb3-consp-of-fb3-bits-lt-r-type))

(defruled fb3-bits-lt-lookup-list-cdr-rs
  (implies (and (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-r ds ys p))
                (consp (cdr ds)))
           (equal (lookup-equal-list (cdr rs) asg)
                  (fb3-bits-lt-r (cdr ds) (cdr ys) p)))
  :enable (fb3-bits-lt-r lookup-equal-list))

(defruled fb3-bits-lt-consp-cdr-rs
  (implies (and (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-r ds ys p))
                (consp (cdr ds)))
           (consp (cdr rs)))
  :use (:instance consp-of-lookup-equal-list (keys (cdr rs)) (alist asg))
  :enable (fb3-bits-lt-r lookup-equal-list fb3-consp-of-fb3-bits-lt-r))

(defruled fb3-bits-lt-valuation-bindsp-cadr-rs
  (implies (and (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-r ds ys p))
                (consp (cdr ds))
                (r1cs::valuation-binds-allp asg rs))
           (r1cs::valuation-bindsp asg (cadr rs)))
  :use fb3-bits-lt-consp-cdr-rs
  :enable fb-valuation-bindsp-of-cadr)

(defruled fb3-bitxor-list-lookup-car
  (implies (and (equal (lookup-equal-list ds asg)
                       (bitxor-list a b))
                (consp ds))
           (equal (lookup-equal (car ds) asg)
                  (bitxor (car a) (car b))))
  :enable (bitxor-list lookup-equal-list))

(defruled fb3-bitxor-list-lookup-list-cdr
  (implies (equal (lookup-equal-list ds asg)
                  (bitxor-list a b))
           (equal (lookup-equal-list (cdr ds) asg)
                  (bitxor-list (cdr a) (cdr b))))
  :enable (bitxor-list lookup-equal-list))

(defruled fb3-bitp-of-bitxor
  (bitp (bitxor a b))
  :enable bitxor)

(defruled fb3-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruled fb3-bits-lt-aux-satisfies
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (len ys))
                (equal (len ys) (len ds))
                (equal (len ds) (len rs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list xs asg)
                                    (lookup-equal-list ys asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-r (lookup-equal-list ds asg)
                                      (lookup-equal-list ys asg)
                                      p)))
           (r1cs::r1cs-constraints-holdp
            (bits-lt-gadget-aux xs ys ds rs p) asg p))
  :hints (("Goal"
           :induct (fb3-bits-lt-induct xs ys ds rs)
           :in-theory (e/d (fb3-bits-lt-induct
                            bits-lt-gadget-aux
                            boolean-xor-gadget-to-bitxor
                            if0-gadget-to-if0
                            if-gadget-variant-to-if
                            fb-consp-when-len-pos
                            fb-len-pos-when-consp
                            fb-cdr-of-lookup-equal-list
                            car-of-lookup-equal-list
                            fb-bitp-of-lookup-car-when-bit-listp
                            fb-bit-listp-of-lookup-cdr-when-bit-listp
                            fb3-bits-lt-lookup-car-rs
                            fb3-bits-lt-lookup-list-cdr-rs
                            fb3-bits-lt-valuation-bindsp-cadr-rs
                            fb3-bitxor-list-lookup-car
                            fb3-bitxor-list-lookup-list-cdr
                            fb3-bitp-of-bitxor
                            fb3-lookup-equal-list-of-nil
                            if0)
                           ((:definition pfield::sub)
                            bitp
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-bits-lt-gadget-complete
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (len ys))
                (equal (len ys) (len ds))
                (equal (len ds) (len rs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list xs asg)
                                    (lookup-equal-list ys asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-rs (lookup-equal-list xs asg)
                                       (lookup-equal-list ys asg)
                                       p)))
           (r1cs::r1cs-constraints-holdp
            (bits-lt-gadget xs ys ds rs p) asg p))
  :enable (bits-lt-gadget
           fb3-bits-lt-rs
           fb-r1cs-holdp-of-rev
           lookup-equal-list-of-rev
           acl2::rev-of-rev
           fb-valuation-binds-allp-of-rev
           fb-symbol-listp-of-rev
           fb-bit-listp-of-rev
           bitxor-list-of-rev)
  :use (:instance fb3-bits-lt-aux-satisfies
                  (xs (rev xs))
                  (ys (rev ys))
                  (ds (rev ds))
                  (rs (rev rs))))

(defruled fb3-bits-equal-when-equal-1
  (implies (and (bitp a) (bitp b))
           (equal (equal (equal a 1) (equal b 1))
                  (equal a b)))
  :hints (("Goal" :in-theory (enable bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-len-of-fb3-bits-lt-rs
  (equal (len (fb3-bits-lt-rs xs ys p))
         (len xs))
  :enable fb3-bits-lt-rs)

(defruled fb3-bitp-of-car-last-when-bits-lt-rs
  (implies (and (equal vs (fb3-bits-lt-rs xs ys p))
                (bit-listp xs)
                (bit-listp ys)
                (equal (len xs) (len ys))
                (consp xs)
                (primep p))
           (bitp (car (last vs))))
  :do-not-induct t
  :disable bitp
  :use ((:instance bitp-of-car-of-last-when-bit-listp
                   (bits (fb3-bits-lt-rs xs ys p)))
        fb3-len-of-fb3-bits-lt-rs
        (:instance fb-consp-when-len-pos
                   (x (fb3-bits-lt-rs xs ys p)))))

(defruled fb3-field-is-less-than-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list xrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list yrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list xs asg)
                                    (lookup-equal-list ys asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-rs (lookup-equal-list xs asg)
                                       (lookup-equal-list ys asg)
                                       p)))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-is-less-than-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p)
                (equal (car (last (lookup-equal-list rs asg)))
                       (field-is-less-than-funspec
                        (lookup-equal x asg)
                        (lookup-equal y asg)))))
  :do-not-induct t
  :enable (fb-field-is-less-than-gadget
           field-lt-gadget
           fb-field-write-bits-le-gadget
           fb3-bits-lt-gadget-complete
           bitp-of-car-of-last-when-bit-listp
           field-bits-le
           acl2::bit-listp-of-nat=>lebits)
  :use ((:instance fb3-bitp-of-car-last-when-bits-lt-rs
                   (vs (lookup-equal-list rs asg))
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x x) (bits xs) (rs xrs) (u u) (p p) (asg asg))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x y) (bits ys) (rs yrs) (u u) (p p) (asg asg))
        fb3-bits-lt-gadget-complete
        fb-field-is-less-than-gadget-sound)
  :disable ((:definition pfield::sub)))

(defruled fb3-field-is-greater-than-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list xrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list yrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list ys asg)
                                    (lookup-equal-list xs asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-rs (lookup-equal-list ys asg)
                                       (lookup-equal-list xs asg)
                                       p)))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-greater-than-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p)
                (equal (car (last (lookup-equal-list rs asg)))
                       (field-is-greater-than-funspec
                        (lookup-equal x asg)
                        (lookup-equal y asg)))))
  :do-not-induct t
  :enable (field-is-greater-than-gadget
           field-lt-gadget
           fb-field-write-bits-le-gadget
           fb3-bits-lt-gadget-complete
           fb3-bits-equal-when-equal-1
           bitp-of-car-of-last-when-bit-listp
           field-is-greater-than-funspec
           field-bits-le
           bitp
           acl2::bit-listp-of-nat=>lebits)
  :use ((:instance fb3-bitp-of-car-last-when-bits-lt-rs
                   (vs (lookup-equal-list rs asg))
                   (xs (lookup-equal-list ys asg))
                   (ys (lookup-equal-list xs asg)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x x) (bits xs) (rs xrs) (u u) (p p) (asg asg))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x y) (bits ys) (rs yrs) (u u) (p p) (asg asg))
        (:instance fb3-bits-lt-gadget-complete
                   (xs ys) (ys xs))
        field-is-greater-than-gadget-sound)
  :disable ((:definition pfield::sub)))

(defruled fb3-field-is-greater-than-or-equal-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list xrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list yrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list xs asg)
                                    (lookup-equal-list ys asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-rs (lookup-equal-list xs asg)
                                       (lookup-equal-list ys asg)
                                       p)))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-greater-than-or-equal-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p)
                (equal (pfield::sub 1
                                    (car (last (lookup-equal-list rs asg)))
                                    p)
                       (field-is-greater-than-or-equal-funspec
                        (lookup-equal x asg)
                        (lookup-equal y asg)))))
  :do-not-induct t
  :enable (field-is-greater-than-or-equal-gadget
           field-lt-gadget
           fb-field-write-bits-le-gadget
           fb3-bits-lt-gadget-complete
           bitp-of-car-of-last-when-bit-listp
           field-bits-le
           acl2::bit-listp-of-nat=>lebits)
  :use ((:instance fb3-bitp-of-car-last-when-bits-lt-rs
                   (vs (lookup-equal-list rs asg))
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x x) (bits xs) (rs xrs) (u u) (p p) (asg asg))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x y) (bits ys) (rs yrs) (u u) (p p) (asg asg))
        fb3-bits-lt-gadget-complete
        field-is-greater-than-or-equal-gadget-sound)
  :disable ((:definition pfield::sub)))

(defruled fb3-field-is-less-than-or-equal-gadget-complete
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (equal p (base-prime))
                (primep p)
                (oddp p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (fieldp (lookup-equal x asg))
                (fieldp (lookup-equal y asg))
                (equal (lookup-equal u asg) 1)
                (equal (lookup-equal-list xs asg)
                       (field-bits-le (lookup-equal x asg)))
                (equal (lookup-equal-list ys asg)
                       (field-bits-le (lookup-equal y asg)))
                (equal (lookup-equal-list xrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list xs asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list yrs asg)
                       (fb-bits-lte-const-witness
                        (lookup-equal-list ys asg)
                        (nat=>lebits* (1- p))))
                (equal (lookup-equal-list ds asg)
                       (bitxor-list (lookup-equal-list ys asg)
                                    (lookup-equal-list xs asg)))
                (equal (lookup-equal-list rs asg)
                       (fb3-bits-lt-rs (lookup-equal-list ys asg)
                                       (lookup-equal-list xs asg)
                                       p)))
           (and (r1cs::r1cs-constraints-holdp
                 (field-is-less-than-or-equal-gadget
                  x xs xrs y ys yrs ds rs u p)
                 asg p)
                (equal (pfield::sub 1
                                    (car (last (lookup-equal-list rs asg)))
                                    p)
                       (field-is-less-than-or-equal-funspec
                        (lookup-equal x asg)
                        (lookup-equal y asg)))))
  :do-not-induct t
  :enable (field-is-less-than-or-equal-gadget
           field-lt-gadget
           fb-field-write-bits-le-gadget
           fb3-bits-lt-gadget-complete
           bitp-of-car-of-last-when-bit-listp
           field-bits-le
           acl2::bit-listp-of-nat=>lebits)
  :use ((:instance fb3-bitp-of-car-last-when-bits-lt-rs
                   (vs (lookup-equal-list rs asg))
                   (xs (lookup-equal-list ys asg))
                   (ys (lookup-equal-list xs asg)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x x) (bits xs) (rs xrs) (u u) (p p) (asg asg))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x y) (bits ys) (rs yrs) (u u) (p p) (asg asg))
        (:instance fb3-bits-lt-gadget-complete
                   (xs ys) (ys xs))
        field-is-less-than-or-equal-gadget-sound)
  :disable ((:definition pfield::sub)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime 5.  1 < 2.  Bits (1 0 0) and (0 1 0), range folds (1 0),
; xor bits (1 1 0), comparison bits (0 1 1).  The last bit is 1.
; is_greater_than_or_equal uses this same assignment; its result is 1 - r.
; is_greater_than(2, 1) is the swapped comparison, and
; is_less_than_or_equal uses that assignment.

(defconst *fb3-field-compare-prime* 5)

(defconst *fb3-field-is-less-than-asg*
  '((x . 1) (y . 2)
    (x0 . 1) (x1 . 0) (x2 . 0)
    (y0 . 0) (y1 . 1) (y2 . 0)
    (xz0 . 1) (xz1 . 0)
    (yz0 . 1) (yz1 . 0)
    (d0 . 1) (d1 . 1) (d2 . 0)
    (r0 . 0) (r1 . 1) (r2 . 1)
    (u . 1)))

(defconst *fb3-field-is-greater-than-asg*
  '((x . 2) (y . 1)
    (x0 . 0) (x1 . 1) (x2 . 0)
    (y0 . 1) (y1 . 0) (y2 . 0)
    (xz0 . 1) (xz1 . 0)
    (yz0 . 1) (yz1 . 0)
    (d0 . 1) (d1 . 1) (d2 . 0)
    (r0 . 0) (r1 . 1) (r2 . 1)
    (u . 1)))

(defrule fb3-field-is-less-than-sample
  (r1cs::r1cs-constraints-holdp
   (fb-field-is-less-than-gadget
    'x '(x0 x1 x2) '(xz0 xz1)
    'y '(y0 y1 y2) '(yz0 yz1)
    '(d0 d1 d2) '(r0 r1 r2) 'u
    *fb3-field-compare-prime*)
   *fb3-field-is-less-than-asg*
   *fb3-field-compare-prime*)
  :enable (fb-field-is-less-than-gadget
           field-lt-gadget
           field-to-bits-gadget
           bits-lt-gadget
           bits-lt-gadget-aux
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
           boolean-xor-gadget
           zero-unit-gadget
           if0-gadget
           if-gadget-variant
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb3-field-is-greater-than-or-equal-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-greater-than-or-equal-gadget
    'x '(x0 x1 x2) '(xz0 xz1)
    'y '(y0 y1 y2) '(yz0 yz1)
    '(d0 d1 d2) '(r0 r1 r2) 'u
    *fb3-field-compare-prime*)
   *fb3-field-is-less-than-asg*
   *fb3-field-compare-prime*)
  :enable (field-is-greater-than-or-equal-gadget
           fb-field-is-less-than-gadget)
  :use fb3-field-is-less-than-sample)

(defrule fb3-field-is-greater-than-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-greater-than-gadget
    'x '(x0 x1 x2) '(xz0 xz1)
    'y '(y0 y1 y2) '(yz0 yz1)
    '(d0 d1 d2) '(r0 r1 r2) 'u
    *fb3-field-compare-prime*)
   *fb3-field-is-greater-than-asg*
   *fb3-field-compare-prime*)
  :enable (field-is-greater-than-gadget
           field-lt-gadget
           field-to-bits-gadget
           bits-lt-gadget
           bits-lt-gadget-aux
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
           boolean-xor-gadget
           zero-unit-gadget
           if0-gadget
           if-gadget-variant
           nat=>lebits*
           acl2::nat=>lendian*
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pfield::add
           pfield::mul))

(defrule fb3-field-is-less-than-or-equal-sample
  (r1cs::r1cs-constraints-holdp
   (field-is-less-than-or-equal-gadget
    'x '(x0 x1 x2) '(xz0 xz1)
    'y '(y0 y1 y2) '(yz0 yz1)
    '(d0 d1 d2) '(r0 r1 r2) 'u
    *fb3-field-compare-prime*)
   *fb3-field-is-greater-than-asg*
   *fb3-field-compare-prime*)
  :enable (field-is-less-than-or-equal-gadget
           field-is-greater-than-gadget)
  :use fb3-field-is-greater-than-sample)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-lt2-bit ((x0 bitp) (x1 bitp) (y0 bitp) (y1 bitp))
  :returns (b bitp :hyp :guard)
  (b* ((d0 (bitxor x0 y0))
       (d1 (bitxor x1 y1))
       (r0 (if (equal d0 1) y0 0)))
    (if (equal d1 1) y1 r0))
  ///
  (defruled fb3-lt2-correct
    (implies (and (bitp x0) (bitp x1) (bitp y0) (bitp y1))
             (equal (fb3-lt2-bit x0 x1 y0 y1)
                    (if (< (+ x0 (* 2 x1))
                           (+ y0 (* 2 y1)))
                        1
                      0)))
    :hints (("Goal"
             :cases ((equal x0 0) (equal x0 1))
             :in-theory (enable fb3-lt2-bit bitp bitxor))
            ("Subgoal 1" :cases ((equal x1 0) (equal x1 1)))
            ("Subgoal 2" :cases ((equal x1 0) (equal x1 1)))
            ("Subgoal 1.1" :cases ((equal y0 0) (equal y0 1)))
            ("Subgoal 1.2" :cases ((equal y0 0) (equal y0 1)))
            ("Subgoal 2.1" :cases ((equal y0 0) (equal y0 1)))
            ("Subgoal 2.2" :cases ((equal y0 0) (equal y0 1)))
            ("Subgoal 1.1.1" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 1.1.2" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 1.2.1" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 1.2.2" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 2.1.1" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 2.1.2" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 2.2.1" :cases ((equal y1 0) (equal y1 1)))
            ("Subgoal 2.2.2" :cases ((equal y1 0) (equal y1 1))))))

(defruled fb3-lt2-is-funspec
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp x0)
                (bitp x1)
                (bitp y0)
                (bitp y1)
                (equal x (+ x0 (* 2 x1)))
                (equal y (+ y0 (* 2 y1)))
                (equal d0 (bitxor x0 y0))
                (equal d1 (bitxor x1 y1))
                (equal r0 (if (equal d0 1) y0 0))
                (equal b (if (equal d1 1) y1 r0)))
           (equal (field-is-less-than-funspec x y) b))
  :enable (field-is-less-than-funspec
           fieldp
           pfield::fep-fix-when-fep
           fb3-lt2-bit
           fb3-lt2-correct
           fb3-two-bits-below-4))

(defruled fb3-gt2-is-funspec
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp x0)
                (bitp x1)
                (bitp y0)
                (bitp y1)
                (equal x (+ x0 (* 2 x1)))
                (equal y (+ y0 (* 2 y1)))
                (equal d0 (bitxor y0 x0))
                (equal d1 (bitxor y1 x1))
                (equal r0 (if (equal d0 1) x0 0))
                (equal b (if (equal d1 1) x1 r0)))
           (equal (field-is-greater-than-funspec x y) b))
  :enable field-is-greater-than-funspec
  :use (:instance fb3-lt2-is-funspec
                  (x y) (y x)
                  (x0 y0) (x1 y1)
                  (y0 x0) (y1 x1)))

(defruled fb3-gte2-is-funspec
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp x0)
                (bitp x1)
                (bitp y0)
                (bitp y1)
                (equal x (+ x0 (* 2 x1)))
                (equal y (+ y0 (* 2 y1)))
                (equal d0 (bitxor x0 y0))
                (equal d1 (bitxor x1 y1))
                (equal r0 (if (equal d0 1) y0 0))
                (equal b (if (equal d1 1) y1 r0))
                (equal z (if (equal b 1) 0 1)))
           (equal (field-is-greater-than-or-equal-funspec x y) z))
  :enable (field-is-greater-than-or-equal-funspec
           boolean-not-funspec
           bitp)
  :use fb3-lt2-is-funspec)

(defruled fb3-lte2-is-funspec
  (implies (and (equal p (base-prime))
                (fieldp x)
                (fieldp y)
                (bitp x0)
                (bitp x1)
                (bitp y0)
                (bitp y1)
                (equal x (+ x0 (* 2 x1)))
                (equal y (+ y0 (* 2 y1)))
                (equal d0 (bitxor y0 x0))
                (equal d1 (bitxor y1 x1))
                (equal r0 (if (equal d0 1) x0 0))
                (equal b (if (equal d1 1) x1 r0))
                (equal z (if (equal b 1) 0 1)))
           (equal (field-is-less-than-or-equal-funspec x y) z))
  :enable (field-is-less-than-or-equal-funspec
           field-is-greater-than-or-equal-funspec
           field-is-greater-than-funspec
           field-is-less-than-funspec
           boolean-not-funspec
           bitp)
  :use fb3-gt2-is-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *fb3-base-prime-minus-1*
  (1- primes::*bls12-377-scalar-field-prime*))

(defruled fb3-sub-1-equal-minus-1
  (implies (pfield::fep b primes::*bls12-377-scalar-field-prime*)
           (equal (equal *fb3-base-prime-minus-1*
                         (pfield::sub b 1 primes::*bls12-377-scalar-field-prime*))
                  (equal b 0)))
  :enable (pfield::sub pfield::add pfield::neg acl2::mod-sum-cases))

(define fb3-field-is-less-than-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Two-bit PFCS for @('Field::is_less_than')."
  (pfcs::parse-def
   "field_is_less_than_2(x, y, b, x0, x1, y0, y1, d0, d1, r0) := {
    (1 - x0) * (x0) == (0),
    (1 - x1) * (x1) == (0),
    (1 - y0) * (y0) == (0),
    (1 - y1) * (y1) == (0),
    (x) * (1) == (x0 + 2 * x1),
    (y) * (1) == (y0 + 2 * y1),
    (2 * x0) * (y0) == (x0 + y0 - d0),
    (2 * x1) * (y1) == (x1 + y1 - d1),
    (d0) * (y0) == (r0),
    (d1) * (y1 - r0) == (b - r0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-is-less-than-2-circuit)
            :pred fb3-field-is-less-than-2-pred
            :prime prime)

(defruled fb3-field-is-less-than-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b prime)
                (pfield::fep x0 prime)
                (pfield::fep x1 prime)
                (pfield::fep y0 prime)
                (pfield::fep y1 prime)
                (pfield::fep d0 prime)
                (pfield::fep d1 prime)
                (pfield::fep r0 prime))
           (equal (fb3-field-is-less-than-2-pred
                   x y b x0 x1 y0 y1 d0 d1 r0 prime)
                  (and (bitp x0)
                       (bitp x1)
                       (bitp y0)
                       (bitp y1)
                       (equal x (+ x0 (* 2 x1)))
                       (equal y (+ y0 (* 2 y1)))
                       (equal d0 (bitxor x0 y0))
                       (equal d1 (bitxor x1 y1))
                       (equal r0 (if (equal d0 1) y0 0))
                       (equal b (if (equal d1 1) y1 r0))
                       (< x 4)
                       (< y 4)
                       (equal b (field-is-less-than-funspec x y))
                       (equal (list x0 x1)
                              (take 2 (field-bits-le x)))
                       (equal (list y0 y1)
                              (take 2 (field-bits-le y))))))
  :enable (fb3-field-is-less-than-2-pred
           fb3-bool-check-is-bitp
           fb3-weighted-2
           fb3-xor-is-bitxor
           fb3-if0-is-if0
           fb3-if-is-if
           fb3-two-bits-below-4
           fb3-lt2-is-funspec
           fb3-bits-match-2
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp
           fb3-sub-1-equal-minus-1)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))

(define fb3-field-is-greater-than-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Two-bit PFCS for @('Field::is_greater_than').
          The then-branch of the fold is the bits of @('x')."
  (pfcs::parse-def
   "field_is_greater_than_2(x, y, b, x0, x1, y0, y1, d0, d1, r0) := {
    (1 - x0) * (x0) == (0),
    (1 - x1) * (x1) == (0),
    (1 - y0) * (y0) == (0),
    (1 - y1) * (y1) == (0),
    (x) * (1) == (x0 + 2 * x1),
    (y) * (1) == (y0 + 2 * y1),
    (2 * y0) * (x0) == (y0 + x0 - d0),
    (2 * y1) * (x1) == (y1 + x1 - d1),
    (d0) * (x0) == (r0),
    (d1) * (x1 - r0) == (b - r0)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-is-greater-than-2-circuit)
            :pred fb3-field-is-greater-than-2-pred
            :prime prime)

(defruled fb3-field-is-greater-than-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep b prime)
                (pfield::fep x0 prime)
                (pfield::fep x1 prime)
                (pfield::fep y0 prime)
                (pfield::fep y1 prime)
                (pfield::fep d0 prime)
                (pfield::fep d1 prime)
                (pfield::fep r0 prime))
           (equal (fb3-field-is-greater-than-2-pred
                   x y b x0 x1 y0 y1 d0 d1 r0 prime)
                  (and (bitp x0)
                       (bitp x1)
                       (bitp y0)
                       (bitp y1)
                       (equal x (+ x0 (* 2 x1)))
                       (equal y (+ y0 (* 2 y1)))
                       (equal d0 (bitxor y0 x0))
                       (equal d1 (bitxor y1 x1))
                       (equal r0 (if (equal d0 1) x0 0))
                       (equal b (if (equal d1 1) x1 r0))
                       (< x 4)
                       (< y 4)
                       (equal b (field-is-greater-than-funspec x y))
                       (equal (list x0 x1)
                              (take 2 (field-bits-le x)))
                       (equal (list y0 y1)
                              (take 2 (field-bits-le y))))))
  :enable (fb3-field-is-greater-than-2-pred
           fb3-bool-check-is-bitp
           fb3-weighted-2
           fb3-xor-is-bitxor
           fb3-if0-is-if0
           fb3-if-is-if
           fb3-two-bits-below-4
           fb3-gt2-is-funspec
           fb3-bits-match-2
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp
           fb3-sub-1-equal-minus-1)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))

(define fb3-field-is-greater-than-or-equal-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Two-bit PFCS for @('Field::is_greater_than_or_equal').
          @('z') is @($1 - b$)."
  (pfcs::parse-def
   "field_is_greater_than_or_equal_2(x, y, z, b, x0, x1, y0, y1, d0, d1, r0) := {
    (1 - x0) * (x0) == (0),
    (1 - x1) * (x1) == (0),
    (1 - y0) * (y0) == (0),
    (1 - y1) * (y1) == (0),
    (x) * (1) == (x0 + 2 * x1),
    (y) * (1) == (y0 + 2 * y1),
    (2 * x0) * (y0) == (x0 + y0 - d0),
    (2 * x1) * (y1) == (x1 + y1 - d1),
    (d0) * (y0) == (r0),
    (d1) * (y1 - r0) == (b - r0),
    (z) * (1) == (1 - b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-is-greater-than-or-equal-2-circuit)
            :pred fb3-field-is-greater-than-or-equal-2-pred
            :prime prime)

(defruled fb3-field-is-greater-than-or-equal-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep z prime)
                (pfield::fep b prime)
                (pfield::fep x0 prime)
                (pfield::fep x1 prime)
                (pfield::fep y0 prime)
                (pfield::fep y1 prime)
                (pfield::fep d0 prime)
                (pfield::fep d1 prime)
                (pfield::fep r0 prime))
           (equal (fb3-field-is-greater-than-or-equal-2-pred
                   x y z b x0 x1 y0 y1 d0 d1 r0 prime)
                  (and (bitp x0)
                       (bitp x1)
                       (bitp y0)
                       (bitp y1)
                       (equal x (+ x0 (* 2 x1)))
                       (equal y (+ y0 (* 2 y1)))
                       (equal d0 (bitxor x0 y0))
                       (equal d1 (bitxor x1 y1))
                       (equal r0 (if (equal d0 1) y0 0))
                       (equal b (if (equal d1 1) y1 r0))
                       (equal z (if (equal b 1) 0 1))
                       (< x 4)
                       (< y 4)
                       (equal b (field-is-less-than-funspec x y))
                       (equal z (field-is-greater-than-or-equal-funspec x y))
                       (equal (list x0 x1)
                              (take 2 (field-bits-le x)))
                       (equal (list y0 y1)
                              (take 2 (field-bits-le y))))))
  :enable (fb3-field-is-greater-than-or-equal-2-pred
           fb3-bool-check-is-bitp
           fb3-weighted-2
           fb3-xor-is-bitxor
           fb3-if0-is-if0
           fb3-if-is-if
           fb3-not-is-boolean-not
           fb3-two-bits-below-4
           fb3-lt2-is-funspec
           fb3-gte2-is-funspec
           fb3-bits-match-2
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp
           fb3-sub-1-equal-minus-1)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))

(define fb3-field-is-less-than-or-equal-2-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Two-bit PFCS for @('Field::is_less_than_or_equal')."
  (pfcs::parse-def
   "field_is_less_than_or_equal_2(x, y, z, b, x0, x1, y0, y1, d0, d1, r0) := {
    (1 - x0) * (x0) == (0),
    (1 - x1) * (x1) == (0),
    (1 - y0) * (y0) == (0),
    (1 - y1) * (y1) == (0),
    (x) * (1) == (x0 + 2 * x1),
    (y) * (1) == (y0 + 2 * y1),
    (2 * y0) * (x0) == (y0 + x0 - d0),
    (2 * y1) * (x1) == (y1 + x1 - d1),
    (d0) * (x0) == (r0),
    (d1) * (x1 - r0) == (b - r0),
    (z) * (1) == (1 - b)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-is-less-than-or-equal-2-circuit)
            :pred fb3-field-is-less-than-or-equal-2-pred
            :prime prime)

(defruled fb3-field-is-less-than-or-equal-2-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (fieldp y)
                (pfield::fep z prime)
                (pfield::fep b prime)
                (pfield::fep x0 prime)
                (pfield::fep x1 prime)
                (pfield::fep y0 prime)
                (pfield::fep y1 prime)
                (pfield::fep d0 prime)
                (pfield::fep d1 prime)
                (pfield::fep r0 prime))
           (equal (fb3-field-is-less-than-or-equal-2-pred
                   x y z b x0 x1 y0 y1 d0 d1 r0 prime)
                  (and (bitp x0)
                       (bitp x1)
                       (bitp y0)
                       (bitp y1)
                       (equal x (+ x0 (* 2 x1)))
                       (equal y (+ y0 (* 2 y1)))
                       (equal d0 (bitxor y0 x0))
                       (equal d1 (bitxor y1 x1))
                       (equal r0 (if (equal d0 1) x0 0))
                       (equal b (if (equal d1 1) x1 r0))
                       (equal z (if (equal b 1) 0 1))
                       (< x 4)
                       (< y 4)
                       (equal b (field-is-greater-than-funspec x y))
                       (equal z (field-is-less-than-or-equal-funspec x y))
                       (equal (list x0 x1)
                              (take 2 (field-bits-le x)))
                       (equal (list y0 y1)
                              (take 2 (field-bits-le y))))))
  :enable (fb3-field-is-less-than-or-equal-2-pred
           fb3-bool-check-is-bitp
           fb3-weighted-2
           fb3-xor-is-bitxor
           fb3-if0-is-if0
           fb3-if-is-if
           fb3-not-is-boolean-not
           fb3-two-bits-below-4
           fb3-gt2-is-funspec
           fb3-lte2-is-funspec
           fb3-bits-match-2
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp
           fb3-sub-1-equal-minus-1)
  :disable ((:definition pfield::sub)
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            bitp
            fieldp))
