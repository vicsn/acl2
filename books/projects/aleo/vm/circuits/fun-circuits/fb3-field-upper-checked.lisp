; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::to_upper_bits_be / _le with the range check of snarkVM staging
; (963c6189e): after the shifted pow2sum, the reversed bits are
; Boolean::assert_less_than_or_equal_constant against the upper k bits of
; modulus - 1.  That check bounds the shifted value by p - 1, so soundness
; holds for every satisfying assignment, without the hypothesis of
; fb2-field-to-upper-bits-be-gadget-sound.

(in-package "ALEOVM")

(include-book "fb2-field-bits")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/last" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-upper-cs ((k natp))
  :verify-guards nil
  :short "@('modulus_minus_one.to_bits_le()[n - k..]')."
  (nthcdr (- (base-field-size-in-bits) (nfix k))
          (acl2::nat=>lebits (base-field-size-in-bits) (1- (base-prime)))))

(define fb3-field-to-upper-bits-be-gadget ((x symbolp)
                                           (bits symbol-listp)
                                           (k natp)
                                           (n natp)
                                           (rs symbol-listp)
                                           (p primep))
  :guard (<= k n)
  :verify-guards nil
  :short "@('Field::to_upper_bits_be') of snarkVM staging: the unchecked
          constraints, then the range check of the reversed bits."
  (append (fb-field-to-upper-bits-be-gadget x bits k n p)
          (fb-boolean-assert-lte-const-gadget (rev bits) (fb3-upper-cs k) rs p)))

(define fb3-field-to-upper-bits-le-gadget ((x symbolp)
                                           (bits symbol-listp)
                                           (k natp)
                                           (n natp)
                                           (rs symbol-listp)
                                           (p primep))
  :guard (<= k n)
  :verify-guards nil
  :short "@('to_upper_bits_le') reverses the output of @('to_upper_bits_be')."
  (fb3-field-to-upper-bits-be-gadget x (rev bits) k n rs p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-lebits=>nat-of-nthcdr-bound
  (implies (and (bit-listp ys)
                (natp s))
           (<= (* (expt 2 s) (lebits=>nat (nthcdr s ys)))
               (lebits=>nat ys)))
  :induct (nthcdr s ys)
  :enable (nthcdr acl2::lebits=>nat-of-cons expt)
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled fb3-last-of-nthcdr
  (implies (< (nfix n) (len x))
           (equal (last (nthcdr n x)) (last x)))
  :induct (nthcdr n x)
  :enable (nthcdr last))

(defruled fb3-upper-cs-facts
  (implies (and (natp k)
                (<= k (base-field-size-in-bits)))
           (and (bit-listp (fb3-upper-cs k))
                (equal (len (fb3-upper-cs k)) k)
                (or (endp (fb3-upper-cs k))
                    (equal (car (last (fb3-upper-cs k))) 1))
                (<= (* (expt 2 (- (base-field-size-in-bits) k))
                       (lebits=>nat (fb3-upper-cs k)))
                    (1- (base-prime)))))
  :do-not-induct t
  :enable (fb3-upper-cs base-field-size-in-bits)
  :use ((:instance fb3-lebits=>nat-of-nthcdr-bound
         (s (- (base-field-size-in-bits) k))
         (ys (acl2::nat=>lebits (base-field-size-in-bits) (1- (base-prime)))))
        (:instance fb3-last-of-nthcdr
         (n (- (base-field-size-in-bits) k))
         (x (acl2::nat=>lebits (base-field-size-in-bits) (1- (base-prime)))))))

(defruled fb3-shift-bound
  (implies (and (natp v) (natp c) (natp e) (integerp q)
                (<= v c)
                (<= (* (expt 2 e) c) (1- q)))
           (< (* (expt 2 e) v) q))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled fb3-field-to-upper-bits-be-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (equal (len rs) (bits-lte-const-check-rlen (fb3-upper-cs k)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal x asg))
                (r1cs::r1cs-constraints-holdp
                 (fb3-field-to-upper-bits-be-gadget x bits k n rs p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-upper-bits-be-funspec (lookup-equal x asg) k)))
  :do-not-induct t
  :use (fb3-upper-cs-facts
        primep-of-base-prime
        (:instance fb-field-to-upper-bits-be-gadget-to-mod (p (base-prime)))
        (:instance fb-boolean-assert-lte-const-gadget-sound
         (xs (rev bits)) (cs (fb3-upper-cs k)) (p (base-prime)))
        (:instance fb2-field-to-upper-bits-be-gadget-sound (p (base-prime)))
        (:instance fb3-shift-bound
         (v (lebits=>nat (rev (lookup-equal-list bits asg))))
         (c (lebits=>nat (fb3-upper-cs k)))
         (e (- (base-field-size-in-bits) k))
         (q (base-prime))))
  :enable (fb3-field-to-upper-bits-be-gadget
           r1cs::r1cs-constraints-holdp-of-append
           lookup-equal-list-of-rev
           fb-valuation-binds-allp-of-rev
           fb-symbol-listp-of-rev
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec)
  :disable (fb-field-to-upper-bits-be-gadget-to-mod
            fb-boolean-assert-lte-const-gadget-sound
            fb2-field-to-upper-bits-be-gadget-sound
            (:e base-prime) (:e fb3-upper-cs)))

(defruled fb3-not-reserrp-when-bit-listp
  (implies (bit-listp x) (not (reserrp x)))
  :enable (reserrp bit-listp))

(defruled fb3-field-to-upper-bits-le-gadget-sound
  (implies (and (symbolp x)
                (symbol-listp bits)
                (symbol-listp rs)
                (equal p (base-prime))
                (natp k)
                (equal (len bits) k)
                (<= k (base-field-size-in-bits))
                (equal n (base-field-size-in-bits))
                (equal (len rs) (bits-lte-const-check-rlen (fb3-upper-cs k)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg rs)
                (fieldp (lookup-equal x asg))
                (r1cs::r1cs-constraints-holdp
                 (fb3-field-to-upper-bits-le-gadget x bits k n rs p) asg p))
           (equal (lookup-equal-list bits asg)
                  (field-to-upper-bits-le-funspec (lookup-equal x asg) k)))
  :do-not-induct t
  :use ((:instance fb3-field-to-upper-bits-be-gadget-sound (bits (rev bits)))
        (:instance fb-field-to-upper-bits-be-gadget-to-mod
         (bits (rev bits)) (n (base-field-size-in-bits)) (p (base-prime))))
  :enable (fb3-field-to-upper-bits-le-gadget
           fb3-field-to-upper-bits-be-gadget
           r1cs::r1cs-constraints-holdp-of-append
           fb3-not-reserrp-when-bit-listp
           primep-of-base-prime
           field-to-upper-bits-le-funspec
           lookup-equal-list-of-rev
           fb-valuation-binds-allp-of-rev
           fb-symbol-listp-of-rev)
  :disable (fb3-field-to-upper-bits-be-gadget-sound fb-field-to-upper-bits-be-gadget-to-mod))
