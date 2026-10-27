; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Integer::from_field_lossy
; (circuit/types/integers/src/helpers/from_field_lossy.rs).
;
; The integer bits are the first n bits of Field::to_bits_le.  Those
; constraints are field-to-bits-gadget: boolean checks, the power-of-two
; sum, the bits-below-prime comparator, and the zero check against the
; public unit wire.  zero-unit-gadget does not force that wire.
; (lookup-equal u asg) = 1 is the public one.
;
; The integer is lebits->int of those n wires.  It is an int-valuep of
; the type, and it is int-from-field-lossy-spec of the field wire.
; Completeness still needs a bits-below-prime witness.

(in-package "ALEOVM")

(include-book "../r1cs/field-to-bits")
(include-book "int-support")

(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule int-lossy-base-prime-oddp
  (and (primep (base-prime))
       (oddp (base-prime))
       (equal (integer-length (base-prime)) 253))
  :in-theory '((:e base-prime) (:e primep) (:e oddp) (:e integer-length)))

(define int-from-field-lossy-sound-gadget ((f symbolp)
                                           (xs symbol-listp)
                                           (rs symbol-listp)
                                           (u symbolp)
                                           (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Integer::from_field_lossy'): @('Field::to_bits_le')."
  (field-to-bits-gadget f xs rs u p))

(local
 (defthm int-lossy-mod-low-plus-high
   (implies (and (integerp lo)
                 (integerp hi)
                 (integerp m))
            (equal (mod (+ lo (* m hi)) m)
                   (mod lo m)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable acl2::mod-of-+-of-*-same-arg2-arg1
                                     acl2::mod-of-+-of-*-same-arg2-arg2)))))

(local
 (defthm int-lossy-mod-below-bound
   (implies (and (integerp lo)
                 (integerp m)
                 (<= 0 lo)
                 (< lo m))
            (equal (mod lo m) lo))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable acl2::mod-when-<)))))

(defruledl int-lossy-low-lebits-are-mod
  (implies (and (natp n)
                (<= n (len bits)))
           (equal (lebits=>nat (take n bits))
                  (mod (lebits=>nat bits) (expt 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (disable acl2::lebits=>nat-upper-bound)
           :use ((:instance acl2::lebits=>nat-upper-bound
                            (digits (take n bits)))
                 (:instance acl2::lebits=>nat-of-append
                            (lodigits (take n bits))
                            (hidigits (nthcdr n bits)))
                 (:instance acl2::append-of-take-and-nthcdr
                            (n n)
                            (x bits))
                 (:instance acl2::len-of-take (n n) (xs bits))
                 (:instance int-lossy-mod-low-plus-high
                            (lo (lebits=>nat (take n bits)))
                            (hi (lebits=>nat (nthcdr n bits)))
                            (m (expt 2 n)))
                 (:instance int-lossy-mod-below-bound
                            (lo (lebits=>nat (take n bits)))
                            (m (expt 2 n)))))))

(defruled int-lossy-bits-are-funspec
  :short "The first @('n') canonical field bits, read as an integer,
          are @('int-from-field-lossy-spec')."
  (implies (and (fieldp f)
                (bit-listp xs)
                (equal (len xs) 253)
                (equal (lebits=>nat xs) f)
                (integer-widthp n))
           (b* ((bits (take n xs))
                (y (lebits->int bits signedp)))
             (and (equal (len bits) n)
                  (bit-listp bits)
                  (int-valuep y signedp n)
                  (equal y (int-from-field-lossy-spec f signedp n)))))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-from-field-lossy-spec
                            int-wrap
                            lebits->int
                            fieldp
                            pfield::fep
                            nfix
                            ifix
                            integer-widthp
                            posp-when-integer-widthp
                            int-width-lt-prime-bits
                            integer-length-of-base-prime
                            int-lossy-low-lebits-are-mod
                            int-valuep-of-lebits->int
                            acl2::bit-listp-of-take
                            acl2::len-of-take
                            acl2::pos-fix-when-posp)
                           (acl2::lebits=>nat-upper-bound))
           :use ((:instance int-lossy-low-lebits-are-mod
                            (bits xs)
                            (n n))
                 (:instance int-valuep-of-lebits->int
                            (bits (take n xs))
                            (n n)
                            (signedp signedp))))))

(defruled int-from-field-lossy-sound-gadget-sound
  :short "Wire soundness of @('Integer::from_field_lossy').  The unit
          wire is the public one.  The integer is @('lebits->int') of
          the first @('n') bit wires, for either signedness."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbolp f)
                (symbol-listp xs)
                (symbol-listp rs)
                (symbolp u)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (integer-widthp n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg f)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (int-from-field-lossy-sound-gadget f xs rs u p) asg p))
           (b* ((f$ (lookup-equal f asg))
                (xs$ (lookup-equal-list xs asg))
                (bits (take n xs$))
                (y (lebits->int bits signedp)))
             (and (bit-listp xs$)
                  (equal f$ (lebits=>nat xs$))
                  (fieldp f$)
                  (bit-listp bits)
                  (equal (len bits) n)
                  (int-valuep y signedp n)
                  (equal y (int-from-field-lossy-spec f$ signedp n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance field-to-bits-soundness
                            (x f) (xs xs) (rs rs) (u u) (p p))
                 (:instance int-lossy-bits-are-funspec
                            (f (lookup-equal f asg))
                            (xs (lookup-equal-list xs asg))
                            (n n)
                            (signedp signedp)))
           :in-theory (e/d (int-from-field-lossy-sound-gadget
                            int-lossy-base-prime-oddp
                            r1cs::fep-of-lookup-equal
                            fieldp
                            pfield::fep
                            integer-length-of-base-prime)
                           (field-to-bits-soundness
                            int-lossy-bits-are-funspec
                            (:e base-prime))))))
