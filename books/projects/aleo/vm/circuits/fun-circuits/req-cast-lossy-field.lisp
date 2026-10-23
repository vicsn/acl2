; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field::cast_lossy (circuit/program/src/data/literal/cast_lossy/field.rs),
; the destinations other than Address and Group:
;   Boolean   Field::to_bits_le, then bit 0
;   Field     none (clone)
;   Integer   Integer::from_field_lossy = Field::to_bits_le, first n bits
;   Scalar    Scalar::from_field_lossy = Field::to_bits_le, first 250 bits
;   Signature, String  no CastLossy impl; field-cast-lossy fails.
; The three bit arms emit the same constraints, field-to-bits-gadget on the
; input (the 253 bit wires, the bits-below-prime comparator and the unit
; wire).

(in-package "ALEOVM")

(include-book "int-divshift-from-field-lossy-complete")
(include-book "progx-field-cast-complete")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled req-car-is-mod-2
  (implies (and (bit-listp xs) (consp xs))
           (equal (mod (lebits=>nat xs) 2) (car xs)))
  :enable (lebits=>nat acl2::lendian=>nat acl2::dab-digit-list-fix
           acl2::dab-digit-fix acl2::dab-digitp bitp)
  :expand ((lebits=>nat xs) (acl2::lendian=>nat 2 xs)))

(defruled req-int-wrap-is-of-unsigned-mod
  (implies (and (natp x) (posp n))
           (equal (int-wrap x signedp n)
                  (values-int-of-unsigned (mod x (expt 2 n)) signedp n)))
  :enable (int-wrap values-int-of-unsigned acl2::pos-fix))

(defruled req-take-is-mod
  (implies (and (natp n)
                (<= n (len bits)))
           (equal (lebits=>nat (take n bits))
                  (mod (lebits=>nat bits) (expt 2 n))))
  :do-not-induct t
  :use ((:instance acl2::lebits=>nat-upper-bound (digits (take n bits)))
        (:instance acl2::lebits=>nat-of-append
                   (lodigits (take n bits))
                   (hidigits (nthcdr n bits)))
        (:instance acl2::append-of-take-and-nthcdr (n n) (x bits)))
  :in-theory (e/d (acl2::mod-of-+-of-*-same-arg2-arg1
                   acl2::mod-of-+-of-*-same-arg2-arg2
                   acl2::mod-when-<)
                  (acl2::lebits=>nat-upper-bound
                   acl2::lebits=>nat-of-append
                   acl2::append-of-take-and-nthcdr)))

(defruled req-scalar-lossy-funspec-is-values
  (implies (fieldp x)
           (equal (scalar-from-field-lossy-funspec x)
                  (values-scalar-from-field-lossy x)))
  :enable (values-scalar-from-field-lossy values-field-fix-when-fieldp)
  :use (req-field-bits-le-facts
        (:instance scalar-lossy-low-bits-are-funspec
                   (p (base-prime))
                   (xs (field-bits-le x)))
        (:instance req-take-is-mod (n 250) (bits (field-bits-le x))))
  :prep-lemmas
  ((defruled req-field-bits-le-facts
     (implies (fieldp x)
              (and (bit-listp (field-bits-le x))
                   (equal (len (field-bits-le x)) 253)
                   (equal (lebits=>nat (field-bits-le x)) x)))
     :enable (field-bits-le fieldp base-field-size-in-bits
              acl2::lebits=>nat-of-nat=>lebits)
     :use fb-base-prime-below-2-253)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro req-fcl-nongroupp (to)
  `(not (or (literal-type-case ,to :address)
            (literal-type-case ,to :group))))

(define req-fcl-bits-arm-p ((to literal-typep))
  :short "Destinations whose arm is Field::to_bits_le."
  (or (values-literal-type-integerp to)
      (literal-type-case to :boolean)
      (literal-type-case to :scalar)))

(define req-fcl-nongroup-gadget ((to literal-typep) f xs rs u (p primep))
  :verify-guards nil
  :short "Constraints of Field::cast_lossy for the destinations other than
          Address and Group."
  (if (req-fcl-bits-arm-p to)
      (field-to-bits-gadget f xs rs u p)
    nil))

(define req-fcl-nongroup-out ((to literal-typep) f xs asg)
  :verify-guards nil
  :short "The literal the output wires denote."
  (b* ((xs$ (lookup-equal-list xs asg)))
    (cond ((values-literal-type-integerp to)
           (values-integer-literal
            to (lebits->int (take (values-literal-type-width to) xs$)
                            (values-literal-type-signedp to))))
          (t (literal-type-case
              to
              :boolean (literal-boolean (car xs$))
              :field (literal-field (lookup-equal f asg))
              :scalar (literal-scalar (lebits=>nat (take 250 xs$)))
              :otherwise (spec-error))))))

(defmacro req-fcl-hyps (&rest more)
  `(and (literal-typep to)
        (equal p (base-prime))
        (symbolp f)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg f)
        (implies (req-fcl-bits-arm-p to)
                 (and (symbol-listp xs)
                      (symbol-listp rs)
                      (symbolp u)
                      (equal (len xs) 253)
                      (equal (len rs) (bits-lt-prime-rlen p))
                      (r1cs::valuation-binds-allp asg xs)
                      (r1cs::valuation-binds-allp asg rs)
                      (r1cs::valuation-bindsp asg u)
                      (equal (lookup-equal u asg) 1)))
        ,@more))

(defruled req-fcl-bits-facts
  (implies (and (req-fcl-hyps)
                (req-fcl-bits-arm-p to)
                (r1cs::r1cs-constraints-holdp
                 (field-to-bits-gadget f xs rs u p) asg p))
           (b* ((f$ (lookup-equal f asg))
                (xs$ (lookup-equal-list xs asg)))
             (and (bit-listp xs$)
                  (equal (len xs$) 253)
                  (equal f$ (lebits=>nat xs$))
                  (fieldp f$))))
  :use ((:instance field-to-bits-soundness (x f)))
  :in-theory (e/d (int-lossy-base-prime-oddp r1cs::fep-of-lookup-equal
                   fieldp integer-length-of-base-prime)
                  (field-to-bits-soundness (:e base-prime))))

(defruled req-fcl-nongroup-sound
  :short "R1CS-SOUND of Field::cast_lossy, destinations other than Address
          and Group: the literal of the output wires is the funspec of the
          input wire.  No type hypothesis on the input."
  (implies (and (req-fcl-hyps)
                (req-fcl-nongroupp to)
                (r1cs::r1cs-constraints-holdp
                 (req-fcl-nongroup-gadget to f xs rs u p) asg p))
           (equal (req-fcl-nongroup-out to f xs asg)
                  (field-cast-lossy (lookup-equal f asg) to)))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (literal-type-case to :boolean)
          (literal-type-case to :scalar)
          (literal-type-case to :field))
  :hints (("Subgoal 4"
           :use (req-fcl-bits-facts
                 progx-integer-widthp-of-width
                 (:instance int-lossy-bits-are-funspec
                            (f (lookup-equal f asg))
                            (xs (lookup-equal-list xs asg))
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to)))
                 (:instance req-int-wrap-is-of-unsigned-mod
                            (x (lookup-equal f asg))
                            (n (values-literal-type-width to))
                            (signedp (values-literal-type-signedp to))))
           :in-theory (e/d (req-fcl-nongroup-gadget req-fcl-nongroup-out
                            req-fcl-bits-arm-p field-cast-lossy
                            int-from-field-lossy-spec
                            values-field-fix-when-fieldp
                            posp-when-integer-widthp)
                           (int-wrap values-int-of-unsigned lebits->int
                            values-literal-type-width integer-widthp)))
          ("Subgoal 3"
           :use (req-fcl-bits-facts
                 progx-literal-type-when-boolean
                 (:instance req-car-is-mod-2 (xs (lookup-equal-list xs asg))))
           :in-theory (e/d (req-fcl-nongroup-gadget req-fcl-nongroup-out
                            req-fcl-bits-arm-p field-cast-lossy
                            values-field-fix-when-fieldp)
                           ()))
          ("Subgoal 2"
           :use (req-fcl-bits-facts
                 progx-literal-type-when-scalar
                 (:instance scalar-lossy-low-bits-are-funspec
                            (x (lookup-equal f asg))
                            (xs (lookup-equal-list xs asg)))
                 (:instance req-scalar-lossy-funspec-is-values
                            (x (lookup-equal f asg))))
           :in-theory (e/d (req-fcl-nongroup-gadget req-fcl-nongroup-out
                            req-fcl-bits-arm-p field-cast-lossy
                            values-field-fix-when-fieldp)
                           ()))
          ("Subgoal 1"
           :use (progx-literal-type-when-field)
           :in-theory (e/d (req-fcl-nongroup-out field-cast-lossy
                            values-field-fix-when-fieldp
                            fieldp r1cs::fep-of-lookup-equal)
                           ()))
          ("Subgoal 5"
           :in-theory (e/d (req-fcl-nongroup-out field-cast-lossy)
                           ()))))

(defruled req-fcl-nongroup-complete
  :short "R1CS-COMPLETE of Field::cast_lossy, destinations other than
          Address and Group: on a field input, the canonical bits and the
          bits-below-prime witness satisfy the constraints (Field and the
          unsupported destinations have none)."
  (implies (and (req-fcl-hyps)
                (fieldp (lookup-equal f asg))
                (implies (req-fcl-bits-arm-p to)
                         (and (equal (lookup-equal-list xs asg)
                                     (field-bits-le (lookup-equal f asg)))
                              (equal (lookup-equal-list rs asg)
                                     (fb-bits-lte-const-witness
                                      (lookup-equal-list xs asg)
                                      (nat=>lebits* (1- p)))))))
           (r1cs::r1cs-constraints-holdp
            (req-fcl-nongroup-gadget to f xs rs u p) asg p))
  :do-not-induct t
  :cases ((req-fcl-bits-arm-p to))
  :use ((:instance int-divshift-from-field-lossy-gadget-complete))
  :in-theory (e/d (req-fcl-nongroup-gadget int-from-field-lossy-sound-gadget
                   integer-length-of-base-prime)
                  (req-fcl-bits-arm-p (:e base-prime))))
