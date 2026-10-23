; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Group::from_bits_le / from_bits_be (circuit/types/group/src/helpers/
; from_bits.rs): Field::from_bits_le/be, then from_x_coordinate.  The field
; output is a linear combination; the from_x_coordinate wire x stands for it
; and the theorems take its value to be that combination's value.
;
; The group spec reads the field as the value of all the bits below p
; (curve-field-from-bits-le); the field spec checks the excess bits by their
; field sum.  They agree for lists shorter than p
; (grp-curve-field-from-bits-le-is-funspec).

(in-package "ALEOVM")

(include-book "grp-from-x-coordinate")
(include-book "fb2-field-bits")

(define grp-bitsum ((bits bit-listp))
  :returns (n natp)
  (if (endp bits) 0 (+ (acl2::bfix (car bits)) (grp-bitsum (cdr bits)))))

(defruled grp-bitsum-bound
  (<= (grp-bitsum bits) (len bits))
  :induct (len bits)
  :enable (grp-bitsum acl2::bfix len))

(defruled grp-bits-field-sum-is-bitsum
  (implies (< (len bits) (base-prime))
           (equal (bits-field-sum bits) (grp-bitsum bits)))
  :induct (len bits)
  :enable (bits-field-sum grp-bitsum len)
  :prep-books ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
  :hints (("Subgoal *1/1" :use ((:instance grp-bitsum-bound (bits (cdr bits))))
           :in-theory (enable pfield::add acl2::bfix))))

(defruled grp-bitsum-zero-iff-lebits-zero
  (implies (bit-listp bits)
           (equal (equal (grp-bitsum bits) 0)
                  (equal (acl2::lebits=>nat bits) 0)))
  :induct (len bits)
  :enable (grp-bitsum len bit-listp acl2::lebits=>nat
           acl2::lendian=>nat-of-cons acl2::dab-digit-fix
           acl2::dab-digitp acl2::dab-base-fix))

(defruled grp-lebits-split
  (implies (<= (nfix n) (len bits))
           (equal (acl2::lebits=>nat bits)
                  (+ (acl2::lebits=>nat (take n bits))
                     (* (acl2::lebits=>nat (nthcdr n bits))
                        (expt 2 (nfix n))))))
  :use (:instance acl2::lendian=>nat-of-append
                  (acl2::base 2)
                  (acl2::lodigits (take n bits))
                  (acl2::hidigits (nthcdr n bits)))
  :enable (acl2::lebits=>nat))

(defruled grp-base-prime-facts
  (and (equal (base-field-size-in-bits) 253)
       (< (base-prime) (expt 2 253))
       (< (expt 2 252) (base-prime))
       (equal (acl2::lebits=>nat (acl2::nat=>lebits 253 (1- (base-prime))))
              (1- (base-prime)))
       (equal (len (acl2::nat=>lebits 253 (1- (base-prime)))) 253))
  :in-theory '((:e base-field-size-in-bits) (:e base-prime) (:e expt)
               (:e acl2::lebits=>nat) (:e acl2::nat=>lebits) (:e len)))

(defruled grp-high-part-big-gen
  (implies (and (< q k) (natp k) (natp lo) (natp hi) (not (equal hi 0)))
           (<= q (+ lo (* k hi))))
  :nonlinearp t
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled grp-high-part-big
  (implies (and (natp lo) (natp hi) (not (equal hi 0)))
           (<= (base-prime) (+ lo (* (expt 2 253) hi))))
  :use (:instance grp-high-part-big-gen (q (base-prime)) (k (expt 2 253)))
  :in-theory '((:e base-prime) (:e expt) (:e <) (:e natp)))

(defruled grp-curve-field-from-bits-le-is-funspec
  :short "The group spec's @('curve-field-from-bits-le') (the value of all
          the bits below @($p$)) is @(tsee field-from-bits-le-funspec) for
          lists shorter than @($p$) (the field sum of the excess bits is then
          their integer sum)."
  (implies (and (bit-listp bits)
                (< (len bits) (base-prime)))
           (equal (curve-field-from-bits-le bits)
                  (field-from-bits-le-funspec bits)))
  :do-not-induct t
  :cases ((<= (len bits) 252) (equal (len bits) 253))
  :use (grp-base-prime-facts
        (:instance grp-lebits-split (n 253))
        (:instance grp-bits-field-sum-is-bitsum (bits (nthcdr 253 bits)))
        (:instance grp-bitsum-zero-iff-lebits-zero (bits (nthcdr 253 bits)))
        (:instance acl2::lendian=>nat-upper-bound (acl2::base 2) (acl2::digits bits))
        (:instance grp-bitsum-bound (bits (nthcdr 253 bits)))
        (:instance grp-high-part-big
                   (lo (acl2::lebits=>nat (take 253 bits)))
                   (hi (acl2::lebits=>nat (nthcdr 253 bits)))))
  :in-theory (e/d (curve-field-from-bits-le field-from-bits-le-funspec
                   boolean-assert-bits-are-zero-funspec
                   boolean-assert-less-than-or-equal-constant-funspec
                   boolean-is-less-than-or-equal-constant-funspec
                   assert-funspec assert-eq-funspec enforce-funspec
                   acl2::lebits=>nat)
                  ((:e base-prime) (:e base-field-size-in-bits) (:e expt)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled grp-curve-field-from-bits-be-is-funspec
  (implies (and (bit-listp bits)
                (< (len bits) (base-prime)))
           (equal (curve-field-from-bits-be bits)
                  (field-from-bits-be-funspec bits)))
  :use (:instance grp-curve-field-from-bits-le-is-funspec (bits (rev bits)))
  :in-theory (enable curve-field-from-bits-be field-from-bits-be-funspec))

(define grp-from-bits-le-gadget ((bits symbol-listp) (rs symbol-listp)
                                 (x symbolp) (y symbolp)
                                 (qx symbolp) (qy symbolp)
                                 (cx2 symbolp) (cy2 symbolp)
                                 (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                 (x3 symbolp) (y3 symbolp)
                                 (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                 (p primep))
  :verify-guards nil
  :short "@('Group::from_bits_le'): @('Field::from_bits_le'), then
          @('from_x_coordinate') on its output.  The output of
          @('Field::from_bits_le') is a linear combination; the wire @('x')
          stands for it, and the theorems below take its value to be the
          value of that linear combination."
  (append (fb-field-from-bits-le-gadget bits rs p)
          (grp-from-x-coordinate-gadget
           x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)))

(define grp-from-bits-be-gadget ((bits symbol-listp) (rs symbol-listp)
                                 (x symbolp) (y symbolp)
                                 (qx symbolp) (qy symbolp)
                                 (cx2 symbolp) (cy2 symbolp)
                                 (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                                 (x3 symbolp) (y3 symbolp)
                                 (exy symbolp) (ex2 symbolp) (ey2 symbolp)
                                 (p primep))
  :verify-guards nil
  :short "@('Group::from_bits_be'): @('Field::from_bits_be'), then
          @('from_x_coordinate'); @('x') stands for the output linear
          combination as in @(tsee grp-from-bits-le-gadget)."
  (append (fb-field-from-bits-be-gadget bits rs p)
          (grp-from-x-coordinate-gadget
           x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)))

(defmacro grp-fb-hyps (bits-binding &rest more)
  `(grp-from-xy-wire-hyps
    (symbol-listp bits)
    (symbol-listp rs)
    (< (len bits) (base-prime))
    (r1cs::valuation-binds-allp asg ,bits-binding)
    (r1cs::valuation-binds-allp asg rs)
    (bit-listp (lookup-equal-list ,bits-binding asg))
    (equal (len rs)
           (if (>= (len bits) (integer-length p))
               (bits-lte-const-check-rlen (nat=>lebits* (1- p)))
             0))
    (equal (lookup-equal x asg)
           (lebits=>nat (take (min (len bits) (integer-length p))
                              (lookup-equal-list ,bits-binding asg))))
    ,@more))

(defruled grp-not-reserrp-when-natp
  (implies (natp x) (not (reserrp x)))
  :enable reserrp)

(defruled grp-lookup-not-reserrp
  (implies (and (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (not (reserrp (lookup-equal x asg))))
  :use (:instance grp-not-reserrp-when-natp (x (lookup-equal x asg)))
  :enable (pfield::fep))

(defruled grp-true-listp-of-lookup-equal-list
  (true-listp (lookup-equal-list keys alist))
  :induct (len keys)
  :enable lookup-equal-list)
(defruled grp-true-list-fix-id (implies (true-listp x) (equal (true-list-fix x) x)))

(defruled grp-fb-prime-facts
  (and (primep (base-prime)) (oddp (base-prime)))
  :in-theory '((:e base-prime) (:e primep) (:e oddp)))

(defruled grp-from-bits-le-gadget-sound
  :short "R1CS-SOUND of @('Group::from_bits_le') given
          @('Boolean::new') on each input bit: the funspec does not fail
          and is the point of the @('x') and @('y') wires."
  (implies (grp-fb-hyps bits
            (r1cs::r1cs-constraints-holdp
             (grp-from-bits-le-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                      x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (group-from-bits-le-funspec (lookup-equal-list bits asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :do-not-induct t
  :use (grp-fb-prime-facts
        fb2-field-from-bits-le-sound
        grp-from-x-coordinate-gadget-sound
        (:instance grp-curve-field-from-bits-le-is-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance len-of-lookup-equal-list (keys bits) (alist asg)))
  :in-theory '(grp-from-bits-le-gadget group-from-bits-le-funspec
               r1cs::r1cs-constraints-holdp-of-append
               (:e reserrp) fieldp r1cs::fep-of-lookup-equal
               grp-lookup-not-reserrp))

(defruled grp-from-bits-be-gadget-sound
  :short "R1CS-SOUND of @('Group::from_bits_be') given
          @('Boolean::new') on each input bit."
  (implies (grp-fb-hyps (rev bits)
            (r1cs::r1cs-constraints-holdp
             (grp-from-bits-be-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                      x3 y3 exy ex2 ey2 p)
             asg p))
           (equal (group-from-bits-be-funspec (lookup-equal-list bits asg))
                  (ecurve::point-finite (lookup-equal x asg)
                                        (lookup-equal y asg))))
  :do-not-induct t
  :use (grp-fb-prime-facts
        fb2-field-from-bits-be-sound
        grp-from-x-coordinate-gadget-sound
        (:instance grp-curve-field-from-bits-be-is-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance acl2::bit-listp-of-rev (acl2::x (lookup-equal-list bits asg)))
        (:instance lookup-equal-list-of-rev (keys bits) (alist asg))
        (:instance len-of-lookup-equal-list (keys bits) (alist asg)))
  :in-theory '(grp-from-bits-be-gadget group-from-bits-be-funspec
               r1cs::r1cs-constraints-holdp-of-append
               acl2::rev-of-rev acl2::len-of-rev
               grp-true-listp-of-lookup-equal-list grp-true-list-fix-id
               (:e reserrp) fieldp r1cs::fep-of-lookup-equal
               grp-lookup-not-reserrp))

(defmacro grp-fb-canon (bits-binding funspec)
  `(and (not (reserrp (,funspec (lookup-equal-list bits asg))))
        (equal (lookup-equal-list rs asg)
               (if (>= (len bits) (integer-length p))
                   (fb-bits-lte-const-witness
                    (take (integer-length p)
                          (lookup-equal-list ,bits-binding asg))
                    (nat=>lebits* (1- p)))
                 nil))
        (group-enforce-in-group-witness-lookupsp
         x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
         (,funspec (lookup-equal-list bits asg)) asg p)))

(defruled grp-from-bits-le-gadget-complete
  :short "R1CS-COMPLETE of @('Group::from_bits_le'): the fold witness of
          @('Field::from_bits_le') and the canonical @('enforce_in_group')
          witnesses of the funspec's point satisfy the constraints."
  (implies (grp-fb-hyps bits
            (grp-fb-canon bits group-from-bits-le-funspec))
           (r1cs::r1cs-constraints-holdp
            (grp-from-bits-le-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                     x3 y3 exy ex2 ey2 p)
            asg p))
  :do-not-induct t
  :use (grp-fb-prime-facts
        fb2-field-from-bits-le-complete
        (:instance group-enforce-in-group-gadget-complete
                   (pt (group-from-bits-le-funspec (lookup-equal-list bits asg))))
        (:instance return-type-of-group-from-bits-le-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance grp-curve-field-from-bits-le-is-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance len-of-lookup-equal-list (keys bits) (alist asg)))
  :in-theory '(grp-from-bits-le-gadget grp-from-x-coordinate-gadget
               group-from-bits-le-funspec
               group-enforce-in-group-witness-lookupsp
               r1cs::r1cs-constraints-holdp-of-append))

(defruled grp-from-bits-be-gadget-complete
  :short "R1CS-COMPLETE of @('Group::from_bits_be')."
  (implies (grp-fb-hyps (rev bits)
            (grp-fb-canon (rev bits) group-from-bits-be-funspec))
           (r1cs::r1cs-constraints-holdp
            (grp-from-bits-be-gadget bits rs x y qx qy cx2 cy2 dxy dx2 dy2
                                     x3 y3 exy ex2 ey2 p)
            asg p))
  :do-not-induct t
  :use (grp-fb-prime-facts
        fb2-field-from-bits-be-complete
        (:instance group-enforce-in-group-gadget-complete
                   (pt (group-from-bits-be-funspec (lookup-equal-list bits asg))))
        (:instance return-type-of-group-from-bits-be-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance grp-curve-field-from-bits-be-is-funspec
                   (bits (lookup-equal-list bits asg)))
        (:instance acl2::bit-listp-of-rev (acl2::x (lookup-equal-list bits asg)))
        (:instance lookup-equal-list-of-rev (keys bits) (alist asg))
        (:instance len-of-lookup-equal-list (keys bits) (alist asg)))
  :in-theory '(grp-from-bits-be-gadget grp-from-x-coordinate-gadget
               group-from-bits-be-funspec
               group-enforce-in-group-witness-lookupsp
               r1cs::r1cs-constraints-holdp-of-append
               acl2::rev-of-rev acl2::len-of-rev
               grp-true-listp-of-lookup-equal-list grp-true-list-fix-id))
