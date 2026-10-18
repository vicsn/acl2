; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE of Field::cast (snarkVM
; circuit/program/src/data/literal/cast/field.rs) on the dispatch gadget
; progx-field-cast-gadget: for every destination, when field-cast does not
; fail, the canonical witnesses of that destination's arm
; (progx-field-cast-witsp) satisfy the constraints.

(in-package "ALEOVM")

(include-book "progx-field-cast")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-cast success implies the arm funspec's success.

(defruled progx-group-from-x-ok-when-values-ok
  (implies (and (fieldp x)
                (not (reserrp (values-group-from-x x))))
           (not (reserrp (group-from-x-coordinate-funspec x))))
  :use ((:instance curve-x-coordinate-in-group-p-suff
                   (y (values-x-in-subgroupp-witness x)))
        (:instance progx-y-of-groupp-is-fieldp
                   (p (ecurve::point-finite
                       x (values-x-in-subgroupp-witness x))))
        (:instance progx-not-reserrp-of-point-finite
                   (a x) (b (nfix (curve-x-coordinate-in-group-witness x)))))
  :in-theory '(values-group-from-x values-x-in-subgroupp
               group-from-x-coordinate-funspec curve-x-coordinate-to-group
               ecurve::point-finite->y-of-point-finite
               nfix acl2::natp-compound-recognizer
               (:e reserrp) (:e spec-error)))

(defruled progx-int-from-field-ok-when-values-ok
  (implies (and (fieldp f)
                (integer-widthp n)
                (not (reserrp (values-int-from-field f signedp n))))
           (not (equal (int-from-field-spec f signedp n) (spec-error))))
  :enable (values-int-from-field int-from-field-spec
           values-field-fix-when-fieldp
           posp-when-integer-widthp acl2::pos-fix-when-posp
           fieldp pfield::fep))

(defruled progx-field-bits-le-below-scalar
  (implies (and (natp x) (< x (scalar-prime)))
           (equal (field-bits-le x)
                  (append (acl2::nat=>lebits 251 x) '(0 0))))
  :use ((:instance acl2::nat=>lebits-of-lebits=>nat
                   (digits (append (acl2::nat=>lebits 251 x) '(0 0)))))
  :enable (field-bits-le base-field-size-in-bits
           acl2::lebits=>nat-of-append
           pfield::fep-fix pfield::fep))

(defruled progx-nthcdr-len-append
  (equal (nthcdr (len a) (append a y)) y)
  :induct (len a))

(defruled progx-nthcdr-251-of-lebits-append
  (equal (nthcdr 251 (append (acl2::nat=>lebits 251 x) y)) y)
  :use (:instance progx-nthcdr-len-append (a (acl2::nat=>lebits 251 x)))
  :enable acl2::len-of-nat=>lebits)

(defruled progx-take-251-of-lebits-append
  (equal (take 251 (append (acl2::nat=>lebits 251 x) y))
         (acl2::nat=>lebits 251 x))
  :enable acl2::len-of-nat=>lebits)

(defruled progx-scalar-from-field-ok-when-values-ok
  (implies (and (fieldp x)
                (not (reserrp (values-scalar-from-field x))))
           (not (reserrp (scalar-from-field-funspec x))))
  :enable (progx-field-bits-le-below-scalar
           acl2::len-of-nat=>lebits assert-eq-funspec enforce-funspec
           progx-nthcdr-251-of-lebits-append progx-take-251-of-lebits-append
           values-scalar-from-field values-field-fix-when-fieldp
           scalar-from-field-funspec scalar-from-bits-le-funspec
           scalar-field-size-in-bits
           boolean-assert-bits-are-zero-funspec
           boolean-assert-less-than-or-equal-constant-funspec
           boolean-is-less-than-or-equal-constant-funspec
           assert-funspec
           acl2::lebits=>nat-of-nat=>lebits
           fieldp pfield::fep)
  :disable ((:e scalar-prime) (:e base-prime)))

(defruled progx-field-cast-boolean-ok-bitp
  (implies (and (fieldp x)
                (not (reserrp (field-cast x (literal-type-boolean)))))
           (bitp x))
  :enable (field-cast values-literal-type-integerp values-field-fix-when-fieldp
           bitp (:e reserrp) (:e spec-error)))

(defruled progx-integer-widthp-of-width
  (integer-widthp (values-literal-type-width to))
  :enable (integer-widthp values-literal-type-width))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Canonical witnesses, by destination.

(define progx-field-cast-witsp ((to literal-typep) x
                                y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                                m-z r-z m-o r-o or-bit
                                ixs
                                sxs frs u srs
                                rs bitrows excess witrows partial uscore islet
                                (p primep) asg)
  :verify-guards nil
  :ignore-ok t
  :irrelevant-formals-ok t
  :short "The canonical witnesses of the arm that the destination selects."
  (b* ((xv (lookup-equal x asg)))
    (cond
     ((values-literal-type-integerp to)
      (equal (lookup-equal-list ixs asg)
             (int->lebits xv (values-literal-type-width to))))
     ((or (literal-type-case to :address) (literal-type-case to :group))
      (and (no-duplicatesp-equal
            (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2))
           (equal asg (group-enforce-in-group-assignment
                       x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                       (group-from-x-coordinate-funspec xv)))))
     ((literal-type-case to :boolean)
      (and (equal (lookup-equal r-z asg) (if (equal xv 0) 0 1))
           (equal (lookup-equal m-z asg)
                  (if (equal xv 0) 1 (pfield::inv xv p)))
           (equal (lookup-equal r-o asg) (if (equal xv 1) 0 1))
           (equal (lookup-equal m-o asg)
                  (if (equal xv 1) 1 (pfield::inv (pfield::sub xv 1 p) p)))
           (equal (lookup-equal or-bit asg) 1)))
     ((literal-type-case to :scalar)
      (and (equal (lookup-equal-list sxs asg) (field-bits-le xv))
           (equal (lookup-equal-list frs asg)
                  (crv-bits-lte-const-witness
                   (lookup-equal-list sxs asg) (nat=>lebits* (1- p))))
           (equal (lookup-equal-list srs asg)
                  (crv-bits-lte-const-witness
                   (take 251 (lookup-equal-list sxs asg))
                   (scalar-modulus-minus-one-bits)))))
     ((literal-type-case to :identifier)
      (b* ((bytes (id-decode-rows bitrows asg))
           (xs (append (fsa-id-flatten bitrows) excess)))
        (and (equal (lookup-equal-list xs asg) (field-bits-le xv))
             (equal (lookup-equal-list rs asg)
                    (fb-bits-lte-const-witness
                     (lookup-equal-list xs asg) (nat=>lebits* (1- p))))
             (id-wits-matchp bytes witrows asg)
             (equal (lookup-equal partial asg)
                    (nth 0 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
             (equal (lookup-equal uscore asg)
                    (nth 1 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
             (equal (lookup-equal islet asg)
                    (nth 2 (id-first-wits (values-nat-to-lebits 8 (car bytes))))))))
     (t t))))

(defmacro progx-field-cast-wits-call ()
  '(progx-field-cast-witsp to x
    y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
    m-z r-z m-o r-o or-bit ixs sxs frs u srs
    rs bitrows excess witrows partial uscore islet p asg))

(defruled progx-field-cast-complete
  :short "R1CS-COMPLETE of Field::cast: for every destination type on which
          field-cast does not fail, the canonical witnesses satisfy the
          dispatch gadget."
  (implies (progx-field-cast-hyps
            (not (reserrp (field-cast (lookup-equal x asg) to)))
            (progx-field-cast-wits-call))
           (r1cs::r1cs-constraints-holdp (progx-field-cast-call) asg p))
  :do-not-induct t
  :cases ((values-literal-type-integerp to)
          (literal-type-case to :address)
          (literal-type-case to :group)
          (literal-type-case to :boolean)
          (literal-type-case to :field)
          (literal-type-case to :scalar)
          (literal-type-case to :identifier))
  :hints (("Subgoal 7"
           :use (progx-field-cast-gadget-when-integer
                 progx-integer-widthp-of-width
                 (:instance int-from-field-gadget-complete
                            (f x) (xs ixs) (n (len ixs))
                            (signedp (values-literal-type-signedp to)))
                 (:instance progx-int-from-field-ok-when-values-ok
                            (f (lookup-equal x asg)) (n (len ixs))
                            (signedp (values-literal-type-signedp to))))
           :in-theory '(progx-field-cast-witsp field-cast
                        values-field-fix-when-fieldp
                        fieldp r1cs::fep-of-lookup-equal
                        progx-integer-widthp-of-width
                        (:e integer-widthp) (:e member-equal)
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 6"
           :use (progx-literal-type-when-address
                 progx-field-cast-gadget-when-address
                 (:instance grp-from-x-coordinate-gadget-complete
                            (xv (lookup-equal x asg)))
                 (:instance progx-group-from-x-ok-when-values-ok
                            (x (lookup-equal x asg))))
           :in-theory '(progx-field-cast-witsp field-cast
                        values-literal-type-integerp literal-type-kind
                        values-field-fix-when-fieldp
                        fieldp r1cs::fep-of-lookup-equal
                        (:e literal-type-address) (:e member-eq)
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 5"
           :use (progx-literal-type-when-group
                 progx-field-cast-gadget-when-group
                 (:instance grp-from-x-coordinate-gadget-complete
                            (xv (lookup-equal x asg)))
                 (:instance progx-group-from-x-ok-when-values-ok
                            (x (lookup-equal x asg))))
           :in-theory '(progx-field-cast-witsp field-cast
                        values-literal-type-integerp literal-type-kind
                        values-field-fix-when-fieldp
                        fieldp r1cs::fep-of-lookup-equal
                        (:e literal-type-group) (:e member-eq)
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 4"
           :use (progx-literal-type-when-boolean
                 progx-field-cast-gadget-when-boolean
                 field-cast-to-boolean-gadget-complete
                 (:instance progx-field-cast-boolean-ok-bitp
                            (x (lookup-equal x asg))))
           :in-theory '(progx-field-cast-witsp
                        values-literal-type-integerp
                        fieldp r1cs::fep-of-lookup-equal
                        (:e literal-type-boolean) (:e member-eq)))
          ("Subgoal 3"
           :use (progx-literal-type-when-field
                 progx-field-cast-gadget-when-field)
           :in-theory '(r1cs::r1cs-constraints-holdp
                        (:e literal-type-field)))
          ("Subgoal 2"
           :use (progx-literal-type-when-scalar
                 progx-field-cast-gadget-when-scalar
                 (:instance scalar-from-field-gadget-complete (xs sxs))
                 (:instance progx-scalar-from-field-ok-when-values-ok
                            (x (lookup-equal x asg))))
           :in-theory '(progx-field-cast-witsp field-cast
                        values-literal-type-integerp
                        values-field-fix-when-fieldp
                        fieldp r1cs::fep-of-lookup-equal primep-of-base-prime
                        (:e literal-type-scalar) (:e member-eq)
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 1"
           :use (progx-literal-type-when-identifier
                 progx-field-cast-gadget-when-identifier
                 fsa-idlit-from-field-gadget-complete)
           :in-theory '(progx-field-cast-witsp field-cast
                        values-literal-type-integerp
                        values-field-fix-when-fieldp
                        fieldp r1cs::fep-of-lookup-equal
                        (:e literal-type-identifier) (:e member-eq)
                        (:e reserrp) (:e spec-error)))
          ("Subgoal 8"
           :in-theory '(progx-field-cast-gadget values-literal-type-integerp
                        r1cs::r1cs-constraints-holdp (:e member-eq)))))
