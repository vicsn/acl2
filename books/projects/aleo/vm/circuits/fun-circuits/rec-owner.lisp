; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Owner (snarkVM circuit/program/src/data/record/helpers/owner.rs).
; The variant (Public / Private) is fixed at synthesis time.
;
; new:           Owner<Plaintext>: both variants are Address::new(Mode::Private),
;                i.e. Group::new = enforce_in_group on the point's wires.
;                Owner<Ciphertext>: Public is Address::new, Private is
;                Ciphertext::new (no constraint, rec-ciphertext-new-gadget).
; is_equal:      same variant: Address::is_equal (Public, and Private plaintext
;                via Plaintext::Literal / Literal::Address), or
;                Ciphertext::is_equal (Private ciphertext); otherwise the
;                constant false.  is_not_equal likewise with the constant true.
; to_entry:      no constraint: the entry reuses the owner's address wires.

(in-package "ALEOVM")

(include-book "rec-ciphertext")
(include-book "group-wire-sound")
(include-book "group-enforce-in-group-complete")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner::new

(define rec-owner-new-gadget ((x symbolp) (y symbolp)
                              (qx symbolp) (qy symbolp)
                              (cx2 symbolp) (cy2 symbolp)
                              (dxy symbolp) (dx2 symbolp) (dy2 symbolp)
                              (x3 symbolp) (y3 symbolp)
                              (exy symbolp) (ex2 symbolp) (ey2 symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Owner<Plaintext>::new') (either variant) and of
          @('Owner<Ciphertext>::new') for a public owner: Address::new."
  (group-enforce-in-group-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3
                                 exy ex2 ey2 (base-prime)))

(defmacro rec-owner-new-hyps ()
  '(and (symbolp x) (symbolp y)
        (symbolp qx) (symbolp qy)
        (symbolp cx2) (symbolp cy2)
        (symbolp dxy) (symbolp dx2) (symbolp dy2)
        (symbolp x3) (symbolp y3)
        (symbolp exy) (symbolp ex2) (symbolp ey2)))

(defruled rec-owner-new-sound
  (b* ((pt (ecurve::point-finite (lookup-equal x asg) (lookup-equal y asg))))
    (implies (and (rec-owner-new-hyps)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg x)
                  (r1cs::valuation-bindsp asg y)
                  (r1cs::valuation-bindsp asg qx)
                  (r1cs::valuation-bindsp asg qy)
                  (r1cs::valuation-bindsp asg cx2)
                  (r1cs::valuation-bindsp asg cy2)
                  (r1cs::valuation-bindsp asg dxy)
                  (r1cs::valuation-bindsp asg dx2)
                  (r1cs::valuation-bindsp asg dy2)
                  (r1cs::valuation-bindsp asg x3)
                  (r1cs::valuation-bindsp asg y3)
                  (r1cs::valuation-bindsp asg exy)
                  (r1cs::valuation-bindsp asg ex2)
                  (r1cs::valuation-bindsp asg ey2)
                  (r1cs::r1cs-constraints-holdp
                   (rec-owner-new-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3
                                         exy ex2 ey2)
                   asg (base-prime)))
             (and (groupp pt)
                  (equal (crypto-owner-new t pt) (owner-public pt))
                  (equal (crypto-owner-new nil (plaintext-literal (literal-address pt)))
                         (owner-private pt))
                  (ownerp (owner-public pt))
                  (ownerp (owner-private pt))
                  (crypto-ciphertext-ownerp (crypto-ciphertext-owner-public pt))
                  (equal (crypto-ciphertext-owner-public->address
                          (crypto-ciphertext-owner-public pt))
                         pt))))
  :enable (rec-owner-new-gadget crypto-owner-new)
  :use (:instance group-new-wire-sound (p (base-prime))))

(defruled rec-owner-new-complete
  (implies (and (rec-owner-new-hyps)
                (no-duplicatesp-equal
                 (list x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2))
                (groupp pt))
           (b* ((asg (group-enforce-in-group-assignment
                      x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 pt)))
             (and (r1cs::r1cs-valuationp asg (base-prime))
                  (equal (lookup-equal x asg) (ecurve::point-finite->x pt))
                  (equal (lookup-equal y asg) (ecurve::point-finite->y pt))
                  (r1cs::r1cs-constraints-holdp
                   (rec-owner-new-gadget x y qx qy cx2 cy2 dxy dx2 dy2 x3 y3
                                         exy ex2 ey2)
                   asg (base-prime)))))
  :enable rec-owner-new-gadget
  :use (:instance group-enforce-in-group-gadget-satisfiable (p (base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner::to_entry

(define rec-owner-to-entry-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('Owner<Plaintext>::to_entry'): none."
  nil)

(defruled rec-owner-to-entry-sound
  (b* ((pt (ecurve::point-finite (lookup-equal x asg) (lookup-equal y asg))))
    (implies (and (groupp pt)
                  (r1cs::r1cs-constraints-holdp (rec-owner-to-entry-gadget)
                                                asg (base-prime)))
             (and (equal (crypto-owner-to-entry (owner-public pt))
                         (entry-public (plaintext-literal (literal-address pt))))
                  (equal (crypto-owner-to-entry (owner-private pt))
                         (entry-private (plaintext-literal (literal-address pt)))))))
  :enable crypto-owner-to-entry)

(defruled rec-owner-to-entry-complete
  (r1cs::r1cs-constraints-holdp (rec-owner-to-entry-gadget) asg p)
  :enable (rec-owner-to-entry-gadget r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner<Plaintext>::is_equal / is_not_equal

(define rec-owner-make ((publicp booleanp) (pt groupp))
  :returns (o ownerp)
  (if publicp (owner-public pt) (owner-private pt)))

(define rec-owner-is-equal-gadget ((pa booleanp) (pb booleanp)
                                   (x1 symbolp) (y1 symbolp)
                                   (x2 symbolp) (y2 symbolp)
                                   (mx symbolp) (rx symbolp)
                                   (my symbolp) (ry symbolp)
                                   (out symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Owner<Plaintext>::is_equal') and
          @('is_not_equal'): Address::is_equal when the variants agree."
  (if (equal pa pb)
      (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out (base-prime))
    nil))

(define rec-owner-is-equal-value ((pa booleanp) (pb booleanp)
                                  (out symbolp) (asg alistp))
  :verify-guards nil
  (if (equal pa pb) (lookup-equal out asg) 0))

(define rec-owner-is-not-equal-value ((pa booleanp) (pb booleanp)
                                      (out symbolp) (asg alistp))
  :verify-guards nil
  (if (equal pa pb) (pfield::sub 1 (lookup-equal out asg) (base-prime)) 1))

(defruled rec-owner-is-equal-sound
  (implies (and (booleanp pa) (booleanp pb)
                (groupp p1) (groupp p2)
                (eq-wire-hyps
                 (r1cs::r1cs-constraints-holdp
                  (rec-owner-is-equal-gadget pa pb x1 y1 x2 y2 mx rx my ry out)
                  asg p)))
           (and (equal (rec-owner-is-equal-value pa pb out asg)
                       (crypto-owner-is-equal (rec-owner-make pa p1)
                                              (rec-owner-make pb p2)))
                (equal (rec-owner-is-not-equal-value pa pb out asg)
                       (crypto-owner-is-not-equal (rec-owner-make pa p1)
                                                  (rec-owner-make pb p2)))))
  :do-not-induct t
  :enable (rec-owner-is-equal-gadget rec-owner-is-equal-value
           rec-owner-is-not-equal-value rec-owner-make
           crypto-owner-is-equal crypto-owner-is-not-equal
           crypto-plaintext-is-equal crypto-bit-not
           address-is-equal-funspec address-is-not-equal-funspec
           group-is-equal-funspec group-is-not-equal-funspec)
  :use ((:instance crv-address-is-equal-wire-sound)
        (:instance crv-address-is-not-equal-wire-sound)))

(defmacro rec-eq-witness-hyps ()
  '(and (equal (lookup-equal rx asg)
               (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg)) 0 1))
        (equal (lookup-equal mx asg)
               (if (equal (lookup-equal x1 asg) (lookup-equal x2 asg))
                   0
                 (pfield::inv (pfield::sub (lookup-equal x1 asg)
                                           (lookup-equal x2 asg) p)
                              p)))
        (equal (lookup-equal ry asg)
               (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg)) 0 1))
        (equal (lookup-equal my asg)
               (if (equal (lookup-equal y1 asg) (lookup-equal y2 asg))
                   0
                 (pfield::inv (pfield::sub (lookup-equal y1 asg)
                                           (lookup-equal y2 asg) p)
                              p)))
        (equal (lookup-equal out asg) (address-is-equal-funspec p1 p2))))

(defruled rec-owner-is-equal-complete
  (implies (and (booleanp pa) (booleanp pb)
                (eq-wire-hyps (rec-eq-witness-hyps)))
           (r1cs::r1cs-constraints-holdp
            (rec-owner-is-equal-gadget pa pb x1 y1 x2 y2 mx rx my ry out)
            asg p))
  :enable rec-owner-is-equal-gadget
  :use crv-address-is-equal-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Owner<Ciphertext>::is_equal / is_not_equal

(defruled rec-ciphertext-owner-public-sound
  (implies (and (groupp p1) (groupp p2)
                (eq-wire-hyps
                 (r1cs::r1cs-constraints-holdp
                  (crv-address-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
                  asg p)))
           (and (equal (lookup-equal out asg)
                       (crypto-ciphertext-owner-is-equal
                        (crypto-ciphertext-owner-public p1)
                        (crypto-ciphertext-owner-public p2)))
                (equal (pfield::sub 1 (lookup-equal out asg) p)
                       (crypto-ciphertext-owner-is-not-equal
                        (crypto-ciphertext-owner-public p1)
                        (crypto-ciphertext-owner-public p2)))))
  :do-not-induct t
  :enable (crypto-ciphertext-owner-is-equal crypto-ciphertext-owner-is-not-equal
           crypto-bit-not
           address-is-equal-funspec address-is-not-equal-funspec
           group-is-equal-funspec group-is-not-equal-funspec)
  :use ((:instance crv-address-is-equal-wire-sound)
        (:instance crv-address-is-not-equal-wire-sound)
        (:instance crv-address-is-not-equal-gadget (p (base-prime)))))

(defruled rec-ciphertext-owner-private-sound
  (b* ((xvals (lookup-equal-list xs asg))
       (yvals (lookup-equal-list ys asg))
       (oa (crypto-ciphertext-owner-private xvals))
       (ob (crypto-ciphertext-owner-private yvals)))
    (implies (rec-vec-hyps)
             (and (implies (r1cs::r1cs-constraints-holdp
                            (rec-fields-is-equal-gadget xs ys ms rs zs)
                            asg (base-prime))
                           (equal (rec-fields-is-equal-value xs ys rs zs asg)
                                  (crypto-ciphertext-owner-is-equal oa ob)))
                  (implies (r1cs::r1cs-constraints-holdp
                            (rec-fields-is-not-equal-gadget xs ys ms rs zs)
                            asg (base-prime))
                           (equal (rec-fields-is-not-equal-value xs ys rs zs asg)
                                  (crypto-ciphertext-owner-is-not-equal oa ob))))))
  :do-not-induct t
  :in-theory (e/d (crypto-ciphertext-owner-is-equal
                   crypto-ciphertext-owner-is-not-equal
                   crypto-ciphertext-is-not-equal)
                  (lookup-equal-list))
  :use (rec-ciphertext-is-equal-sound rec-ciphertext-is-not-equal-sound))

(defruled rec-ciphertext-owner-mixed
  (and (equal (crypto-ciphertext-owner-is-equal
               (crypto-ciphertext-owner-public p1)
               (crypto-ciphertext-owner-private cs))
              0)
       (equal (crypto-ciphertext-owner-is-equal
               (crypto-ciphertext-owner-private cs)
               (crypto-ciphertext-owner-public p1))
              0)
       (equal (crypto-ciphertext-owner-is-not-equal
               (crypto-ciphertext-owner-public p1)
               (crypto-ciphertext-owner-private cs))
              1)
       (equal (crypto-ciphertext-owner-is-not-equal
               (crypto-ciphertext-owner-private cs)
               (crypto-ciphertext-owner-public p1))
              1))
  :enable (crypto-ciphertext-owner-is-equal crypto-ciphertext-owner-is-not-equal
           crypto-bit-not))
