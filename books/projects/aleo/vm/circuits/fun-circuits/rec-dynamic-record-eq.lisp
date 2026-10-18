; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DynamicRecord::is_equal / is_not_equal
; (snarkVM circuit/program/src/data/dynamic/record/equal.rs), variable mode:
;
;   owner.is_equal(&o.owner) & root.is_equal(&o.root)
;     & nonce.is_equal(&o.nonce) & version.is_equal(&o.version)
;
; evaluated left to right.  Each & of two non-constant booleans allocates
; z = a * b.  Field::is_equal is !is_not_equal, the linear combination 1 - r,
; so an & with it is z * (1 - r) = w.  U8::is_equal is
; to_field().is_equal(..), where to_field is the linear combination
; sum 2^i b_i of the bit wires; its is_not_equal gadget therefore has
; linear-combination operands.  is_not_equal is 1 - is_equal (no constraint).
;
; The owner and nonce points come from Address::new / Group::new and the
; version bits from Integer::new (R1CS-SOUND-IF); they are hypotheses here.

(in-package "ALEOVM")

(include-book "rec-owner")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/pow2sum-vectors")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Field::is_not_equal on linear-combination operands va, vb:
;   (va - vb) * (m) = (r)    and    (va - vb) * (1 - r) = (0)

(define rec-lc-neq-gadget ((va r1cs::sparse-vectorp)
                           (vb r1cs::sparse-vectorp)
                           (m symbolp)
                           (r symbolp)
                           (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (r1cs::sparse-vectorp va)
                              (r1cs::sparse-vectorp vb)
                              (symbolp m) (symbolp r) (primep p)))
  (b* ((delta (append va (vector-neg-prime vb p))))
    (list (r1cs::make-r1cs-constraint
           :a delta
           :b (list (list 1 m))
           :c (list (list 1 r)))
          (r1cs::make-r1cs-constraint
           :a delta
           :b (list (list 1 1)
                    (list (1- p) r))
           :c nil))))

(defruled rec-dot-of-var
  (implies (and (symbolp m) (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg m))
           (equal (r1cs::dot-product (list (list 1 m)) asg p)
                  (lookup-equal m asg)))
  :enable (r1cs::dot-product r1cs::fep-of-lookup-equal))

(defruled rec-dot-of-one-minus-var
  (implies (and (symbolp r) (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg r))
           (equal (r1cs::dot-product (list (list 1 1) (list (1- p) r)) asg p)
                  (pfield::sub 1 (lookup-equal r asg) p)))
  :enable (r1cs::dot-product r1cs::fep-of-lookup-equal))

(defruled rec-dot-of-delta
  (implies (and (primep p) (r1cs::sparse-vectorp vb))
           (equal (r1cs::dot-product (append va (vector-neg-prime vb p)) asg p)
                  (pfield::sub (r1cs::dot-product va asg p)
                               (r1cs::dot-product vb asg p)
                               p)))
  :enable (dot-product-of-vector-neg-prime-to-neg-of-dot-product
           pfield::sub))

(defruled rec-lc-neq-gadget-to-spec
  (implies (and (r1cs::sparse-vectorp va) (r1cs::sparse-vectorp vb)
                (symbolp m) (symbolp r) (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r))
           (b* ((delta (pfield::sub (r1cs::dot-product va asg p)
                                    (r1cs::dot-product vb asg p)
                                    p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (rec-lc-neq-gadget va vb m r p) asg p)
                    (and (equal (pfield::mul delta (lookup-equal m asg) p)
                                (lookup-equal r asg))
                         (equal (pfield::mul delta
                                             (pfield::sub 1 (lookup-equal r asg) p)
                                             p)
                                0)))))
  :enable (rec-lc-neq-gadget r1cs::r1cs-constraint-holdsp
           rec-dot-of-var rec-dot-of-one-minus-var rec-dot-of-delta)
  :expand ((r1cs::dot-product nil asg p)))

(defruled rec-lc-neq-gadget-bit
  (implies (and (r1cs::sparse-vectorp va) (r1cs::sparse-vectorp vb)
                (symbolp m) (symbolp r)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::r1cs-constraints-holdp
                 (rec-lc-neq-gadget va vb m r (base-prime)) asg (base-prime)))
           (equal (lookup-equal r asg)
                  (if (equal (r1cs::dot-product va asg (base-prime))
                             (r1cs::dot-product vb asg (base-prime)))
                      0 1)))
  :use ((:instance rec-lc-neq-gadget-to-spec (p (base-prime)))
        (:instance rec-neq-bit-when-constraints
                   (p (base-prime))
                   (x (r1cs::dot-product va asg (base-prime)))
                   (y (r1cs::dot-product vb asg (base-prime)))
                   (m (lookup-equal m asg))
                   (r (lookup-equal r asg))))
  :enable (r1cs::fep-of-lookup-equal primep-of-base-prime))

(defruled rec-lc-neq-gadget-complete
  (b* ((da (r1cs::dot-product va asg (base-prime)))
       (db (r1cs::dot-product vb asg (base-prime))))
    (implies (and (r1cs::sparse-vectorp va) (r1cs::sparse-vectorp vb)
                  (symbolp m) (symbolp r)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-bindsp asg m)
                  (r1cs::valuation-bindsp asg r)
                  (equal (lookup-equal r asg) (if (equal da db) 0 1))
                  (equal (lookup-equal m asg) (rec-neq-mult da db)))
             (r1cs::r1cs-constraints-holdp
              (rec-lc-neq-gadget va vb m r (base-prime)) asg (base-prime))))
  :use ((:instance rec-lc-neq-gadget-to-spec (p (base-prime)))
        (:instance prog-field-neq-constraints-when-witness
                   (p (base-prime))
                   (x (r1cs::dot-product va asg (base-prime)))
                   (y (r1cs::dot-product vb asg (base-prime)))
                   (m (lookup-equal m asg))
                   (r (lookup-equal r asg))))
  :enable (rec-neq-mult fieldp primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; U8::to_field: the linear combination sum 2^i b_i of the 8 bit wires.

(defruled rec-u8-dot
  (implies (and (symbol-listp vs)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg vs)
                (bit-listp (lookup-equal-list vs asg))
                (equal (len (lookup-equal-list vs asg)) 8))
           (equal (r1cs::dot-product (pow2sum-vector vs 0) asg (base-prime))
                  (lebits=>nat (lookup-equal-list vs asg))))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat
                   (xs vs) (i 0) (p (base-prime)))
        (:instance rec-lebits=>nat-bound (bs (lookup-equal-list vs asg))))
  :enable primep-of-base-prime)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The gadget.

(define rec-dynamic-record-is-equal-gadget
  ((ox1 symbolp) (oy1 symbolp) (ox2 symbolp) (oy2 symbolp)
   (omx symbolp) (orx symbolp) (omy symbolp) (ory symbolp) (oout symbolp)
   (ra symbolp) (rb symbolp) (rm symbolp) (rr symbolp) (z1 symbolp)
   (nx1 symbolp) (ny1 symbolp) (nx2 symbolp) (ny2 symbolp)
   (nmx symbolp) (nrx symbolp) (nmy symbolp) (nry symbolp) (nout symbolp)
   (z2 symbolp)
   (vas symbol-listp) (vbs symbol-listp) (vm symbolp) (vr symbolp)
   (z3 symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('DynamicRecord::is_equal'); the output is @('z3')."
  (b* ((p (base-prime)))
    (append (crv-group-is-equal-gadget ox1 oy1 ox2 oy2 omx orx omy ory oout p)
            (prog-field-neq-gadget ra rb rm rr p)
            (prog-and-var-eq-gadget oout rr z1 p)
            (crv-group-is-equal-gadget nx1 ny1 nx2 ny2 nmx nrx nmy nry nout p)
            (boolean-and-gadget z1 nout z2)
            (rec-lc-neq-gadget (pow2sum-vector vas 0) (pow2sum-vector vbs 0)
                               vm vr p)
            (prog-and-var-eq-gadget z2 vr z3 p))))

(define rec-dynamic-record-is-not-equal-value ((z3 symbolp) (asg alistp))
  :verify-guards nil
  :short "@('DynamicRecord::is_not_equal'): the linear combination 1 - z3."
  (pfield::sub 1 (lookup-equal z3 asg) (base-prime)))

(define rec-dynamic-record-make (o (ra symbolp) n (vs symbol-listp) (asg alistp))
  :verify-guards nil
  (dynamic-record o (lookup-equal ra asg) n
                  (lebits=>nat (lookup-equal-list vs asg))))

(defmacro rec-dre-hyps (&rest more)
  `(and (symbolp ox1) (symbolp oy1) (symbolp ox2) (symbolp oy2)
        (symbolp omx) (symbolp orx) (symbolp omy) (symbolp ory) (symbolp oout)
        (symbolp ra) (symbolp rb) (symbolp rm) (symbolp rr) (symbolp z1)
        (symbolp nx1) (symbolp ny1) (symbolp nx2) (symbolp ny2)
        (symbolp nmx) (symbolp nrx) (symbolp nmy) (symbolp nry) (symbolp nout)
        (symbolp z2)
        (symbol-listp vas) (symbol-listp vbs) (symbolp vm) (symbolp vr)
        (symbolp z3)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-binds-allp
         asg (list ox1 oy1 ox2 oy2 omx orx omy ory oout ra rb rm rr z1
                   nx1 ny1 nx2 ny2 nmx nrx nmy nry nout z2 vm vr z3))
        (r1cs::valuation-binds-allp asg vas)
        (r1cs::valuation-binds-allp asg vbs)
        (groupp p1) (groupp p2) (groupp q1) (groupp q2)
        (ecurve::edwards-bls12-pointp p1)
        (ecurve::edwards-bls12-pointp p2)
        (ecurve::edwards-bls12-pointp q1)
        (ecurve::edwards-bls12-pointp q2)
        (equal (lookup-equal ox1 asg) (ecurve::point-finite->x p1))
        (equal (lookup-equal oy1 asg) (ecurve::point-finite->y p1))
        (equal (lookup-equal ox2 asg) (ecurve::point-finite->x p2))
        (equal (lookup-equal oy2 asg) (ecurve::point-finite->y p2))
        (equal (lookup-equal nx1 asg) (ecurve::point-finite->x q1))
        (equal (lookup-equal ny1 asg) (ecurve::point-finite->y q1))
        (equal (lookup-equal nx2 asg) (ecurve::point-finite->x q2))
        (equal (lookup-equal ny2 asg) (ecurve::point-finite->y q2))
        (bit-listp (lookup-equal-list vas asg))
        (bit-listp (lookup-equal-list vbs asg))
        (equal (len (lookup-equal-list vas asg)) 8)
        (equal (len (lookup-equal-list vbs asg)) 8)
        ,@more))

(defthm rec-dre-fold
  (implies (and (bitp go) (bitp gn)
                (equal rr (if c1 0 1))
                (equal z1 (pfield::mul go (pfield::sub 1 rr (base-prime))
                                       (base-prime)))
                (equal z2 (bitand z1 gn))
                (equal vr (if c3 0 1))
                (equal z3 (pfield::mul z2 (pfield::sub 1 vr (base-prime))
                                       (base-prime))))
           (and (bitp z1)
                (equal (if (and (equal go 1) c1 (equal gn 1) c3) 1 0) z3)))
  :rule-classes nil
  :hints (("Goal" :cases ((equal go 0)) :in-theory (enable bitp))))

(defruled rec-dynamic-record-equal-iff
  (implies (and (groupp o1) (groupp o2) (groupp n1) (groupp n2)
                (fieldp r1) (fieldp r2)
                (acl2::ubyte8p v1) (acl2::ubyte8p v2))
           (equal (equal (dynamic-record o1 r1 n1 v1)
                         (dynamic-record o2 r2 n2 v2))
                  (and (equal o1 o2) (equal r1 r2)
                       (equal n1 n2) (equal v1 v2))))
  :use ((:instance dynamic-record->owner-of-dynamic-record
                   (owner o1) (root r1) (nonce n1) (version v1))
        (:instance dynamic-record->owner-of-dynamic-record
                   (owner o2) (root r2) (nonce n2) (version v2))
        (:instance dynamic-record->root-of-dynamic-record
                   (owner o1) (root r1) (nonce n1) (version v1))
        (:instance dynamic-record->root-of-dynamic-record
                   (owner o2) (root r2) (nonce n2) (version v2))
        (:instance dynamic-record->nonce-of-dynamic-record
                   (owner o1) (root r1) (nonce n1) (version v1))
        (:instance dynamic-record->nonce-of-dynamic-record
                   (owner o2) (root r2) (nonce n2) (version v2))
        (:instance dynamic-record->version-of-dynamic-record
                   (owner o1) (root r1) (nonce n1) (version v1))
        (:instance dynamic-record->version-of-dynamic-record
                   (owner o2) (root r2) (nonce n2) (version v2)))
  :disable (dynamic-record->owner-of-dynamic-record
            dynamic-record->root-of-dynamic-record
            dynamic-record->nonce-of-dynamic-record
            dynamic-record->version-of-dynamic-record))

(defruled rec-ubyte8p-of-lebits=>nat
  (implies (and (bit-listp bs) (equal (len bs) 8))
           (acl2::ubyte8p (lebits=>nat bs)))
  :enable acl2::ubyte8p
  :use (:instance rec-unsigned-byte-p-of-lebits=>nat (n 8)))

(defruled rec-dre-gadget-split
  (implies (equal p (base-prime))
  (equal (r1cs::r1cs-constraints-holdp
          (rec-dynamic-record-is-equal-gadget
           ox1 oy1 ox2 oy2 omx orx omy ory oout ra rb rm rr z1
           nx1 ny1 nx2 ny2 nmx nrx nmy nry nout z2 vas vbs vm vr z3)
          asg p)
         (and (r1cs::r1cs-constraints-holdp
               (crv-group-is-equal-gadget ox1 oy1 ox2 oy2 omx orx omy ory oout
                                          p)
               asg p)
              (r1cs::r1cs-constraints-holdp
               (prog-field-neq-gadget ra rb rm rr p) asg p)
              (r1cs::r1cs-constraints-holdp
               (prog-and-var-eq-gadget oout rr z1 p) asg p)
              (r1cs::r1cs-constraints-holdp
               (crv-group-is-equal-gadget nx1 ny1 nx2 ny2 nmx nrx nmy nry nout
                                          p)
               asg p)
              (r1cs::r1cs-constraints-holdp
               (boolean-and-gadget z1 nout z2) asg p)
              (r1cs::r1cs-constraints-holdp
               (rec-lc-neq-gadget (pow2sum-vector vas 0) (pow2sum-vector vbs 0)
                                  vm vr p)
               asg p)
              (r1cs::r1cs-constraints-holdp
               (prog-and-var-eq-gadget z2 vr z3 p) asg p))))
  :in-theory '(rec-dynamic-record-is-equal-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled rec-dre-wire-sound
  (implies (rec-dre-hyps
            (r1cs::r1cs-constraints-holdp
             (rec-dynamic-record-is-equal-gadget
              ox1 oy1 ox2 oy2 omx orx omy ory oout ra rb rm rr z1
              nx1 ny1 nx2 ny2 nmx nrx nmy nry nout z2 vas vbs vm vr z3)
             asg (base-prime)))
           (equal (lookup-equal z3 asg)
                  (if (and (equal p1 p2)
                           (equal (lookup-equal ra asg) (lookup-equal rb asg))
                           (equal q1 q2)
                           (equal (lebits=>nat (lookup-equal-list vas asg))
                                  (lebits=>nat (lookup-equal-list vbs asg))))
                      1 0)))
  :do-not-induct t
  :in-theory (e/d (rec-dre-gadget-split
                   group-is-equal-funspec
                   r1cs::valuation-binds-allp
                   r1cs::fep-of-lookup-equal primep-of-base-prime)
                  (rec-dynamic-record-is-equal-gadget
                   crv-group-is-equal-gadget prog-field-neq-gadget
                   prog-and-var-eq-gadget boolean-and-gadget rec-lc-neq-gadget
                   bitp))
  :use ((:instance rec-u8-dot (vs vas))
        (:instance rec-u8-dot (vs vbs))
        (:instance crv-group-is-equal-wire-sound
                   (x1 ox1) (y1 oy1) (x2 ox2) (y2 oy2)
                   (mx omx) (rx orx) (my omy) (ry ory) (out oout)
                   (p (base-prime)))
        (:instance crv-group-is-equal-wire-sound
                   (x1 nx1) (y1 ny1) (x2 nx2) (y2 ny2)
                   (mx nmx) (rx nrx) (my nmy) (ry nry) (out nout)
                   (p1 q1) (p2 q2) (p (base-prime)))
        (:instance rec-neq-gadget-bit (x ra) (y rb) (m rm) (r rr))
        (:instance rec-lc-neq-gadget-bit
                   (va (pow2sum-vector vas 0)) (vb (pow2sum-vector vbs 0))
                   (m vm) (r vr))
        (:instance prog-and-var-eq-gadget-to-mul
                   (z oout) (r rr) (w z1) (p (base-prime)))
        (:instance prog-and-var-eq-gadget-to-mul
                   (z z2) (r vr) (w z3) (p (base-prime)))
        (:instance boolean-and-gadget-to-bitand
                   (x z1) (y nout) (z z2) (p (base-prime)))
        (:instance rec-dre-fold
                   (go (lookup-equal oout asg)) (gn (lookup-equal nout asg))
                   (rr (lookup-equal rr asg))
                   (c1 (equal (lookup-equal ra asg) (lookup-equal rb asg)))
                   (z1 (lookup-equal z1 asg)) (z2 (lookup-equal z2 asg))
                   (vr (lookup-equal vr asg))
                   (c3 (equal (lebits=>nat (lookup-equal-list vas asg))
                              (lebits=>nat (lookup-equal-list vbs asg))))
                   (z3 (lookup-equal z3 asg)))))

(defruled rec-dynamic-record-is-equal-sound
  (b* ((dra (rec-dynamic-record-make p1 ra q1 vas asg))
       (drb (rec-dynamic-record-make p2 rb q2 vbs asg)))
    (implies (rec-dre-hyps
              (r1cs::r1cs-constraints-holdp
               (rec-dynamic-record-is-equal-gadget
                ox1 oy1 ox2 oy2 omx orx omy ory oout ra rb rm rr z1
                nx1 ny1 nx2 ny2 nmx nrx nmy nry nout z2 vas vbs vm vr z3)
               asg (base-prime)))
             (and (equal (lookup-equal z3 asg)
                         (dynamic-record-is-equal dra drb))
                  (equal (rec-dynamic-record-is-not-equal-value z3 asg)
                         (dynamic-record-is-not-equal dra drb)))))
  :do-not-induct t
  :in-theory (e/d (rec-dynamic-record-is-not-equal-value
                   rec-dynamic-record-make
                   dynamic-record-is-equal dynamic-record-is-not-equal
                   values-bool-to-bit values-b-not
                   rec-dynamic-record-equal-iff
                   r1cs::valuation-binds-allp
                   fieldp r1cs::fep-of-lookup-equal primep-of-base-prime)
                  (rec-dynamic-record-is-equal-gadget))
  :use (rec-dre-wire-sound
        (:instance rec-ubyte8p-of-lebits=>nat (bs (lookup-equal-list vas asg)))
        (:instance rec-ubyte8p-of-lebits=>nat (bs (lookup-equal-list vbs asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Completeness: snarkVM's witnesses, named so the hypotheses stay if-free.

(define rec-neq-bit (x y)
  (if (equal x y) 0 1))

(define rec-grp-mult (x y)
  :verify-guards nil
  (if (equal x y)
      0
    (pfield::inv (pfield::sub x y (base-prime)) (base-prime))))

(define rec-and-eq-value (z x y)
  (if (equal x y) z 0))

(defrule rec-bitp-of-rec-and-eq-value
  (implies (bitp z) (bitp (rec-and-eq-value z x y)))
  :enable rec-and-eq-value)

(defruled rec-grp-complete
  (implies (eq-wire-hyps
            (equal (lookup-equal rx asg)
                   (rec-neq-bit (lookup-equal x1 asg) (lookup-equal x2 asg)))
            (equal (lookup-equal mx asg)
                   (rec-grp-mult (lookup-equal x1 asg) (lookup-equal x2 asg)))
            (equal (lookup-equal ry asg)
                   (rec-neq-bit (lookup-equal y1 asg) (lookup-equal y2 asg)))
            (equal (lookup-equal my asg)
                   (rec-grp-mult (lookup-equal y1 asg) (lookup-equal y2 asg)))
            (equal (lookup-equal out asg) (group-is-equal-funspec p1 p2)))
           (r1cs::r1cs-constraints-holdp
            (crv-group-is-equal-gadget x1 y1 x2 y2 mx rx my ry out p)
            asg p))
  :use crv-group-is-equal-gadget-complete
  :enable (rec-neq-bit rec-grp-mult))

(defruled rec-and-var-complete
  (implies (and (symbolp z) (symbolp r) (symbolp w)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg w)
                (equal (lookup-equal r asg) (rec-neq-bit x y))
                (equal (lookup-equal w asg)
                       (rec-and-eq-value (lookup-equal z asg) x y)))
           (r1cs::r1cs-constraints-holdp
            (prog-and-var-eq-gadget z r w (base-prime)) asg (base-prime)))
  :use (:instance prog-and-var-eq-gadget-to-mul (p (base-prime)))
  :enable (rec-neq-bit rec-and-eq-value
           r1cs::fep-of-lookup-equal primep-of-base-prime))

(defruled rec-root-complete
  (implies (and (symbolp x) (symbolp y) (symbolp m) (symbolp r)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (equal (lookup-equal r asg)
                       (rec-neq-bit (lookup-equal x asg) (lookup-equal y asg)))
                (equal (lookup-equal m asg)
                       (rec-neq-mult (lookup-equal x asg) (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (prog-field-neq-gadget x y m r (base-prime)) asg (base-prime)))
  :use rec-neq-gadget-complete
  :enable rec-neq-bit)

(defruled rec-u8-neq-complete
  (b* ((a (lebits=>nat (lookup-equal-list vas asg)))
       (b (lebits=>nat (lookup-equal-list vbs asg))))
    (implies (and (symbol-listp vas) (symbol-listp vbs)
                  (symbolp m) (symbolp r)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg vas)
                  (r1cs::valuation-binds-allp asg vbs)
                  (r1cs::valuation-bindsp asg m)
                  (r1cs::valuation-bindsp asg r)
                  (bit-listp (lookup-equal-list vas asg))
                  (bit-listp (lookup-equal-list vbs asg))
                  (equal (len (lookup-equal-list vas asg)) 8)
                  (equal (len (lookup-equal-list vbs asg)) 8)
                  (equal (lookup-equal r asg) (rec-neq-bit a b))
                  (equal (lookup-equal m asg) (rec-neq-mult a b)))
             (r1cs::r1cs-constraints-holdp
              (rec-lc-neq-gadget (pow2sum-vector vas 0) (pow2sum-vector vbs 0)
                                 m r (base-prime))
              asg (base-prime))))
  :use ((:instance rec-u8-dot (vs vas))
        (:instance rec-u8-dot (vs vbs))
        (:instance rec-lc-neq-gadget-complete
                   (va (pow2sum-vector vas 0)) (vb (pow2sum-vector vbs 0))))
  :enable rec-neq-bit)

(defruled rec-band-complete
  (implies (and (symbolp x) (symbolp y) (symbolp z)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal x asg))
                (bitp (lookup-equal y asg))
                (equal (lookup-equal z asg)
                       (bitand (lookup-equal x asg) (lookup-equal y asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-and-gadget x y z) asg (base-prime)))
  :use (:instance boolean-and-gadget-to-bitand (p (base-prime)))
  :enable primep-of-base-prime)

;; snarkVM's witness assignment for the gadget.
(defmacro rec-dre-witness-hyps ()
  '(rec-dre-hyps
    (equal (lookup-equal orx asg) (rec-neq-bit (lookup-equal ox1 asg) (lookup-equal ox2 asg)))
    (equal (lookup-equal omx asg) (rec-grp-mult (lookup-equal ox1 asg) (lookup-equal ox2 asg)))
    (equal (lookup-equal ory asg) (rec-neq-bit (lookup-equal oy1 asg) (lookup-equal oy2 asg)))
    (equal (lookup-equal omy asg) (rec-grp-mult (lookup-equal oy1 asg) (lookup-equal oy2 asg)))
    (equal (lookup-equal oout asg) (group-is-equal-funspec p1 p2))
    (equal (lookup-equal rr asg) (rec-neq-bit (lookup-equal ra asg) (lookup-equal rb asg)))
    (equal (lookup-equal rm asg) (rec-neq-mult (lookup-equal ra asg) (lookup-equal rb asg)))
    (equal (lookup-equal z1 asg) (rec-and-eq-value (lookup-equal oout asg) (lookup-equal ra asg) (lookup-equal rb asg)))
    (equal (lookup-equal nrx asg) (rec-neq-bit (lookup-equal nx1 asg) (lookup-equal nx2 asg)))
    (equal (lookup-equal nmx asg) (rec-grp-mult (lookup-equal nx1 asg) (lookup-equal nx2 asg)))
    (equal (lookup-equal nry asg) (rec-neq-bit (lookup-equal ny1 asg) (lookup-equal ny2 asg)))
    (equal (lookup-equal nmy asg) (rec-grp-mult (lookup-equal ny1 asg) (lookup-equal ny2 asg)))
    (equal (lookup-equal nout asg) (group-is-equal-funspec q1 q2))
    (equal (lookup-equal z2 asg) (bitand (lookup-equal z1 asg) (lookup-equal nout asg)))
    (equal (lookup-equal vr asg) (rec-neq-bit (lebits=>nat (lookup-equal-list vas asg)) (lebits=>nat (lookup-equal-list vbs asg))))
    (equal (lookup-equal vm asg) (rec-neq-mult (lebits=>nat (lookup-equal-list vas asg)) (lebits=>nat (lookup-equal-list vbs asg))))
    (equal (lookup-equal z3 asg) (rec-and-eq-value (lookup-equal z2 asg) (lebits=>nat (lookup-equal-list vas asg)) (lebits=>nat (lookup-equal-list vbs asg))))))

(defmacro rec-dre-part (name part &rest use)
  `(defruled ,name
     (implies (rec-dre-witness-hyps)
              (r1cs::r1cs-constraints-holdp ,part asg (base-prime)))
     :do-not-induct t
     :in-theory (e/d (r1cs::valuation-binds-allp)
                     (rec-neq-bit rec-grp-mult rec-and-eq-value rec-neq-mult
                      group-is-equal-funspec
                      crv-group-is-equal-gadget prog-field-neq-gadget
                      prog-and-var-eq-gadget boolean-and-gadget
                      rec-lc-neq-gadget))
     :use ,(car use)))

(rec-dre-part rec-dre-part-owner
  (crv-group-is-equal-gadget ox1 oy1 ox2 oy2 omx orx omy ory oout (base-prime))
  ((:instance rec-grp-complete
              (x1 ox1) (y1 oy1) (x2 ox2) (y2 oy2)
              (mx omx) (rx orx) (my omy) (ry ory) (out oout)
              (p (base-prime)))))

(rec-dre-part rec-dre-part-root
  (prog-field-neq-gadget ra rb rm rr (base-prime))
  ((:instance rec-root-complete (x ra) (y rb) (m rm) (r rr))))

(rec-dre-part rec-dre-part-and1
  (prog-and-var-eq-gadget oout rr z1 (base-prime))
  ((:instance rec-and-var-complete
              (z oout) (r rr) (w z1) (x (lookup-equal ra asg)) (y (lookup-equal rb asg)))))

(rec-dre-part rec-dre-part-nonce
  (crv-group-is-equal-gadget nx1 ny1 nx2 ny2 nmx nrx nmy nry nout (base-prime))
  ((:instance rec-grp-complete
              (x1 nx1) (y1 ny1) (x2 nx2) (y2 ny2)
              (mx nmx) (rx nrx) (my nmy) (ry nry) (out nout)
              (p1 q1) (p2 q2) (p (base-prime)))))

(rec-dre-part rec-dre-part-and2
  (boolean-and-gadget z1 nout z2)
  ((:instance rec-band-complete (x z1) (y nout) (z z2))))

(rec-dre-part rec-dre-part-version
  (rec-lc-neq-gadget (pow2sum-vector vas 0) (pow2sum-vector vbs 0)
                     vm vr (base-prime))
  ((:instance rec-u8-neq-complete (m vm) (r vr))))

(rec-dre-part rec-dre-part-and3
  (prog-and-var-eq-gadget z2 vr z3 (base-prime))
  ((:instance rec-and-var-complete
              (z z2) (r vr) (w z3) (x (lebits=>nat (lookup-equal-list vas asg))) (y (lebits=>nat (lookup-equal-list vbs asg))))))

(defruled rec-dynamic-record-is-equal-complete
  (implies (rec-dre-witness-hyps)
           (r1cs::r1cs-constraints-holdp
            (rec-dynamic-record-is-equal-gadget
               ox1 oy1 ox2 oy2 omx orx omy ory oout ra rb rm rr z1
               nx1 ny1 nx2 ny2 nmx nrx nmy nry nout z2 vas vbs vm vr z3)
            asg (base-prime)))
  :use (rec-dre-part-owner rec-dre-part-root rec-dre-part-and1
        rec-dre-part-nonce rec-dre-part-and2 rec-dre-part-version
        rec-dre-part-and3
        (:instance rec-dre-gadget-split (p (base-prime))))
  :in-theory nil)
