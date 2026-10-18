; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Record<Plaintext> write_bits_le / write_bits_be / to_fields /
; num_randomizers / find (snarkVM circuit/program/src/data/record), over the
; record wires of rec-record.lisp.
;
; write_bits_*: owner.is_private() is a constant; the owner address and the
;   nonce write the bits of their x-coordinate (Field::write_bits_*); each
;   entry writes its constant name bits and Entry::write_bits_*; the data
;   length bits are constants; is_hiding is !version.is_zero(), i.e.
;   !(to_field(version).is_equal(0)) = the is_not_equal bit of the version's
;   linear combination against 0; the version writes its bit wires.
;   Constraint order: owner bits, entries, is_hiding, nonce bits.
; to_fields: write_bits_le, a constant 1, packed (linear, no constraints).
; num_randomizers, find: synthesis-time, no constraints.

(in-package "ALEOVM")

(include-book "rec-record")
(include-book "rec-dynamic-record-eq")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Bridges between the record funspecs and the values-* functions.

(defruled rec-crypto-entry-bits-le
  (implies (entryp e)
           (equal (crypto-entry-bits-le e) (entry-to-bits-le e)))
  :enable (crypto-entry-bits-le entry-to-bits-le
           entry-write-bits-le-with-visibility-as-mode
           values-entry-visibility-bits values-entry-plaintext
           crypto-entry-visibility-bits entry-kind))

(defruled rec-crypto-entry-bits-be
  (implies (entryp e)
           (equal (crypto-entry-bits-be e) (entry-to-bits-be e)))
  :enable (crypto-entry-bits-be entry-to-bits-be
           values-entry-visibility-bits values-entry-plaintext
           crypto-entry-visibility-bits entry-kind))

(defruled rec-crypto-entry-num-randomizers
  (equal (crypto-entry-num-randomizers e) (entry-num-randomizers e))
  :enable (crypto-entry-num-randomizers entry-num-randomizers))

(defruled rec-crypto-pack-bits
  (equal (crypto-pack-bits bits) (values-pack-bits bits))
  :induct (crypto-pack-bits bits)
  :enable (crypto-pack-bits values-pack-bits crypto-lebits->field))

(defruled rec-crypto-group-bits
  (implies (and (natp x) (groupp (ecurve::point-finite x y)))
           (and (equal (crypto-group-bits-le (ecurve::point-finite x y))
                       (crypto-field-bits-le x))
                (equal (crypto-group-bits-be (ecurve::point-finite x y))
                       (crypto-field-bits-be x))))
  :enable (crypto-group-bits-le crypto-group-bits-be crypto-group-x
           ecurve::edwards-bls12-point->u groupp
           curve-edwards-bls12-pointp-when-groupp))

(defruled rec-dab-fix-bits
  (implies (bit-listp bs) (equal (acl2::dab-digit-list-fix 2 bs) bs))
  :induct (len bs)
  :enable (acl2::dab-digit-list-fix acl2::dab-digit-fix acl2::dab-digitp))

(defruled rec-nat=>lendian-of-lebits=>nat
  (implies (bit-listp bs)
           (equal (acl2::nat=>lendian 2 (len bs) (lebits=>nat bs))
                  bs))
  :use (:instance acl2::nat=>lendian-of-lendian=>nat
                  (acl2::base 2) (acl2::digits bs))
  :enable (lebits=>nat rec-dab-fix-bits)
  :disable acl2::nat=>lendian-of-lendian=>nat)

(defruled rec-u8-bits
  (implies (and (bit-listp bs) (equal (len bs) 8))
           (and (equal (crypto-nat->lebits 8 (acl2::ubyte8-fix (lebits=>nat bs)))
                       bs)
                (equal (crypto-nat->bebits 8 (acl2::ubyte8-fix (lebits=>nat bs)))
                       (rev bs))))
  :use ((:instance rec-unsigned-byte-p-of-lebits=>nat (n 8))
        (:instance rec-lebits=>nat-bound)
        (:instance rec-nat=>lendian-of-lebits=>nat))
  :enable (crypto-nat->lebits crypto-nat->bebits
           acl2::ubyte8-fix acl2::ubyte8p
           acl2::nat=>bebits acl2::nat=>bendian acl2::nat=>lebits
           acl2::nat=>lebits-of-lebits=>nat acl2::bit-list-fix))

(defruled rec-terms-val-of-symbols
  (implies (symbol-listp xs)
           (equal (ptx-terms-val xs asg) (lookup-equal-list xs asg)))
  :induct (len xs)
  :enable (ptx-terms-val ptx-term-val lookup-equal-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The data part.

(define rec-record-data-typed (data asg)
  (if (atom data)
      t
    (and (ptx-typed (cdr (cdar data)) asg)
         (rec-record-data-typed (cdr data) asg))))

(define rec-record-data-bits-gadget (data bigp)
  (if (atom data)
      nil
    (append (ptx-entry-bits-gadget (cdar data) (and bigp t))
            (rec-record-data-bits-gadget (cdr data) bigp))))

(define rec-record-data-bits-out (data bigp)
  (if (atom data)
      nil
    (append (if bigp
                (crypto-identifier-bits-be (caar data))
              (crypto-identifier-bits-le (caar data)))
            (ptx-entry-bits-out (cdar data) (and bigp t))
            (rec-record-data-bits-out (cdr data) bigp))))

(defruled rec-record-data-bits-sound
  (implies (and (primep p)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-record-data-bits-gadget data bigp) asg p))
           (equal (ptx-terms-val (rec-record-data-bits-out data bigp) asg)
                  (if bigp
                      (crypto-record-data-bits-be (rec-record-data-eval data asg))
                    (crypto-record-data-bits-le (rec-record-data-eval data asg)))))
  :induct (rec-record-datawp data)
  :enable (rec-record-datawp rec-record-data-typed rec-record-data-eval
           rec-record-data-bits-gadget rec-record-data-bits-out
           crypto-record-data-bits-le crypto-record-data-bits-be
           rec-crypto-entry-bits-le rec-crypto-entry-bits-be
           r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use ((:instance ptx-entry-write-bits-le-sound (ew (cdar data)))
                 (:instance ptx-entry-write-bits-be-sound (ew (cdar data)))))))

(define rec-record-data-bits-witnessp (data bigp asg p)
  (if (atom data)
      t
    (and (ptx-bits-witnessp (cdr (cdar data)) (and bigp t) asg p)
         (rec-record-data-bits-witnessp (cdr data) bigp asg p))))

(defruled rec-record-data-bits-complete
  (implies (and (primep p)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (rec-record-data-bits-witnessp data bigp asg p))
           (r1cs::r1cs-constraints-holdp
            (rec-record-data-bits-gadget data bigp) asg p))
  :induct (rec-record-datawp data)
  :enable (rec-record-datawp rec-record-data-typed rec-record-data-bits-witnessp
           rec-record-data-bits-gadget r1cs::r1cs-constraints-holdp-of-append)
  :hints (("Subgoal *1/2"
           :use (:instance ptx-entry-write-bits-complete (ew (cdar data))
                           (bigp (and bigp t))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; write_bits_le / write_bits_be.

(define rec-record-bits-gadget (og data ng vbits obits ors nbits nrs u vm vr
                                   bigp)
  (append (rec-fields-write-bits-gadget (list (nth 0 og)) (list obits)
                                        (list ors) u)
          (rec-record-data-bits-gadget data bigp)
          (rec-lc-neq-gadget (pow2sum-vector vbits 0) nil vm vr (base-prime))
          (rec-fields-write-bits-gadget (list (nth 0 ng)) (list nbits)
                                        (list nrs) u)))

(define rec-record-bits-out (pubp data vbits obits nbits vr bigp)
  :short "The output bit terms, or @(':error') where snarkVM halts."
  (b* ((dterms (rec-record-data-bits-out data bigp))
       (n (len dterms))
       ((when (>= n (expt 2 31))) :error)
       (priv (if pubp 0 1)))
    (if bigp
        (append (list priv) (rev obits) (list vr)
                (nthcdr 1 (crypto-nat->bebits 32 n))
                dterms (rev nbits) (rev vbits))
      (append (list priv) obits
              (take 31 (crypto-nat->lebits 32 n))
              (list vr) dterms nbits vbits))))

(defmacro rec-record-bits-hyps (&rest more)
  `(and (rec-record-new-hyps)
        (groupp (rec-point-of og asg))
        (groupp (rec-point-of ng asg))
        (bit-listp (lookup-equal-list vbits asg))
        (rec-record-data-typed data asg)
        (symbolp u) (symbolp vm) (symbolp vr)
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)
        (r1cs::valuation-bindsp asg vm)
        (r1cs::valuation-bindsp asg vr)
        (rec-bits-shapep (list (nth 0 og)) (list obits) (list ors))
        (rec-bits-shapep (list (nth 0 ng)) (list nbits) (list nrs))
        (rec-bits-boundp asg (list (nth 0 og)) (list obits) (list ors))
        (rec-bits-boundp asg (list (nth 0 ng)) (list nbits) (list nrs))
        ,@more))

(defruled rec-dot-product-of-nil
  (equal (r1cs::dot-product nil asg p) 0)
  :enable r1cs::dot-product)

(defruled rec-record-hiding-bit
  (implies (and (symbol-listp vbits) (equal (len vbits) 8)
                (symbolp vm) (symbolp vr)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg vbits)
                (r1cs::valuation-bindsp asg vm)
                (r1cs::valuation-bindsp asg vr)
                (bit-listp (lookup-equal-list vbits asg))
                (r1cs::r1cs-constraints-holdp
                 (rec-lc-neq-gadget (pow2sum-vector vbits 0) nil vm vr (base-prime))
                 asg (base-prime)))
           (equal (lookup-equal vr asg)
                  (crypto-record-is-hiding
                   (lebits=>nat (lookup-equal-list vbits asg)))))
  :use ((:instance rec-lc-neq-gadget-bit
                   (va (pow2sum-vector vbits 0)) (vb nil) (m vm) (r vr))
        (:instance rec-u8-dot (vs vbits))
        (:instance rec-ubyte8p-of-lebits=>nat
                   (bs (lookup-equal-list vbits asg))))
  :do-not-induct t
  :enable (crypto-record-is-hiding acl2::ubyte8-fix r1cs::valuation-binds-allp
           r1cs::fep-of-lookup-equal primep-of-base-prime
           rec-dot-product-of-nil)
  :disable (rec-lc-neq-gadget bitp))

(defruled rec-record-field-bits
  (b* ((g (rec-point-of og asg)))
    (implies (and (symbol-listp og) (equal (len og) 14)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg og)
                  (groupp g)
                  (symbolp u) (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (rec-bits-shapep (list (nth 0 og)) (list obits) (list ors))
                  (rec-bits-boundp asg (list (nth 0 og)) (list obits) (list ors))
                  (r1cs::r1cs-constraints-holdp
                   (rec-fields-write-bits-gadget (list (nth 0 og)) (list obits)
                                                 (list ors) u)
                   asg (base-prime)))
             (and (symbol-listp obits)
                  (equal (lookup-equal-list obits asg) (crypto-group-bits-le g))
                  (equal (lookup-equal-list (rev obits) asg)
                         (crypto-group-bits-be g)))))
  :do-not-induct t
  :use ((:instance rec-fields-write-bits-sound
                   (xs (list (nth 0 og))) (bitss (list obits)) (rss (list ors)))
        (:instance rec-crypto-group-bits
                   (x (lookup-equal (nth 0 og) asg))
                   (y (lookup-equal (nth 1 og) asg)))
        (:instance rec-valuation-bindsp-of-nth (g og) (i 0)))
  :enable (rec-point-of rec-concat-le rec-concat-be rec-bits-shapep
           crypto-field-list-bits-le crypto-field-list-bits-be
           lookup-equal-list r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type))

(defruled rec-symbol-listp-of-rev
  (implies (symbol-listp xs) (symbol-listp (rev xs)))
  :enable rev)

(defruled rec-lookup-equal-list-of-append
  (equal (lookup-equal-list (append xs ys) asg)
         (append (lookup-equal-list xs asg) (lookup-equal-list ys asg)))
  :enable lookup-equal-list)

(defruled rec-record-bits-out-val
  (b* ((out (rec-record-bits-out pubp data vbits obits nbits vr bigp))
       (dv (ptx-terms-val (rec-record-data-bits-out data bigp) asg))
       (n (len dv))
       (priv (if pubp 0 1)))
    (implies (and (symbol-listp obits) (symbol-listp nbits)
                  (symbol-listp vbits) (symbolp vr))
             (and (iff (equal out :error) (>= n (expt 2 31)))
                  (implies (not (equal out :error))
                           (equal (ptx-terms-val out asg)
                                  (if bigp
                                      (append (list priv)
                                              (lookup-equal-list (rev obits) asg)
                                              (list (lookup-equal vr asg))
                                              (nthcdr 1 (crypto-nat->bebits 32 n))
                                              dv
                                              (lookup-equal-list (rev nbits) asg)
                                              (lookup-equal-list (rev vbits) asg))
                                    (append (list priv)
                                            (lookup-equal-list obits asg)
                                            (take 31 (crypto-nat->lebits 32 n))
                                            (list (lookup-equal vr asg))
                                            dv
                                            (lookup-equal-list nbits asg)
                                            (lookup-equal-list vbits asg))))))))
  :do-not-induct t
  :enable (rec-record-bits-out rec-terms-val-of-symbols ptx-term-val
           rec-symbol-listp-of-rev rec-lookup-equal-list-of-append))

(defruled rec-record-write-bits-sound
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (out (rec-record-bits-out pubp data vbits obits nbits vr bigp))
       (spec (if bigp (crypto-record-write-bits-be r) (crypto-record-write-bits-le r))))
    (implies (rec-record-bits-hyps
              (r1cs::r1cs-constraints-holdp
               (rec-record-bits-gadget og data ng vbits obits ors nbits nrs u
                                       vm vr bigp)
               asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-terms-val out asg) spec)))))
  :do-not-induct t
  :use ((:instance rec-record-field-bits)
        (:instance rec-record-field-bits (og ng) (obits nbits) (ors nrs))
        (:instance rec-record-hiding-bit)
        (:instance rec-record-data-bits-sound (p (base-prime)))
        (:instance rec-u8-bits (bs (lookup-equal-list vbits asg)))
        (:instance rec-record-bits-out-val))
  :in-theory (e/d (rec-record-bits-gadget rec-record-of-wires
                   crypto-record-write-bits-le crypto-record-write-bits-be
                   crypto-record-layout-bits-le crypto-record-layout-bits-be
                   crypto-owner-address crypto-owner-privatep
                   lookup-equal-list-of-rev
                   r1cs::r1cs-constraints-holdp-of-append spec-error
                   primep-of-base-prime)
                  (rec-record-bits-out ptx-terms-val rec-record-data-bits-out
                   rec-lc-neq-gadget rec-fields-write-bits-gadget
                   rec-record-data-bits-gadget)))

(defruled rec-record-write-bits-complete
  :short "The constraints hold iff each component holds: the owner and nonce
          bits by rec-fields-write-bits-complete, the entries by
          rec-record-data-bits-complete, and is_hiding by
          rec-lc-neq-gadget-complete."
  (equal (r1cs::r1cs-constraints-holdp
          (rec-record-bits-gadget og data ng vbits obits ors nbits nrs u vm vr
                                  bigp)
          asg (base-prime))
         (and (r1cs::r1cs-constraints-holdp
               (rec-fields-write-bits-gadget (list (nth 0 og)) (list obits)
                                             (list ors) u)
               asg (base-prime))
              (r1cs::r1cs-constraints-holdp
               (rec-record-data-bits-gadget data bigp) asg (base-prime))
              (r1cs::r1cs-constraints-holdp
               (rec-lc-neq-gadget (pow2sum-vector vbits 0) nil vm vr (base-prime))
               asg (base-prime))
              (r1cs::r1cs-constraints-holdp
               (rec-fields-write-bits-gadget (list (nth 0 ng)) (list nbits)
                                             (list nrs) u)
               asg (base-prime))))
  :enable (rec-record-bits-gadget r1cs::r1cs-constraints-holdp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; to_fields: the constraints of write_bits_le.

(define rec-record-to-fields-out (pubp data vbits obits nbits vr)
  (b* ((bits (rec-record-bits-out pubp data vbits obits nbits vr nil)))
    (if (equal bits :error)
        :error
      (ptx-to-fields-out (append bits (list 1))))))

(defruled rec-record-to-fields-sound
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (out (rec-record-to-fields-out pubp data vbits obits nbits vr))
       (spec (crypto-record-to-fields r)))
    (implies (rec-record-bits-hyps
              (r1cs::r1cs-constraints-holdp
               (rec-record-bits-gadget og data ng vbits obits ors nbits nrs u
                                       vm vr nil)
               asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :do-not-induct t
  :use ((:instance rec-record-write-bits-sound (bigp nil))
        (:instance ptx-to-fields-out-correct
                   (terms (append (rec-record-bits-out pubp data vbits obits
                                                       nbits vr nil)
                                  (list 1))))
        (:instance bit-listp-of-crypto-record-write-bits-le
                   (r (rec-record-of-wires pubp og data ng vbits asg))))
  :enable (rec-record-to-fields-out crypto-record-to-fields
           crypto-bits-to-fields-checked crypto-bits-to-fields-with-terminus
           rec-crypto-pack-bits values-pack-bits-bounded spec-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; num_randomizers: synthesis-time (u16 checked additions, then the size
; bound); no constraints.

(define rec-record-entries-num-randomizers (data acc)
  (b* (((when (atom data)) (nfix acc))
       (k (ptx-entry-num-randomizers (cdar data)))
       ((when (equal k :error)) :error)
       (acc (+ (nfix acc) (nfix k)))
       ((when (>= acc 65536)) :error))
    (rec-record-entries-num-randomizers (cdr data) acc)))

(define rec-record-num-randomizers (pubp data)
  (b* ((n (rec-record-entries-num-randomizers data (if pubp 0 1)))
       ((when (equal n :error)) :error)
       ((when (> n (crypto-max-data-size-in-fields))) :error))
    n))

(defruled rec-entry-num-randomizers-val
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew nil) asg p))
           (equal (ptx-entry-num-randomizers ew)
                  (b* ((spec (crypto-entry-num-randomizers (ptx-eval ew asg))))
                    (if (reserrp spec) :error spec))))
  :use ptx-entry-num-randomizers-sound
  :enable rec-crypto-entry-num-randomizers)

(defruled rec-record-entries-num-randomizers-val
  (implies (and (primep p)
                (natp acc)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-record-data-bits-gadget data nil) asg p))
           (equal (rec-record-entries-num-randomizers data acc)
                  (b* ((spec (crypto-record-entries-num-randomizers
                              (rec-record-data-eval data asg) acc)))
                    (if (reserrp spec) :error spec))))
  :induct (rec-record-entries-num-randomizers data acc)
  :in-theory (e/d (rec-record-entries-num-randomizers
                   crypto-record-entries-num-randomizers
                   rec-record-datawp rec-record-data-typed rec-record-data-eval
                   rec-record-data-bits-gadget rec-entry-num-randomizers-val
                   r1cs::r1cs-constraints-holdp-of-append spec-error)
                  (ptx-entry-num-randomizers crypto-entry-num-randomizers)))

(defruled rec-record-entries-num-randomizers-sound
  (implies (and (primep p)
                (natp acc)
                (rec-record-datawp data)
                (rec-record-data-typed data asg)
                (r1cs::r1cs-constraints-holdp
                 (rec-record-data-bits-gadget data nil) asg p))
           (b* ((out (rec-record-entries-num-randomizers data acc))
                (spec (crypto-record-entries-num-randomizers
                       (rec-record-data-eval data asg) acc)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use rec-record-entries-num-randomizers-val
  :in-theory (enable reserrp))

(defruled rec-record-num-randomizers-sound
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (out (rec-record-num-randomizers pubp data))
       (spec (crypto-record-num-randomizers r)))
    (implies (and (rec-record-datawp data)
                  (rec-record-data-typed data asg)
                  (r1cs::r1cs-constraints-holdp
                   (rec-record-data-bits-gadget data nil) asg (base-prime)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :do-not-induct t
  :use (:instance rec-record-entries-num-randomizers-sound
                  (p (base-prime)) (acc (if pubp 0 1)))
  :enable (rec-record-num-randomizers crypto-record-num-randomizers
           rec-record-of-wires crypto-owner-privatep spec-error
           primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; find: the path ["owner"] gives Owner::to_entry (output :owner, the owner's
; wires); otherwise IndexMap::get on the constant names (Identifier equality
; is on the field) and Entry::find on the rest.  No constraints.

(define rec-record-data-lookup (name data)
  (cond ((atom data) :error)
        ((equal (identifier->field (caar data)) (identifier->field name))
         (cdar data))
        (t (rec-record-data-lookup name (cdr data)))))

(define rec-record-find (data path)
  (b* (((when (and (equal (len path) 1)
                   (acl2::access-case (car path) :member)
                   (equal (identifier->field
                           (acl2::access-member->name (car path)))
                          (identifier->field (crypto-owner-identifier)))))
        :owner)
       ((when (endp path)) :error)
       (first (car path))
       ((unless (acl2::access-case first :member)) :error)
       (ew (rec-record-data-lookup (acl2::access-member->name first) data))
       ((when (equal ew :error)) :error))
    (if (endp (cdr path))
        ew
      (ptx-entry-find ew (cdr path)))))

(defruled rec-record-data-lookup-sound
  (implies (rec-record-datawp data)
           (b* ((out (rec-record-data-lookup name data))
                (spec (crypto-record-entry-lookup
                       name (rec-record-data-eval data asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (ptx-ewtp out)
                                (equal (ptx-eval out asg) spec))))))
  :induct (rec-record-datawp data)
  :enable (rec-record-data-lookup crypto-record-entry-lookup
           rec-record-datawp rec-record-data-eval spec-error))

(defruled rec-record-find-sound
  (b* ((r (rec-record-of-wires pubp og data ng vbits asg))
       (out (rec-record-find data path))
       (spec (crypto-record-find r path)))
    (implies (and (rec-record-datawp data)
                  (access-listp path))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (equal out :owner)
                           (equal spec (crypto-owner-to-entry
                                        (record->owner r))))
                  (implies (and (not (equal out :error))
                                (not (equal out :owner)))
                           (and (ptx-ewtp out)
                                (equal (ptx-eval out asg) spec))))))
  :do-not-induct t
  :use ((:instance rec-record-data-lookup-sound
                   (name (acl2::access-member->name (car path))))
        (:instance ptx-entry-find-sound
                   (ew (rec-record-data-lookup
                        (acl2::access-member->name (car path)) data))
                   (path (cdr path)) (p (base-prime))))
  :enable (rec-record-find crypto-record-find crypto-entry-find
           rec-record-of-wires ptx-entry-find-gadget spec-error))

(defruled rec-record-find-complete
  :short "find emits no constraint."
  (r1cs::r1cs-constraints-holdp nil asg p))
