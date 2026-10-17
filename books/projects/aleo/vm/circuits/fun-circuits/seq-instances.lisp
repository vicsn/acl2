; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two concrete instances of seq-framework, by functional instantiation:
;
;   seq-bool: Vec<Boolean> / tuples of Booleans.  Each element owns one
;     wire b, constrained by Boolean::new (boolean-check-gadget, the
;     booleanity constraint (1 - b) b = 0); write_bits_* pushes b and adds
;     no constraint.  Shared wires are left abstract.
;
;   seq-fld: Vec<Field> / tuples of Fields.  Each element owns the wires
;     (x b_0 ... b_252 r_0 ... r_{k-1}): x is the field element (Field::new
;     adds no constraint), b the bits and r the range-check fold witnesses
;     of Field::write_bits_le (fb-field-write-bits-le-gadget).  The
;     constant-one variable is the shared wire SEQ-ONE.
;
; Also general lemmas about seq-agree and lookup-equal-list that help
; prove the element obligations of other instances.

(in-package "ALEOVM")

(include-book "seq-framework")
(include-book "fb2-field-bits")
(include-book "../r1cs/boolean-check")
(include-book "../library-extensions/lookup-equal-list")

(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General lemmas for element obligations.

(defruled seq-lookup-when-agree
  (implies (and (seq-agree ws a b)
                (member-equal k ws))
           (equal (lookup-equal k a) (lookup-equal k b)))
  :induct (len ws))

(defruled seq-lookup-equal-list-when-agree
  (implies (and (seq-agree ws a b)
                (subsetp-equal sub ws))
           (equal (lookup-equal-list sub a) (lookup-equal-list sub b)))
  :induct (len sub)
  :enable (lookup-equal-list seq-lookup-when-agree))

(defruled seq-bindsp-when-lookup
  (implies (and (alistp a)
                (lookup-equal k a))
           (r1cs::valuation-bindsp a k))
  :enable (r1cs::valuation-bindsp lookup-equal))

(defruled seq-bindsp-when-agree-key
  (implies (and (alistp a)
                (r1cs::r1cs-valuationp b p)
                (r1cs::valuation-bindsp b k)
                (equal (lookup-equal k a) (lookup-equal k b)))
           (r1cs::valuation-bindsp a k))
  :use ((:instance seq-bindsp-when-lookup)
        (:instance r1cs::fep-of-lookup-equal
                   (valuation b) (var k) (prime p)))
  :in-theory (e/d (pfield::fep) (r1cs::fep-of-lookup-equal)))

(defruled seq-binds-all-when-agree
  (implies (and (seq-agree ws a b)
                (alistp a)
                (r1cs::r1cs-valuationp b p)
                (r1cs::valuation-binds-allp b ws))
           (r1cs::valuation-binds-allp a ws))
  :induct (len ws)
  :enable (r1cs::valuation-binds-allp seq-bindsp-when-agree-key))

(defrule seq-lookup-equal-list-of-cons-skip
  (implies (not (member-equal k ks))
           (equal (lookup-equal-list ks (cons (cons k v) a))
                  (lookup-equal-list ks a)))
  :induct (len ks)
  :enable lookup-equal-list)

(defrule seq-lookup-equal-list-of-pairlis
  (implies (and (no-duplicatesp-equal keys)
                (equal (len keys) (len vals))
                (true-listp vals))
           (equal (lookup-equal-list keys (pairlis$ keys vals))
                  vals))
  :induct (seq-cdr2-ind keys vals)
  :enable lookup-equal-list
  :prep-lemmas
  ((defun seq-cdr2-ind (a b)
     (if (atom a) (list a b) (seq-cdr2-ind (cdr a) (cdr b))))))

(defruled seq-lookup-equal-list-of-append-hit
  (implies (and (alistp a)
                (subsetp-equal ks (strip-cars a)))
           (equal (lookup-equal-list ks (append a b))
                  (lookup-equal-list ks a)))
  :induct (len ks)
  :enable (lookup-equal-list acl2::lookup-equal-of-append))

(defruled seq-lookup-equal-list-of-append-skip
  (implies (and (alistp a)
                (not (intersectp-equal ks (strip-cars a))))
           (equal (lookup-equal-list ks (append a b))
                  (lookup-equal-list ks b)))
  :induct (len ks)
  :enable (lookup-equal-list acl2::lookup-equal-of-append))

(defrule seq-fe-listp-when-bit-listp
  (implies (bit-listp bs)
           (pfield::fe-listp bs (base-prime)))
  :induct (len bs)
  :enable (pfield::fe-listp pfield::fep bit-listp)
  :prep-lemmas
  ((defrule seq-base-prime-gt-1
     (< 1 (base-prime))
     :enable base-prime)))

(local (in-theory (disable base-prime (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Boolean.

(defun seq-bool-wiresp (ty wires)
  (declare (ignore ty))
  (and (symbol-listp wires)
       (no-duplicatesp-equal wires)
       (equal (len wires) 1)))

(defun seq-bool-valp (ty x)
  (declare (ignore ty))
  (bitp x))

(defun seq-bool-elem-gadget (ty wires)
  (declare (ignore ty))
  (boolean-check-gadget (car wires) (base-prime)))

(defun seq-bool-in (ty wires asg)
  (declare (ignore ty))
  (lookup-equal (car wires) asg))

(defun seq-bool-out (ty wires asg)
  (declare (ignore ty))
  (list (lookup-equal (car wires) asg)))

; snarkVM circuit/types/boolean/src/helpers/to_bits.rs: write_bits_le and
; write_bits_be both push the boolean itself.
(defun seq-bool-elem-spec (ty acc x)
  (declare (ignore ty))
  (append acc (list x)))

(defun seq-bool-elem-witness (ty wires x)
  (declare (ignore ty))
  (list (cons (car wires) x)))

(defruled seq-bool-wires-shape
  (implies (seq-bool-wiresp ty wires)
           (equal (list (car wires)) wires))
  :expand ((len wires) (len (cdr wires)) (symbol-listp wires)
           (symbol-listp (cdr wires))))

(defrule seq-bool-elem-sound
  (implies (and (seq-bool-wiresp ty wires)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg wires)
                (r1cs::r1cs-constraints-holdp (seq-bool-elem-gadget ty wires)
                                              asg (base-prime)))
           (and (seq-bool-valp ty (seq-bool-in ty wires asg))
                (equal (seq-bool-elem-spec ty acc (seq-bool-in ty wires asg))
                       (append acc (seq-bool-out ty wires asg)))))
  :use ((:instance boolean-check-gadget-to-bitp (x (car wires)) (p (base-prime))))
  :enable r1cs::valuation-binds-allp)

(defrule seq-bool-witness-props
  (implies (and (seq-bool-wiresp ty wires)
                (seq-bool-valp ty x))
           (and (r1cs::r1cs-valuationp (seq-bool-elem-witness ty wires x)
                                       (base-prime))
                (alistp (seq-bool-elem-witness ty wires x))
                (equal (strip-cars (seq-bool-elem-witness ty wires x)) wires)))
  :use seq-bool-wires-shape
  :enable (r1cs::r1cs-valuationp pfield::fep bitp)
  :prep-lemmas
  ((defrule seq-base-prime-gt-1-local
     (< 1 (base-prime))
     :enable base-prime)))

(defrule seq-bool-elem-complete
  (implies (and (seq-bool-wiresp ty wires)
                (seq-bool-valp ty x)
                (r1cs::r1cs-valuationp asg (base-prime))
                (seq-agree wires asg (seq-bool-elem-witness ty wires x)))
           (and (r1cs::r1cs-constraints-holdp (seq-bool-elem-gadget ty wires)
                                              asg (base-prime))
                (equal (seq-bool-in ty wires asg) x)))
  :use ((:instance boolean-check-gadget-to-bitp (x (car wires)) (p (base-prime)))
        (:instance seq-lookup-when-agree (k (car wires)) (ws wires) (a asg)
                   (b (seq-bool-elem-witness ty wires x)))
        (:instance seq-bindsp-when-lookup (k (car wires)) (a asg)))
  :enable bitp)

(defrule seq-bool-wiresp-necc
  (implies (seq-bool-wiresp ty wires)
           (and (symbol-listp wires)
                (no-duplicatesp-equal wires))))

(defrule seq-bool-true-listp-of-out
  (true-listp (seq-bool-out ty wires asg)))

(local (in-theory (disable seq-bool-wiresp seq-bool-valp seq-bool-elem-gadget
                           seq-bool-in seq-bool-out seq-bool-elem-spec
                           seq-bool-elem-witness)))

(seq-instantiate-write-bits
 seq-bool
 :wiresp seq-bool-wiresp :valp seq-bool-valp :gadget seq-bool-elem-gadget
 :in seq-bool-in :out seq-bool-out :spec seq-bool-elem-spec
 :witness seq-bool-elem-witness
 :theory (enable seq-bool-blocks-wiresp seq-bool-gadget seq-bool-ins
                 seq-bool-outs seq-bool-valsp seq-bool-spec seq-bool-witness
                 seq-bool-blocks-disjointp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field.

(defconst *seq-fld-nbits* 253)

(defun seq-fld-rlen () (bits-lt-prime-rlen (base-prime)))

(defun seq-fld-cs () (nat=>lebits* (1- (base-prime))))

(defun seq-fld-shared-wires () '(seq-one))
(defun seq-fld-shared-witness () '((seq-one . 1)))
(defun seq-fld-shared-ok (asg) (equal (lookup-equal 'seq-one asg) 1))

(defun seq-fld-wiresp (ty wires)
  (declare (ignore ty))
  (and (symbol-listp wires)
       (no-duplicatesp-equal wires)
       (equal (len wires) (+ 1 *seq-fld-nbits* (seq-fld-rlen)))))

(defun seq-fld-valp (ty x)
  (declare (ignore ty))
  (fieldp x))

(defun seq-fld-x (wires) (car wires))
(defun seq-fld-bits (wires) (take *seq-fld-nbits* (cdr wires)))
(defun seq-fld-rs (wires) (nthcdr *seq-fld-nbits* (cdr wires)))

(defun seq-fld-elem-gadget (ty wires)
  (declare (ignore ty))
  (fb-field-write-bits-le-gadget (seq-fld-x wires) (seq-fld-bits wires)
                                 (seq-fld-rs wires) 'seq-one (base-prime)))

(defun seq-fld-in (ty wires asg)
  (declare (ignore ty))
  (lookup-equal (seq-fld-x wires) asg))

(defun seq-fld-out (ty wires asg)
  (declare (ignore ty))
  (lookup-equal-list (seq-fld-bits wires) asg))

(defun seq-fld-elem-spec (ty acc x)
  (declare (ignore ty))
  (field-write-bits-le-funspec acc x))

(defun seq-fld-rs-witness (x)
  (fb-bits-lte-const-witness (field-bits-le x) (seq-fld-cs)))

(defun seq-fld-elem-witness (ty wires x)
  (declare (ignore ty))
  (cons (cons (seq-fld-x wires) x)
        (append (pairlis$ (seq-fld-bits wires) (field-bits-le x))
                (pairlis$ (seq-fld-rs wires) (seq-fld-rs-witness x)))))

(defruled seq-fld-prime-facts
  (and (primep (base-prime))
       (oddp (base-prime))
       (equal (integer-length (base-prime)) 253)
       (bit-listp (seq-fld-cs))
       (equal (len (seq-fld-cs)) 253)
       (member-equal 0 (seq-fld-cs))
       (equal (car (last (seq-fld-cs))) 1))
  :in-theory '((:e base-prime) (:e primep) (:e oddp) (:e integer-length)
               (:e seq-fld-cs) (:e bit-listp) (:e len) (:e member-equal)
               (:e car) (:e last) (:e equal) seq-fld-cs))

(defrule seq-fld-rs-witness-props
  (implies (fieldp x)
           (and (bit-listp (seq-fld-rs-witness x))
                (equal (len (seq-fld-rs-witness x)) (seq-fld-rlen))))
  :use (seq-fld-prime-facts
        (:instance fb-bits-lte-const-witness
                   (xs (field-bits-le x)) (cs (seq-fld-cs))))
  :enable (bits-lt-prime-rlen)
  :disable (seq-fld-cs)
  :prep-lemmas
  ((defrule base-field-size-in-bits-253
     (equal (base-field-size-in-bits) 253)
     :enable base-field-size-in-bits)))

(defthm seq-member-of-append
  (iff (member-equal k (append a b))
       (or (member-equal k a) (member-equal k b)))
  :rule-classes nil)

(defruled seq-take-nthcdr-facts
  (implies (and (natp n) (<= n (len l)))
           (and (iff (member-equal k l)
                     (or (member-equal k (take n l))
                         (member-equal k (nthcdr n l))))
                (equal (no-duplicatesp-equal l)
                       (and (no-duplicatesp-equal (take n l))
                            (no-duplicatesp-equal (nthcdr n l))
                            (not (intersectp-equal (take n l) (nthcdr n l)))))))
  :use ((:instance seq-member-of-append (a (take n l)) (b (nthcdr n l)))
        (:instance seq-no-dups-of-append (a (take n l)) (b (nthcdr n l))))
  :disable (seq-no-dups-of-append acl2::nthcdr-of-cdr))

(defrule seq-fld-rlen-natp
  (natp (seq-fld-rlen))
  :rule-classes :type-prescription)

(in-theory (disable seq-fld-rlen (:e seq-fld-rlen)))

(defruled seq-fld-wires-split
  (implies (seq-fld-wiresp ty wires)
           (and (equal (cons (seq-fld-x wires)
                             (append (seq-fld-bits wires) (seq-fld-rs wires)))
                       wires)
                (equal (len (seq-fld-bits wires)) 253)
                (equal (len (seq-fld-rs wires)) (seq-fld-rlen))
                (symbolp (seq-fld-x wires))
                (symbol-listp (seq-fld-bits wires))
                (symbol-listp (seq-fld-rs wires))
                (true-listp (seq-fld-bits wires))
                (true-listp (seq-fld-rs wires))
                (not (member-equal (seq-fld-x wires) (seq-fld-bits wires)))
                (not (member-equal (seq-fld-x wires) (seq-fld-rs wires)))
                (no-duplicatesp-equal (seq-fld-bits wires))
                (no-duplicatesp-equal (seq-fld-rs wires))
                (not (intersectp-equal (seq-fld-bits wires) (seq-fld-rs wires)))))
  :use ((:instance seq-take-nthcdr-facts (n 253) (l (cdr wires))
                   (k (car wires)))
        (:instance acl2::append-of-take-and-nthcdr (n 253) (x (cdr wires))))
  :disable (acl2::nthcdr-of-cdr acl2::append-of-take-and-nthcdr)
  :expand ((len wires) (no-duplicatesp-equal wires) (symbol-listp wires)))

(defruled seq-fld-wires-subsets
  (implies (seq-fld-wiresp ty wires)
           (and (subsetp-equal (seq-fld-bits wires) wires)
                (subsetp-equal (seq-fld-rs wires) wires)
                (member-equal (seq-fld-x wires) wires)))
  :use ((:instance acl2::subsetp-trans
                   (x (take 253 (cdr wires))) (y (cdr wires)) (z wires))
        (:instance acl2::subsetp-trans
                   (x (nthcdr 253 (cdr wires))) (y (cdr wires)) (z wires)))
  :disable (acl2::nthcdr-of-cdr acl2::subsetp-trans acl2::subsetp-trans2))

(defruled seq-binds-all-when-subsetp-of
  (implies (and (r1cs::valuation-binds-allp a l)
                (subsetp-equal sub l))
           (r1cs::valuation-binds-allp a sub))
  :induct (len sub)
  :enable r1cs::valuation-binds-allp)

(defrule seq-fld-shared-props
  (and (symbol-listp (seq-fld-shared-wires))
       (no-duplicatesp-equal (seq-fld-shared-wires))
       (r1cs::r1cs-valuationp (seq-fld-shared-witness) (base-prime))
       (alistp (seq-fld-shared-witness))
       (equal (strip-cars (seq-fld-shared-witness)) (seq-fld-shared-wires)))
  :enable (r1cs::r1cs-valuationp pfield::fep)
  :prep-lemmas
  ((defrule seq-base-prime-gt-1-fld
     (< 1 (base-prime))
     :enable base-prime)))

(defrule seq-fld-shared-ok-when-agree
  (implies (seq-agree (seq-fld-shared-wires) asg (seq-fld-shared-witness))
           (seq-fld-shared-ok asg)))

(defrule seq-fld-wiresp-necc
  (implies (seq-fld-wiresp ty wires)
           (and (symbol-listp wires)
                (no-duplicatesp-equal wires))))

(defrule seq-fld-true-listp-of-out
  (true-listp (seq-fld-out ty wires asg)))

(defruled seq-fld-shared-binds
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (seq-fld-shared-ok asg))
           (r1cs::valuation-bindsp asg 'seq-one))
  :use ((:instance seq-bindsp-when-lookup (a asg) (k 'seq-one))))

(defrule seq-fld-elem-sound
  (implies (and (seq-fld-wiresp ty wires)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg wires)
                (seq-fld-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-fld-elem-gadget ty wires)
                                              asg (base-prime)))
           (and (seq-fld-valp ty (seq-fld-in ty wires asg))
                (equal (seq-fld-elem-spec ty acc (seq-fld-in ty wires asg))
                       (append acc (seq-fld-out ty wires asg)))))
  :do-not-induct t
  :use (seq-fld-prime-facts
        seq-fld-wires-split
        seq-fld-wires-subsets
        seq-fld-shared-binds
        (:instance fb-field-write-bits-le-gadget-sound
                   (x (seq-fld-x wires)) (bits (seq-fld-bits wires))
                   (rs (seq-fld-rs wires)) (u 'seq-one) (p (base-prime))
                   (acc nil))
        (:instance seq-binds-all-when-subsetp-of (a asg) (l wires)
                   (sub (seq-fld-bits wires)))
        (:instance seq-binds-all-when-subsetp-of (a asg) (l wires)
                   (sub (seq-fld-rs wires)))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg) (vars wires) (var (seq-fld-x wires)))
        (:instance r1cs::fep-of-lookup-equal
                   (valuation asg) (var (seq-fld-x wires)) (prime (base-prime))))
  :in-theory (e/d (field-write-bits-le-funspec fieldp seq-fld-rlen)
                  (seq-fld-wiresp seq-fld-x seq-fld-bits seq-fld-rs
                                  r1cs::fep-of-lookup-equal
                                  r1cs::valuation-bindsp-when-valuation-binds-allp
                                  seq-fld-cs bits-lt-prime-rlen)))

(defruled seq-fld-witness-facts
  (implies (and (seq-fld-wiresp ty wires)
                (fieldp x))
           (b* ((w (seq-fld-elem-witness ty wires x)))
             (and (alistp w)
                  (equal (strip-cars w) wires)
                  (r1cs::r1cs-valuationp w (base-prime))
                  (equal (lookup-equal (seq-fld-x wires) w) x)
                  (equal (lookup-equal-list (seq-fld-bits wires) w)
                         (field-bits-le x))
                  (equal (lookup-equal-list (seq-fld-rs wires) w)
                         (seq-fld-rs-witness x)))))
  :do-not-induct t
  :use (seq-fld-wires-split
        seq-fld-rs-witness-props
        (:instance seq-lookup-equal-list-of-append-hit
                   (ks (seq-fld-bits wires))
                   (a (pairlis$ (seq-fld-bits wires) (field-bits-le x)))
                   (b (pairlis$ (seq-fld-rs wires) (seq-fld-rs-witness x))))
        (:instance seq-lookup-equal-list-of-append-skip
                   (ks (seq-fld-rs wires))
                   (a (pairlis$ (seq-fld-bits wires) (field-bits-le x)))
                   (b (pairlis$ (seq-fld-rs wires) (seq-fld-rs-witness x))))
        (:instance seq-intersectp-commute
                   (a (seq-fld-bits wires)) (b (seq-fld-rs wires))))
  :in-theory (e/d (r1cs::r1cs-valuationp fieldp seq-fe-listp-of-append-2)
                  (seq-fld-wiresp seq-fld-x seq-fld-bits seq-fld-rs
                                  seq-fld-rs-witness seq-fld-rs-witness-props
                                  seq-fld-cs bits-lt-prime-rlen))
  :prep-lemmas
  ((defrule base-field-size-in-bits-253-b
     (equal (base-field-size-in-bits) 253)
     :enable base-field-size-in-bits)
   (defruled seq-fe-listp-of-append-2
     (implies (and (pfield::fe-listp a p) (pfield::fe-listp b p))
              (pfield::fe-listp (append a b) p))
     :enable pfield::fe-listp)))

(defrule seq-fld-witness-props
  (implies (and (seq-fld-wiresp ty wires)
                (seq-fld-valp ty x))
           (and (r1cs::r1cs-valuationp (seq-fld-elem-witness ty wires x)
                                       (base-prime))
                (alistp (seq-fld-elem-witness ty wires x))
                (equal (strip-cars (seq-fld-elem-witness ty wires x)) wires)))
  :use seq-fld-witness-facts
  :in-theory (disable seq-fld-wiresp seq-fld-elem-witness))

(defrule seq-fld-elem-complete
  (implies (and (seq-fld-wiresp ty wires)
                (seq-fld-valp ty x)
                (r1cs::r1cs-valuationp asg (base-prime))
                (seq-fld-shared-ok asg)
                (seq-agree wires asg (seq-fld-elem-witness ty wires x)))
           (and (r1cs::r1cs-constraints-holdp (seq-fld-elem-gadget ty wires)
                                              asg (base-prime))
                (equal (seq-fld-in ty wires asg) x)))
  :do-not-induct t
  :use (seq-fld-prime-facts
        seq-fld-wires-split
        seq-fld-wires-subsets
        seq-fld-witness-facts
        seq-fld-shared-binds
        (:instance seq-lookup-when-agree (ws wires) (a asg)
                   (b (seq-fld-elem-witness ty wires x))
                   (k (seq-fld-x wires)))
        (:instance seq-lookup-equal-list-when-agree (ws wires) (a asg)
                   (b (seq-fld-elem-witness ty wires x))
                   (sub (seq-fld-bits wires)))
        (:instance seq-lookup-equal-list-when-agree (ws wires) (a asg)
                   (b (seq-fld-elem-witness ty wires x))
                   (sub (seq-fld-rs wires)))
        (:instance seq-binds-all-when-agree (ws wires) (a asg)
                   (b (seq-fld-elem-witness ty wires x)) (p (base-prime)))
        (:instance seq-binds-all-when-subsetp
                   (ws wires) (a (seq-fld-elem-witness ty wires x)))
        (:instance seq-binds-all-when-subsetp-of (a asg) (l wires)
                   (sub (seq-fld-bits wires)))
        (:instance seq-binds-all-when-subsetp-of (a asg) (l wires)
                   (sub (seq-fld-rs wires)))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg) (vars wires) (var (seq-fld-x wires)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x (seq-fld-x wires)) (bits (seq-fld-bits wires))
                   (rs (seq-fld-rs wires)) (u 'seq-one) (p (base-prime))))
  :in-theory (e/d (seq-fld-rlen seq-fld-cs)
                  (seq-fld-wiresp seq-fld-x seq-fld-bits seq-fld-rs
                                  seq-fld-elem-witness seq-fld-witness-props
                                  r1cs::valuation-bindsp-when-valuation-binds-allp
                                  bits-lt-prime-rlen (:e seq-fld-cs)
                                  fieldp)))

(local (in-theory (disable seq-fld-wiresp seq-fld-valp seq-fld-elem-gadget
                           seq-fld-in seq-fld-out seq-fld-elem-spec
                           seq-fld-elem-witness seq-fld-shared-wires
                           seq-fld-shared-witness seq-fld-shared-ok
                           (:e seq-fld-shared-wires) (:e seq-fld-shared-witness))))

(seq-instantiate-write-bits
 seq-fld
 :wiresp seq-fld-wiresp :valp seq-fld-valp :gadget seq-fld-elem-gadget
 :in seq-fld-in :out seq-fld-out :spec seq-fld-elem-spec
 :witness seq-fld-elem-witness
 :shared-wires seq-fld-shared-wires :shared-witness seq-fld-shared-witness
 :shared-ok seq-fld-shared-ok
 :theory (enable seq-fld-blocks-wiresp seq-fld-gadget seq-fld-ins
                 seq-fld-outs seq-fld-valsp seq-fld-spec seq-fld-witness
                 seq-fld-blocks-disjointp))
