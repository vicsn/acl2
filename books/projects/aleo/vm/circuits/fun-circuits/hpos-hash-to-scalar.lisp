; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Poseidon::hash_to_scalar (circuit/algorithms/src/poseidon/hash_to_scalar.rs):
; Scalar::from_field_lossy(hash(input)).
;
; The constraints are those of hash_many(input, 1) followed by those of
; Field::to_bits_le on the output linear combination.  The latter are
; scalar-from-field-lossy-gadget with the linear combination substituted
; for its input variable (hpos-cs-subst).  The 253 bit wires and the
; comparator wires are the next fresh variables; the variable after them is
; only a placeholder for the substitution and occurs in no constraint.  U is
; the public unit wire.

(in-package "ALEOVM")

(include-book "hpos-aleo")
(include-book "hpos-subst")
(include-book "scalar-from-field-lossy-r1cs")
(include-book "fsa-scalar-from-field-lossy")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp
                            scalar-from-field-lossy-gadget)))

(defrule hpos-base-prime-value
  (equal (base-prime) primes::*bls12-377-scalar-field-prime*)
  :enable base-prime)

(defund hpos-h2s-wires (vs)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime))
       (n (integer-length p))
       (r (bits-lt-prime-rlen p))
       (rest (nthcdr (+ n r) vs)))
    (mv (take n vs) (take r (nthcdr n vs)) (car rest) rest)))

(defund hpos-c-lc-to-scalar-bits (h u vs asg)
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime))
       ((mv bs rs x vs) (hpos-h2s-wires vs))
       (hv (hpos-lc-eval h asg p))
       (bv (field-bits-le hv))
       (rv (fb-bits-lte-const-witness bv (nat=>lebits* (1- p))))
       (asg (append (pairlis$ rs rv) (append (pairlis$ bs bv) asg)))
       (cs (hpos-cs-subst (scalar-from-field-lossy-gadget x bs rs u p) x h)))
    (mv (take 250 bs) cs vs asg)))

(defund hpos-c-hash-to-scalar (rate xs u vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv outs cs1 vs asg) (hpos-c-poseidon-hash-many rate xs 1 vs asg))
       ((mv bits cs2 vs asg) (hpos-c-lc-to-scalar-bits (car outs) u vs asg)))
    (mv bits (append cs1 cs2) vs asg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Binding the placeholder variable.

(defrule hpos-r1cs-valuationp-of-acons
  (implies (and (r1cs::r1cs-valuationp a p)
                (symbolp x)
                (not (r1cs::valuation-bindsp a x))
                (pfield::fep v p))
           (r1cs::r1cs-valuationp (cons (cons x v) a) p))
  :enable (r1cs::r1cs-valuationp r1cs::valuation-bindsp r1cs::var-listp))

(defrule hpos-valuation-bindsp-of-acons
  (iff (r1cs::valuation-bindsp (cons (cons x v) a) y)
       (or (equal x y) (r1cs::valuation-bindsp a y)))
  :enable r1cs::valuation-bindsp)

(defrule hpos-valuation-binds-allp-of-acons
  (implies (r1cs::valuation-binds-allp a vars)
           (r1cs::valuation-binds-allp (cons (cons x v) a) vars))
  :enable r1cs::valuation-binds-allp)

(defrule hpos-lookup-equal-of-acons
  (equal (lookup-equal y (cons (cons x v) a))
         (if (equal x y) v (lookup-equal y a)))
  :enable lookup-equal)

(defrule hpos-lookup-equal-list-of-acons
  (implies (not (member-equal x vars))
           (equal (lookup-equal-list vars (cons (cons x v) a))
                  (lookup-equal-list vars a)))
  :enable lookup-equal-list)

(defrule hpos-lc-eval-of-car
  (implies (consp l)
           (equal (hpos-lc-eval (car l) asg p)
                  (car (hpos-lc-eval-list l asg p))))
  :enable hpos-lc-eval-list)

(defrule hpos-consp-of-hpos-poseidon-hash-many-1
  (consp (hpos-poseidon-hash-many rate inputs 1))
  :use (:instance hpos-len-of-hpos-poseidon-hash-many (num-outputs 1))
  :disable hpos-len-of-hpos-poseidon-hash-many)

;; Poseidon::hash.

(defrule hpos-c-poseidon-hash-many-1-sound
  (b* (((mv outs cs & &) (hpos-c-poseidon-hash-many rate xs 1 vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval (car outs) asgx p)
                    (hpos-poseidon-hash rate (hpos-lc-eval-list xs asgx p)))))
  :enable hpos-poseidon-hash
  :disable (hpos-c-poseidon-hash-many-sound hpos-lc-eval-decomp
                                            hpos-consp-of-hpos-lc-eval-list)
  :use ((:instance hpos-c-poseidon-hash-many-sound (nout 1))
        (:instance hpos-consp-of-hpos-lc-eval-list
                   (l (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (asg asgx)
                   (p primes::*bls12-377-scalar-field-prime*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Witness extension by fresh wires.

(defrule hpos-strip-cars-of-append-pairlis
  (implies (equal (len vals) (len ks))
           (equal (strip-cars (append (pairlis$ ks vals) a))
                  (append (true-list-fix ks) (strip-cars a))))
  :induct (pairlis$ ks vals)
  :enable pairlis$)

(defrule hpos-r1cs-valuationp-of-append-pairlis
  (implies (and (r1cs::r1cs-valuationp a p)
                (symbol-listp ks)
                (no-duplicatesp-equal ks)
                (not (intersectp-equal ks (strip-cars a)))
                (pfield::fe-listp vals p)
                (equal (len vals) (len ks)))
           (r1cs::r1cs-valuationp (append (pairlis$ ks vals) a) p))
  :induct (pairlis$ ks vals)
  :enable (pairlis$ r1cs::valuation-bindsp intersectp-equal))

(defrule hpos-ext-p-of-append
  (hpos-ext-p a (append x a))
  :induct (len x)
  :enable hpos-ext-p)

(defrule hpos-lookup-equal-list-of-append-pairlis-same
  (implies (and (no-duplicatesp-equal ks)
                (true-listp vals)
                (equal (len vals) (len ks)))
           (equal (lookup-equal-list ks (append (pairlis$ ks vals) a))
                  vals))
  :induct (pairlis$ ks vals)
  :enable (pairlis$ lookup-equal-list lookup-equal))

(defrule hpos-lookup-equal-of-append-pairlis-other
  (implies (and (not (member-equal v ks))
                (equal (len vals) (len ks)))
           (equal (lookup-equal v (append (pairlis$ ks vals) a))
                  (lookup-equal v a)))
  :induct (pairlis$ ks vals)
  :enable (pairlis$ lookup-equal))

(defrule hpos-lookup-equal-list-of-append-pairlis-other
  (implies (and (not (intersectp-equal vars ks))
                (equal (len vals) (len ks)))
           (equal (lookup-equal-list vars (append (pairlis$ ks vals) a))
                  (lookup-equal-list vars a)))
  :induct (lookup-equal-list vars a)
  :enable (lookup-equal-list intersectp-equal))

(defrule hpos-valuation-binds-allp-of-append-pairlis-same
  (implies (equal (len vals) (len ks))
           (r1cs::valuation-binds-allp (append (pairlis$ ks vals) a) ks))
  :induct (pairlis$ ks vals)
  :enable (pairlis$ r1cs::valuation-binds-allp r1cs::valuation-bindsp))

(defrulel hpos-member-strip-cars-of-append
  (implies (member-equal k (strip-cars a))
           (member-equal k (strip-cars (append x a))))
  :induct (len x))

(defrule hpos-valuation-binds-allp-of-append-other
  (implies (r1cs::valuation-binds-allp a vars)
           (r1cs::valuation-binds-allp (append x a) vars))
  :induct (r1cs::valuation-binds-allp a vars)
  :enable (r1cs::valuation-binds-allp r1cs::valuation-bindsp))

;; Splitting the supply.

(defrulel hpos-split3
  (implies (and (natp n) (natp r) (equal k (+ n r)) (<= k (len l)))
           (equal (append (take n l)
                          (append (take r (nthcdr n l))
                                  (nthcdr k l)))
                  l))
  :use ((:instance acl2::append-of-take-and-nthcdr (n n) (x l))
        (:instance acl2::append-of-take-and-nthcdr (n r) (x (nthcdr n l)))))

(defrulel hpos-symbol-listp-of-append
  (implies (true-listp a)
           (equal (symbol-listp (append a b))
                  (and (symbol-listp a) (symbol-listp b))))
  :induct (len a))

(defrulel hpos-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b)))
  :induct (len a))

(defrulel hpos-intersectp-of-append-left
  (equal (intersectp-equal (append a b) k)
         (or (intersectp-equal a k) (intersectp-equal b k)))
  :induct (len a)
  :enable intersectp-equal)

(defrulel hpos-intersectp-of-cons-right
  (equal (intersectp-equal a (cons x k))
         (or (and (member-equal x a) t) (intersectp-equal a k)))
  :induct (len a)
  :enable intersectp-equal)

(defrulel hpos-intersectp-of-append-right
  (equal (intersectp-equal a (append b k))
         (or (intersectp-equal a b) (intersectp-equal a k)))
  :induct (len b)
  :enable intersectp-equal)

(defruledl hpos-intersectp-commutes
  (iff (intersectp-equal a b) (intersectp-equal b a))
  :induct (len a)
  :enable intersectp-equal)

(defrulel hpos-no-dups-of-append
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a)
              (no-duplicatesp-equal b)
              (not (intersectp-equal a b))))
  :induct (len a)
  :enable intersectp-equal)

(defruledl hpos-split-facts
  (implies (and (true-listp a)
                (true-listp b)
                (equal l (append a (append b c)))
                (symbol-listp l)
                (no-duplicatesp-equal l)
                (not (intersectp-equal l k))
                (consp c))
           (and (symbol-listp a)
                (symbol-listp b)
                (symbolp (car c))
                (no-duplicatesp-equal a)
                (no-duplicatesp-equal b)
                (not (intersectp-equal a b))
                (not (intersectp-equal b a))
                (not (intersectp-equal a k))
                (not (intersectp-equal b k))
                (not (intersectp-equal k a))
                (not (intersectp-equal k b))
                (not (member-equal (car c) a))
                (not (member-equal (car c) b))
                (not (member-equal (car c) k))
                (symbol-listp c)
                (no-duplicatesp-equal c)
                (not (intersectp-equal c k))
                (not (intersectp-equal c a))
                (not (intersectp-equal c b))))
  :do-not-induct t
  :expand ((intersectp-equal c k) (no-duplicatesp-equal c) (symbol-listp c))
  :use ((:instance hpos-intersectp-commutes (a a) (b b))
        (:instance hpos-intersectp-commutes (a a) (b k))
        (:instance hpos-intersectp-commutes (a b) (b k))
        (:instance hpos-intersectp-commutes (a a) (b c))
        (:instance hpos-intersectp-commutes (a b) (b c))))

(defrule hpos-supply-okp-of-append-pairlis
  (implies (and (hpos-supply-okp vs a)
                (not (intersectp-equal vs ks))
                (equal (len vals) (len ks)))
           (hpos-supply-okp vs (append (pairlis$ ks vals) a)))
  :enable hpos-supply-okp)

(defruled hpos-h2s-wires-facts
  (b* (((mv bs rs x rest) (hpos-h2s-wires vs))
       (p (base-prime)))
    (implies (and (hpos-supply-okp vs a)
                  (< (+ (integer-length p) (bits-lt-prime-rlen p)) (len vs)))
             (and (equal (len bs) (integer-length p))
                  (equal (len rs) (bits-lt-prime-rlen p))
                  (symbol-listp bs)
                  (symbol-listp rs)
                  (symbolp x)
                  (no-duplicatesp-equal bs)
                  (no-duplicatesp-equal rs)
                  (not (intersectp-equal bs rs))
                  (not (intersectp-equal rs bs))
                  (not (intersectp-equal bs (strip-cars a)))
                  (not (intersectp-equal rs (strip-cars a)))
                  (not (member-equal x bs))
                  (not (member-equal x rs))
                  (not (member-equal x (strip-cars a)))
                  (not (intersectp-equal rest bs))
                  (not (intersectp-equal rest rs))
                  (hpos-supply-okp rest a))))
  :do-not-induct t
  :enable (hpos-h2s-wires hpos-supply-okp)
  :disable (hpos-symbol-listp-of-append hpos-no-dups-of-append
            hpos-intersectp-of-append-left)
  :use ((:instance hpos-split-facts
                   (l vs)
                   (a (take (integer-length (base-prime)) vs))
                   (b (take (bits-lt-prime-rlen (base-prime))
                            (nthcdr (integer-length (base-prime)) vs)))
                   (c (nthcdr (+ (integer-length (base-prime))
                                 (bits-lt-prime-rlen (base-prime)))
                              vs))
                   (k (strip-cars a)))))

(defrulel hpos-fe-listp-when-bit-listp
  (implies (and (bit-listp bits) (integerp p) (< 1 p))
           (pfield::fe-listp bits p))
  :induct (len bits)
  :enable (pfield::fe-listp bit-listp pfield::fep))

(defrule hpos-ext-p-of-append-append
  (hpos-ext-p a (append x (append y a)))
  :disable hpos-ext-p-of-append
  :use ((:instance hpos-ext-p-of-append (x (append x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field::to_bits_le of a linear combination, then the low 250 bits.

(defrule hpos-c-lc-to-scalar-bits-parts
  (b* (((mv bs rs x rest) (hpos-h2s-wires vs)))
    (and (equal (mv-nth 0 (hpos-c-lc-to-scalar-bits h u vs asg)) (take 250 bs))
         (equal (mv-nth 1 (hpos-c-lc-to-scalar-bits h u vs asg))
                (hpos-cs-subst (scalar-from-field-lossy-gadget x bs rs u (base-prime))
                               x h))
         (equal (mv-nth 2 (hpos-c-lc-to-scalar-bits h u vs asg)) rest)))
  :enable hpos-c-lc-to-scalar-bits)

(defrule hpos-c-lc-to-scalar-bits-asg
  (b* (((mv bs rs & &) (hpos-h2s-wires vs))
       (p (base-prime))
       (bv (field-bits-le (hpos-lc-eval h asg p)))
       (rv (fb-bits-lte-const-witness bv (nat=>lebits* (1- p)))))
    (equal (mv-nth 3 (hpos-c-lc-to-scalar-bits h u vs asg))
           (append (pairlis$ rs rv) (append (pairlis$ bs bv) asg))))
  :enable hpos-c-lc-to-scalar-bits
  :disable (field-bits-le fb-bits-lte-const-witness pairlis$ take nthcdr))

(defrule hpos-c-lc-to-scalar-bits-sound
  (b* (((mv bits cs & &) (hpos-c-lc-to-scalar-bits h u vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs))
       (p (base-prime))
       (hx (hpos-lc-eval h asgx p)))
    (implies (and (symbolp u)
                  (symbolp x)
                  (not (equal u x))
                  (symbol-listp bs)
                  (symbol-listp rs)
                  (not (member-equal x bs))
                  (not (member-equal x rs))
                  (equal (len bs) (integer-length p))
                  (equal (len rs) (bits-lt-prime-rlen p))
                  (r1cs::r1cs-valuationp asgx p)
                  (not (r1cs::valuation-bindsp asgx x))
                  (r1cs::valuation-binds-allp asgx bs)
                  (r1cs::valuation-binds-allp asgx rs)
                  (r1cs::valuation-bindsp asgx u)
                  (equal (lookup-equal u asgx) 1)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (scalar-from-field-lossy-funspec hx))
                  (equal (lebits=>nat (lookup-equal-list bs asgx)) hx))))
  :do-not-induct t
  :disable (hpos-holdp-of-hpos-cs-subst hpos-lc-eval-decomp hpos-c-lc-to-scalar-bits-asg
            (:e base-prime) hpos-base-prime-value)
  :use ((:instance hpos-holdp-of-hpos-cs-subst
                   (p (base-prime))
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (lc h)
                   (asg asgx)
                   (cs (scalar-from-field-lossy-gadget
                        (mv-nth 2 (hpos-h2s-wires vs))
                        (mv-nth 0 (hpos-h2s-wires vs))
                        (mv-nth 1 (hpos-h2s-wires vs))
                        u (base-prime))))
        (:instance scalar-from-field-lossy-gadget-sound
                   (p (base-prime))
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (xs (mv-nth 0 (hpos-h2s-wires vs)))
                   (rs (mv-nth 1 (hpos-h2s-wires vs)))
                   (asg (cons (cons (mv-nth 2 (hpos-h2s-wires vs))
                                    (hpos-lc-eval h asgx (base-prime)))
                              asgx)))))

(defrule hpos-c-lc-to-scalar-bits-asg-facts
  (b* (((mv & & vs2 asg2) (hpos-c-lc-to-scalar-bits h u vs asg))
       ((mv & & x &) (hpos-h2s-wires vs))
       (p (base-prime)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (< (+ (integer-length p) (bits-lt-prime-rlen p)) (len vs)))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (hpos-supply-okp vs2 asg2)
                  (not (r1cs::valuation-bindsp asg2 x)))))
  :do-not-induct t
  :enable r1cs::valuation-bindsp
  :disable hpos-lc-eval-decomp
  :use ((:instance hpos-h2s-wires-facts (a asg))))

(defrule hpos-c-lc-to-scalar-bits-complete
  (b* (((mv & cs vs2 asg2) (hpos-c-lc-to-scalar-bits h u vs asg))
       (p (base-prime)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (< (+ (integer-length p) (bits-lt-prime-rlen p)) (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (hpos-supply-okp vs2 asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p))))
  :do-not-induct t
  :enable (hpos-c-lc-to-scalar-bits r1cs::valuation-bindsp fieldp)
  :disable (hpos-holdp-of-hpos-cs-subst hpos-lc-eval-decomp hpos-lc-eval-when-ext-p
            hpos-c-lc-to-scalar-bits-asg-facts hpos-r1cs-valuationp-of-acons)
  :use ((:instance hpos-h2s-wires-facts (a asg))
        (:instance hpos-c-lc-to-scalar-bits-asg-facts)
        (:instance hpos-r1cs-valuationp-of-acons
                   (a (mv-nth 3 (hpos-c-lc-to-scalar-bits h u vs asg)))
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (v (hpos-lc-eval h asg (base-prime)))
                   (p (base-prime)))
        (:instance hpos-lc-eval-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-lc-to-scalar-bits h u vs asg)))
                   (lc h)
                   (p (base-prime)))
        (:instance hpos-holdp-of-hpos-cs-subst
                   (p (base-prime))
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (lc h)
                   (asg (mv-nth 3 (hpos-c-lc-to-scalar-bits h u vs asg)))
                   (cs (scalar-from-field-lossy-gadget
                        (mv-nth 2 (hpos-h2s-wires vs))
                        (mv-nth 0 (hpos-h2s-wires vs))
                        (mv-nth 1 (hpos-h2s-wires vs))
                        u (base-prime))))
        (:instance fsa-scalar-from-field-lossy-gadget-complete
                   (p (base-prime))
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (xs (mv-nth 0 (hpos-h2s-wires vs)))
                   (rs (mv-nth 1 (hpos-h2s-wires vs)))
                   (asg (cons (cons (mv-nth 2 (hpos-h2s-wires vs))
                                    (hpos-lc-eval h asg (base-prime)))
                              (mv-nth 3 (hpos-c-lc-to-scalar-bits h u vs asg)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Poseidon::hash_to_scalar.

(defrule hpos-c-hash-to-scalar-sound
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar rate xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many rate xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (p (base-prime))
       (h (hpos-poseidon-hash rate (hpos-lc-eval-list xs asgx p))))
    (implies (and (hpos-aleo-rate-p rate)
                  (symbolp u)
                  (symbolp x)
                  (not (equal u x))
                  (symbol-listp bs)
                  (symbol-listp rs)
                  (not (member-equal x bs))
                  (not (member-equal x rs))
                  (equal (len bs) (integer-length p))
                  (equal (len rs) (bits-lt-prime-rlen p))
                  (r1cs::r1cs-valuationp asgx p)
                  (not (r1cs::valuation-bindsp asgx x))
                  (r1cs::valuation-binds-allp asgx bs)
                  (r1cs::valuation-binds-allp asgx rs)
                  (r1cs::valuation-bindsp asgx u)
                  (equal (lookup-equal u asgx) 1)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (scalar-from-field-lossy-funspec h))
                  (equal (lebits=>nat (lookup-equal-list bs asgx)) h))))
  :do-not-induct t
  :enable hpos-c-hash-to-scalar
  :disable (hpos-c-lc-to-scalar-bits-sound hpos-c-poseidon-hash-many-1-sound
            hpos-lc-eval-decomp hpos-c-lc-to-scalar-bits-asg)
  :use ((:instance hpos-c-poseidon-hash-many-1-sound)
        (:instance hpos-c-lc-to-scalar-bits-sound
                   (h (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))
                   (vs (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))))

(defund hpos-h2s-bound (rate nin)
  (declare (xargs :verify-guards nil))
  (+ 1 (hpos-poseidon-bound rate nin 1)
     (integer-length (base-prime))
     (bits-lt-prime-rlen (base-prime))))

(defrule hpos-c-hash-to-scalar-complete
  (b* (((mv & cs & asg2) (hpos-c-hash-to-scalar rate xs u vs asg))
       (p (base-prime)))
    (implies (and (hpos-aleo-rate-p rate)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-h2s-bound rate (len xs)) (len vs))
                  (hpos-lc-list-boundp xs asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1))
             (and (r1cs::r1cs-valuationp asg2 p)
                  (hpos-ext-p asg asg2)
                  (r1cs::r1cs-constraints-holdp cs asg2 p))))
  :do-not-induct t
  :enable (hpos-c-hash-to-scalar hpos-h2s-bound hpos-wit-okp r1cs::valuation-bindsp)
  :disable (hpos-c-lc-to-scalar-bits-complete hpos-c-poseidon-hash-many-complete
            hpos-lc-eval-decomp hpos-c-lc-to-scalar-bits-parts
            hpos-c-lc-to-scalar-bits-asg hpos-holdp-when-ext-p hpos-lookup-when-ext-p
            hpos-ext-p-transitive)
  :use ((:instance hpos-c-poseidon-hash-many-complete (nout 1))
        (:instance hpos-c-poseidon-hash-many-vs-len (nout 1))
        (:instance hpos-ext-p-transitive
                   (a asg)
                   (b (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (c (mv-nth 3 (hpos-c-lc-to-scalar-bits
                                 (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                                 u
                                 (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg))
                                 (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))))
        (:instance hpos-no-duplicatesp-strip-cars-when-valuationp
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (p (base-prime)))
        (:instance hpos-valuation-bindsp-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (v u))
        (:instance hpos-lookup-when-ext-p
                   (old asg)
                   (new (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (v u))
        (:instance hpos-holdp-when-ext-p
                   (old (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (new (mv-nth 3 (hpos-c-lc-to-scalar-bits
                                   (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                                   u
                                   (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg))
                                   (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))))
                   (cs (mv-nth 1 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (p (base-prime)))
        (:instance hpos-c-lc-to-scalar-bits-complete
                   (h (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))
                   (vs (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))))
