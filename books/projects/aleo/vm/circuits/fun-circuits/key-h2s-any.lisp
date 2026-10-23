; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Poseidon::hash_to_scalar soundness without the hypothesis that the
; substitution placeholder wire is unbound.  The placeholder occurs in no
; constraint (hpos-cs-subst replaces it), and the substitution lemma
; hpos-holdp-of-hpos-cs-subst conses its value in front of the assignment,
; shadowing any binding; removing the old binding (key-rem) keeps the
; extended assignment a valuation.  So the conclusions of
; hpos-c-hash-to-scalar-sound, key-h2s-sound{,-psd4,-psd8} and key-ck-from-sound
; hold whatever the assignment binds the placeholder to,
; and compositions that later allocate that wire stay non-vacuous.

(in-package "ALEOVM")

(include-book "key-ck-from")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(local
 (progn
(defund key-rem (x a)
  (declare (xargs :verify-guards nil))
  (cond ((atom a) nil)
        ((equal (caar a) x) (key-rem x (cdr a)))
        (t (cons (car a) (key-rem x (cdr a))))))

(defrule key-lookup-equal-of-key-rem
  (equal (lookup-equal y (key-rem x a))
         (if (equal y x) nil (lookup-equal y a)))
  :enable (key-rem lookup-equal))

(defrule key-dot-product-of-acons-key-rem
  (equal (r1cs::dot-product sv (cons (cons x v) (key-rem x a)) p)
         (r1cs::dot-product sv (cons (cons x v) a) p))
  :induct (len sv)
  :enable (r1cs::dot-product lookup-equal))

(defrule key-holdp-of-acons-key-rem
  (equal (r1cs::r1cs-constraints-holdp cs (cons (cons x v) (key-rem x a)) p)
         (r1cs::r1cs-constraints-holdp cs (cons (cons x v) a) p))
  :induct (len cs)
  :enable (r1cs::r1cs-constraints-holdp r1cs::r1cs-constraint-holdsp))

(defrule key-member-strip-cars-of-key-rem
  (iff (member-equal y (strip-cars (key-rem x a)))
       (and (not (equal y x)) (member-equal y (strip-cars a))))
  :enable key-rem)

(defrule key-no-dups-strip-cars-of-key-rem
  (implies (no-duplicatesp-equal (strip-cars a))
           (no-duplicatesp-equal (strip-cars (key-rem x a))))
  :enable key-rem)

(defrule key-r1cs-valuationp-of-key-rem
  (implies (r1cs::r1cs-valuationp a p)
           (r1cs::r1cs-valuationp (key-rem x a) p))
  :enable (key-rem r1cs::r1cs-valuationp))

(defrule key-valuation-bindsp-of-acons-key-rem
  (iff (r1cs::valuation-bindsp (cons (cons x v) (key-rem x a)) y)
       (or (equal y x) (r1cs::valuation-bindsp a y)))
  :enable r1cs::valuation-bindsp)

(defrule key-valuation-binds-allp-of-acons-key-rem
  (implies (r1cs::valuation-binds-allp a l)
           (r1cs::valuation-binds-allp (cons (cons x v) (key-rem x a)) l))
  :induct (len l)
  :enable r1cs::valuation-binds-allp)

(defrule key-r1cs-valuationp-of-acons-key-rem
  (implies (and (r1cs::r1cs-valuationp a p)
                (symbolp x)
                (pfield::fep v p))
           (r1cs::r1cs-valuationp (cons (cons x v) (key-rem x a)) p))
  :use (:instance hpos-r1cs-valuationp-of-acons (a (key-rem x a)))
  :disable hpos-r1cs-valuationp-of-acons
  :enable r1cs::valuation-bindsp)))

(local
 (progn
(defruled key-lel-of-acons-rem
  (implies (not (member-equal x l))
           (equal (lookup-equal-list l (cons (cons x v) (key-rem x a)))
                  (lookup-equal-list l a)))
  :induct (len l)
  :enable lookup-equal-list)

(defrule key-lookup-of-acons-rem
  (implies (not (equal y x))
           (equal (lookup-equal y (cons (cons x v) (key-rem x a)))
                  (lookup-equal y a)))
  :do-not-induct t
  :use (:instance key-lookup-equal-of-key-rem)
  :enable lookup-equal)))

(defrule hpos-c-lc-to-scalar-bits-sound-any
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
                              (key-rem (mv-nth 2 (hpos-h2s-wires vs)) asgx))))
        (:instance key-lel-of-acons-rem
                   (x (mv-nth 2 (hpos-h2s-wires vs)))
                   (v (hpos-lc-eval h asgx (base-prime)))
                   (l (mv-nth 0 (hpos-h2s-wires vs)))
                   (a asgx))))

(defrule hpos-c-hash-to-scalar-sound-any
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
  :disable (hpos-c-lc-to-scalar-bits-sound-any hpos-c-poseidon-hash-many-1-sound
            hpos-lc-eval-decomp hpos-c-lc-to-scalar-bits-asg)
  :use ((:instance hpos-c-poseidon-hash-many-1-sound)
        (:instance hpos-c-lc-to-scalar-bits-sound-any
                   (h (car (mv-nth 0 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))
                   (vs (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg)))
                   (asg (mv-nth 3 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))))

(defmacro key-h2s-hyps-any ()
  '(and (hpos-aleo-rate-p rate)
        (symbolp u)
        (symbolp x)
        (not (equal u x))
        (symbol-listp bs)
        (symbol-listp rs)
        (not (member-equal x bs))
        (not (member-equal x rs))
        (equal (len bs) (integer-length (base-prime)))
        (equal (len rs) (bits-lt-prime-rlen (base-prime)))
        (r1cs::r1cs-valuationp asgx (base-prime))
        (r1cs::valuation-binds-allp asgx bs)
        (r1cs::valuation-binds-allp asgx rs)
        (r1cs::valuation-bindsp asgx u)
        (equal (lookup-equal u asgx) 1)
        (r1cs::r1cs-constraints-holdp cs asgx (base-prime))))

(defrule key-h2s-sound-any
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar rate xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many rate xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime))))
    (implies (key-h2s-hyps-any)
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (curve-hash-to-scalar-psd rate ins)))))
  :do-not-induct t
  :enable key-curve-hash-to-scalar-psd-is-mod
  :disable hpos-c-hash-to-scalar-sound-any
  :use (hpos-c-hash-to-scalar-sound-any
        (:instance int-mulpow-lebits=>nat-take-nthcdr
                   (h 250)
                   (b (lookup-equal-list
                       (mv-nth 0 (hpos-h2s-wires
                                  (mv-nth 2 (hpos-c-poseidon-hash-many rate xs 1 vs asg))))
                       asgx)))))

(defrule key-h2s-psd4-sound-any
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar 4 xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many 4 xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime)))
       (sk (lebits=>nat (take 250 (lookup-equal-list bs asgx)))))
    (implies (let ((rate 4)) (key-h2s-hyps-any))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal sk (aleo-hash-to-scalar-psd4-funspec ins))
                  (equal sk (values-hash-to-scalar-psd4 ins)))))
  :do-not-induct t
  :enable (aleo-hash-to-scalar-psd4-funspec key-values-hash-to-scalar-psd4-is-mod
           key-curve-hash-to-scalar-psd-is-mod hpos-aleo-rate-p)
  :disable key-h2s-sound-any
  :use ((:instance key-h2s-sound-any (rate 4))
        hpos-primep-of-base))

(defrule key-h2s-psd8-sound-any
  (b* (((mv bits cs & &) (hpos-c-hash-to-scalar 8 xs u vs asg))
       ((mv & & vs1 &) (hpos-c-poseidon-hash-many 8 xs 1 vs asg))
       ((mv bs rs x &) (hpos-h2s-wires vs1))
       (ins (hpos-lc-eval-list xs asgx (base-prime))))
    (implies (let ((rate 8)) (key-h2s-hyps-any))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asgx)))
                         (aleo-hash-to-scalar-psd8-funspec ins)))))
  :do-not-induct t
  :enable (aleo-hash-to-scalar-psd8-funspec hpos-aleo-rate-p)
  :disable key-h2s-sound-any
  :use (:instance key-h2s-sound-any (rate 8)))

(local
 (progn
(defrule key-fieldp-of-lookup-any
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg v))
           (equal (mod (ifix (lookup-equal v asg)) (base-prime))
                  (lookup-equal v asg)))
  :use (:instance r1cs::fep-of-lookup-equal (var v) (valuation asg)
                  (prime (base-prime)))
  :enable pfield::fep)

(defrule key-eval-of-two-vars-any
  (implies (and (symbolp px) (symbolp rx)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg px)
                (r1cs::valuation-bindsp asg rx))
           (equal (hpos-lc-eval-list (list (hpos-lc-var px) (hpos-lc-var rx))
                                     asg (base-prime))
                  (list (lookup-equal px asg) (lookup-equal rx asg))))
  :enable hpos-lc-eval-list)))

(defrule key-ck-from-sound-any
  (b* (((mv bits cs & &) (key-ck-from-gadget px rx u vs asg))
       ((mv bs rs x &) (key-ck-from-wires px rx vs asg))
       (pk (ecurve::point-finite (lookup-equal px asgx) (lookup-equal py asgx)))
       (pr (ecurve::point-finite (lookup-equal rx asgx) (lookup-equal ry asgx))))
    (implies (and (symbolp px) (symbolp rx)
                  (r1cs::valuation-bindsp asgx px)
                  (r1cs::valuation-bindsp asgx rx)
                  (ecurve::edwards-bls12-pointp pk)
                  (ecurve::edwards-bls12-pointp pr)
                  (let ((rate 4)) (key-h2s-hyps-any)))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asgx))
                  (equal (list pk pr (key-sk-of-wires bs asgx))
                         (compute-key-from-funspec pk pr)))))
  :do-not-induct t
  :enable (key-ck-from-gadget key-ck-from-wires key-sk-of-wires key-eval-of-two-vars-any
           compute-key-from-funspec)
  :disable (key-h2s-psd4-sound key-h2s-sound hpos-c-hash-to-scalar-sound
            key-h2s-psd4-sound-any key-h2s-sound-any hpos-c-hash-to-scalar-sound-any)
  :use (:instance key-h2s-psd4-sound-any
                  (xs (list (hpos-lc-var px) (hpos-lc-var rx)))))
