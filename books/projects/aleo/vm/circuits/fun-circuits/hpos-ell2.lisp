; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Elligator2::encode on a linear combination, with witness generation, for
; Poseidon::hash_to_group.
;
; The constraints are hped-elligator2-gadget (hped-elligator2.lisp) with the
; input linear combination substituted for its input variable
; (hpos-cs-subst).  The next 1041 fresh variables are: a placeholder for the
; substitution (it occurs in no constraint; the witness binds it to the value
; of the input), then the
; 33 named wires of hped-ell2-w, then 251 pairs (square, product) for the
; square-and-multiply of the Legendre power, then the 253 bits of the square
; root and the 252 range-check wires.  The product wire of a pair is unused
; (occurs in no constraint) when its exponent bit is 0; snarkVM allocates no
; variable there.  The witness is the canonical one of
; hped-elligator2-gadget-complete.  U is the public unit wire.

(in-package "ALEOVM")

(include-book "hpos-ell2-wit")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Points as pairs of variables.

(defund hpos-pt-eval (pt asg)
  (declare (xargs :verify-guards nil))
  (ecurve::point-finite (lookup-equal (car pt) asg) (lookup-equal (cdr pt) asg)))

(defund hpos-pt-boundp (pt asg)
  (declare (xargs :verify-guards nil))
  (and (symbolp (car pt))
       (symbolp (cdr pt))
       (r1cs::valuation-bindsp asg (car pt))
       (r1cs::valuation-bindsp asg (cdr pt))))

(defrule hpos-pt-boundp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (hpos-pt-boundp pt old))
           (hpos-pt-boundp pt new))
  :enable hpos-pt-boundp)

(defrule hpos-pt-eval-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (hpos-pt-boundp pt old))
           (equal (hpos-pt-eval pt new)
                  (hpos-pt-eval pt old)))
  :enable (hpos-pt-eval hpos-pt-boundp r1cs::valuation-bindsp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assignments.

(defrule hpos-dot-product-of-acons-same
  (implies (equal (lookup-equal x a) v)
           (equal (r1cs::dot-product sv (cons (cons x v) a) p)
                  (r1cs::dot-product sv a p)))
  :induct (len sv)
  :enable (r1cs::dot-product lookup-equal))

(defrule hpos-holdp-of-acons-same
  (implies (equal (lookup-equal x a) v)
           (equal (r1cs::r1cs-constraints-holdp cs (cons (cons x v) a) p)
                  (r1cs::r1cs-constraints-holdp cs a p)))
  :induct (len cs)
  :enable (r1cs::r1cs-constraints-holdp r1cs::r1cs-constraint-holdsp))

(defund hpos-rem (x a)
  (declare (xargs :verify-guards nil))
  (cond ((atom a) nil)
        ((equal (caar a) x) (hpos-rem x (cdr a)))
        (t (cons (car a) (hpos-rem x (cdr a))))))

(defrule hpos-lookup-equal-of-hpos-rem
  (equal (lookup-equal y (hpos-rem x a))
         (if (equal y x) nil (lookup-equal y a)))
  :enable (hpos-rem lookup-equal))

(defrule hpos-dot-product-of-acons-hpos-rem
  (equal (r1cs::dot-product sv (cons (cons x v) (hpos-rem x a)) p)
         (r1cs::dot-product sv (cons (cons x v) a) p))
  :induct (len sv)
  :enable (r1cs::dot-product lookup-equal))

(defrule hpos-holdp-of-acons-hpos-rem
  (equal (r1cs::r1cs-constraints-holdp cs (cons (cons x v) (hpos-rem x a)) p)
         (r1cs::r1cs-constraints-holdp cs (cons (cons x v) a) p))
  :induct (len cs)
  :enable (r1cs::r1cs-constraints-holdp r1cs::r1cs-constraint-holdsp))

(defrulel hpos-member-strip-cars-of-hpos-rem
  (iff (member-equal y (strip-cars (hpos-rem x a)))
       (and (not (equal y x)) (member-equal y (strip-cars a))))
  :enable hpos-rem)

(defrulel hpos-no-dups-strip-cars-of-hpos-rem
  (implies (no-duplicatesp-equal (strip-cars a))
           (no-duplicatesp-equal (strip-cars (hpos-rem x a))))
  :enable hpos-rem)

(defrulel hpos-r1cs-valuationp-of-hpos-rem
  (implies (r1cs::r1cs-valuationp a p)
           (r1cs::r1cs-valuationp (hpos-rem x a) p))
  :enable (hpos-rem r1cs::r1cs-valuationp))

(defrule hpos-valuation-bindsp-of-acons-hpos-rem
  (iff (r1cs::valuation-bindsp (cons (cons x v) (hpos-rem x a)) y)
       (or (equal y x) (r1cs::valuation-bindsp a y)))
  :enable r1cs::valuation-bindsp)

(defrule hpos-valuation-binds-allp-of-acons-hpos-rem
  (implies (r1cs::valuation-binds-allp a l)
           (r1cs::valuation-binds-allp (cons (cons x v) (hpos-rem x a)) l))
  :induct (len l)
  :enable r1cs::valuation-binds-allp)

(defrule hpos-r1cs-valuationp-of-acons-hpos-rem
  (implies (and (r1cs::r1cs-valuationp a p)
                (symbolp x)
                (pfield::fep v p))
           (r1cs::r1cs-valuationp (cons (cons x v) (hpos-rem x a)) p))
  :use (:instance hpos-r1cs-valuationp-of-acons (a (hpos-rem x a)))
  :disable hpos-r1cs-valuationp-of-acons
  :enable r1cs::valuation-bindsp)

(defrule hpos-lookup-equal-list-when-ext-p
  (implies (and (hpos-ext-p old new)
                (no-duplicatesp-equal (strip-cars new))
                (r1cs::valuation-binds-allp old l))
           (equal (lookup-equal-list l new)
                  (lookup-equal-list l old)))
  :induct (len l)
  :enable (lookup-equal-list r1cs::valuation-binds-allp r1cs::valuation-bindsp))

(defrule hpos-valuation-binds-allp-when-ext-p
  (implies (and (hpos-ext-p old new)
                (r1cs::valuation-binds-allp old l))
           (r1cs::valuation-binds-allp new l))
  :induct (len l)
  :enable r1cs::valuation-binds-allp)

(defrule hpos-lookup-equal-list-of-take
  (implies (<= (nfix n) (len l))
           (equal (lookup-equal-list (take n l) a)
                  (take n (lookup-equal-list l a))))
  :induct (take n l)
  :enable (lookup-equal-list take))

(defrule hpos-lookup-equal-list-of-nthcdr
  (equal (lookup-equal-list (nthcdr n l) a)
         (nthcdr n (lookup-equal-list l a)))
  :induct (nthcdr n l)
  :enable (lookup-equal-list nthcdr))

(defrule hpos-lookup-equal-list-of-cdr
  (equal (lookup-equal-list (cdr l) a)
         (cdr (lookup-equal-list l a)))
  :enable lookup-equal-list)

(defrule hpos-take-of-append-len
  (implies (and (equal n (len x)) (true-listp x))
           (equal (take n (append x y)) x))
  :induct (len x))

(defrule hpos-nthcdr-of-append-len
  (implies (equal n (len x))
           (equal (nthcdr n (append x y)) y))
  :induct (nthcdr n x)
  :enable nthcdr)

(defrule hpos-valuation-binds-allp-of-take
  (implies (and (r1cs::valuation-binds-allp a l)
                (<= (nfix n) (len l)))
           (r1cs::valuation-binds-allp a (take n l)))
  :induct (take n l)
  :enable (r1cs::valuation-binds-allp take))

(defrule hpos-valuation-binds-allp-of-nthcdr
  (implies (r1cs::valuation-binds-allp a l)
           (r1cs::valuation-binds-allp a (nthcdr n l)))
  :induct (nthcdr n l)
  :enable (r1cs::valuation-binds-allp nthcdr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The gadget instance.

(defund hpos-ell2-wires (vs)
  (declare (xargs :verify-guards nil))
  (b* ((blk (take *hpos-ell2-nblock* vs))
       (ws (cdr blk))
       (ws1 (nthcdr 33 ws))
       (ws2 (nthcdr 502 ws1))
       (ws3 (nthcdr 253 ws2)))
    (mv (car blk) (take 33 ws) (take 502 ws1) (take 253 ws2) ws3)))

(defund hpos-ell2-vals (r)
  (declare (xargs :verify-guards nil))
  (b* ((q (ecurve::edwards-bls12-q))
       (gv (hpos-ell2-gval r))
       (bv (field-bits-le (hpos-ell2-root r))))
    (cons r (append (hpos-ell2-wvals r)
                    (append (hpos-pw-vals (hped-ell2-exp-bits) gv gv q)
                            (append bv
                                    (fb-bits-lte-const-witness
                                     bv (acl2::nat=>lebits* (1- q)))))))))

(defund hpos-ell2-gcs (u vs)
  (declare (xargs :verify-guards nil))
  (b* (((mv x w pwf bits rs) (hpos-ell2-wires vs)))
    (hped-ell2-gadget x w (hpos-pairs pwf) bits rs u)))

(defund hpos-ell2-pt (vs)
  (declare (xargs :verify-guards nil))
  (b* (((mv & w & & &) (hpos-ell2-wires vs)))
    (cons (nth 31 w) (nth 32 w))))

(defund hpos-c-ell2 (h u vs asg)
  (declare (xargs :verify-guards nil))
  (b* ((r (hpos-lc-eval h asg primes::*bls12-377-scalar-field-prime*)))
    (mv (hpos-ell2-pt vs)
        (hpos-cs-subst (hpos-ell2-gcs u vs) (car vs) h)
        (nthcdr *hpos-ell2-nblock* vs)
        (append (pairlis$ (take *hpos-ell2-nblock* vs) (hpos-ell2-vals r)) asg))))

(defrule hpos-len-of-ell2-range-witness
  (equal (len (fb-bits-lte-const-witness
               (field-bits-le x)
               (acl2::nat=>lebits* (+ -1 (ecurve::edwards-bls12-q)))))
         252)
  :use (:instance len-of-fb-bits-lte-const-witness
                  (xs (field-bits-le x))
                  (cs (acl2::nat=>lebits* (+ -1 (ecurve::edwards-bls12-q)))))
  :in-theory '(len-of-field-bits-le (:e base-field-size-in-bits) (:e len)
               (:e acl2::nat=>lebits*) (:e ecurve::edwards-bls12-q) (:e binary-+)
               (:e member-equal) (:e last) (:e car) (:e bits-lte-const-rlen) (:e equal)))

(defrule hpos-bit-listp-of-ell2-range-witness
  (bit-listp (fb-bits-lte-const-witness
              (field-bits-le x)
              (acl2::nat=>lebits* (+ -1 (ecurve::edwards-bls12-q)))))
  :use (:instance bit-listp-of-fb-bits-lte-const-witness
                  (xs (field-bits-le x))
                  (cs (acl2::nat=>lebits* (+ -1 (ecurve::edwards-bls12-q)))))
  :in-theory '(len-of-field-bits-le bit-listp-of-field-bits-le
               (:e base-field-size-in-bits) (:e len) (:e bit-listp)
               (:e acl2::nat=>lebits*) (:e ecurve::edwards-bls12-q) (:e binary-+)
               (:e member-equal) (:e last) (:e car) (:e equal)))

(defrulel hpos-fe-listp-when-bit-listp-2
  (implies (and (bit-listp bits) (integerp p) (< 1 p))
           (pfield::fe-listp bits p))
  :induct (len bits)
  :enable (pfield::fe-listp bit-listp pfield::fep))

(defrule hpos-len-of-hpos-ell2-vals
  (equal (len (hpos-ell2-vals r)) *hpos-ell2-nblock*)
  :enable hpos-ell2-vals)

(defrule hpos-true-listp-of-hpos-ell2-vals
  (true-listp (hpos-ell2-vals r))
  :enable hpos-ell2-vals)

(defrulel hpos-valuationp-q-when-p
  (equal (r1cs::r1cs-valuationp a (ecurve::edwards-bls12-q))
         (r1cs::r1cs-valuationp a primes::*bls12-377-scalar-field-prime*))
  :in-theory '((:e ecurve::edwards-bls12-q)))

(defrulel hpos-fe-listp-q-when-p
  (equal (pfield::fe-listp l (ecurve::edwards-bls12-q))
         (pfield::fe-listp l primes::*bls12-377-scalar-field-prime*))
  :in-theory '((:e ecurve::edwards-bls12-q)))

(defrule hpos-fe-listp-of-hpos-ell2-vals
  (implies (pfield::fep r primes::*bls12-377-scalar-field-prime*)
           (pfield::fe-listp (hpos-ell2-vals r) primes::*bls12-377-scalar-field-prime*))
  :enable (hpos-ell2-vals pfield::fe-listp-of-append)
  :use (hpos-fe-listp-of-hpos-ell2-wvals
        (:instance hpos-fe-listp-of-hpos-pw-vals
                   (cs (hped-ell2-exp-bits))
                   (gv (hpos-ell2-gval r))
                   (av (hpos-ell2-gval r))
                   (p (ecurve::edwards-bls12-q))))
  :disable (hpos-fe-listp-of-hpos-ell2-wvals hpos-fe-listp-of-hpos-pw-vals
            (:e hped-ell2-exp-bits)))

(defund hpos-pw-symsp (pw)
  (declare (xargs :verify-guards nil))
  (if (endp pw)
      t
    (and (symbolp (first (car pw)))
         (symbolp (second (car pw)))
         (hpos-pw-symsp (cdr pw)))))

(defrule hpos-pw-symsp-of-hpos-pairs
  (implies (symbol-listp l)
           (hpos-pw-symsp (hpos-pairs l)))
  :induct (hpos-pairs l)
  :enable (hpos-pairs hpos-pw-symsp))

(defrule hpos-r1cs-constraint-listp-of-hped-pow-gadget
  (implies (and (r1cs::sparse-vectorp g)
                (r1cs::sparse-vectorp acc)
                (hpos-pw-symsp pw))
           (r1cs::r1cs-constraint-listp (hped-pow-gadget g cs pw acc)))
  :induct (hped-pow-gadget g cs pw acc)
  :enable (hped-pow-gadget hped-c hpos-pw-symsp))

(defrule hpos-sparse-vectorp-of-hped-pow-out
  (implies (and (r1cs::sparse-vectorp acc)
                (hpos-pw-symsp pw))
           (r1cs::sparse-vectorp (hped-pow-out cs pw acc)))
  :induct (hped-pow-out cs pw acc)
  :enable (hped-pow-out hpos-pw-symsp))

(defrulel hpos-symbolp-of-nth-when-symbol-listp
  (implies (symbol-listp l)
           (symbolp (nth n l)))
  :enable nth)

(defrule hpos-sparse-vectorp-of-hped-ell2-g-lc
  (implies (symbol-listp w)
           (r1cs::sparse-vectorp (hped-ell2-g-lc w)))
  :enable hped-ell2-g-lc)

(defrulel hpos-bits-lt-prime-rlen-of-q
  (equal (bits-lt-prime-rlen (ecurve::edwards-bls12-q)) 252)
  :in-theory '((:e bits-lt-prime-rlen) (:e ecurve::edwards-bls12-q)))

(defrulel hpos-integer-length-of-q
  (equal (integer-length (ecurve::edwards-bls12-q)) 253)
  :in-theory '((:e integer-length) (:e ecurve::edwards-bls12-q)))

(defrule hpos-r1cs-constraint-listp-of-hped-ell2-gadget
  (implies (and (symbolp in)
                (symbol-listp w)
                (hpos-pw-symsp pw)
                (symbol-listp bits)
                (equal (len bits) 253)
                (symbol-listp rs)
                (equal (len rs) 252)
                (symbolp u))
           (r1cs::r1cs-constraint-listp (hped-ell2-gadget in w pw bits rs u)))
  :enable (hped-ell2-gadget hped-c hped-ell2-e-lc)
  :disable ((:e hped-ell2-exp-bits))
  :use ((:instance r1cs-constraint-listp-of-fb-field-write-bits-le-gadget
                   (x (nth 10 w)) (p (ecurve::edwards-bls12-q)))
        (:instance r1cs-constraint-listp-of-crv-group-enforce-on-curve-gadget
                   (x (nth 18 w)) (y (nth 20 w)) (x2 (nth 21 w)) (y2 (nth 22 w))
                   (p (ecurve::edwards-bls12-q)))
        (:instance r1cs-constraint-listp-of-crv-group-mul-by-cofactor-gadget
                   (x (nth 18 w)) (y (nth 20 w))
                   (xy1 (nth 23 w)) (x21 (nth 24 w)) (y21 (nth 25 w))
                   (x4 (nth 26 w)) (y4 (nth 27 w))
                   (xy2 (nth 28 w)) (x22 (nth 29 w)) (y22 (nth 30 w))
                   (x3 (nth 31 w)) (y3 (nth 32 w))
                   (p (ecurve::edwards-bls12-q)))))

(defrule hpos-symbol-listp-of-take
  (implies (symbol-listp l) (symbol-listp (take n l)))
  :induct (take n l)
  :enable (take repeat))

(defrule hpos-symbol-listp-of-nthcdr
  (implies (symbol-listp l) (symbol-listp (nthcdr n l)))
  :enable nthcdr)

(defrule hpos-len-of-nthcdr
  (equal (len (nthcdr n l)) (nfix (- (len l) (nfix n))))
  :induct (nthcdr n l)
  :enable nthcdr)

(defrulel hpos-len-of-cdr-nthcdr
  (equal (len (cdr (nthcdr n l))) (nfix (- (len l) (+ 1 (nfix n)))))
  :induct (nthcdr n l)
  :enable nthcdr)

(defrulel hpos-ell2-blk-facts
  (implies (and (symbol-listp l) (equal (len l) 1041))
           (b* ((ws (cdr l))
                (ws1 (nthcdr 33 ws))
                (ws2 (nthcdr 502 ws1))
                (ws3 (nthcdr 253 ws2)))
             (and (symbolp (car l))
                  (symbol-listp (take 33 ws))
                  (equal (len (take 33 ws)) 33)
                  (symbol-listp (take 502 ws1))
                  (equal (len (take 502 ws1)) 502)
                  (symbol-listp (take 253 ws2))
                  (equal (len (take 253 ws2)) 253)
                  (symbol-listp ws3)
                  (equal (len ws3) 252))))
  :rule-classes nil)

(defrulel hpos-len-of-take-1041
  (implies (<= 1041 (len vs))
           (equal (len (take 1041 vs)) 1041)))

(defrule hpos-ell2-wires-facts
  (implies (and (symbol-listp (take *hpos-ell2-nblock* vs))
                (<= *hpos-ell2-nblock* (len vs)))
           (b* (((mv x w pwf bits rs) (hpos-ell2-wires vs)))
             (and (symbolp x)
                  (symbol-listp w)
                  (equal (len w) 33)
                  (symbol-listp pwf)
                  (equal (len pwf) 502)
                  (symbol-listp bits)
                  (equal (len bits) 253)
                  (symbol-listp rs)
                  (equal (len rs) 252))))
  :rule-classes nil
  :in-theory '(hpos-ell2-wires mv-nth car-cons cdr-cons (:e zp) (:e nfix)
               hpos-len-of-take-1041)
  :use (:instance hpos-ell2-blk-facts (l (take 1041 vs))))

(defrule hpos-r1cs-constraint-listp-of-hpos-ell2-gcs
  (implies (and (symbolp u)
                (symbol-listp (take *hpos-ell2-nblock* vs))
                (<= *hpos-ell2-nblock* (len vs)))
           (r1cs::r1cs-constraint-listp (hpos-ell2-gcs u vs)))
  :in-theory '(hpos-ell2-gcs hpos-r1cs-constraint-listp-of-hped-ell2-gadget
               hpos-pw-symsp-of-hpos-pairs)
  :use hpos-ell2-wires-facts)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The wire block.

(defrulel hpos-len-of-cdr-take-1041
  (implies (<= 1041 (len vs))
           (equal (len (cdr (take 1041 vs))) 1040)))

(defrule hpos-ell2-wires-binds
  (implies (and (r1cs::valuation-binds-allp a (cdr (take *hpos-ell2-nblock* vs)))
                (<= *hpos-ell2-nblock* (len vs)))
           (b* (((mv & w pwf bits rs) (hpos-ell2-wires vs)))
             (and (r1cs::valuation-binds-allp a w)
                  (r1cs::valuation-binds-allp a pwf)
                  (r1cs::valuation-binds-allp a bits)
                  (r1cs::valuation-binds-allp a rs))))
  :in-theory '(hpos-ell2-wires mv-nth car-cons cdr-cons (:e zp) (:e nfix) (:e <)
               (:e binary-+) (:e unary--) (:e len) nfix fix
               hpos-valuation-binds-allp-of-take hpos-valuation-binds-allp-of-nthcdr
               hpos-len-of-nthcdr hpos-len-of-cdr-take-1041))

(defrule hpos-ell2-wires-0
  (equal (mv-nth 0 (hpos-ell2-wires vs)) (car vs))
  :enable hpos-ell2-wires)

(defrulel hpos-member-nth
  (implies (< (nfix n) (len l))
           (member-equal (nth n l) l))
  :enable nth)

(defrulel hpos-member-of-take
  (implies (and (member-equal a (take n l))
                (<= (nfix n) (len l)))
           (member-equal a l))
  :induct (take n l)
  :enable take)

(defrule hpos-ell2-x-not-in-w
  (implies (and (no-duplicatesp-equal (take *hpos-ell2-nblock* vs))
                (<= *hpos-ell2-nblock* (len vs)))
           (b* (((mv x w & & &) (hpos-ell2-wires vs)))
             (and (not (equal (nth 31 w) x))
                  (not (equal (nth 32 w) x)))))
  :enable hpos-ell2-wires
  :disable (take hpos-member-nth hpos-member-of-take)
  :use ((:instance hpos-member-nth (n 31) (l (take 33 (cdr (take 1041 vs)))))
        (:instance hpos-member-nth (n 32) (l (take 33 (cdr (take 1041 vs)))))
        (:instance hpos-member-of-take (n 33) (l (cdr (take 1041 vs)))
                   (a (nth 31 (take 33 (cdr (take 1041 vs))))))
        (:instance hpos-member-of-take (n 33) (l (cdr (take 1041 vs)))
                   (a (nth 32 (take 33 (cdr (take 1041 vs))))))
        (:instance hpos-len-of-take-1041)))

(defund hpos-ell2-sound-hyps (u vs asgx)
  (declare (xargs :verify-guards nil))
  (b* ((blk (take *hpos-ell2-nblock* vs)))
    (and (symbol-listp blk)
         (no-duplicatesp-equal blk)
         (<= *hpos-ell2-nblock* (len vs))
         (symbolp u)
         (not (equal u (car blk)))
         (r1cs::r1cs-valuationp asgx primes::*bls12-377-scalar-field-prime*)
         (r1cs::valuation-binds-allp asgx (cdr blk))
         (r1cs::valuation-bindsp asgx u)
         (equal (lookup-equal u asgx) 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(defrulel hpos-ell2-sound-core
  (b* (((mv x w & & &) (hpos-ell2-wires vs))
       (a (cons (cons x v) (hpos-rem x asgx))))
    (implies (and (hpos-ell2-sound-hyps u vs asgx)
                  (pfield::fep v primes::*bls12-377-scalar-field-prime*)
                  (r1cs::r1cs-constraints-holdp (hpos-ell2-gcs u vs) a
                                                primes::*bls12-377-scalar-field-prime*))
             (and (hped-elligator2-encode-validp v)
                  (equal (ecurve::point-finite (lookup-equal (nth 31 w) asgx)
                                               (lookup-equal (nth 32 w) asgx))
                         (hped-elligator2-encode v)))))
  :do-not-induct t
  :enable (hpos-ell2-sound-hyps hpos-ell2-gcs)
  :disable (hped-elligator2-encode hped-elligator2-encode-validp)
  :use (hpos-ell2-wires-facts
        (:instance hpos-ell2-wires-binds (a asgx))
        hpos-ell2-x-not-in-w
        (:instance hped-elligator2-gadget-sound
                   (in (car vs))
                   (w (mv-nth 1 (hpos-ell2-wires vs)))
                   (pw (hpos-pairs (mv-nth 2 (hpos-ell2-wires vs))))
                   (bits (mv-nth 3 (hpos-ell2-wires vs)))
                   (rs (mv-nth 4 (hpos-ell2-wires vs)))
                   (p (base-prime))
                   (asg (cons (cons (car vs) v) (hpos-rem (car vs) asgx))))))

(defrule hpos-c-ell2-sound
  (b* (((mv pt cs & &) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (r (hpos-lc-eval h asgx p)))
    (implies (and (hpos-ell2-sound-hyps u vs asgx)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (hped-elligator2-encode-validp r)
                  (equal (hpos-pt-eval pt asgx)
                         (hped-elligator2-encode r)))))
  :do-not-induct t
  :enable (hpos-c-ell2 hpos-ell2-pt hpos-pt-eval hpos-ell2-sound-hyps)
  :disable (hped-elligator2-encode hped-elligator2-encode-validp
            hpos-holdp-of-hpos-cs-subst hpos-ell2-sound-core)
  :use (hpos-ell2-wires-facts
        (:instance hpos-ell2-sound-core
                   (v (hpos-lc-eval h asgx primes::*bls12-377-scalar-field-prime*)))
        (:instance hpos-holdp-of-hpos-cs-subst
                   (p primes::*bls12-377-scalar-field-prime*)
                   (cs (hpos-ell2-gcs u vs))
                   (x (car vs))
                   (lc h)
                   (asg asgx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defrulel hpos-true-listp-when-bit-listp
  (implies (bit-listp l) (true-listp l))
  :induct (len l)
  :enable bit-listp)

(defrulel hpos-len-of-field-bits-le-253
  (equal (len (field-bits-le x)) 253)
  :in-theory '(len-of-field-bits-le (:e base-field-size-in-bits)))

(defrulel hpos-lookup-car
  (implies (consp l)
           (equal (lookup-equal (car l) a)
                  (car (lookup-equal-list l a))))
  :enable lookup-equal-list)

(defrulel hpos-consp-of-take-1041
  (implies (<= 1041 (len vs))
           (and (consp (take 1041 vs))
                (equal (car (take 1041 vs)) (car vs)))))

(defrulel hpos-len-of-cdr-1041
  (implies (equal (len l) 1041)
           (equal (len (cdr l)) 1040)))

(defrulel hpos-consp-when-len-1041
  (implies (equal (len l) 1041) (consp l)))

(defrulel hpos-ell2-blk-vals
  (implies (and (equal (lookup-equal-list l a) (hpos-ell2-vals r))
                (equal (len l) 1041))
           (b* ((ws (cdr l))
                (ws1 (nthcdr 33 ws))
                (ws2 (nthcdr 502 ws1))
                (ws3 (nthcdr 253 ws2))
                (q (ecurve::edwards-bls12-q))
                (gv (hpos-ell2-gval r))
                (bv (field-bits-le (hpos-ell2-root r))))
             (and (equal (lookup-equal (car l) a) r)
                  (equal (lookup-equal-list (take 33 ws) a) (hpos-ell2-wvals r))
                  (equal (lookup-equal-list (take 502 ws1) a)
                         (hpos-pw-vals (hped-ell2-exp-bits) gv gv q))
                  (equal (lookup-equal-list (take 253 ws2) a) bv)
                  (equal (lookup-equal-list ws3 a)
                         (fb-bits-lte-const-witness
                          bv (acl2::nat=>lebits* (1- q)))))))
  :rule-classes nil
  :in-theory '(hpos-ell2-vals car-cons cdr-cons
               (:e zp) (:e nfix) (:e <) (:e binary-+) (:e binary-*) (:e unary--) nfix fix
               hpos-lookup-equal-list-of-take hpos-lookup-equal-list-of-nthcdr
               hpos-lookup-equal-list-of-cdr hpos-take-of-append-len
               hpos-nthcdr-of-append-len hpos-len-of-nthcdr hpos-len-of-cdr-1041
               hpos-lookup-car hpos-consp-when-len-1041
               hpos-len-of-hpos-ell2-wvals hpos-true-listp-of-hpos-ell2-wvals
               hpos-len-of-hpos-pw-vals hpos-true-listp-of-hpos-pw-vals
               hpos-len-of-hped-ell2-exp-bits hpos-len-of-field-bits-le-253
               hpos-true-listp-when-bit-listp bit-listp-of-field-bits-le
               hpos-len-of-ell2-range-witness))

(defrule hpos-ell2-wires-vals
  (implies (and (equal (lookup-equal-list (take *hpos-ell2-nblock* vs) a)
                       (hpos-ell2-vals r))
                (<= *hpos-ell2-nblock* (len vs)))
           (b* (((mv & w pwf bits rs) (hpos-ell2-wires vs))
                (q (ecurve::edwards-bls12-q))
                (gv (hpos-ell2-gval r))
                (bv (field-bits-le (hpos-ell2-root r))))
             (and (equal (lookup-equal (car vs) a) r)
                  (equal (lookup-equal-list w a) (hpos-ell2-wvals r))
                  (equal (lookup-equal-list pwf a)
                         (hpos-pw-vals (hped-ell2-exp-bits) gv gv q))
                  (equal (lookup-equal-list bits a) bv)
                  (equal (lookup-equal-list rs a)
                         (fb-bits-lte-const-witness
                          bv (acl2::nat=>lebits* (1- q)))))))
  :in-theory '(hpos-ell2-wires mv-nth car-cons cdr-cons (:e zp) hpos-len-of-take-1041
               hpos-consp-of-take-1041)
  :use (:instance hpos-ell2-blk-vals (l (take 1041 vs))))

(defrulel hpos-valuation-binds-allp-of-cdr
  (implies (r1cs::valuation-binds-allp a l)
           (r1cs::valuation-binds-allp a (cdr l)))
  :enable r1cs::valuation-binds-allp)

(defrulel hpos-valuation-bindsp-of-car
  (implies (and (r1cs::valuation-binds-allp a l) (consp l))
           (r1cs::valuation-bindsp a (car l)))
  :enable r1cs::valuation-binds-allp)

(defrulel hpos-ell2-complete-wires
  (b* ((q (ecurve::edwards-bls12-q))
       (gv (hpos-ell2-gval r))
       (bv (field-bits-le (hpos-ell2-root r))))
    (implies (and (symbolp x)
                  (symbol-listp w)
                  (equal (len w) 33)
                  (symbol-listp pwf)
                  (equal (len pwf) 502)
                  (symbol-listp bits)
                  (equal (len bits) 253)
                  (symbol-listp rs)
                  (equal (len rs) 252)
                  (symbolp u)
                  (r1cs::r1cs-valuationp f primes::*bls12-377-scalar-field-prime*)
                  (r1cs::valuation-bindsp f x)
                  (r1cs::valuation-binds-allp f w)
                  (r1cs::valuation-binds-allp f pwf)
                  (r1cs::valuation-binds-allp f bits)
                  (r1cs::valuation-binds-allp f rs)
                  (r1cs::valuation-bindsp f u)
                  (equal (lookup-equal u f) 1)
                  (equal (lookup-equal x f) r)
                  (equal (lookup-equal-list w f) (hpos-ell2-wvals r))
                  (equal (lookup-equal-list pwf f)
                         (hpos-pw-vals (hped-ell2-exp-bits) gv gv q))
                  (equal (lookup-equal-list bits f) bv)
                  (equal (lookup-equal-list rs f)
                         (fb-bits-lte-const-witness bv (acl2::nat=>lebits* (1- q))))
                  (hped-elligator2-encode-validp r))
             (r1cs::r1cs-constraints-holdp (hped-ell2-gadget x w (hpos-pairs pwf) bits rs u)
                                           f primes::*bls12-377-scalar-field-prime*)))
  :do-not-induct t
  :in-theory (union-theories '(hpos-ell2-wires-okp hpos-valuationp-q-when-p
                               hpos-primep-of-edwards-bls12-q
                               hpos-hped-pw-boundp-of-hpos-pairs
                               hpos-len-of-hped-ell2-exp-bits
                               (:e base-prime) (:e integer-length) (:e bits-lt-prime-rlen)
                               (:e binary-*) (:e binary-+) (:e unary--))
                             (theory 'minimal-theory))
  :use ((:instance hpos-ell2-g-lc-value (asg f))
        (:instance hpos-hped-pw-canonp-of-hpos-pw-vals
                   (p (ecurve::edwards-bls12-q)) (asg f)
                   (cs (hped-ell2-exp-bits))
                   (gv (hpos-ell2-gval r)) (av (hpos-ell2-gval r))
                   (g (hped-ell2-g-lc w)) (acc (hped-ell2-g-lc w)))
        (:instance hpos-ell2-gadget-complete-wit
                   (in x) (pw (hpos-pairs pwf)) (p (base-prime)) (asg f))))

(defrule hpos-ell2-complete-core
  (b* ((blk (take *hpos-ell2-nblock* vs)))
    (implies (and (symbol-listp blk)
                  (<= *hpos-ell2-nblock* (len vs))
                  (symbolp u)
                  (r1cs::r1cs-valuationp f primes::*bls12-377-scalar-field-prime*)
                  (r1cs::valuation-binds-allp f blk)
                  (equal (lookup-equal-list blk f) (hpos-ell2-vals r))
                  (r1cs::valuation-bindsp f u)
                  (equal (lookup-equal u f) 1)
                  (hped-elligator2-encode-validp r))
             (r1cs::r1cs-constraints-holdp (hpos-ell2-gcs u vs) f
                                           primes::*bls12-377-scalar-field-prime*)))
  :do-not-induct t
  :in-theory '(hpos-ell2-gcs hpos-ell2-wires-0 hpos-consp-of-take-1041)
  :use (hpos-ell2-wires-facts
        (:instance hpos-ell2-wires-vals (a f))
        (:instance hpos-ell2-wires-binds (a f))
        (:instance hpos-valuation-binds-allp-of-cdr (a f) (l (take 1041 vs)))
        (:instance hpos-valuation-bindsp-of-car (a f) (l (take 1041 vs)))
        (:instance hpos-ell2-complete-wires
                   (x (car vs))
                   (w (mv-nth 1 (hpos-ell2-wires vs)))
                   (pwf (mv-nth 2 (hpos-ell2-wires vs)))
                   (bits (mv-nth 3 (hpos-ell2-wires vs)))
                   (rs (mv-nth 4 (hpos-ell2-wires vs))))))

(defrule hpos-no-dups-of-take
  (implies (and (no-duplicatesp-equal l) (<= (nfix n) (len l)))
           (no-duplicatesp-equal (take n l)))
  :induct (take n l)
  :enable (take no-duplicatesp-equal)
  :prep-lemmas
  ((defrule hpos-member-of-take-2
     (implies (and (member-equal a (take n l)) (<= (nfix n) (len l)))
              (member-equal a l))
     :induct (take n l)
     :enable take)))

(defrule hpos-intersectp-of-take
  (implies (and (not (intersectp-equal l k)) (<= (nfix n) (len l)))
           (not (intersectp-equal (take n l) k)))
  :induct (take n l)
  :enable (take intersectp-equal))

(defrulel hpos-not-member-when-not-intersectp
  (implies (and (not (intersectp-equal l k)) (member-equal a k))
           (not (member-equal a l)))
  :enable intersectp-equal)

(defrule hpos-ell2-blk-supply
  (implies (and (hpos-supply-okp vs asg)
                (<= *hpos-ell2-nblock* (len vs)))
           (b* ((blk (take *hpos-ell2-nblock* vs)))
             (and (symbol-listp blk)
                  (no-duplicatesp-equal blk)
                  (not (intersectp-equal blk (strip-cars asg))))))
  :rule-classes nil
  :enable hpos-supply-okp)

(defruledl hpos-c-ell2-asg-facts
  (b* (((mv & & & a2) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (r (hpos-lc-eval h asg p))
       (blk (take *hpos-ell2-nblock* vs)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs)))
             (and (r1cs::r1cs-valuationp a2 p)
                  (hpos-ext-p asg a2)
                  (equal (lookup-equal-list blk a2) (hpos-ell2-vals r))
                  (r1cs::valuation-binds-allp a2 blk))))
  :do-not-induct t
  :enable hpos-c-ell2
  :disable (take hpos-lc-eval-decomp hpos-lookup-equal-list-of-take)
  :use (hpos-ell2-blk-supply
        (:instance hpos-len-of-take-1041)))

(defrule hpos-member-strip-cars-when-bindsp
  (implies (r1cs::valuation-bindsp a v)
           (member-equal v (strip-cars a)))
  :enable r1cs::valuation-bindsp)

(defruledl hpos-ell2-at-f
  (b* ((p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp a2 p)
                  (r1cs::r1cs-valuationp f p)
                  (hpos-ext-p asg a2)
                  (hpos-ext-p a2 f)
                  (equal (lookup-equal-list blk a2) vals)
                  (r1cs::valuation-binds-allp a2 blk)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hpos-lc-boundp h asg))
             (and (equal (lookup-equal-list blk f) vals)
                  (r1cs::valuation-binds-allp f blk)
                  (r1cs::valuation-bindsp f u)
                  (equal (lookup-equal u f) 1)
                  (equal (hpos-lc-eval h f p) (hpos-lc-eval h asg p)))))
  :do-not-induct t
  :in-theory '(hpos-no-duplicatesp-strip-cars-when-valuationp
               hpos-valuation-binds-allp-when-ext-p hpos-valuation-bindsp-when-ext-p
               hpos-ext-p-transitive hpos-member-strip-cars-when-bindsp)
  :use ((:instance hpos-lookup-equal-list-when-ext-p (old a2) (new f) (l blk))
        (:instance hpos-lookup-when-ext-p (old asg) (new a2) (v u))
        (:instance hpos-lookup-when-ext-p (old a2) (new f) (v u))
        (:instance hpos-lookup-when-ext-p (old asg) (new f) (v u))
        (:instance hpos-lc-eval-when-ext-p (old asg) (new f) (lc h)
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-ext-p-transitive (a asg) (b a2) (c f))))

(defrulel hpos-c-ell2-cs
  (equal (mv-nth 1 (hpos-c-ell2 h u vs asg))
         (hpos-cs-subst (hpos-ell2-gcs u vs) (car vs) h))
  :enable hpos-c-ell2)

(defrule hpos-c-ell2-complete-frame
  (b* (((mv & cs & a2) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hped-elligator2-encode-validp (hpos-lc-eval h asg p))
                  (hpos-ext-p a2 f)
                  (r1cs::r1cs-valuationp f p))
             (r1cs::r1cs-constraints-holdp cs f p)))
  :do-not-induct t
  :in-theory '(hpos-c-ell2-cs hpos-ell2-wires-0 (:e posp) acons)
  :use (hpos-c-ell2-asg-facts
        hpos-ell2-blk-supply
        hpos-ell2-wires-facts
        hpos-r1cs-constraint-listp-of-hpos-ell2-gcs
        (:instance hpos-ell2-at-f
                   (a2 (mv-nth 3 (hpos-c-ell2 h u vs asg)))
                   (blk (take 1041 vs))
                   (vals (hpos-ell2-vals
                          (hpos-lc-eval h asg primes::*bls12-377-scalar-field-prime*))))
        (:instance hpos-ell2-complete-core
                   (r (hpos-lc-eval h asg primes::*bls12-377-scalar-field-prime*)))
        (:instance hpos-ell2-wires-vals
                   (a f)
                   (r (hpos-lc-eval h asg primes::*bls12-377-scalar-field-prime*)))
        (:instance hpos-holdp-of-acons-same
                   (cs (hpos-ell2-gcs u vs)) (x (car vs)) (a f)
                   (v (hpos-lc-eval h asg primes::*bls12-377-scalar-field-prime*))
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-holdp-of-hpos-cs-subst
                   (p primes::*bls12-377-scalar-field-prime*)
                   (cs (hpos-ell2-gcs u vs)) (x (car vs)) (lc h) (asg f))))

(defrule hpos-member-of-nthcdr
  (implies (member-equal a (nthcdr n l))
           (member-equal a l))
  :induct (nthcdr n l)
  :enable nthcdr)

(defrule hpos-intersectp-of-cons-right-2
  (equal (intersectp-equal a (cons x k))
         (or (and (member-equal x a) t) (intersectp-equal a k)))
  :induct (len a)
  :enable intersectp-equal)

(defrule hpos-nthcdr-take-disjoint
  (implies (no-duplicatesp-equal l)
           (not (intersectp-equal (nthcdr n l) (take n l))))
  :induct (take n l)
  :enable (take nthcdr no-duplicatesp-equal intersectp-equal repeat)
  :prep-lemmas
  ((defrule hpos-intersectp-of-nil-right
     (not (intersectp-equal l nil))
     :enable intersectp-equal)))

(defrule hpos-no-dups-of-nthcdr
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (nthcdr n l)))
  :induct (nthcdr n l)
  :enable nthcdr)

(defrule hpos-intersectp-of-nthcdr
  (implies (not (intersectp-equal l k))
           (not (intersectp-equal (nthcdr n l) k)))
  :induct (nthcdr n l)
  :enable (nthcdr intersectp-equal))

(defrule hpos-ext-p-of-nthcdr
  (implies (true-listp l)
           (hpos-ext-p (nthcdr n l) l))
  :induct (nthcdr n l)
  :enable (nthcdr hpos-ext-p))

(defrule hpos-supply-okp-of-nthcdr
  (implies (hpos-supply-okp vs asg)
           (hpos-supply-okp (nthcdr n vs) asg))
  :enable hpos-supply-okp)

(defrule hpos-c-ell2-vs
  (equal (mv-nth 2 (hpos-c-ell2 h u vs asg))
         (nthcdr *hpos-ell2-nblock* vs))
  :enable hpos-c-ell2)

(defrule hpos-c-ell2-pt
  (equal (mv-nth 0 (hpos-c-ell2 h u vs asg))
         (hpos-ell2-pt vs))
  :enable hpos-c-ell2)

(defruledl hpos-c-ell2-asg-facts-2
  (b* (((mv & & vs2 a2) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs)))
             (and (hpos-ext-p vs2 vs)
                  (hpos-supply-okp vs2 a2))))
  :do-not-induct t
  :enable (hpos-c-ell2 hpos-supply-okp-of-append-pairlis)
  :disable (take hpos-lc-eval-decomp hpos-supply-okp-of-nthcdr)
  :use ((:instance hpos-supply-okp-of-nthcdr (n 1041))
        (:instance hpos-nthcdr-take-disjoint (n 1041) (l vs))
        (:instance hpos-len-of-take-1041))
  :prep-lemmas
  ((defrule hpos-supply-okp-forward
     (implies (hpos-supply-okp vs asg)
              (and (no-duplicatesp-equal vs) (true-listp vs)))
     :rule-classes :forward-chaining
     :enable hpos-supply-okp)))

(defrulel hpos-u-not-car-blk
  (implies (and (hpos-supply-okp vs asg)
                (<= *hpos-ell2-nblock* (len vs))
                (r1cs::valuation-bindsp asg u))
           (not (equal u (car vs))))
  :enable (hpos-supply-okp r1cs::valuation-bindsp intersectp-equal)
  :expand ((intersectp-equal vs (strip-cars asg))))

(defrule hpos-pt-boundp-of-hpos-ell2-pt
  (implies (and (symbol-listp (take *hpos-ell2-nblock* vs))
                (<= *hpos-ell2-nblock* (len vs))
                (r1cs::valuation-binds-allp a (cdr (take *hpos-ell2-nblock* vs))))
           (hpos-pt-boundp (hpos-ell2-pt vs) a))
  :do-not-induct t
  :enable (hpos-ell2-pt hpos-pt-boundp)
  :use (hpos-ell2-wires-facts
        (:instance hpos-ell2-wires-binds)
        (:instance hpos-bindsp-of-nth-2 (n 31) (l (mv-nth 1 (hpos-ell2-wires vs))))
        (:instance hpos-bindsp-of-nth-2 (n 32) (l (mv-nth 1 (hpos-ell2-wires vs)))))
  :prep-lemmas
  ((defruled hpos-bindsp-of-nth-2
     (implies (and (r1cs::valuation-binds-allp a l)
                   (< (nfix n) (len l)))
              (r1cs::valuation-bindsp a (nth n l)))
     :enable (nth r1cs::valuation-binds-allp))))

(defrule hpos-c-ell2-complete
  (b* (((mv pt cs vs2 a2) (hpos-c-ell2 h u vs asg))
       (p primes::*bls12-377-scalar-field-prime*)
       (r (hpos-lc-eval h asg p)))
    (implies (and (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= *hpos-ell2-nblock* (len vs))
                  (hpos-lc-boundp h asg)
                  (symbolp u)
                  (r1cs::valuation-bindsp asg u)
                  (equal (lookup-equal u asg) 1)
                  (hped-elligator2-encode-validp r))
             (and (r1cs::r1cs-valuationp a2 p)
                  (hpos-ext-p asg a2)
                  (hpos-ext-p vs2 vs)
                  (hpos-supply-okp vs2 a2)
                  (r1cs::r1cs-constraints-holdp cs a2 p)
                  (hpos-pt-boundp pt a2)
                  (equal (hpos-pt-eval pt a2) (hped-elligator2-encode r)))))
  :do-not-induct t
  :in-theory '(hpos-ext-p-reflexive hpos-c-ell2-pt hpos-c-ell2-vs hpos-ell2-sound-hyps
               hpos-consp-of-take-1041 hpos-valuation-binds-allp-of-cdr
               hpos-no-duplicatesp-strip-cars-when-valuationp)
  :use (hpos-c-ell2-asg-facts
        hpos-c-ell2-asg-facts-2
        hpos-ell2-blk-supply
        hpos-u-not-car-blk
        (:instance hpos-c-ell2-complete-frame (f (mv-nth 3 (hpos-c-ell2 h u vs asg))))
        (:instance hpos-pt-boundp-of-hpos-ell2-pt (a (mv-nth 3 (hpos-c-ell2 h u vs asg))))
        (:instance hpos-lookup-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h u vs asg))) (v u))
        (:instance hpos-member-strip-cars-when-bindsp (a asg) (v u))
        (:instance hpos-valuation-bindsp-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h u vs asg))) (v u))
        (:instance hpos-lc-eval-when-ext-p
                   (old asg) (new (mv-nth 3 (hpos-c-ell2 h u vs asg))) (lc h)
                   (p primes::*bls12-377-scalar-field-prime*))
        (:instance hpos-c-ell2-sound (asgx (mv-nth 3 (hpos-c-ell2 h u vs asg))))))

(defrule hpos-edwards-bls12-pointp-of-hped-elligator2-encode
  (implies (hped-elligator2-encode-validp r)
           (ecurve::edwards-bls12-pointp (hped-elligator2-encode r)))
  :enable (hped-elligator2-encode-validp
           ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp))
