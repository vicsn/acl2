; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHP::hash_uncompressed: the first iteration (hbhp-iter0), then for every
; further chunk of at most max input bits, Field::write_bits_le of the
; previous digest's x-coordinate (fb-field-bits), truncated to 252 bits and
; followed by the chunk, hashed by BHPHasher::hash_uncompressed
; (hbhp-hasher-full).  An empty input runs no iteration: the result is the
; constant zero and no constraint is emitted.

(in-package "ALEOVM")

(include-book "hbhp-iter0")
(include-book "fb2-field-bits")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

(defruledl hbhp-hu-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The iterations after the first.  xd is the wire of the previous digest's
;; x-coordinate and u the wire of the constant one used by the bit
;; decomposition.  Each element of its is (fbs rs wins): the 253 bit wires
;; and the range-check wires of Field::write_bits_le, and the hasher wires.

(defmacro hbhp-hu-n () '(min (acl2::pos-fix max) (len rest)))
(defmacro hbhp-hu-it () '(car its))
(defmacro hbhp-hu-bits ()
  '(append (take (hbhp-data-bits) (nth 0 (hbhp-hu-it))) (take (hbhp-hu-n) rest)))
(defmacro hbhp-hu-out1 ()
  '(hbhp-hasher-full-out (hbhp-hu-bits) (nth 2 (hbhp-hu-it)) gens w))

(define hbhp-iters-gadget (rest its gens (w posp) (max posp) xd u (p posp))
  :verify-guards nil
  :measure (len rest)
  :hints (("Goal" :in-theory (enable hbhp-hu-len-of-nthcdr acl2::pos-fix)))
  (b* (((when (endp rest)) nil))
    (append (fb-field-write-bits-le-gadget xd (nth 0 (hbhp-hu-it))
                                           (nth 1 (hbhp-hu-it)) u p)
            (hbhp-hasher-full-gadget (hbhp-hu-bits) (nth 2 (hbhp-hu-it)) gens w p)
            (hbhp-iters-gadget (nthcdr (hbhp-hu-n) rest) (cdr its) gens w max
                               (car (hbhp-hu-out1)) u p))))

(define hbhp-iters-out (rest its gens (w posp) (max posp) xd yd)
  :verify-guards nil
  :measure (len rest)
  :hints (("Goal" :in-theory (enable hbhp-hu-len-of-nthcdr acl2::pos-fix)))
  (b* (((when (endp rest)) (cons xd yd)))
    (hbhp-iters-out (nthcdr (hbhp-hu-n) rest) (cdr its) gens w max
                    (car (hbhp-hu-out1)) (cdr (hbhp-hu-out1)))))

;; The hasher's wire conditions include the booleanity of its input wires;
;; for the digest bits this is enforced by the bit decomposition, so it is
;; only required of the structure when those wires hold bits.

(define hbhp-iters-wires-okp (rest its gens (w posp) (max posp) xd asg)
  :verify-guards nil
  :measure (len rest)
  :hints (("Goal" :in-theory (enable hbhp-hu-len-of-nthcdr acl2::pos-fix)))
  (b* (((when (endp rest)) t)
       (fbs (nth 0 (hbhp-hu-it)))
       (rs (nth 1 (hbhp-hu-it))))
    (and (symbolp xd) (r1cs::valuation-bindsp asg xd)
         (symbol-listp fbs) (equal (len fbs) (integer-length (base-prime)))
         (symbol-listp rs) (equal (len rs) (bits-lt-prime-rlen (base-prime)))
         (r1cs::valuation-binds-allp asg fbs)
         (r1cs::valuation-binds-allp asg rs)
         (implies (bit-listp (lookup-equal-list fbs asg))
                  (hbhp-hasher-full-wires-okp (hbhp-hu-bits) (nth 2 (hbhp-hu-it))
                                              gens w asg))
         (hbhp-wire-okp (car (hbhp-hu-out1)))
         (hbhp-wire-okp (cdr (hbhp-hu-out1)))
         (hbhp-iters-wires-okp (nthcdr (hbhp-hu-n) rest) (cdr its) gens w max
                               (car (hbhp-hu-out1)) asg))))

(define hbhp-iters-canon (rest its gens (w posp) (max posp) xd asg)
  :verify-guards nil
  :measure (len rest)
  :hints (("Goal" :in-theory (enable hbhp-hu-len-of-nthcdr acl2::pos-fix)))
  (b* (((when (endp rest)) t)
       (fbs (nth 0 (hbhp-hu-it)))
       (rs (nth 1 (hbhp-hu-it))))
    (and (equal (lookup-equal-list fbs asg) (field-bits-le (lookup-equal xd asg)))
         (equal (lookup-equal-list rs asg)
                (fb-bits-lte-const-witness (lookup-equal-list fbs asg)
                                           (nat=>lebits* (1- (base-prime)))))
         (hbhp-hasher-full-canon (hbhp-hu-bits) (nth 2 (hbhp-hu-it)) gens w asg)
         (hbhp-iters-canon (nthcdr (hbhp-hu-n) rest) (cdr its) gens w max
                           (car (hbhp-hu-out1)) asg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl hbhp-hu-oddp-base-prime
  (oddp (base-prime))
  :in-theory '((:e base-prime) (:e oddp)))

(defruledl hbhp-hu-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defruledl hbhp-hu-append-nil
  (equal (append nil x) x))

(defruled hbhp-hu-lk-list-is-lookup-equal-list
  (equal (hbhp-lk-list bs asg) (lookup-equal-list bs asg))
  :induct (len bs)
  :enable (hbhp-lk-list lookup-equal-list))

(defruled hbhp-hu-lk-list-of-append
  (equal (hbhp-lk-list (append a b) asg)
         (append (hbhp-lk-list a asg) (hbhp-lk-list b asg)))
  :induct (len a)
  :enable hbhp-lk-list)

(defruled hbhp-hu-digest-bits
  (implies (pfield::fep x (base-prime))
           (equal (hbhp-digest-bits (ecurve::point-finite x y))
                  (take (hbhp-data-bits) (field-bits-le x))))
  :enable (hbhp-digest-bits field-bits-le pfield::fep-fix-when-fep
           base-field-size-in-bits pfield::fep))

(defruled hbhp-hu-not-reserrp-point
  (not (reserrp (ecurve::point-finite x y)))
  :enable (reserrp ecurve::point-finite))

(defmacro hbhp-iters-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gens-okp gens)
        (posp w) (<= w 63)
        (posp max) (<= (+ (hbhp-data-bits) max) (* 3 w (len gens)))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)))

(defruledl hbhp-hu-step-nums
  (implies (and (posp w) (<= w 63) (posp max) (consp rest)
                (<= (+ 252 max) lim))
           (and (< (* 3 w) (+ 252 (min max (len rest))))
                (<= (+ 252 (min max (len rest))) lim)
                (<= (min max (len rest)) (len rest))
                (posp (min max (len rest))))))

(defruled hbhp-hu-fbs-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbolp u) (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (symbolp xd) (r1cs::valuation-bindsp asg xd)
                (symbol-listp fbs) (equal (len fbs) (integer-length (base-prime)))
                (symbol-listp rs) (equal (len rs) (bits-lt-prime-rlen (base-prime)))
                (r1cs::valuation-binds-allp asg fbs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget xd fbs rs u p) asg p))
           (and (equal (hbhp-lk-list fbs asg) (field-bits-le (lookup-equal xd asg)))
                (bit-listp (lookup-equal-list fbs asg))))
  :use ((:instance fb-field-write-bits-le-gadget-sound
                   (x xd) (bits fbs) (acc nil))
        (:instance hbhp-hu-lk-list-is-lookup-equal-list (bs fbs))
        primep-of-base-prime)
  :in-theory '(field-write-bits-le-funspec bit-listp-of-field-bits-le
               hbhp-hu-oddp-base-prime hbhp-hu-append-nil (:e bit-listp)))

(defruled hbhp-hu-step-sound
  (implies (and (hbhp-iters-hyps)
                (consp rest)
                (hbhp-iters-wires-okp rest its gens w max xd asg)
                (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget xd (nth 0 (hbhp-hu-it))
                                                (nth 1 (hbhp-hu-it)) u p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-full-gadget (hbhp-hu-bits) (nth 2 (hbhp-hu-it)) gens w p)
                 asg p))
           (equal (hbhp-hasher-hash-uncompressed
                   gens w
                   (append (hbhp-digest-bits
                            (ecurve::point-finite (lookup-equal xd asg) y))
                           (take (hbhp-hu-n) (hbhp-lk-list rest asg))))
                  (ecurve::point-finite (lookup-equal (car (hbhp-hu-out1)) asg)
                                        (lookup-equal (cdr (hbhp-hu-out1)) asg))))
  :expand ((hbhp-iters-wires-okp rest its gens w max xd asg))
  :use ((:instance hbhp-hu-fbs-sound
                   (fbs (nth 0 (hbhp-hu-it))) (rs (nth 1 (hbhp-hu-it))))
        (:instance hbhp-hasher-full-gadget-sound
                   (bits (hbhp-hu-bits)) (wins (nth 2 (hbhp-hu-it))))
        (:instance hbhp-hu-lk-list-of-append
                   (a (take (hbhp-data-bits) (nth 0 (hbhp-hu-it))))
                   (b (take (hbhp-hu-n) rest)))
        (:instance hbhp-take-of-lk-list (bs (nth 0 (hbhp-hu-it))) (n (hbhp-data-bits)))
        (:instance hbhp-take-of-lk-list (bs rest) (n (hbhp-hu-n)))
        (:instance hbhp-hu-digest-bits (x (lookup-equal xd asg)))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var xd)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance hbhp-hu-step-nums (lim (* 3 w (len gens))))
        (:instance hbhp-ph-len-of-take (x (nth 0 (hbhp-hu-it))) (n (hbhp-data-bits)))
        (:instance hbhp-ph-len-of-take (x rest) (n (hbhp-hu-n)))
        primep-of-base-prime fb-integer-length-of-base-prime)
  :in-theory '(hbhp-iters-wires-okp field-write-bits-le-funspec
               bit-listp-of-field-bits-le hbhp-len-of-lk-list
               (:e hbhp-data-bits) (:e base-field-size-in-bits)
               hbhp-hu-oddp-base-prime
               acl2::pos-fix posp natp nfix car-cons cdr-cons
               hbhp-hu-append-nil hbhp-hu-len-append (:t len) (:e bit-listp))
  :do-not-induct t)

(defun hbhp-iters-induct (rest its gens w max xd yd)
  (declare (xargs :measure (len rest) :verify-guards nil
                  :hints (("Goal" :in-theory (enable hbhp-hu-len-of-nthcdr
                                                     acl2::pos-fix)))))
  (if (endp rest)
      (list its xd yd)
    (hbhp-iters-induct (nthcdr (hbhp-hu-n) rest) (cdr its) gens w max
                       (car (hbhp-hu-out1)) (cdr (hbhp-hu-out1)))))

(defruled hbhp-iters-sound
  (implies (and (hbhp-iters-hyps)
                (hbhp-iters-wires-okp rest its gens w max xd asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-iters-gadget rest its gens w max xd u p) asg p))
           (b* ((out (hbhp-iters-out rest its gens w max xd yd)))
             (equal (ecurve::point-finite (lookup-equal (car out) asg)
                                          (lookup-equal (cdr out) asg))
                    (hbhp-hash-iter gens w max (hbhp-lk-list rest asg)
                                    (ecurve::point-finite (lookup-equal xd asg)
                                                          (lookup-equal yd asg))))))
  :induct (hbhp-iters-induct rest its gens w max xd yd)
  :in-theory '((:induction hbhp-iters-induct)
               r1cs::r1cs-constraints-holdp-of-append
               acl2::pos-fix posp natp hbhp-len-of-lk-list car-cons cdr-cons endp)
  :hints (("Subgoal *1/2"
           :expand ((:free (p) (hbhp-iters-gadget rest its gens w max xd u p))
                    (hbhp-iters-out rest its gens w max xd yd)
                    (hbhp-iters-wires-okp rest its gens w max xd asg)
                    (:free (digest)
                     (hbhp-hash-iter gens w max (hbhp-lk-list rest asg) digest)))
           :use ((:instance hbhp-hu-step-sound (y (lookup-equal yd asg)))
                 (:instance hbhp-hu-not-reserrp-point
                            (x (lookup-equal (car (hbhp-hu-out1)) asg))
                            (y (lookup-equal (cdr (hbhp-hu-out1)) asg)))
                 (:instance hbhp-nthcdr-of-lk-list (bs rest) (n (hbhp-hu-n)))
                 (:instance hbhp-consp-of-lk-list (bs rest))))
          ("Subgoal *1/1"
           :expand ((hbhp-iters-out rest its gens w max xd yd)
                    (:free (digest)
                     (hbhp-hash-iter gens w max (hbhp-lk-list rest asg) digest)))
           :use ((:instance hbhp-consp-of-lk-list (bs rest))))))

(defruledl hbhp-hu-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var x)
                   (r1cs::prime (base-prime)) (r1cs::valuation asg))
        primep-of-base-prime)
  :in-theory '(fieldp))

(defruled hbhp-hu-step-complete
  (implies (and (hbhp-iters-hyps)
                (consp rest)
                (hbhp-iters-wires-okp rest its gens w max xd asg)
                (hbhp-iters-canon rest its gens w max xd asg))
           (and (r1cs::r1cs-constraints-holdp
                 (fb-field-write-bits-le-gadget xd (nth 0 (hbhp-hu-it))
                                                (nth 1 (hbhp-hu-it)) u p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-full-gadget (hbhp-hu-bits) (nth 2 (hbhp-hu-it)) gens w p)
                 asg p)))
  :expand ((hbhp-iters-wires-okp rest its gens w max xd asg)
           (hbhp-iters-canon rest its gens w max xd asg))
  :use ((:instance fb2-field-write-bits-le-gadget-complete
                   (x xd) (bits (nth 0 (hbhp-hu-it))) (rs (nth 1 (hbhp-hu-it))))
        (:instance hbhp-hasher-full-gadget-complete
                   (bits (hbhp-hu-bits)) (wins (nth 2 (hbhp-hu-it))))
        (:instance bit-listp-of-field-bits-le (x (lookup-equal xd asg)))
        (:instance hbhp-hu-fieldp-of-lookup (x xd))
        (:instance hbhp-hu-step-nums (lim (* 3 w (len gens))))
        (:instance hbhp-ph-len-of-take (x (nth 0 (hbhp-hu-it))) (n (hbhp-data-bits)))
        (:instance hbhp-ph-len-of-take (x rest) (n (hbhp-hu-n)))
        primep-of-base-prime fb-integer-length-of-base-prime)
  :in-theory '(hbhp-hu-oddp-base-prime hbhp-hu-len-append
               (:e hbhp-data-bits) (:e base-field-size-in-bits)
               acl2::pos-fix posp natp nfix (:t len))
  :do-not-induct t)

(defruledl hbhp-hu-holdp-nil
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(defruled hbhp-iters-complete
  (implies (and (hbhp-iters-hyps)
                (hbhp-iters-wires-okp rest its gens w max xd asg)
                (hbhp-iters-canon rest its gens w max xd asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-iters-gadget rest its gens w max xd u p) asg p))
  :induct (hbhp-iters-induct rest its gens w max xd yd)
  :in-theory '((:induction hbhp-iters-induct)
               r1cs::r1cs-constraints-holdp-of-append endp)
  :hints (("Subgoal *1/2"
           :expand ((:free (p) (hbhp-iters-gadget rest its gens w max xd u p))
                    (hbhp-iters-wires-okp rest its gens w max xd asg)
                    (hbhp-iters-canon rest its gens w max xd asg))
           :use (hbhp-hu-step-complete))
          ("Subgoal *1/1"
           :expand ((:free (p) (hbhp-iters-gadget rest its gens w max xd u p)))
           :use (hbhp-hu-holdp-nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHP::hash_uncompressed.  cbits are the constant bits domain || length,
;; 252 = 3(wm + c) of them; wins0 are the wires of the first iteration.

(defmacro hbhp-hu-n0 () '(min (acl2::pos-fix max) (len vb)))
(defmacro hbhp-hu-out0 ()
  '(hbhp-iter0-out cbits (take (hbhp-hu-n0) vb) wins0 gens w m c))

(define hbhp-hu-gadget (cbits vb wins0 its gens (w posp) m c (max posp) u (p posp))
  :verify-guards nil
  (if (endp vb)
      nil
    (append (hbhp-iter0-gadget cbits (take (hbhp-hu-n0) vb) wins0 gens w m c p)
            (hbhp-iters-gadget (nthcdr (hbhp-hu-n0) vb) its gens w max
                               (car (hbhp-hu-out0)) u p))))

(define hbhp-hu-out (cbits vb wins0 its gens (w posp) m c (max posp))
  :verify-guards nil
  :short "The output wires; the empty input has the constant zero instead."
  (hbhp-iters-out (nthcdr (hbhp-hu-n0) vb) its gens w max
                  (car (hbhp-hu-out0)) (cdr (hbhp-hu-out0))))

(define hbhp-hu-wires-okp (cbits vb wins0 its gens (w posp) m c (max posp) asg)
  :verify-guards nil
  (and (hbhp-iter0-wires-okp cbits (take (hbhp-hu-n0) vb) wins0 gens w m c asg)
       (hbhp-iters-wires-okp (nthcdr (hbhp-hu-n0) vb) its gens w max
                             (car (hbhp-hu-out0)) asg)))

(define hbhp-hu-canon (cbits vb wins0 its gens (w posp) m c (max posp) asg)
  :verify-guards nil
  (and (hbhp-iter0-canon cbits (take (hbhp-hu-n0) vb) wins0 gens w m c asg)
       (hbhp-iters-canon (nthcdr (hbhp-hu-n0) vb) its gens w max
                         (car (hbhp-hu-out0)) asg)))

(defruled hbhp-hu-len-of-domain-bits
  (equal (len (hbhp-domain-bits domain)) (hbhp-domain-size))
  :enable (hbhp-domain-bits)
  :prep-books ((include-book "std/lists/top" :dir :system)))

(defruled hbhp-hu-hasher-hash-when-ok
  (implies (and (posp w) (< (* 3 w) (len bits)) (<= (len bits) (* 3 w (len gens))))
           (equal (hbhp-hasher-hash-uncompressed gens w bits)
                  (hbhp-hasher-sum (hbhp-pad bits) gens w (ecurve::twisted-edwards-zero))))
  :enable (hbhp-hasher-hash-uncompressed acl2::pos-fix))

(defmacro hbhp-hu-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gens-okp gens)
        (posp w) (<= w 63)
        (natp m) (natp c) (<= 1 c) (< c w) (equal (+ (* w m) c) 84)
        (< m (len gens))
        (hbhp-domain-okp domain)
        (equal cbits (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (< 0 max)
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)
        (hbhp-hu-wires-okp cbits vb wins0 its gens w m c max asg)))

(defruledl hbhp-hu-nums
  (implies (and (posp w) (<= w 63) (natp m) (natp c) (equal (+ (* w m) c) 84)
                (posp max) (equal max (- lim 252)) (consp vb))
           (and (equal (+ (* 3 w m) (* 3 c)) 252)
                (posp (min max (len vb)))
                (<= (min max (len vb)) (len vb))
                (< (* 3 w) (+ 252 (min max (len vb))))
                (<= (+ 252 (min max (len vb))) lim)
                (<= (+ 252 max) lim)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-hu-gens-okp-parts
  (implies (hbhp-gens-okp gens)
           (and (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)))
  :enable hbhp-gens-okp)

(defruledl hbhp-hu-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defruledl hbhp-hu-bit-listp-append
  (implies (and (bit-listp a) (bit-listp b)) (bit-listp (append a b)))
  :enable bit-listp)

(defruledl hbhp-i0-consp-take-pub
  (implies (posp k) (consp (take k x)))
  :enable take)

(defruled hbhp-hu-first-sound
  (implies (and (hbhp-hu-hyps)
                (consp vb)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-iter0-gadget cbits (take (hbhp-hu-n0) vb) wins0 gens w m c p)
                 asg p))
           (equal (ecurve::point-finite (lookup-equal (car (hbhp-hu-out0)) asg)
                                        (lookup-equal (cdr (hbhp-hu-out0)) asg))
                  (hbhp-hasher-hash-uncompressed
                   gens w
                   (append (hbhp-domain-bits domain)
                           (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))
                           (take (hbhp-hu-n0) (hbhp-lk-list vb asg))))))
  :use ((:instance hbhp-iter0-sound (vb (take (hbhp-hu-n0) vb)) (wins wins0))
        (:instance hbhp-hu-hasher-hash-when-ok
                   (bits (append (hbhp-domain-bits domain)
                                 (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))
                                 (take (hbhp-hu-n0) (hbhp-lk-list vb asg)))))
        (:instance hbhp-take-of-lk-list (bs vb) (n (hbhp-hu-n0)))
        (:instance hbhp-hu-len-of-domain-bits)
        (:instance hbhp-hu-nums (lim (* 3 w (len gens))))
        (:instance hbhp-ph-len-of-take (x vb) (n (hbhp-hu-n0)))
        (:instance hbhp-i0-consp-take-pub (k (hbhp-hu-n0)) (x vb))
        (:instance hbhp-hu-bit-listp-append
                   (a (hbhp-domain-bits domain))
                   (b (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        hbhp-hu-gens-okp-parts)
  :in-theory '(hbhp-hu-wires-okp hbhp-max-bits-per-iteration
               hbhp-hu-append-assoc hbhp-hu-len-append hbhp-len-of-lk-list
               acl2::len-of-nat=>lebits acl2::bit-listp-of-nat=>lebits
               bit-listp-of-hbhp-domain-bits
               (:e hbhp-domain-size) (:e hbhp-data-bits) (:e expt)
               acl2::pos-fix posp natp nfix (:t len))
  :do-not-induct t)

(defruled hbhp-hu-sound
  (implies (and (hbhp-hu-hyps)
                (consp vb)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
           (b* ((out (hbhp-hu-out cbits vb wins0 its gens w m c max)))
             (equal (ecurve::point-finite (lookup-equal (car out) asg)
                                          (lookup-equal (cdr out) asg))
                    (hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg)))))
  :expand ((hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg)))
  :use (hbhp-hu-first-sound
        (:instance hbhp-iters-sound
                   (rest (nthcdr (hbhp-hu-n0) vb))
                   (xd (car (hbhp-hu-out0))) (yd (cdr (hbhp-hu-out0))))
        (:instance hbhp-hu-not-reserrp-point
                   (x (lookup-equal (car (hbhp-hu-out0)) asg))
                   (y (lookup-equal (cdr (hbhp-hu-out0)) asg)))
        (:instance hbhp-nthcdr-of-lk-list (bs vb) (n (hbhp-hu-n0)))
        (:instance hbhp-consp-of-lk-list (bs vb))
        (:instance hbhp-hu-nums (lim (* 3 w (len gens)))))
  :in-theory '(hbhp-hu-gadget hbhp-hu-out hbhp-hu-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-max-bits-per-iteration (:e hbhp-data-bits)
               acl2::pos-fix posp natp hbhp-len-of-lk-list endp (:t len))
  :do-not-induct t)

(defruled hbhp-hu-empty
  (implies (and (not (consp vb))
                (hbhp-domain-okp domain)
                (< 0 (hbhp-max-bits-per-iteration gens w)))
           (and (equal (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) nil)
                (equal (hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg))
                       (ecurve::twisted-edwards-zero))))
  :expand ((hbhp-hash-uncompressed domain gens w (hbhp-lk-list vb asg)))
  :use ((:instance hbhp-consp-of-lk-list (bs vb)))
  :in-theory '(hbhp-hu-gadget hbhp-max-bits-per-iteration acl2::pos-fix endp))

(defruled hbhp-hu-complete
  (implies (and (hbhp-hu-hyps)
                (consp vb)
                (hbhp-hu-canon cbits vb wins0 its gens w m c max asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
  :use ((:instance hbhp-iter0-complete (vb (take (hbhp-hu-n0) vb)) (wins wins0))
        (:instance hbhp-iters-complete
                   (rest (nthcdr (hbhp-hu-n0) vb)) (xd (car (hbhp-hu-out0))))
        (:instance hbhp-hu-len-of-domain-bits)
        (:instance hbhp-hu-nums (lim (* 3 w (len gens))))
        (:instance hbhp-ph-len-of-take (x vb) (n (hbhp-hu-n0)))
        (:instance hbhp-i0-consp-take-pub (k (hbhp-hu-n0)) (x vb))
        (:instance hbhp-hu-bit-listp-append
                   (a (hbhp-domain-bits domain))
                   (b (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        hbhp-hu-gens-okp-parts)
  :in-theory '(hbhp-hu-gadget hbhp-hu-canon hbhp-hu-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-max-bits-per-iteration
               hbhp-hu-len-append acl2::len-of-nat=>lebits
               acl2::bit-listp-of-nat=>lebits bit-listp-of-hbhp-domain-bits
               (:e hbhp-domain-size) (:e hbhp-data-bits) (:e expt)
               acl2::pos-fix posp natp nfix endp (:t len))
  :do-not-induct t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The network instances: 84 chunks of constant prefix give m = 1, 1, 3, 1
;; constant windows and c = 27, 41, 15, 30 constant chunks in window m.

(defmacro hbhp-sizep (size) `(member-equal ,size '(256 512 768 1024)))

(defruled hbhp-hu-instance-params
  (implies (hbhp-sizep size)
           (b* ((w (hbhp-size-window-size size))
                (gens (hbhp-setup-gens size)))
             (and (posp w) (<= w 63)
                  (natp (floor 84 w)) (natp (mod 84 w))
                  (<= 1 (mod 84 w)) (< (mod 84 w) w)
                  (equal (+ (* w (floor 84 w)) (mod 84 w)) 84)
                  (< (floor 84 w) (len gens))
                  (hbhp-gens-okp gens)
                  (hbhp-domain-okp (hbhp-size-domain size))
                  (< 0 (hbhp-max-bits-per-iteration gens w)))))
  :in-theory '(hbhp-len-of-setup-gens hbhp-gens-okp-of-setup-gens
               hbhp-max-bits-per-iteration member-equal
               (:e hbhp-size-window-size) (:e hbhp-size-num-windows)
               (:e hbhp-size-domain) (:e hbhp-domain-okp) (:e hbhp-data-bits)
               (:e floor) (:e mod) (:e acl2::pos-fix) (:e posp) (:e natp)
               (:e <) (:e binary-*) (:e binary-+) (:e unary--) (:e equal)
               (:e len)))

(defmacro hbhp-bhp-hu-hyps ()
  '(and (hbhp-sizep size)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal w (hbhp-size-window-size size))
        (equal gens (hbhp-setup-gens size))
        (equal domain (hbhp-size-domain size))
        (equal m (floor 84 w))
        (equal c (mod 84 w))
        (equal cbits (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)
        (hbhp-hu-wires-okp cbits vb wins0 its gens w m c max asg)))

(defruled hbhp-bhp-hu-sound
  (implies (and (hbhp-bhp-hu-hyps)
                (consp vb)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
           (b* ((out (hbhp-hu-out cbits vb wins0 its gens w m c max)))
             (equal (ecurve::point-finite (lookup-equal (car out) asg)
                                          (lookup-equal (cdr out) asg))
                    (hbhp-bhp-hash-uncompressed size (hbhp-lk-list vb asg)))))
  :use (hbhp-hu-instance-params hbhp-hu-sound
        (:instance hbhp-hu-not-reserrp-point
                   (x (lookup-equal (car (hbhp-hu-out cbits vb wins0 its gens w m c max))
                                    asg))
                   (y (lookup-equal (cdr (hbhp-hu-out cbits vb wins0 its gens w m c max))
                                    asg))))
  :in-theory '(hbhp-bhp-hash-uncompressed))

(defruled hbhp-bhp-hu-empty
  (implies (and (hbhp-sizep size)
                (equal w (hbhp-size-window-size size))
                (equal gens (hbhp-setup-gens size))
                (equal domain (hbhp-size-domain size))
                (not (consp vb)))
           (and (equal (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) nil)
                (equal (hbhp-bhp-hash-uncompressed size (hbhp-lk-list vb asg))
                       (ecurve::twisted-edwards-zero))))
  :use (hbhp-hu-instance-params hbhp-hu-empty
        (:instance hbhp-hu-not-reserrp-point (x 0) (y 1)))
  :in-theory '(hbhp-bhp-hash-uncompressed (:e ecurve::twisted-edwards-zero)
               (:e reserrp)))

(defruled hbhp-bhp-hu-complete
  (implies (and (hbhp-bhp-hu-hyps)
                (consp vb)
                (hbhp-hu-canon cbits vb wins0 its gens w m c max asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
  :use (hbhp-hu-instance-params hbhp-hu-complete)
  :in-theory nil)
