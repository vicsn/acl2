; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PathHash::hash_children for BHP (circuit/collections/src/merkle_tree/
; helpers/path_hash.rs): the input is [Boolean::constant(true)] followed by
; Field::write_bits_le of left and of right (253 bits each), hashed by
; BHP::hash, i.e. hash_uncompressed then the x-coordinate (no constraint).
;
; hash_uncompressed on [true] ++ vb: the first iteration is hbhp-iterx on
; the first max - 1 wires of vb (the constant true bit is the first of its
; max input bits), the later iterations are hbhp-iters on the remaining
; wires, exactly as in hbhp-hu.

(in-package "ALEOVM")

(include-book "hbhp-xwin")
(include-book "hbhp-hu")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHP::hash_uncompressed on [true] ++ vb.

(defmacro hbhp-hc-n0 () '(min (acl2::pos-fix max) (+ 1 (len vb))))
(defmacro hbhp-hc-k0 () '(- (hbhp-hc-n0) 1))
(defmacro hbhp-hc-out0 ()
  '(hbhp-iterx-out cbits (take (hbhp-hc-k0) vb) wins0 gens w m c))

(define hbhp-hux-gadget (cbits vb wins0 its gens (w posp) m c (max posp) u (p posp))
  :verify-guards nil
  (append (hbhp-iterx-gadget cbits (take (hbhp-hc-k0) vb) wins0 gens w m c p)
          (hbhp-iters-gadget (nthcdr (hbhp-hc-k0) vb) its gens w max
                             (car (hbhp-hc-out0)) u p)))

(define hbhp-hux-out (cbits vb wins0 its gens (w posp) m c (max posp))
  :verify-guards nil
  (hbhp-iters-out (nthcdr (hbhp-hc-k0) vb) its gens w max
                  (car (hbhp-hc-out0)) (cdr (hbhp-hc-out0))))

(define hbhp-hux-wires-okp (cbits vb wins0 its gens (w posp) m c (max posp) asg)
  :verify-guards nil
  (and (hbhp-iterx-wires-okp cbits (take (hbhp-hc-k0) vb) wins0 gens w m c asg)
       (hbhp-iters-wires-okp (nthcdr (hbhp-hc-k0) vb) its gens w max
                             (car (hbhp-hc-out0)) asg)))

(define hbhp-hux-canon (cbits vb wins0 its gens (w posp) m c (max posp) asg)
  :verify-guards nil
  (and (hbhp-iterx-canon cbits (take (hbhp-hc-k0) vb) wins0 gens w m c asg)
       (hbhp-iters-canon (nthcdr (hbhp-hc-k0) vb) its gens w max
                         (car (hbhp-hc-out0)) asg)))

(defmacro hbhp-hux-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gens-okp gens)
        (posp w) (<= w 63)
        (natp m) (natp c) (<= 1 c) (< c w) (equal (+ (* w m) c) 84)
        (< m (len gens))
        (hbhp-domain-okp domain)
        (equal cbits (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (+ 1 (len vb)) (expt 2 64)))))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (< 0 max)
        (< (* 3 (- w c)) max)
        (<= (* 3 (- w c)) (len vb))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)
        (hbhp-hux-wires-okp cbits vb wins0 its gens w m c max asg)))

(defruledl hbhp-hc-nums
  (implies (and (posp w) (<= w 63) (natp m) (natp c) (<= 1 c) (< c w)
                (equal (+ (* w m) c) 84)
                (posp max) (equal max (- lim 252))
                (< (* 3 (- w c)) max) (natp lv) (<= (* 3 (- w c)) lv))
           (and (equal (+ (* 3 w m) (* 3 c)) 252)
                (natp (- (min max (+ 1 lv)) 1))
                (<= (- (min max (+ 1 lv)) 1) lv)
                (< (- (* 3 (- w c)) 1) (- (min max (+ 1 lv)) 1))
                (posp (min max (+ 1 lv)))
                (< (* 3 w) (+ 253 (- (min max (+ 1 lv)) 1)))
                (<= (+ 253 (- (min max (+ 1 lv)) 1)) lim)
                (<= (+ 252 1 (- (min max (+ 1 lv)) 1)) lim)
                (equal (+ 1 (- (min max (+ 1 lv)) 1)) (min max (+ 1 lv)))
                (<= (+ 252 max) lim)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-hc-gens-okp-parts
  (implies (hbhp-gens-okp gens)
           (and (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)))
  :enable hbhp-gens-okp)

(defruledl hbhp-hc-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defruledl hbhp-hc-bit-listp-append
  (implies (and (bit-listp a) (bit-listp b)) (bit-listp (append a b)))
  :enable bit-listp)

(defruledl hbhp-hc-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defruledl hbhp-hc-len-cons
  (equal (len (cons a x)) (+ 1 (len x))))

(defruledl hbhp-hc-take-cons
  (implies (posp n)
           (equal (take n (cons a x)) (cons a (take (- n 1) x))))
  :enable take)

(defruledl hbhp-hc-nthcdr-cons
  (implies (posp n)
           (equal (nthcdr n (cons a x)) (nthcdr (- n 1) x)))
  :enable nthcdr)

(defun hbhp-hc-first-uses ()
  (declare (xargs :guard t :mode :program))
  '((:instance hbhp-hu-len-of-domain-bits)
    (:instance hbhp-hc-nums (lim (* 3 w (len gens))) (lv (len vb)))
    (:instance hbhp-ph-len-of-take (x vb) (n (hbhp-hc-k0)))
    (:instance hbhp-hc-bit-listp-append
               (a (hbhp-domain-bits domain))
               (b (acl2::nat=>lebits 64 (mod (+ 1 (len vb)) (expt 2 64)))))
    hbhp-hc-gens-okp-parts))

(make-event
 `(defruled hbhp-hux-first-sound
    (implies (and (hbhp-hux-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-iterx-gadget cbits (take (hbhp-hc-k0) vb) wins0 gens w m c p)
                   asg p))
             (equal (ecurve::point-finite (lookup-equal (car (hbhp-hc-out0)) asg)
                                          (lookup-equal (cdr (hbhp-hc-out0)) asg))
                    (hbhp-hasher-hash-uncompressed
                     gens w
                     (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (+ 1 (len vb)) (expt 2 64)))
                             (cons 1 (take (hbhp-hc-k0) (hbhp-lk-list vb asg)))))))
    :use ((:instance hbhp-iterx-sound (vb (take (hbhp-hc-k0) vb)) (wins wins0))
          (:instance hbhp-hu-hasher-hash-when-ok
                     (bits (append (hbhp-domain-bits domain)
                                   (acl2::nat=>lebits 64 (mod (+ 1 (len vb)) (expt 2 64)))
                                   (cons 1 (take (hbhp-hc-k0) (hbhp-lk-list vb asg))))))
          (:instance hbhp-take-of-lk-list (bs vb) (n (hbhp-hc-k0)))
          ,@(hbhp-hc-first-uses))
    :in-theory '(hbhp-hux-wires-okp hbhp-max-bits-per-iteration
                 hbhp-hc-append-assoc hbhp-hc-len-append hbhp-hc-len-cons
                 hbhp-len-of-lk-list
                 acl2::len-of-nat=>lebits acl2::bit-listp-of-nat=>lebits
                 bit-listp-of-hbhp-domain-bits
                 (:e hbhp-domain-size) (:e hbhp-data-bits) (:e expt)
                 acl2::pos-fix posp natp nfix (:t len))
    :do-not-induct t))

(defruled hbhp-hux-sound
  (implies (and (hbhp-hux-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hux-gadget cbits vb wins0 its gens w m c max u p) asg p))
           (b* ((out (hbhp-hux-out cbits vb wins0 its gens w m c max)))
             (equal (ecurve::point-finite (lookup-equal (car out) asg)
                                          (lookup-equal (cdr out) asg))
                    (hbhp-hash-uncompressed domain gens w
                                            (cons 1 (hbhp-lk-list vb asg))))))
  :expand ((hbhp-hash-uncompressed domain gens w (cons 1 (hbhp-lk-list vb asg))))
  :use (hbhp-hux-first-sound
        (:instance hbhp-iters-sound
                   (rest (nthcdr (hbhp-hc-k0) vb))
                   (xd (car (hbhp-hc-out0))) (yd (cdr (hbhp-hc-out0))))
        (:instance hbhp-hu-not-reserrp-point
                   (x (lookup-equal (car (hbhp-hc-out0)) asg))
                   (y (lookup-equal (cdr (hbhp-hc-out0)) asg)))
        (:instance hbhp-nthcdr-of-lk-list (bs vb) (n (hbhp-hc-k0)))
        (:instance hbhp-hc-take-cons (n (hbhp-hc-n0)) (a 1) (x (hbhp-lk-list vb asg)))
        (:instance hbhp-hc-nthcdr-cons (n (hbhp-hc-n0)) (a 1) (x (hbhp-lk-list vb asg)))
        (:instance hbhp-hc-nums (lim (* 3 w (len gens))) (lv (len vb))))
  :in-theory '(hbhp-hux-gadget hbhp-hux-out hbhp-hux-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-max-bits-per-iteration (:e hbhp-data-bits)
               hbhp-hc-len-cons
               acl2::pos-fix posp natp hbhp-len-of-lk-list endp (:t len))
  :do-not-induct t)

(make-event
 `(defruled hbhp-hux-complete
    (implies (and (hbhp-hux-hyps)
                  (hbhp-hux-canon cbits vb wins0 its gens w m c max asg))
             (r1cs::r1cs-constraints-holdp
              (hbhp-hux-gadget cbits vb wins0 its gens w m c max u p) asg p))
    :use ((:instance hbhp-iterx-complete (vb (take (hbhp-hc-k0) vb)) (wins wins0))
          (:instance hbhp-iters-complete
                     (rest (nthcdr (hbhp-hc-k0) vb)) (xd (car (hbhp-hc-out0))))
          ,@(hbhp-hc-first-uses))
    :in-theory '(hbhp-hux-gadget hbhp-hux-canon hbhp-hux-wires-okp
                 r1cs::r1cs-constraints-holdp-of-append
                 hbhp-max-bits-per-iteration
                 hbhp-hc-len-append acl2::len-of-nat=>lebits
                 acl2::bit-listp-of-nat=>lebits bit-listp-of-hbhp-domain-bits
                 (:e hbhp-domain-size) (:e hbhp-data-bits) (:e expt)
                 acl2::pos-fix posp natp nfix (:t len))
    :do-not-induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PathHash::hash_children.  l and r are the wires of the two field
;; elements; fl, rl (fr, rr) the bit and range-check wires of
;; Field::write_bits_le of l (r).  The hash input is [true] ++ fl ++ fr.

(define hbhp-hc-gadget (l r fl rl fr rr cbits wins0 its gens (w posp) m c (max posp)
                        u (p posp))
  :verify-guards nil
  (append (fb-field-write-bits-le-gadget l fl rl u p)
          (fb-field-write-bits-le-gadget r fr rr u p)
          (hbhp-hux-gadget cbits (append fl fr) wins0 its gens w m c max u p)))

(define hbhp-hc-out (fl fr cbits wins0 its gens (w posp) m c (max posp))
  :verify-guards nil
  :short "The output wires of hash_uncompressed; BHP::hash returns the first."
  (hbhp-hux-out cbits (append fl fr) wins0 its gens w m c max))

;; The booleanity of fl and fr, required by the hasher's wire conditions,
;; is enforced by Field::write_bits_le.

(define hbhp-hc-wires-okp (l r fl rl fr rr cbits wins0 its gens (w posp) m c
                           (max posp) asg)
  :verify-guards nil
  (and (symbolp l) (r1cs::valuation-bindsp asg l)
       (symbolp r) (r1cs::valuation-bindsp asg r)
       (symbol-listp fl) (equal (len fl) (integer-length (base-prime)))
       (symbol-listp rl) (equal (len rl) (bits-lt-prime-rlen (base-prime)))
       (symbol-listp fr) (equal (len fr) (integer-length (base-prime)))
       (symbol-listp rr) (equal (len rr) (bits-lt-prime-rlen (base-prime)))
       (r1cs::valuation-binds-allp asg fl) (r1cs::valuation-binds-allp asg rl)
       (r1cs::valuation-binds-allp asg fr) (r1cs::valuation-binds-allp asg rr)
       (implies (bit-listp (lookup-equal-list (append fl fr) asg))
                (hbhp-hux-wires-okp cbits (append fl fr) wins0 its gens w m c max
                                    asg))))

(define hbhp-hc-canon (l r fl rl fr rr cbits wins0 its gens (w posp) m c (max posp)
                       asg)
  :verify-guards nil
  (and (equal (lookup-equal-list fl asg) (field-bits-le (lookup-equal l asg)))
       (equal (lookup-equal-list rl asg)
              (fb-bits-lte-const-witness (lookup-equal-list fl asg)
                                         (nat=>lebits* (1- (base-prime)))))
       (equal (lookup-equal-list fr asg) (field-bits-le (lookup-equal r asg)))
       (equal (lookup-equal-list rr asg)
              (fb-bits-lte-const-witness (lookup-equal-list fr asg)
                                         (nat=>lebits* (1- (base-prime)))))
       (hbhp-hux-canon cbits (append fl fr) wins0 its gens w m c max asg)))

(defmacro hbhp-hc-bits ()
  '(cons 1 (append (field-bits-le (lookup-equal l asg))
                   (field-bits-le (lookup-equal r asg)))))

(defruled hbhp-hc-instance-params
  (implies (hbhp-sizep size)
           (b* ((w (hbhp-size-window-size size))
                (gens (hbhp-setup-gens size)))
             (and (< (* 3 (- w (mod 84 w))) (hbhp-max-bits-per-iteration gens w))
                  (<= (* 3 (- w (mod 84 w))) 506))))
  :in-theory '(hbhp-len-of-setup-gens hbhp-max-bits-per-iteration member-equal
               (:e hbhp-size-window-size) (:e hbhp-size-num-windows)
               (:e hbhp-data-bits) (:e mod) (:e acl2::pos-fix)
               (:e <) (:e binary-*) (:e binary-+) (:e unary--) (:e equal)
               (:e len)))

(defmacro hbhp-bhp-hc-hyps ()
  '(and (hbhp-sizep size)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal w (hbhp-size-window-size size))
        (equal gens (hbhp-setup-gens size))
        (equal domain (hbhp-size-domain size))
        (equal m (floor 84 w))
        (equal c (mod 84 w))
        (equal cbits (append (hbhp-domain-bits domain) (acl2::nat=>lebits 64 507)))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)
        (hbhp-hc-wires-okp l r fl rl fr rr cbits wins0 its gens w m c max asg)))

(defruledl hbhp-hc-len-507
  (implies (and (equal (len fl) (integer-length (base-prime)))
                (equal (len fr) (integer-length (base-prime))))
           (and (equal (len (append fl fr)) 506)
                (equal (mod (+ 1 (len (append fl fr))) (expt 2 64)) 507)))
  :use fb-integer-length-of-base-prime
  :in-theory '(hbhp-hc-len-append (:e base-field-size-in-bits) (:e expt) (:e mod)
               (:e binary-+)))

(defruledl hbhp-hc-oddp-base-prime
  (oddp (base-prime))
  :in-theory '((:e base-prime) (:e oddp)))

(defruledl hbhp-hc-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var x)
                   (r1cs::prime (base-prime)) (r1cs::valuation asg))
        primep-of-base-prime)
  :in-theory '(fieldp))

(defruledl hbhp-hc-lookup-list-of-append
  (equal (lookup-equal-list (append a b) asg)
         (append (lookup-equal-list a asg) (lookup-equal-list b asg)))
  :use ((:instance hbhp-hu-lk-list-is-lookup-equal-list (bs (append a b)))
        (:instance hbhp-hu-lk-list-is-lookup-equal-list (bs a))
        (:instance hbhp-hu-lk-list-is-lookup-equal-list (bs b))
        (:instance hbhp-hu-lk-list-of-append))
  :in-theory nil)

(defruled hbhp-bhp-hc-sound
  (implies (and (hbhp-bhp-hc-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hc-gadget l r fl rl fr rr cbits wins0 its gens w m c max u p)
                 asg p))
           (b* ((out (hbhp-hc-out fl fr cbits wins0 its gens w m c max)))
             (and (equal (ecurve::point-finite (lookup-equal (car out) asg)
                                               (lookup-equal (cdr out) asg))
                         (hbhp-bhp-hash-uncompressed size (hbhp-hc-bits)))
                  (equal (nfix (lookup-equal (car out) asg))
                         (hbhp-bhp-hash size (hbhp-hc-bits))))))
  :use (hbhp-hu-instance-params hbhp-hc-instance-params hbhp-hc-len-507
        (:instance hbhp-hu-fbs-sound (xd l) (fbs fl) (rs rl))
        (:instance hbhp-hu-fbs-sound (xd r) (fbs fr) (rs rr))
        (:instance hbhp-hc-bit-listp-append
                   (a (lookup-equal-list fl asg)) (b (lookup-equal-list fr asg)))
        (:instance hbhp-hc-lookup-list-of-append (a fl) (b fr))
        (:instance hbhp-hu-lk-list-of-append (a fl) (b fr))
        (:instance hbhp-hux-sound (vb (append fl fr)))
        (:instance hbhp-hu-not-reserrp-point
                   (x (lookup-equal (car (hbhp-hc-out fl fr cbits wins0 its gens w m c max))
                                    asg))
                   (y (lookup-equal (cdr (hbhp-hc-out fl fr cbits wins0 its gens w m c max))
                                    asg)))
        (:instance ecurve::point-finite->x-of-point-finite
                   (ecurve::x (lookup-equal
                               (car (hbhp-hc-out fl fr cbits wins0 its gens w m c max))
                               asg))
                   (ecurve::y (lookup-equal
                               (cdr (hbhp-hc-out fl fr cbits wins0 its gens w m c max))
                               asg))))
  :in-theory '(hbhp-hc-gadget hbhp-hc-out hbhp-hc-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-bhp-hash-uncompressed hbhp-bhp-hash)
  :do-not-induct t)

(defruled hbhp-bhp-hc-complete
  (implies (and (hbhp-bhp-hc-hyps)
                (hbhp-hc-canon l r fl rl fr rr cbits wins0 its gens w m c max asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hc-gadget l r fl rl fr rr cbits wins0 its gens w m c max u p)
            asg p))
  :use (hbhp-hu-instance-params hbhp-hc-instance-params hbhp-hc-len-507
        primep-of-base-prime hbhp-hc-oddp-base-prime
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x l) (bits fl) (rs rl))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (x r) (bits fr) (rs rr))
        (:instance hbhp-hc-fieldp-of-lookup (x l))
        (:instance hbhp-hc-fieldp-of-lookup (x r))
        (:instance bit-listp-of-field-bits-le (x (lookup-equal l asg)))
        (:instance bit-listp-of-field-bits-le (x (lookup-equal r asg)))
        (:instance hbhp-hc-bit-listp-append
                   (a (lookup-equal-list fl asg)) (b (lookup-equal-list fr asg)))
        (:instance hbhp-hc-lookup-list-of-append (a fl) (b fr))
        (:instance hbhp-hux-complete (vb (append fl fr))))
  :in-theory '(hbhp-hc-gadget hbhp-hc-canon hbhp-hc-wires-okp
               r1cs::r1cs-constraints-holdp-of-append)
  :do-not-induct t)
