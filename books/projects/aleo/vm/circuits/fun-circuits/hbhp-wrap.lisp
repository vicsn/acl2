; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Building blocks for BHP::hash_uncompressed, whose first preimage starts
; with 252 constant bits (domain || length), a multiple of the chunk size.
;
;  - hbhp-rest-full-gadget: the windows after a given accumulator, the last
;    one possibly padded.
;  - hbhp-cwin-acc: snarkVM's native evaluation of the constant chunks of a
;    window (montgomery_add on constants is computed by the witness closures
;    and emits no constraint, since every operand is constant).
;  - hbhp-mwindow-gadget: the variable chunks of the window that straddles
;    the constant/variable boundary.  The accumulator entering the first
;    variable chunk is the constant (Cu, Cv), so montgomery_add takes the
;    constant linear combinations Cu and Cv as `this'.
;  - hbhp-kadd-gadget: Group::add of a variable point (`this', the window)
;    and a constant point (`that', the sum of the constant windows).  The
;    products with a constant factor are scalings, so only three constraints
;    remain: v0 * v1 = v01 and the two division checks.

(in-package "ALEOVM")

(include-book "hbhp-const")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

(defruledl hbhp-w-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The windows after an accumulator.

(defruledl hbhp-w-floor-bounds
  (implies (and (natp x) (posp m))
           (and (natp (floor x m))
                (<= (* m (floor x m)) x)
                (< x (+ m (* m (floor x m))))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-w-q-lemma
  (implies (and (posp m) (natp q) (natp g) (natp n)
                (<= (* m q) (- n 1)) (< (- n 1) (+ m (* m q)))
                (< 0 n) (<= n (* m g)))
           (< q g))
  :hints (("Goal" :nonlinearp t))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-w-mod3
  (implies (and (integerp k) (integerp n))
           (and (equal (mod (* 3 k) 3) 0)
                (equal (mod (- n (* 3 k)) 3) (mod n 3))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-nfull-facts0
  (implies (and (posp w) (natp g) (< 0 (len bits))
                (<= (len bits) (* 3 w g)))
           (b* ((q (hbhp-nfull bits w)) (f (* 3 w q)))
             (and (natp q)
                  (< q g)
                  (natp f)
                  (< f (len bits))
                  (<= (- (len bits) f) (* 3 w))
                  (equal (mod f 3) 0)
                  (equal (mod (- (len bits) f) 3) (mod (len bits) 3)))))
  :use ((:instance hbhp-w-floor-bounds (x (- (len bits) 1)) (m (* 3 w)))
        (:instance hbhp-w-q-lemma (m (* 3 w)) (n (len bits))
                   (q (floor (- (len bits) 1) (* 3 w))))
        (:instance hbhp-w-mod3 (k (* w (floor (- (len bits) 1) (* 3 w))))
                   (n (len bits))))
  :in-theory (e/d (hbhp-nfull) (floor mod))
  :hints (("Goal" :nonlinearp t))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(define hbhp-rest-full-gadget (bits wins gens (w posp) xacc yacc (p posp))
  :verify-guards nil
  :short "The windows of @('bits') folded into the accumulator
          @('(xacc, yacc)'); the last window is padded when the length is
          not a multiple of 3."
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-rest bits wins gens w xacc yacc p)
    (b* ((q (hbhp-nfull bits w))
         (f (* 3 (acl2::pos-fix w) q))
         (pre (take f bits))
         (lst (nthcdr f bits))
         (r (nth q wins))
         (out (hbhp-hasher-rest-out pre wins gens w xacc yacc)))
      (append (hbhp-hasher-rest pre wins gens w xacc yacc p)
              (hbhp-pwindow-gadget lst (nth 0 r) (nth q gens) (nth 1 r) (nth 2 r) p)
              (crv-group-add-gadget (nth 1 r) (nth 2 r) (car out) (cdr out)
                                    (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r)
                                    (nth 7 r) (nth 8 r) p)))))

(define hbhp-rest-full-out (bits wins gens (w posp) xacc yacc)
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-rest-out bits wins gens w xacc yacc)
    (b* ((r (nth (hbhp-nfull bits w) wins)))
      (cons (nth 7 r) (nth 8 r)))))

(define hbhp-rest-full-wires-okp (bits wins gens (w posp) xacc yacc asg)
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-rest-wires-okp bits wins gens w asg)
    (b* ((q (hbhp-nfull bits w))
         (f (* 3 (acl2::pos-fix w) q))
         (pre (take f bits))
         (lst (nthcdr f bits))
         (r (nth q wins))
         (out (hbhp-hasher-rest-out pre wins gens w xacc yacc)))
      (and (hbhp-hasher-rest-wires-okp pre wins gens w asg)
           (hbhp-pwindow-wires-okp lst (nth 0 r) (nth 1 r) (nth 2 r) asg)
           (hbhp-wire-okp (car out)) (hbhp-wire-okp (cdr out))
           (hbhp-wire-okp (nth 3 r)) (hbhp-wire-okp (nth 4 r))
           (hbhp-wire-okp (nth 5 r)) (hbhp-wire-okp (nth 6 r))
           (hbhp-wire-okp (nth 7 r)) (hbhp-wire-okp (nth 8 r))))))

(define hbhp-rest-full-canon (bits wins gens (w posp) xacc yacc acc asg)
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-rest-canon bits wins gens w xacc yacc acc asg)
    (b* ((p (base-prime))
         (q (hbhp-nfull bits w))
         (f (* 3 (acl2::pos-fix w) q))
         (pre (take f bits))
         (lst (nthcdr f bits))
         (r (nth q wins))
         (out (hbhp-hasher-rest-out pre wins gens w xacc yacc))
         (acc2 (hbhp-hasher-sum (hbhp-lk-list pre asg) gens w acc))
         (pw (hbhp-gp (hbhp-pwindow-scalar lst asg) (nth q gens))))
      (and (hbhp-hasher-rest-canon pre wins gens w xacc yacc acc asg)
           (hbhp-pwindow-canon lst (nth 0 r) (nth q gens) (nth 1 r) (nth 2 r) asg)
           (hbhp-add-canon (nth 1 r) (nth 2 r) (car out) (cdr out)
                           (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r)
                           (nth 7 r) (nth 8 r)
                           (ecurve::edwards-bls12-add pw acc2))))))

(defruledl hbhp-w-len-of-take
  (equal (len (take n x)) (nfix n)))

(defruledl hbhp-w-pos-len
  (implies (< 0 (len x)) (consp x)))

(defruledl hbhp-w-mod-nonzero-len
  (implies (not (equal (mod (len x) 3) 0)) (< 0 (len x))))

(defmacro hbhp-rest-full-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
        (posp w) (<= w 63)
        (<= (len bits) (* 3 w (len gens)))
        (ecurve::edwards-bls12-pointp acc)
        (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
        (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
        (hbhp-rest-full-wires-okp bits wins gens w xacc yacc asg)))

(defun hbhp-rest-full-pad-uses (thm)
  (declare (xargs :guard t :mode :program))
  `((:instance hbhp-nfull-facts0 (g (len gens)))
    (:instance hbhp-hasher-rest-sound
               (bits (take (* 3 w (hbhp-nfull bits w)) bits)))
    (:instance ,thm
               (lst (nthcdr (* 3 w (hbhp-nfull bits w)) bits))
               (g (nth (hbhp-nfull bits w) gens))
               (acc (hbhp-hasher-sum
                     (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg)
                     gens w acc))
               (ws (nth 0 (nth (hbhp-nfull bits w) wins)))
               (ex (nth 1 (nth (hbhp-nfull bits w) wins)))
               (ey (nth 2 (nth (hbhp-nfull bits w) wins)))
               (xacc (car (hbhp-hasher-rest-out
                           (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w
                           xacc yacc)))
               (yacc (cdr (hbhp-hasher-rest-out
                           (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w
                           xacc yacc)))
               (u (nth 3 (nth (hbhp-nfull bits w) wins)))
               (v0 (nth 4 (nth (hbhp-nfull bits w) wins)))
               (v1 (nth 5 (nth (hbhp-nfull bits w) wins)))
               (v01 (nth 6 (nth (hbhp-nfull bits w) wins)))
               (x3 (nth 7 (nth (hbhp-nfull bits w) wins)))
               (y3 (nth 8 (nth (hbhp-nfull bits w) wins))))
    (:instance hbhp-gen-okp-of-nth (q (hbhp-nfull bits w)))
    (:instance hbhp-pointp-of-hasher-sum
               (bits (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg)))
    (:instance hbhp-w-len-of-take (n (* 3 w (hbhp-nfull bits w))) (x bits))
    (:instance hbhp-w-mod-nonzero-len (x bits))))

(make-event
 `(defruled hbhp-rest-full-sound
  (implies (and (hbhp-rest-full-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-rest-full-gadget bits wins gens w xacc yacc p) asg p))
           (b* ((out (hbhp-rest-full-out bits wins gens w xacc yacc)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-hasher-sum (hbhp-pad (hbhp-lk-list bits asg)) gens w acc))))
  :use (hbhp-hasher-rest-sound
        (:instance hbhp-pad-when-mod-3 (x (hbhp-lk-list bits asg)))
        (:instance hbhp-phasher-spec-split
                   (q (hbhp-nfull bits w))
                   (pre (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg))
                   (lst (hbhp-lk-list (nthcdr (* 3 w (hbhp-nfull bits w)) bits) asg)))
        (:instance hbhp-append-take-nthcdr
                   (n (* 3 w (hbhp-nfull bits w))) (x (hbhp-lk-list bits asg)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (* 3 w (hbhp-nfull bits w))))
        (:instance hbhp-nthcdr-of-lk-list (bs bits) (n (* 3 w (hbhp-nfull bits w))))
        (:instance hbhp-consp-of-lk-list
                   (bs (nthcdr (* 3 w (hbhp-nfull bits w)) bits)))
        ,@(hbhp-rest-full-pad-uses 'hbhp-phasher-last-step))
  :in-theory '(hbhp-rest-full-gadget hbhp-rest-full-out hbhp-rest-full-wires-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-len-of-lk-list hbhp-true-listp-of-lk-list
               acl2::pos-fix posp natp nfix
               hbhp-w-len-of-nthcdr (:t len) car-cons cdr-cons hbhp-w-pos-len)))

(make-event
 `(defruled hbhp-rest-full-complete
    (implies (and (hbhp-rest-full-hyps)
                  (hbhp-rest-full-canon bits wins gens w xacc yacc acc asg))
             (r1cs::r1cs-constraints-holdp
              (hbhp-rest-full-gadget bits wins gens w xacc yacc p) asg p))
    :use (hbhp-hasher-rest-complete
          (:instance hbhp-hasher-rest-complete
                     (bits (take (* 3 w (hbhp-nfull bits w)) bits)))
          ,@(hbhp-rest-full-pad-uses 'hbhp-phasher-last-step-complete))
    :in-theory '(hbhp-rest-full-gadget hbhp-rest-full-canon
                 hbhp-rest-full-wires-okp
                 r1cs::r1cs-constraints-holdp-of-append
                 hbhp-len-of-lk-list hbhp-true-listp-of-lk-list
                 acl2::pos-fix posp natp nfix
                 hbhp-w-len-of-nthcdr (:t len) car-cons cdr-cons
                 hbhp-w-pos-len)))
