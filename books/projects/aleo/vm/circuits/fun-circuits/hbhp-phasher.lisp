; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHPHasher::hash_uncompressed for every accepted input length: when the
; length is not a multiple of 3, the full windows are emitted as by
; hbhp-hasher-gadget and the last window by hbhp-pwindow-gadget, followed by
; the Group::add into the accumulator.

(in-package "ALEOVM")

(include-book "hbhp-pad")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

(defruledl hbhp-ph-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Relation of the padded window scalar to hbhp-pad and hbhp-window-scalar.

(defruled hbhp-pad-of-append
  (implies (equal (mod (len a) 3) 0)
           (equal (hbhp-pad (append a b)) (append a (hbhp-pad b))))
  :enable hbhp-pad
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defun hbhp-p-ws-induct (a j)
  (declare (xargs :measure (len a)
                  :hints (("Goal" :in-theory (enable hbhp-ph-len-of-nthcdr)))))
  (if (< (len a) 3) j (hbhp-p-ws-induct (nthcdr 3 a) (+ 1 j))))

(defruledl hbhp-ph-app3
  (implies (<= 3 (len a))
           (and (equal (nthcdr 3 (append a b)) (append (nthcdr 3 a) b))
                (equal (car (append a b)) (car a))
                (equal (cadr (append a b)) (cadr a))
                (equal (caddr (append a b)) (caddr a))))
  :expand ((append a b) (append (cdr a) b) (append (cddr a) b)))

(defruled hbhp-window-scalar-of-append
  (implies (and (equal (mod (len a) 3) 0) (natp j))
           (equal (hbhp-window-scalar (append a b) j)
                  (+ (hbhp-window-scalar a j)
                     (hbhp-window-scalar b (+ j (/ (len a) 3))))))
  :induct (hbhp-p-ws-induct a j)
  :hints (("Goal" :in-theory (e/d (hbhp-ph-app3 hbhp-ph-len-of-nthcdr)
                                  (hbhp-window-scalar)))
          ("Subgoal *1/2" :expand ((hbhp-window-scalar (append a b) j)
                                   (hbhp-window-scalar a j)))
          ("Subgoal *1/1" :expand ((hbhp-window-scalar a j)
                                   (append a b))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-window-scalar-of-append-3k
  (implies (and (natp k) (equal (len a) (* 3 k)))
           (and (equal (hbhp-window-scalar (append a b) 0)
                       (+ (hbhp-window-scalar a 0) (hbhp-window-scalar b k)))
                (equal (hbhp-pad (append a b)) (append a (hbhp-pad b)))))
  :use ((:instance hbhp-window-scalar-of-append (j 0))
        hbhp-pad-of-append)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-ph-lk-list-1
  (implies (and (consp tl) (not (consp (cdr tl))))
           (equal (hbhp-lk-list tl asg) (list (hbhp-lk (car tl)))))
  :expand ((hbhp-lk-list tl asg) (hbhp-lk-list (cdr tl) asg)))

(defruledl hbhp-ph-lk-list-2
  (implies (and (consp tl) (consp (cdr tl)) (not (consp (cddr tl))))
           (equal (hbhp-lk-list tl asg)
                  (list (hbhp-lk (car tl)) (hbhp-lk (cadr tl)))))
  :expand ((hbhp-lk-list tl asg) (hbhp-lk-list (cdr tl) asg)
           (hbhp-lk-list (cddr tl) asg)))

(defruledl hbhp-ph-pad-12
  (and (equal (hbhp-pad (list x)) (list x 0 0))
       (equal (hbhp-pad (list x y)) (list x y 0)))
  :enable hbhp-pad)

(defruledl hbhp-ph-ws3
  (implies (natp k)
           (equal (hbhp-window-scalar (list x y z) k)
                  (* (hbhp-chunk-scalar x y z) (expt 16 k))))
  :expand ((hbhp-window-scalar (list x y z) k)
           (hbhp-window-scalar nil (+ 1 k))))

(defruledl hbhp-ph-nth01
  (and (equal (nth 0 x) (car x)) (equal (nth 1 x) (cadr x))))

(defruledl hbhp-ph-len0
  (equal (equal (len x) 0) (not (consp x))))

(defruled hbhp-window-scalar-of-pad-tail
  (implies (and (consp tl) (< (len tl) 3) (natp k))
           (equal (hbhp-window-scalar (hbhp-pad (hbhp-lk-list tl asg)) k)
                  (* (hbhp-pc tl) (expt 16 k))))
  :cases ((consp (cdr tl)))
  :in-theory '(hbhp-ph-lk-list-1 hbhp-ph-lk-list-2 hbhp-ph-pad-12 hbhp-ph-ws3
               hbhp-pb1 hbhp-ph-nth01 hbhp-ph-len0 car-cons cdr-cons
               (:t len) natp fix)
  :do-not-induct t
  :hints (("Subgoal 1" :expand ((len tl) (len (cdr tl))))))

(defruled hbhp-append-take-nthcdr
  (implies (<= (nfix n) (len x))
           (equal (append (take n x) (nthcdr n x)) x))
  :induct (take n x)
  :enable (take nthcdr))

(defruledl hbhp-ph-nthcdr-0
  (equal (nthcdr 0 x) x))

(defruled hbhp-pwindow-scalar-is-spec
  (implies (and (< (len bs) 189)
                (consp (nthcdr (* 3 (hbhp-pwindow-k bs)) bs))
                (< (len (nthcdr (* 3 (hbhp-pwindow-k bs)) bs)) 3))
           (equal (hbhp-window-scalar (hbhp-pad (hbhp-lk-list bs asg)) 0)
                  (hbhp-pwindow-scalar bs asg)))
  :use (hbhp-pwindow-k-facts
        (:instance hbhp-append-take-nthcdr
                   (n (* 3 (hbhp-pwindow-k bs))) (x (hbhp-lk-list bs asg)))
        (:instance hbhp-take-of-lk-list (n (* 3 (hbhp-pwindow-k bs))))
        (:instance hbhp-nthcdr-of-lk-list (n (* 3 (hbhp-pwindow-k bs))))
        (:instance hbhp-window-scalar-of-append-3k
                   (a (hbhp-lk-list (take (* 3 (hbhp-pwindow-k bs)) bs) asg))
                   (b (hbhp-pad (hbhp-lk-list (nthcdr (* 3 (hbhp-pwindow-k bs)) bs)
                                              asg)))
                   (k (hbhp-pwindow-k bs)))
        (:instance hbhp-window-scalar-of-append-3k
                   (a (hbhp-lk-list (take (* 3 (hbhp-pwindow-k bs)) bs) asg))
                   (b (hbhp-lk-list (nthcdr (* 3 (hbhp-pwindow-k bs)) bs) asg))
                   (k (hbhp-pwindow-k bs)))
        (:instance hbhp-window-scalar-of-pad-tail
                   (tl (nthcdr (* 3 (hbhp-pwindow-k bs)) bs))
                   (k (hbhp-pwindow-k bs)))
        (:instance hbhp-steps-scalar-is-window-scalar
                   (bs (take (* 3 (hbhp-pwindow-k bs)) bs)) (j 0)))
  :in-theory '(hbhp-pwindow-scalar hbhp-len-of-lk-list zp natp
               (:e expt) nfix (:e hbhp-lk-list) (:e hbhp-pad)
               (:e hbhp-window-scalar) hbhp-ph-nthcdr-0 (:e take))
  :cases ((zp (hbhp-pwindow-k bs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The window split: q full windows of 3w bits, then the last window.

(define hbhp-nfull (bits (w posp))
  :verify-guards nil
  :short "The number of windows before the last one."
  (floor (- (len bits) 1) (* 3 (acl2::pos-fix w))))

(defruledl hbhp-ph-floor-bounds
  (implies (and (natp x) (posp m))
           (and (natp (floor x m))
                (<= (* m (floor x m)) x)
                (< x (+ m (* m (floor x m))))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-ph-q-lemma
  (implies (and (posp m) (natp q) (natp g) (natp n)
                (<= (* m q) (- n 1)) (< (- n 1) (+ m (* m q)))
                (< m n) (<= n (* m g)))
           (and (posp q) (< q g)))
  :hints (("Goal" :nonlinearp t))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-ph-mod3
  (implies (and (integerp k) (integerp n))
           (and (equal (mod (* 3 k) 3) 0)
                (equal (mod (- n (* 3 k)) 3) (mod n 3))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-nfull-facts
  (implies (and (posp w) (natp g) (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w g)))
           (b* ((q (hbhp-nfull bits w)) (f (* 3 w q)))
             (and (posp q)
                  (< q g)
                  (natp f)
                  (<= (* 3 w) f)
                  (< f (len bits))
                  (<= (- (len bits) f) (* 3 w))
                  (equal (mod f 3) 0)
                  (equal (mod (- (len bits) f) 3) (mod (len bits) 3)))))
  :use ((:instance hbhp-ph-floor-bounds (x (- (len bits) 1)) (m (* 3 w)))
        (:instance hbhp-ph-q-lemma (m (* 3 w)) (n (len bits))
                   (q (floor (- (len bits) 1) (* 3 w))))
        (:instance hbhp-ph-mod3 (k (* w (floor (- (len bits) 1) (* 3 w))))
                   (n (len bits))))
  :in-theory (e/d (hbhp-nfull) (floor mod))
  :hints (("Goal" :nonlinearp t))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;; The spec fold over a split input.

(defun hbhp-ph-sum-induct (a gens w acc q)
  (declare (xargs :measure (nfix q)))
  (if (zp q)
      (list a gens w acc)
    (hbhp-ph-sum-induct (nthcdr (* 3 w) a) (cdr gens) w
                        (ecurve::edwards-bls12-add
                         acc
                         (ecurve::edwards-bls12-mul
                          (hbhp-window-scalar (take (* 3 w) a) 0) (car gens)))
                        (- q 1))))

(defruledl hbhp-ph-take-nthcdr-append
  (implies (<= (nfix n) (len a))
           (and (equal (take n (append a b)) (take n a))
                (equal (nthcdr n (append a b)) (append (nthcdr n a) b))))
  :induct (take n a)
  :enable (take nthcdr))

(defruledl hbhp-ph-sum-arith
  (implies (and (posp w) (natp q) (not (zp q)) (equal la (* 3 w q)))
           (and (<= (* 3 w) la)
                (< 0 la)
                (natp (* 3 w))
                (equal (- la (* 3 w)) (* 3 w (+ -1 q)))
                (natp (+ -1 q))))
  :hints (("Goal" :nonlinearp t))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-ph-list-facts
  (and (implies (< 0 (len x)) (consp x))
       (implies (consp a) (consp (append a b)))
       (equal (len (append a b)) (+ (len a) (len b)))))

(defruledl hbhp-ph-min
  (implies (and (<= m la) (natp lb) (rationalp m) (rationalp la))
           (equal (min m (+ la lb)) m)))

(defruledl hbhp-ph-min2
  (implies (and (<= m la) (rationalp m) (rationalp la))
           (equal (min m la) m)))

(defruled hbhp-hasher-sum-of-append
  (implies (and (posp w) (natp q) (equal (len a) (* 3 w q))
                (<= q (len gens)))
           (equal (hbhp-hasher-sum (append a b) gens w acc)
                  (hbhp-hasher-sum b (nthcdr q gens) w
                                   (hbhp-hasher-sum a gens w acc))))
  :induct (hbhp-ph-sum-induct a gens w acc q)
  :in-theory '((:induction hbhp-ph-sum-induct) hbhp-ph-take-nthcdr-append
               hbhp-ph-len-of-nthcdr hbhp-ph-sum-arith hbhp-ph-list-facts
               hbhp-ph-min hbhp-ph-min2 acl2::pos-fix posp natp nfix zp
               endp atom (:t len) (:t acl2::pos-fix) fix commutativity-of-+ hbhp-ph-nthcdr-0)
  :hints (("Subgoal *1/2"
           :use ((:instance hbhp-ph-sum-arith (la (len a))))
           :expand ((hbhp-hasher-sum (append a b) gens w acc)
                    (hbhp-hasher-sum a gens w acc)
                    (nthcdr q gens)
                    (len gens)))
          ("Subgoal *1/1"
           :expand ((hbhp-hasher-sum a gens w acc)
                    (len a) (append a b) (nthcdr q gens)))))

(defruledl hbhp-ph-nthcdr-len
  (implies (true-listp x) (equal (nthcdr (len x) x) nil))
  :induct (len x)
  :enable nthcdr)

(defruledl hbhp-ph-sum-nil
  (equal (hbhp-hasher-sum nil gs w acc) acc)
  :expand (hbhp-hasher-sum nil gs w acc))

(defruled hbhp-hasher-sum-last
  (implies (and (posp w) (consp b) (true-listp b) (<= (len b) (* 3 w))
                (consp gs))
           (equal (hbhp-hasher-sum b gs w acc)
                  (ecurve::edwards-bls12-add
                   acc (ecurve::edwards-bls12-mul (hbhp-window-scalar b 0)
                                                  (car gs)))))
  :expand ((hbhp-hasher-sum b gs w acc))
  :hints (("Goal" :in-theory (enable acl2::pos-fix hbhp-ph-nthcdr-len
                                     hbhp-ph-sum-nil))))

(defruledl hbhp-ph-ceil3-int
  (implies (and (integerp a) (integerp b) (< a (+ 1 b))) (<= a b)))

(defruledl hbhp-ph-ceil3-aux
  (implies (and (natp n) (posp w) (<= n (* 3 w)) (integerp f)
                (< (- n) (+ 3 (* 3 f))))
           (<= (* -3 f) (* 3 w)))
  :use ((:instance hbhp-ph-ceil3-int (a (- f)) (b w))))

(defruledl hbhp-ph-ceil3
  (implies (and (natp n) (posp w) (<= n (* 3 w)))
           (<= (+ n (mod (- n) 3)) (* 3 w)))
  :use ((:instance hbhp-ph-ceil3-aux (f (floor (- n) 3))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-len-of-pad-bound
  (implies (and (posp w) (<= (len x) (* 3 w)))
           (and (<= (len (hbhp-pad x)) (* 3 w))
                (true-listp (hbhp-pad x))
                (implies (consp x) (consp (hbhp-pad x)))))
  :use ((:instance hbhp-ph-ceil3 (n (len x))))
  :enable hbhp-pad
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generators and fold values.

(defruled hbhp-gen-okp-of-nth
  (implies (and (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
                (< (nfix q) (len gens)))
           (hbhp-gen-okp (nth q gens)))
  :induct (nth q gens)
  :enable (nth hbhp-r-point-listp hbhp-nonzero-listp))

(defruled hbhp-car-of-nthcdr
  (equal (car (nthcdr q x)) (nth q x))
  :enable (nth nthcdr))

(defruled hbhp-r-point-listp-of-nthcdr
  (implies (hbhp-r-point-listp gens)
           (hbhp-r-point-listp (nthcdr q gens)))
  :enable (nthcdr hbhp-r-point-listp))

(defruled hbhp-pointp-of-hasher-sum
  (implies (and (ecurve::edwards-bls12-pointp acc) (hbhp-r-point-listp gens))
           (ecurve::edwards-bls12-pointp (hbhp-hasher-sum bits gens w acc)))
  :induct (hbhp-hasher-sum bits gens w acc)
  :in-theory (e/d (hbhp-hasher-sum hbhp-r-point-listp
                   ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The full windows: hbhp-hasher-gadget yields the fold from zero.

(defruled hbhp-ph-len-of-take
  (equal (len (take n x)) (nfix n)))

(defruledl hbhp-ph-len-atom
  (implies (not (consp x)) (equal (len x) 0)))

(defruled hbhp-hasher-gadget-sum
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (<= (* 3 w) (len bits))
                (hbhp-hasher-wires-okp bits wins gens w asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-gadget bits wins gens w p) asg p))
           (b* ((out (hbhp-hasher-out bits wins gens w)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w
                                     (ecurve::twisted-edwards-zero)))))
  :use ((:instance hbhp-window-gadget-sound-spec
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-wires-okp-from-wwires
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins)))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-nchunks-ok (n (hbhp-win-n bits w)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (hbhp-win-n bits w)))
        (:instance hbhp-win-n-facts (len (len bits)))
        (:instance hbhp-hasher-rest-sound
                   (bits (nthcdr (hbhp-win-n bits w) bits))
                   (wins (cdr wins)) (gens (cdr gens))
                   (xacc (nth 1 (car wins))) (yacc (nth 2 (car wins)))
                   (acc (hbhp-gp (hbhp-window-scalar
                                  (take (hbhp-win-n bits w)
                                        (hbhp-lk-list bits asg)) 0)
                                 (car gens))))
        (:instance hbhp-add-zero-left
                   (pt (hbhp-gp (hbhp-window-scalar
                                 (take (hbhp-win-n bits w)
                                       (hbhp-lk-list bits asg)) 0)
                                (car gens))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (take (hbhp-win-n bits w)
                                          (hbhp-lk-list bits asg)) 0))
                   (point (car gens)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (car gens))))
  :in-theory '(hbhp-hasher-gadget hbhp-hasher-out
               hbhp-hasher-wires-okp hbhp-gens-okp hbhp-r-point-listp
               hbhp-nonzero-listp r1cs::r1cs-constraints-holdp-of-append
               hbhp-nthcdr-of-lk-list hbhp-consp-of-lk-list hbhp-len-of-lk-list
               hbhp-true-listp-of-lk-list acl2::pos-fix posp natp
               hbhp-ph-len-of-nthcdr nfix hbhp-ph-list-facts
               endp atom not car-cons cdr-cons (:t min) (:t len)
               (:t hbhp-lk-list) (:e ecurve::twisted-edwards-zero)
               hbhp-ph-len-of-take hbhp-wwires-okp hbhp-ph-len-atom)
  :hints (("Goal"
           :expand ((:free (gens acc)
                     (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w acc)))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The padded last window plus the addition into the accumulator.

(defruled hbhp-pwindow-wires-facts
  (implies (hbhp-pwindow-wires-okp bs ws ex ey asg)
           (and (consp (nthcdr (* 3 (hbhp-pwindow-k bs)) bs))
                (< (len (nthcdr (* 3 (hbhp-pwindow-k bs)) bs)) 3)
                (hbhp-wire-okp ex) (hbhp-wire-okp ey)))
  :enable (hbhp-pwindow-wires-okp hbhp-ptl-okp hbhp-window-wires-okp))

(defruledl hbhp-ph-len-lt-189
  (implies (and (posp w) (<= w 63) (<= n (* 3 w))
                (not (equal (mod n 3) 0)))
           (< n 189)))

(defruled hbhp-phasher-last-step
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (posp w) (<= w 63)
                (<= (len lst) (* 3 w))
                (not (equal (mod (len lst) 3) 0))
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-pwindow-wires-okp lst ws ex ey asg)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pwindow-gadget lst ws g ex ey p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-add-gadget ex ey xacc yacc u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (hbhp-lk x3) (hbhp-lk y3))
                  (ecurve::edwards-bls12-add
                   acc
                   (hbhp-gp (hbhp-window-scalar
                             (hbhp-pad (hbhp-lk-list lst asg)) 0)
                            g))))
  :use ((:instance hbhp-pwindow-gadget-sound (bs lst))
        (:instance hbhp-pwindow-wires-facts (bs lst))
        (:instance hbhp-pwindow-scalar-is-spec (bs lst))
        (:instance hbhp-ph-len-lt-189 (n (len lst)))
        (:instance crv-group-add-gadget-sound
                   (x1 ex) (y1 ey) (x2 xacc) (y2 yacc)
                   (p1 (hbhp-gp (hbhp-pwindow-scalar lst asg) g))
                   (p2 acc))
        (:instance hbhp-add-comm
                   (a acc) (b (hbhp-gp (hbhp-pwindow-scalar lst asg) g)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-pwindow-scalar lst asg)) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var xacc) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var yacc) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :in-theory (e/d (group-add-funspec hbhp-base-prime-facts pfield::fep)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                   hbhp-pwindow-gadget crv-group-add-gadget
                   hbhp-pwindow-wires-okp hbhp-pwindow-scalar
                   hbhp-window-scalar hbhp-lk-list hbhp-pad hbhp-pwindow-k
                   ecurve::edwards-bls12-r-pointp
                   ecurve::edwards-bls12-pointp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The padded hasher.  `wins' holds the window records of
;; hbhp-hasher-gadget; record q (the last window) is
;; (ws ex ey u v0 v1 v01 x3 y3) with ws the records of hbhp-pwindow-gadget.

(define hbhp-phasher-gadget (bits wins gens (w posp) (p posp))
  :verify-guards nil
  :short "The constraints of @('BHPHasher::hash_uncompressed') when the input
          length is not a multiple of 3."
  (b* ((q (hbhp-nfull bits w))
       (f (* 3 (acl2::pos-fix w) q))
       (pre (take f bits))
       (lst (nthcdr f bits))
       (r (nth q wins))
       (out (hbhp-hasher-out pre wins gens w)))
    (append (hbhp-hasher-gadget pre wins gens w p)
            (hbhp-pwindow-gadget lst (nth 0 r) (nth q gens) (nth 1 r) (nth 2 r) p)
            (crv-group-add-gadget (nth 1 r) (nth 2 r) (car out) (cdr out)
                                  (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r)
                                  (nth 7 r) (nth 8 r) p))))

(define hbhp-phasher-out (bits wins (w posp))
  :verify-guards nil
  (b* ((r (nth (hbhp-nfull bits w) wins)))
    (cons (nth 7 r) (nth 8 r))))

(define hbhp-phasher-wires-okp (bits wins gens (w posp) asg)
  :verify-guards nil
  (b* ((q (hbhp-nfull bits w))
       (f (* 3 (acl2::pos-fix w) q))
       (pre (take f bits))
       (lst (nthcdr f bits))
       (r (nth q wins))
       (out (hbhp-hasher-out pre wins gens w)))
    (and (hbhp-hasher-wires-okp pre wins gens w asg)
         (hbhp-pwindow-wires-okp lst (nth 0 r) (nth 1 r) (nth 2 r) asg)
         (hbhp-wire-okp (car out)) (hbhp-wire-okp (cdr out))
         (hbhp-wire-okp (nth 3 r)) (hbhp-wire-okp (nth 4 r))
         (hbhp-wire-okp (nth 5 r)) (hbhp-wire-okp (nth 6 r))
         (hbhp-wire-okp (nth 7 r)) (hbhp-wire-okp (nth 8 r)))))

(defruled hbhp-phasher-spec-split
  (implies (and (posp w) (natp q) (< q (len gens))
                (equal (len pre) (* 3 w q))
                (consp lst) (<= (len lst) (* 3 w)))
           (equal (hbhp-hasher-sum (hbhp-pad (append pre lst)) gens w acc)
                  (ecurve::edwards-bls12-add
                   (hbhp-hasher-sum pre gens w acc)
                   (ecurve::edwards-bls12-mul
                    (hbhp-window-scalar (hbhp-pad lst) 0) (nth q gens)))))
  :use ((:instance hbhp-pad-of-append (a pre) (b lst))
        (:instance hbhp-hasher-sum-of-append (a pre) (b (hbhp-pad lst)))
        (:instance hbhp-hasher-sum-last (b (hbhp-pad lst)) (gs (nthcdr q gens))
                   (acc (hbhp-hasher-sum pre gens w acc)))
        (:instance hbhp-len-of-pad-bound (x lst))
        hbhp-ph-mod-3wq
        (:instance hbhp-ph-consp-nthcdr (n q) (x gens)))
  :in-theory '(hbhp-car-of-nthcdr)
  :prep-lemmas
  ((defruled hbhp-ph-mod-3wq
     (implies (and (posp w) (natp q))
              (equal (mod (* 3 w q) 3) 0))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defruled hbhp-ph-consp-nthcdr
     (implies (and (natp n) (< n (len x))) (consp (nthcdr n x)))
     :enable nthcdr)))

(defruled hbhp-pointp-of-zero
  (ecurve::edwards-bls12-pointp '(0 . 1))
  :in-theory (enable (:e ecurve::edwards-bls12-pointp)))

(defruledl hbhp-ph-pos-len
  (implies (< 0 (len x)) (consp x)))

(defruled hbhp-phasher-gadget-sound
  :short "Soundness of @('BHPHasher::hash_uncompressed') when the input
          length is not a multiple of 3."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (not (equal (mod (len bits) 3) 0))
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-phasher-wires-okp bits wins gens w asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-phasher-gadget bits wins gens w p) asg p))
           (b* ((out (hbhp-phasher-out bits wins w)))
             (equal (hbhp-hasher-hash-uncompressed gens w (hbhp-lk-list bits asg))
                    (ecurve::point-finite (hbhp-lk (car out))
                                          (hbhp-lk (cdr out))))))
  :use ((:instance hbhp-nfull-facts (g (len gens)))
        (:instance hbhp-hasher-gadget-sum
                   (bits (take (* 3 w (hbhp-nfull bits w)) bits)))
        (:instance hbhp-phasher-last-step
                   (lst (nthcdr (* 3 w (hbhp-nfull bits w)) bits))
                   (g (nth (hbhp-nfull bits w) gens))
                   (acc (hbhp-hasher-sum
                         (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg)
                         gens w (ecurve::twisted-edwards-zero)))
                   (ws (nth 0 (nth (hbhp-nfull bits w) wins)))
                   (ex (nth 1 (nth (hbhp-nfull bits w) wins)))
                   (ey (nth 2 (nth (hbhp-nfull bits w) wins)))
                   (xacc (car (hbhp-hasher-out
                               (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w)))
                   (yacc (cdr (hbhp-hasher-out
                               (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w)))
                   (u (nth 3 (nth (hbhp-nfull bits w) wins)))
                   (v0 (nth 4 (nth (hbhp-nfull bits w) wins)))
                   (v1 (nth 5 (nth (hbhp-nfull bits w) wins)))
                   (v01 (nth 6 (nth (hbhp-nfull bits w) wins)))
                   (x3 (nth 7 (nth (hbhp-nfull bits w) wins)))
                   (y3 (nth 8 (nth (hbhp-nfull bits w) wins))))
        (:instance hbhp-gen-okp-of-nth (q (hbhp-nfull bits w)))
        (:instance hbhp-pointp-of-hasher-sum
                   (bits (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg))
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-phasher-spec-split
                   (q (hbhp-nfull bits w))
                   (pre (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg))
                   (lst (hbhp-lk-list (nthcdr (* 3 w (hbhp-nfull bits w)) bits) asg))
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-append-take-nthcdr
                   (n (* 3 w (hbhp-nfull bits w))) (x (hbhp-lk-list bits asg)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (* 3 w (hbhp-nfull bits w))))
        (:instance hbhp-nthcdr-of-lk-list (bs bits) (n (* 3 w (hbhp-nfull bits w))))
        (:instance hbhp-ph-len-of-take (n (* 3 w (hbhp-nfull bits w))) (x bits))
        (:instance hbhp-consp-of-lk-list
                   (bs (nthcdr (* 3 w (hbhp-nfull bits w)) bits))))
  :in-theory '(hbhp-hasher-hash-uncompressed hbhp-phasher-gadget hbhp-phasher-out
               hbhp-phasher-wires-okp hbhp-gens-okp
               r1cs::r1cs-constraints-holdp-of-append
               hbhp-len-of-lk-list acl2::pos-fix posp natp nfix
               hbhp-ph-len-of-nthcdr hbhp-pointp-of-zero
               (:e ecurve::twisted-edwards-zero) hbhp-ph-pos-len (:t len)
               car-cons cdr-cons))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness of the padded hasher.

(defruled hbhp-hasher-gadget-complete-ge
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (<= (* 3 w) (len bits))
                (hbhp-hasher-wires-okp bits wins gens w asg)
                (hbhp-hasher-canon bits wins gens w asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hasher-gadget bits wins gens w p) asg p))
  :use ((:instance hbhp-window-gadget-complete
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-gadget-sound-spec
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-wires-okp-from-wwires
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins)))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-nchunks-ok (n (hbhp-win-n bits w)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (hbhp-win-n bits w)))
        (:instance hbhp-win-n-facts (len (len bits)))
        (:instance hbhp-hasher-rest-complete
                   (bits (nthcdr (hbhp-win-n bits w) bits))
                   (wins (cdr wins)) (gens (cdr gens))
                   (xacc (nth 1 (car wins))) (yacc (nth 2 (car wins)))
                   (acc (hbhp-gp (hbhp-window-scalar
                                  (take (hbhp-win-n bits w)
                                        (hbhp-lk-list bits asg)) 0)
                                 (car gens))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (take (hbhp-win-n bits w)
                                          (hbhp-lk-list bits asg)) 0))
                   (point (car gens)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (car gens))))
  :in-theory '(hbhp-hasher-gadget hbhp-hasher-canon
               hbhp-hasher-wires-okp hbhp-gens-okp hbhp-r-point-listp
               hbhp-nonzero-listp r1cs::r1cs-constraints-holdp-of-append
               hbhp-len-of-lk-list acl2::pos-fix posp natp
               hbhp-ph-len-of-nthcdr nfix hbhp-ph-list-facts
               endp atom not car-cons cdr-cons (:t min) (:t len)
               hbhp-ph-len-of-take hbhp-wwires-okp hbhp-ph-len-atom))

(define hbhp-pwindow-canon (bs ws g ex ey asg)
  :verify-guards nil
  :short "The canonical witness of the padded last window."
  (b* ((p (base-prime))
       (k (hbhp-pwindow-k bs))
       (tl (nthcdr (* 3 k) bs))
       (full (take (* 3 k) bs))
       (r (nth k ws))
       (pt (hbhp-gp (hbhp-pwindow-scalar bs asg) g)))
    (and (implies (not (zp k))
                  (and (hbhp-window-canon full ws g ex ey asg)
                       (hbhp-mont-canon
                        (hbhp-gp (hbhp-steps-scalar full 0 asg) g)
                        (hbhp-gp (* (hbhp-pc tl) (expt 16 k)) g)
                        (nth 2 r) (nth 3 r) (nth 4 r))))
         (hbhp-pchunk-canon tl (nth 0 r) (nth 1 r) (hbhp-tab-y g k))
         (equal (hbhp-lk ex) (hbhp-x pt))
         (equal (hbhp-lk ey) (hbhp-y pt)))))

(defruled hbhp-phasher-last-step-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (posp w) (<= w 63)
                (<= (len lst) (* 3 w))
                (not (equal (mod (len lst) 3) 0))
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-pwindow-wires-okp lst ws ex ey asg)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (hbhp-pwindow-canon lst ws g ex ey asg)
                (hbhp-add-canon ex ey xacc yacc u v0 v1 v01 x3 y3
                                (ecurve::edwards-bls12-add
                                 (hbhp-gp (hbhp-pwindow-scalar lst asg) g)
                                 acc)))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-pwindow-gadget lst ws g ex ey p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-add-gadget ex ey xacc yacc u v0 v1 v01 x3 y3 p)
                 asg p)))
  :use ((:instance hbhp-pwindow-gadget-complete (bs lst))
        (:instance hbhp-pwindow-gadget-sound (bs lst))
        (:instance hbhp-pwindow-wires-facts (bs lst))
        (:instance hbhp-ph-len-lt-189 (n (len lst)))
        (:instance crv-group-add-gadget-complete
                   (x1 ex) (y1 ey) (x2 xacc) (y2 yacc)
                   (p1 (hbhp-gp (hbhp-pwindow-scalar lst asg) g))
                   (p2 acc))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-pwindow-scalar lst asg)) (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var xacc) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var yacc) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :in-theory (e/d (group-add-funspec hbhp-base-prime-facts pfield::fep
                   hbhp-pwindow-canon)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                   hbhp-pwindow-gadget crv-group-add-gadget
                   hbhp-pwindow-wires-okp hbhp-pwindow-scalar hbhp-window-canon
                   hbhp-window-scalar hbhp-lk-list hbhp-pad hbhp-pwindow-k
                   hbhp-pchunk-gadget hbhp-sel4 hbhp-pb1 hbhp-steps-scalar
                   ecurve::edwards-bls12-r-pointp
                   ecurve::edwards-bls12-pointp)))

(define hbhp-phasher-canon (bits wins gens (w posp) asg)
  :verify-guards nil
  :short "The canonical witness of the padded hasher gadget."
  (b* ((p (base-prime))
       (q (hbhp-nfull bits w))
       (f (* 3 (acl2::pos-fix w) q))
       (pre (take f bits))
       (lst (nthcdr f bits))
       (r (nth q wins))
       (out (hbhp-hasher-out pre wins gens w))
       (acc (hbhp-hasher-sum (hbhp-lk-list pre asg) gens w
                             (ecurve::twisted-edwards-zero)))
       (pw (hbhp-gp (hbhp-pwindow-scalar lst asg) (nth q gens))))
    (and (hbhp-hasher-canon pre wins gens w asg)
         (hbhp-pwindow-canon lst (nth 0 r) (nth q gens) (nth 1 r) (nth 2 r) asg)
         (hbhp-add-canon (nth 1 r) (nth 2 r) (car out) (cdr out)
                         (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r) (nth 7 r) (nth 8 r)
                         (ecurve::edwards-bls12-add pw acc)))))

(defruled hbhp-phasher-gadget-complete
  :short "Completeness of @('BHPHasher::hash_uncompressed') when the input
          length is not a multiple of 3."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (not (equal (mod (len bits) 3) 0))
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-phasher-wires-okp bits wins gens w asg)
                (hbhp-phasher-canon bits wins gens w asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-phasher-gadget bits wins gens w p) asg p))
  :use ((:instance hbhp-nfull-facts (g (len gens)))
        (:instance hbhp-hasher-gadget-complete-ge
                   (bits (take (* 3 w (hbhp-nfull bits w)) bits)))
        (:instance hbhp-hasher-gadget-sum
                   (bits (take (* 3 w (hbhp-nfull bits w)) bits)))
        (:instance hbhp-phasher-last-step-complete
                   (lst (nthcdr (* 3 w (hbhp-nfull bits w)) bits))
                   (g (nth (hbhp-nfull bits w) gens))
                   (acc (hbhp-hasher-sum
                         (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg)
                         gens w (ecurve::twisted-edwards-zero)))
                   (ws (nth 0 (nth (hbhp-nfull bits w) wins)))
                   (ex (nth 1 (nth (hbhp-nfull bits w) wins)))
                   (ey (nth 2 (nth (hbhp-nfull bits w) wins)))
                   (xacc (car (hbhp-hasher-out
                               (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w)))
                   (yacc (cdr (hbhp-hasher-out
                               (take (* 3 w (hbhp-nfull bits w)) bits) wins gens w)))
                   (u (nth 3 (nth (hbhp-nfull bits w) wins)))
                   (v0 (nth 4 (nth (hbhp-nfull bits w) wins)))
                   (v1 (nth 5 (nth (hbhp-nfull bits w) wins)))
                   (v01 (nth 6 (nth (hbhp-nfull bits w) wins)))
                   (x3 (nth 7 (nth (hbhp-nfull bits w) wins)))
                   (y3 (nth 8 (nth (hbhp-nfull bits w) wins))))
        (:instance hbhp-gen-okp-of-nth (q (hbhp-nfull bits w)))
        (:instance hbhp-pointp-of-hasher-sum
                   (bits (hbhp-lk-list (take (* 3 w (hbhp-nfull bits w)) bits) asg))
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-ph-len-of-take (n (* 3 w (hbhp-nfull bits w))) (x bits)))
  :in-theory '(hbhp-phasher-gadget hbhp-phasher-canon
               hbhp-phasher-wires-okp hbhp-gens-okp
               r1cs::r1cs-constraints-holdp-of-append
               acl2::pos-fix posp natp nfix
               hbhp-ph-len-of-nthcdr hbhp-pointp-of-zero
               (:e ecurve::twisted-edwards-zero) hbhp-ph-pos-len (:t len)
               car-cons cdr-cons))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every accepted input length.

(define hbhp-hasher-full-gadget (bits wins gens (w posp) (p posp))
  :verify-guards nil
  :short "The constraints of @('BHPHasher::hash_uncompressed') on variable
          bits of any accepted length."
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-gadget bits wins gens w p)
    (hbhp-phasher-gadget bits wins gens w p)))

(define hbhp-hasher-full-out (bits wins gens (w posp))
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-out bits wins gens w)
    (hbhp-phasher-out bits wins w)))

(define hbhp-hasher-full-wires-okp (bits wins gens (w posp) asg)
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-wires-okp bits wins gens w asg)
    (hbhp-phasher-wires-okp bits wins gens w asg)))

(define hbhp-hasher-full-canon (bits wins gens (w posp) asg)
  :verify-guards nil
  (if (equal (mod (len bits) 3) 0)
      (hbhp-hasher-canon bits wins gens w asg)
    (hbhp-phasher-canon bits wins gens w asg)))

(defruled hbhp-hasher-full-gadget-sound
  :short "Soundness of @('BHPHasher::hash_uncompressed') for every accepted
          input length."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-hasher-full-wires-okp bits wins gens w asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-full-gadget bits wins gens w p) asg p))
           (b* ((out (hbhp-hasher-full-out bits wins gens w)))
             (equal (hbhp-hasher-hash-uncompressed gens w (hbhp-lk-list bits asg))
                    (ecurve::point-finite (hbhp-lk (car out))
                                          (hbhp-lk (cdr out))))))
  :use (hbhp-hasher-gadget-sound hbhp-phasher-gadget-sound)
  :in-theory '(hbhp-hasher-full-gadget hbhp-hasher-full-out
               hbhp-hasher-full-wires-okp))

(defruled hbhp-hasher-full-gadget-complete
  :short "Completeness of @('BHPHasher::hash_uncompressed') for every
          accepted input length."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-hasher-full-wires-okp bits wins gens w asg)
                (hbhp-hasher-full-canon bits wins gens w asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-hasher-full-gadget bits wins gens w p) asg p))
  :use (hbhp-hasher-gadget-complete hbhp-phasher-gadget-complete)
  :in-theory '(hbhp-hasher-full-gadget hbhp-hasher-full-canon
               hbhp-hasher-full-wires-okp))
