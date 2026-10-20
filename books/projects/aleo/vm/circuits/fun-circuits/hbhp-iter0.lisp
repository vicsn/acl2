; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first iteration of BHP::hash_uncompressed, whose preimage starts with
; constant bits (domain || length): the windows made only of constant bits
; are evaluated natively (hbhp-const), then the straddling window
; (hbhp-mwin), then the remaining windows (hbhp-wrap).

(in-package "ALEOVM")

(include-book "hbhp-mwin")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

(defruled hbhp-mwindow-scalar-is-spec
  (implies (and (natp c) (< (+ (* 3 c) (len vb)) 190))
           (equal (hbhp-window-scalar (hbhp-pad (hbhp-lk-list vb asg)) c)
                  (hbhp-mwindow-scalar vb c asg)))
  :cases ((consp (hbhp-m-tl)))
  :use (hbhp-m-k-facts
        (:instance hbhp-append-take-nthcdr
                   (n (* 3 (hbhp-m-k))) (x (hbhp-lk-list vb asg)))
        (:instance hbhp-take-of-lk-list (bs vb) (n (* 3 (hbhp-m-k))))
        (:instance hbhp-nthcdr-of-lk-list (bs vb) (n (* 3 (hbhp-m-k))))
        (:instance hbhp-pad-of-append
                   (a (hbhp-lk-list (hbhp-m-full) asg))
                   (b (hbhp-lk-list (hbhp-m-tl) asg)))
        (:instance hbhp-window-scalar-of-append
                   (a (hbhp-lk-list (hbhp-m-full) asg))
                   (b (hbhp-pad (hbhp-lk-list (hbhp-m-tl) asg)))
                   (j c))
        (:instance hbhp-window-scalar-of-pad-tail
                   (tl (hbhp-m-tl)) (k (+ c (hbhp-m-k))))
        (:instance hbhp-steps-scalar-is-window-scalar
                   (bs (hbhp-m-full)) (j c))
        (:instance hbhp-consp-of-lk-list (bs (hbhp-m-tl))))
  :in-theory '(hbhp-mwindow-scalar hbhp-len-of-lk-list natp lnfix nfix
               hbhp-m-div3 hbhp-m-pad-nil hbhp-m-ws-nil hbhp-m-plus-0
               (:t hbhp-steps-scalar) hbhp-m-mod3k)
  :prep-lemmas
  ((defruled hbhp-m-mod3k
     (implies (natp k) (equal (mod (* 3 k) 3) 0))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defruled hbhp-m-div3
     (implies (natp k) (and (equal (* 1/3 (* 3 k)) k)
                            (equal (* (* 3 k) 1/3) k))))
   (defruled hbhp-m-pad-nil
     (implies (not (consp x)) (equal (hbhp-pad x) nil))
     :enable (hbhp-pad))
   (defruled hbhp-m-ws-nil
     (equal (hbhp-window-scalar nil j) 0)
     :enable hbhp-window-scalar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The windows made only of constant bits, folded natively from zero.

(define hbhp-cwin-point (bits g)
  :verify-guards nil
  (b* ((acc (hbhp-cwin-start bits g)))
    (hbhp-nedwards (car acc) (cdr acc))))

(defruledl hbhp-i-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

(define hbhp-cfold (bits gens (w posp) acc)
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :in-theory (enable hbhp-i-len-of-nthcdr acl2::pos-fix)))
  (b* ((w (acl2::pos-fix w))
       ((when (or (endp bits) (endp gens))) acc)
       (n (min (* 3 w) (len bits))))
    (hbhp-cfold (nthcdr n bits) (cdr gens) w
                (hbhp-nadd acc (hbhp-cwin-point (take n bits) (car gens))))))

(defruled hbhp-cwin-point-correct
  (implies (and (hbhp-gen-okp g) (posp w) (<= w 63)
                (bit-listp bits) (equal (len bits) (* 3 w)))
           (equal (hbhp-cwin-point bits g)
                  (hbhp-gp (hbhp-window-scalar bits 0) g)))
  :use (hbhp-cwin-start-correct
        (:instance hbhp-nchunks-of-3k (x bits) (k w))
        (:instance hbhp-nedwards-correct
                   (s (hbhp-window-scalar bits 0)) (j w)))
  :in-theory '(hbhp-cwin-point natp posp car-cons cdr-cons))

(defun hbhp-cfold-induct (bits gens w acc q)
  (declare (xargs :measure (len bits) :verify-guards nil
                  :hints (("Goal" :in-theory (enable hbhp-i-len-of-nthcdr
                                                     acl2::pos-fix)))))
  (b* ((w (acl2::pos-fix w))
       ((when (or (endp bits) (endp gens))) (list acc q))
       (n (min (* 3 w) (len bits))))
    (hbhp-cfold-induct (nthcdr n bits) (cdr gens) w
                       (ecurve::edwards-bls12-add
                        acc (hbhp-gp (hbhp-window-scalar (take n bits) 0)
                                     (car gens)))
                       (- q 1))))

(defruled hbhp-i-bit-listp-take
  (implies (and (bit-listp x) (<= (nfix n) (len x)))
           (bit-listp (take n x)))
  :induct (take n x)
  :enable (bit-listp take))

(defruled hbhp-i-bit-listp-nthcdr
  (implies (bit-listp x) (bit-listp (nthcdr n x)))
  :induct (nthcdr n x)
  :enable (bit-listp nthcdr))

(defruled hbhp-i-bit-listp-take-nthcdr
  (implies (and (bit-listp x) (<= (nfix n) (len x)))
           (and (bit-listp (take n x)) (bit-listp (nthcdr n x))))
  :enable (hbhp-i-bit-listp-take hbhp-i-bit-listp-nthcdr))

(defruledl hbhp-i-len-pos-when-consp
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)

(defruled hbhp-cfold-correct
  (implies (and (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
                (posp w) (<= w 63)
                (natp q) (<= q (len gens))
                (bit-listp bits) (equal (len bits) (* 3 w q))
                (ecurve::edwards-bls12-pointp acc))
           (equal (hbhp-cfold bits gens w acc)
                  (hbhp-hasher-sum bits gens w acc)))
  :induct (hbhp-cfold-induct bits gens w acc q)
  :in-theory '((:induction hbhp-cfold-induct) acl2::pos-fix posp natp nfix
               endp atom (:t len) (:e len) hbhp-i-len-pos-when-consp hbhp-r-point-listp hbhp-nonzero-listp)
  :hints (("Subgoal *1/2"
           :expand ((hbhp-cfold bits gens w acc)
                    (hbhp-hasher-sum bits gens w acc)
                    (len gens))
           :use ((:instance hbhp-cwin-point-correct
                            (bits (take (* 3 w) bits)) (g (car gens)))
                 (:instance hbhp-nadd-correct
                            (p1 acc)
                            (p2 (hbhp-gp (hbhp-window-scalar (take (* 3 w) bits) 0)
                                         (car gens))))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar (hbhp-window-scalar (take (* 3 w) bits) 0))
                            (point (car gens)))
                 (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                            (ecurve::x (car gens)))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                            (ecurve::point1 acc)
                            (ecurve::point2
                             (hbhp-gp (hbhp-window-scalar (take (* 3 w) bits) 0)
                                      (car gens))))
                 (:instance hbhp-i-bit-listp-take-nthcdr (x bits) (n (* 3 w)))
                 (:instance hbhp-i-len-of-nthcdr (x bits) (n (* 3 w)))
                 (:instance hbhp-ph-len-of-take (x bits) (n (* 3 w)))
                 (:instance hbhp-i-arith (la (len bits)))))
          ("Subgoal *1/1"
           :expand ((hbhp-cfold bits gens w acc)
                    (hbhp-hasher-sum bits gens w acc)
                    (hbhp-cfold bits nil w acc)
                    (hbhp-hasher-sum bits nil w acc))))
  :prep-lemmas
  ((defruled hbhp-i-arith
     (implies (and (posp w) (natp q) (equal la (* 3 w q)) (< 0 la))
              (and (posp q)
                   (<= (* 3 w) la)
                   (equal (min (* 3 w) la) (* 3 w))
                   (equal (nfix (- la (* 3 w))) (* 3 w (- q 1)))
                   (natp (- q 1))))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The specification side of the first iteration: c0 are the constant
;; windows, cm the constant chunks of the straddling window, v the variable
;; bits.  The first 3(w-c) bits of v complete the straddling window.

(defruledl hbhp-i-nthcdr-too-far
  (implies (and (true-listp x) (<= (len x) (nfix n)))
           (equal (nthcdr n x) nil))
  :induct (nthcdr n x)
  :enable nthcdr)

(defruledl hbhp-i-take-len
  (implies (true-listp x) (equal (take (len x) x) x))
  :induct (len x)
  :enable take)

(defruledl hbhp-i-nthcdr-nthcdr
  (implies (natp m)
           (equal (nthcdr 1 (nthcdr m x)) (nthcdr (+ 1 m) x)))
  :induct (nthcdr m x)
  :enable nthcdr)

(defruledl hbhp-i-sum-nil
  (equal (hbhp-hasher-sum nil gs w acc) acc)
  :expand (hbhp-hasher-sum nil gs w acc))

(defruledl hbhp-i-pad-nil
  (equal (hbhp-pad nil) nil)
  :enable hbhp-pad)

(defruledl hbhp-i-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defruledl hbhp-i-true-listp-append
  (implies (true-listp b) (true-listp (append a b))))

(defruledl hbhp-i-true-listp-pad
  (true-listp (hbhp-pad x))
  :enable hbhp-pad)

(defruledl hbhp-i-ceil3
  (implies (and (natp n) (natp k) (<= n (* 3 k)))
           (<= (+ n (mod (- n) 3)) (* 3 k)))
  :cases ((equal (mod n 3) 0))
  :hints (("Subgoal 2"
           :use ((:instance hbhp-i-floor-lt (n n) (k k))
                 (:instance hbhp-i-floor-elim-3 (n n))
                 (:instance hbhp-i-neg-mod-3 (n n))))
          ("Subgoal 1" :use ((:instance hbhp-i-neg-mod0 (n n)))))
  :prep-lemmas
  ((defruled hbhp-i-neg-mod0
     (implies (and (integerp n) (equal (mod n 3) 0)) (equal (mod (- n) 3) 0))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defruled hbhp-i-floor-elim-3
     (implies (natp n) (equal (+ (* 3 (floor n 3)) (mod n 3)) n))
     :enable mod)
   (defruled hbhp-i-neg-mod-3
     (implies (and (natp n) (not (equal (mod n 3) 0)))
              (equal (mod (- n) 3) (- 3 (mod n 3))))
     :cases ((equal (mod n 3) 1) (equal (mod n 3) 2))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defruled hbhp-i-floor-lt
     (implies (and (natp n) (natp k) (<= n (* 3 k)) (not (equal (mod n 3) 0)))
              (<= (+ 1 (floor n 3)) k))
     :hints (("Goal" :nonlinearp t))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

(defruledl hbhp-i-len-pad-bound
  (implies (and (natp k) (<= (len x) (* 3 k)))
           (<= (len (hbhp-pad x)) (* 3 k)))
  :use ((:instance hbhp-i-ceil3 (n (len x))))
  :enable hbhp-pad
  :disable mod)

(defruledl hbhp-i-spec-arith
  (implies (and (posp w) (natp c) (< c w))
           (and (natp (- w c))
                (equal (+ (* 3 c) (* 3 (- w c))) (* 3 w))
                (equal (mod (* 3 (- w c)) 3) 0)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-i-spec-front
  (implies (and (posp w) (natp m) (natp c)
                (equal (len c0) (* 3 w m)) (equal (len cm) (* 3 c))
                (< m (len gens)))
           (equal (hbhp-hasher-sum (hbhp-pad (append c0 cm v)) gens w acc)
                  (hbhp-hasher-sum (append cm (hbhp-pad v)) (nthcdr m gens) w
                                   (hbhp-hasher-sum c0 gens w acc))))
  :use ((:instance hbhp-window-scalar-of-append-3k (a cm) (b v) (k c))
        (:instance hbhp-pad-of-append (a c0) (b (append cm v)))
        (:instance hbhp-hasher-sum-of-append
                   (a c0) (b (append cm (hbhp-pad v))) (q m))
        hbhp-i-mod-3wm)
  :in-theory '(natp posp)
  :prep-lemmas
  ((defruled hbhp-i-mod-3wm
     (implies (and (posp w) (natp m)) (equal (mod (* 3 w m) 3) 0))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

(defruledl hbhp-i-consp-nthcdr
  (implies (< (nfix m) (len x)) (consp (nthcdr m x)))
  :induct (nthcdr m x)
  :enable nthcdr)

(defruledl hbhp-i-consp-when-len
  (implies (< 0 (len x)) (consp x)))

(defmacro hbhp-i-spec-hyps ()
  '(and (posp w) (natp m) (natp c) (<= 1 c) (< c w)
        (equal (len c0) (* 3 w m)) (equal (len cm) (* 3 c))
        (true-listp cm) (true-listp v) (consp v)
        (< m (len gens))))

(defmacro hbhp-i-spec-rhs ()
  '(hbhp-hasher-sum
    (hbhp-pad (nthcdr (* 3 (- w c)) v)) (nthcdr (+ 1 m) gens) w
    (ecurve::edwards-bls12-add
     (hbhp-hasher-sum c0 gens w acc)
     (ecurve::edwards-bls12-mul
      (+ (hbhp-window-scalar cm 0)
         (hbhp-window-scalar (hbhp-pad (take (min (* 3 (- w c)) (len v)) v)) c))
      (nth m gens)))))

(defruledl hbhp-i-spec-short
  (implies (and (hbhp-i-spec-hyps) (<= (len v) (* 3 (- w c))))
           (equal (hbhp-hasher-sum (hbhp-pad (append c0 cm v)) gens w acc)
                  (hbhp-i-spec-rhs)))
  :use (hbhp-i-spec-front hbhp-i-spec-arith
        (:instance hbhp-hasher-sum-last
                   (b (append cm (hbhp-pad v))) (gs (nthcdr m gens))
                   (acc (hbhp-hasher-sum c0 gens w acc)))
        (:instance hbhp-window-scalar-of-append-3k (a cm) (b (hbhp-pad v)) (k c))
        (:instance hbhp-i-len-pad-bound (x v) (k (- w c)))
        (:instance hbhp-i-nthcdr-too-far (x v) (n (* 3 (- w c))))
        (:instance hbhp-i-take-len (x v))
        (:instance hbhp-car-of-nthcdr (q m) (x gens))
        (:instance hbhp-i-len-append (a cm) (b (hbhp-pad v)))
        (:instance hbhp-i-true-listp-append (a cm) (b (hbhp-pad v)))
        (:instance hbhp-i-true-listp-pad (x v))
        (:instance hbhp-i-consp-nthcdr (x gens))
        (:instance hbhp-i-consp-when-len (x (append cm (hbhp-pad v)))))
  :in-theory '(natp posp nfix min hbhp-i-pad-nil hbhp-i-sum-nil (:e len) (:t len)))

(defruledl hbhp-i-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defruledl hbhp-i-true-listp-take
  (true-listp (take n x)))

(defruledl hbhp-i-spec-long
  (implies (and (hbhp-i-spec-hyps) (< (* 3 (- w c)) (len v)))
           (equal (hbhp-hasher-sum (hbhp-pad (append c0 cm v)) gens w acc)
                  (hbhp-i-spec-rhs)))
  :use (hbhp-i-spec-front hbhp-i-spec-arith
        (:instance hbhp-append-take-nthcdr (n (* 3 (- w c))) (x v))
        (:instance hbhp-pad-of-append
                   (a (take (* 3 (- w c)) v)) (b (nthcdr (* 3 (- w c)) v)))
        (:instance hbhp-hasher-sum-of-append
                   (a (append cm (take (* 3 (- w c)) v)))
                   (b (hbhp-pad (nthcdr (* 3 (- w c)) v)))
                   (gens (nthcdr m gens)) (q 1)
                   (acc (hbhp-hasher-sum c0 gens w acc)))
        (:instance hbhp-hasher-sum-last
                   (b (append cm (take (* 3 (- w c)) v))) (gs (nthcdr m gens))
                   (acc (hbhp-hasher-sum c0 gens w acc)))
        (:instance hbhp-window-scalar-of-append-3k
                   (a cm) (b (take (* 3 (- w c)) v)) (k c))
        (:instance hbhp-pad-when-mod-3 (x (take (* 3 (- w c)) v)))
        (:instance hbhp-ph-len-of-take (n (* 3 (- w c))) (x v))
        (:instance hbhp-i-nthcdr-nthcdr (x gens))
        (:instance hbhp-car-of-nthcdr (q m) (x gens))
        (:instance hbhp-i-len-append (a cm) (b (take (* 3 (- w c)) v)))
        (:instance hbhp-i-len-of-nthcdr (n m) (x gens))
        (:instance hbhp-i-true-listp-append (a cm) (b (take (* 3 (- w c)) v)))
        (:instance hbhp-i-consp-nthcdr (x gens))
        (:instance hbhp-i-consp-when-len (x (append cm (take (* 3 (- w c)) v)))))
  :in-theory '(natp posp nfix min hbhp-i-append-assoc hbhp-i-true-listp-take unicity-of-1 commutativity-of-* fix
               (:e len) (:t len)))

(defruled hbhp-iter0-spec
  (implies (hbhp-i-spec-hyps)
           (equal (hbhp-hasher-sum (hbhp-pad (append c0 cm v)) gens w acc)
                  (hbhp-i-spec-rhs)))
  :use (hbhp-i-spec-short hbhp-i-spec-long)
  :in-theory nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The first iteration.  cbits are the constant bits, 3(wm + c) of them with
;; 1 <= c < w: m constant windows, then c constant chunks of window m.  vb
;; are the variable bit wires.  The constant windows fold natively into A.
;; Group::add(A, W) returns W when A is the constant zero (m = 0);
;; otherwise `that' = A is constant (hbhp-kadd-gadget).  wins holds the
;; wires: (car wins) = (ws ex ey v01 x3 y3) for window m, (cdr wins) for
;; the windows after it.

(defmacro hbhp-i0-a ()
  '(hbhp-cfold (take (* 3 w m) cbits) gens w (ecurve::twisted-edwards-zero)))
(defmacro hbhp-i0-g () '(nth m gens))
(defmacro hbhp-i0-cm () '(nthcdr (* 3 w m) cbits))
(defmacro hbhp-i0-cuv () '(hbhp-cwin-start (hbhp-i0-cm) (hbhp-i0-g)))
(defmacro hbhp-i0-vm () '(take (min (* 3 (- w c)) (len vb)) vb))
(defmacro hbhp-i0-vr () '(nthcdr (* 3 (- w c)) vb))
(defmacro hbhp-i0-r () '(car wins))
(defmacro hbhp-i0-zp () '(equal (hbhp-i0-a) (ecurve::twisted-edwards-zero)))
(defmacro hbhp-i0-xacc ()
  '(if (hbhp-i0-zp) (nth 1 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))))
(defmacro hbhp-i0-yacc ()
  '(if (hbhp-i0-zp) (nth 2 (hbhp-i0-r)) (nth 5 (hbhp-i0-r))))
(defmacro hbhp-i0-x ()
  '(hbhp-gp (+ (hbhp-window-scalar (hbhp-i0-cm) 0)
               (hbhp-window-scalar (hbhp-pad (hbhp-lk-list (hbhp-i0-vm) asg)) c))
            (hbhp-i0-g)))

(define hbhp-iter0-gadget (cbits vb wins gens w m c (p posp))
  :verify-guards nil
  (append (hbhp-mwindow-gadget (hbhp-i0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                               (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                               (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p)
          (if (hbhp-i0-zp)
              nil
            (hbhp-kadd-gadget (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r))
                              (ecurve::point-finite->x (hbhp-i0-a))
                              (ecurve::point-finite->y (hbhp-i0-a))
                              (nth 3 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))
                              (nth 5 (hbhp-i0-r)) p))
          (if (consp (hbhp-i0-vr))
              (hbhp-rest-full-gadget (hbhp-i0-vr) (cdr wins) (nthcdr (+ 1 m) gens)
                                     w (hbhp-i0-xacc) (hbhp-i0-yacc) p)
            nil)))

(define hbhp-iter0-out (cbits vb wins gens w m c)
  :verify-guards nil
  (if (consp (hbhp-i0-vr))
      (hbhp-rest-full-out (hbhp-i0-vr) (cdr wins) (nthcdr (+ 1 m) gens)
                          w (hbhp-i0-xacc) (hbhp-i0-yacc))
    (cons (hbhp-i0-xacc) (hbhp-i0-yacc))))

(define hbhp-iter0-wires-okp (cbits vb wins gens w m c asg)
  :verify-guards nil
  (and (hbhp-mwindow-wires-okp (hbhp-i0-vm) (nth 0 (hbhp-i0-r))
                               (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) asg)
       (or (hbhp-i0-zp)
           (and (hbhp-wire-okp (nth 3 (hbhp-i0-r)))
                (hbhp-wire-okp (nth 4 (hbhp-i0-r)))
                (hbhp-wire-okp (nth 5 (hbhp-i0-r)))))
       (implies (consp (hbhp-i0-vr))
                (hbhp-rest-full-wires-okp (hbhp-i0-vr) (cdr wins)
                                          (nthcdr (+ 1 m) gens) w
                                          (hbhp-i0-xacc) (hbhp-i0-yacc) asg))))

(define hbhp-iter0-canon (cbits vb wins gens w m c asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
       (s (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x))))
    (and (hbhp-mwindow-canon (hbhp-i0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c sc
                             (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) asg)
         (or (hbhp-i0-zp)
             (hbhp-kadd-canon (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r))
                              (ecurve::point-finite->x (hbhp-i0-a))
                              (ecurve::point-finite->y (hbhp-i0-a))
                              (nth 3 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))
                              (nth 5 (hbhp-i0-r)) s))
         (implies (consp (hbhp-i0-vr))
                  (hbhp-rest-full-canon (hbhp-i0-vr) (cdr wins)
                                        (nthcdr (+ 1 m) gens) w
                                        (hbhp-i0-xacc) (hbhp-i0-yacc) s asg)))))

(defmacro hbhp-iter0-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
        (posp w) (<= w 63) (natp m) (natp c) (<= 1 c) (< c w)
        (bit-listp cbits) (equal (len cbits) (+ (* 3 w m) (* 3 c)))
        (consp vb) (< m (len gens))
        (<= (+ (len cbits) (len vb)) (* 3 w (len gens)))
        (hbhp-iter0-wires-okp cbits vb wins gens w m c asg)))

(defruledl hbhp-i0-nums
  (implies (and (posp w) (<= w 63) (natp m) (natp c) (<= 1 c) (< c w)
                (posp n))
           (and (natp (* 3 w m)) (natp (* 3 (- w c)))
                (<= 3 (* 3 (- w c)))
                (posp (min (* 3 (- w c)) n))
                (<= (min (* 3 (- w c)) n) n)
                (< (+ (* 3 c) (min (* 3 (- w c)) n)) 190)
                (<= c 63) (<= 3 (* 3 c))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-i0-consp-take
  (implies (posp k) (consp (take k x)))
  :enable take)

(defruledl hbhp-i0-len-pos
  (implies (consp x) (posp (len x))))

(defruled hbhp-i0-window-sound
  (implies (and (hbhp-iter0-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mwindow-gadget (hbhp-i0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                                      (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                                      (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p)
                 asg p))
           (and (equal (ecurve::point-finite (hbhp-lk (nth 1 (hbhp-i0-r)))
                                             (hbhp-lk (nth 2 (hbhp-i0-r))))
                       (hbhp-i0-x))
                (ecurve::edwards-bls12-pointp (hbhp-i0-x))))
  :use ((:instance hbhp-gen-okp-of-nth (q m))
        (:instance hbhp-cwin-start-correct (bits (hbhp-i0-cm)) (g (hbhp-i0-g)))
        (:instance hbhp-nchunks-of-3k (x (hbhp-i0-cm)) (k c))
        (:instance hbhp-i-len-of-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-i-bit-listp-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-i0-nums (n (len vb)))
        (:instance hbhp-i0-len-pos (x vb))
        (:instance hbhp-i0-consp-take (k (min (* 3 (- w c)) (len vb))) (x vb))
        (:instance hbhp-ph-len-of-take (n (min (* 3 (- w c)) (len vb))) (x vb))
        (:instance hbhp-mwindow-sound
                   (vb (hbhp-i0-vm)) (ws (nth 0 (hbhp-i0-r))) (g (hbhp-i0-g))
                   (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
                   (cu (car (hbhp-i0-cuv))) (cv (cdr (hbhp-i0-cuv)))
                   (ex (nth 1 (hbhp-i0-r))) (ey (nth 2 (hbhp-i0-r))))
        (:instance hbhp-mwindow-scalar-is-spec (vb (hbhp-i0-vm)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar
                    (+ (hbhp-window-scalar (hbhp-i0-cm) 0)
                       (hbhp-window-scalar (hbhp-pad (hbhp-lk-list (hbhp-i0-vm) asg))
                                           c)))
                   (point (hbhp-i0-g)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (hbhp-i0-g))))
  :in-theory '(hbhp-iter0-wires-okp natp posp nfix car-cons cdr-cons (:t len)))

(defruledl hbhp-i0-pointp-zero
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero))
  :use hbhp-pointp-of-zero
  :in-theory '((:e ecurve::twisted-edwards-zero)))

(defruled hbhp-i0-a-is-spec
  (implies (hbhp-iter0-hyps)
           (and (equal (hbhp-i0-a)
                       (hbhp-hasher-sum (take (* 3 w m) cbits) gens w
                                        (ecurve::twisted-edwards-zero)))
                (ecurve::edwards-bls12-pointp (hbhp-i0-a))))
  :use ((:instance hbhp-cfold-correct
                   (bits (take (* 3 w m) cbits)) (q m)
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-i-bit-listp-take (x cbits) (n (* 3 w m)))
        (:instance hbhp-ph-len-of-take (x cbits) (n (* 3 w m)))
        (:instance hbhp-pointp-of-hasher-sum
                   (bits (take (* 3 w m) cbits))
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hbhp-i0-nums (n (len vb)))
        (:instance hbhp-i0-len-pos (x vb))
        hbhp-i0-pointp-zero)
  :in-theory '(natp posp nfix))

(defmacro hbhp-i0-mw-gadget ()
  '(hbhp-mwindow-gadget (hbhp-i0-vm) (nth 0 (hbhp-i0-r)) (hbhp-i0-g) c
                        (car (hbhp-i0-cuv)) (cdr (hbhp-i0-cuv))
                        (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r)) p))

(defmacro hbhp-i0-k-gadget ()
  '(hbhp-kadd-gadget (nth 1 (hbhp-i0-r)) (nth 2 (hbhp-i0-r))
                     (ecurve::point-finite->x (hbhp-i0-a))
                     (ecurve::point-finite->y (hbhp-i0-a))
                     (nth 3 (hbhp-i0-r)) (nth 4 (hbhp-i0-r))
                     (nth 5 (hbhp-i0-r)) p))

(defruled hbhp-i0-acc-point
  (implies (and (hbhp-iter0-hyps)
                (r1cs::r1cs-constraints-holdp (hbhp-i0-mw-gadget) asg p)
                (or (hbhp-i0-zp)
                    (r1cs::r1cs-constraints-holdp (hbhp-i0-k-gadget) asg p)))
           (and (equal (ecurve::point-finite (hbhp-lk (hbhp-i0-xacc))
                                             (hbhp-lk (hbhp-i0-yacc)))
                       (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x)))
                (ecurve::edwards-bls12-pointp
                 (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x)))
                (hbhp-wire-okp (hbhp-i0-xacc)) (hbhp-wire-okp (hbhp-i0-yacc))))
  :use (hbhp-i0-window-sound hbhp-i0-a-is-spec
        (:instance hbhp-add-zero-left (pt (hbhp-i0-x)))
        (:instance hbhp-kadd-sound
                   (acc (hbhp-i0-a)) (pt (hbhp-i0-x))
                   (cx (ecurve::point-finite->x (hbhp-i0-a)))
                   (cy (ecurve::point-finite->y (hbhp-i0-a)))
                   (x1 (nth 1 (hbhp-i0-r))) (y1 (nth 2 (hbhp-i0-r)))
                   (v01 (nth 3 (hbhp-i0-r))) (x3 (nth 4 (hbhp-i0-r)))
                   (y3 (nth 5 (hbhp-i0-r))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (hbhp-i0-a)) (ecurve::point2 (hbhp-i0-x))))
  :in-theory '(hbhp-iter0-wires-okp hbhp-mwindow-wires-okp))

(defruled hbhp-i0-acc-sound
  (implies (and (hbhp-iter0-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-iter0-gadget cbits vb wins gens w m c p) asg p))
           (and (equal (ecurve::point-finite (hbhp-lk (hbhp-i0-xacc))
                                             (hbhp-lk (hbhp-i0-yacc)))
                       (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x)))
                (ecurve::edwards-bls12-pointp
                 (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x)))
                (hbhp-wire-okp (hbhp-i0-xacc)) (hbhp-wire-okp (hbhp-i0-yacc))))
  :use hbhp-i0-acc-point
  :in-theory '(hbhp-iter0-gadget r1cs::r1cs-constraints-holdp-of-append))

(defruledl hbhp-i0-nonzero-listp-of-nthcdr
  (implies (hbhp-nonzero-listp gens)
           (hbhp-nonzero-listp (nthcdr q gens)))
  :enable (nthcdr hbhp-nonzero-listp))

(defruledl hbhp-i0-split-append
  (implies (<= (nfix f) (len x))
           (equal (append x l) (append (take f x) (nthcdr f x) l)))
  :use ((:instance hbhp-append-take-nthcdr (n f)))
  :in-theory '(hbhp-i-append-assoc))

(defruledl hbhp-i0-true-listp-nthcdr
  (implies (true-listp x) (true-listp (nthcdr n x)))
  :enable nthcdr)

(defruledl hbhp-i0-len-arith
  (implies (and (posp w) (natp m) (natp c) (< c w) (natp lg) (natp lv)
                (<= (+ (* 3 w m) (* 3 c) lv) (* 3 w lg))
                (< (* 3 (- w c)) lv))
           (<= (- lv (* 3 (- w c))) (* 3 w (- lg (+ 1 m)))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-i0-lk-list-atom
  (implies (not (consp bs)) (equal (hbhp-lk-list bs asg) nil))
  :enable hbhp-lk-list)

(defruledl hbhp-i0-true-listp-when-bit-listp
  (implies (bit-listp x) (true-listp x))
  :enable bit-listp)

(defruledl hbhp-i0-consp-nthcdr-len
  (implies (and (consp (nthcdr n x)) (natp n)) (< n (len x)))
  :induct (nthcdr n x)
  :enable nthcdr)

(defun hbhp-i0-spec-uses ()
  (declare (xargs :guard t :mode :program))
  '((:instance hbhp-i0-split-append (f (* 3 w m)) (x cbits)
               (l (hbhp-lk-list vb asg)))
    (:instance hbhp-iter0-spec
               (c0 (take (* 3 w m) cbits)) (cm (hbhp-i0-cm))
               (v (hbhp-lk-list vb asg)) (acc (ecurve::twisted-edwards-zero)))
    (:instance hbhp-ph-len-of-take (x cbits) (n (* 3 w m)))
    (:instance hbhp-i-len-of-nthcdr (x cbits) (n (* 3 w m)))
    (:instance hbhp-i0-true-listp-nthcdr (x cbits) (n (* 3 w m)))
    (:instance hbhp-consp-of-lk-list (bs vb))
    (:instance hbhp-true-listp-of-lk-list (bs vb))
    (:instance hbhp-take-of-lk-list (bs vb) (n (min (* 3 (- w c)) (len vb))))
    (:instance hbhp-nthcdr-of-lk-list (bs vb) (n (* 3 (- w c))))
    (:instance hbhp-i0-nums (n (len vb)))
    (:instance hbhp-i0-len-pos (x vb))
    hbhp-i0-a-is-spec hbhp-i0-acc-sound))

(make-event
 `(defruledl hbhp-i0-sound-short
    (implies (and (hbhp-iter0-hyps)
                  (not (consp (hbhp-i0-vr)))
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-iter0-gadget cbits vb wins gens w m c p) asg p))
             (b* ((out (hbhp-iter0-out cbits vb wins gens w m c)))
               (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                      (hbhp-hasher-sum (hbhp-pad (append cbits (hbhp-lk-list vb asg)))
                                       gens w (ecurve::twisted-edwards-zero)))))
    :use (,@(hbhp-i0-spec-uses)
          (:instance hbhp-i0-lk-list-atom (bs (hbhp-i0-vr))))
    :in-theory '(hbhp-iter0-out natp posp nfix car-cons cdr-cons
                 hbhp-len-of-lk-list hbhp-i0-true-listp-when-bit-listp
                 hbhp-i-pad-nil hbhp-i-sum-nil (:t len))))

(make-event
 `(defruledl hbhp-i0-sound-long
    (implies (and (hbhp-iter0-hyps)
                  (consp (hbhp-i0-vr))
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-iter0-gadget cbits vb wins gens w m c p) asg p))
             (b* ((out (hbhp-iter0-out cbits vb wins gens w m c)))
               (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                      (hbhp-hasher-sum (hbhp-pad (append cbits (hbhp-lk-list vb asg)))
                                       gens w (ecurve::twisted-edwards-zero)))))
    :use (,@(hbhp-i0-spec-uses)
          (:instance hbhp-rest-full-sound
                     (bits (hbhp-i0-vr)) (wins (cdr wins))
                     (gens (nthcdr (+ 1 m) gens))
                     (xacc (hbhp-i0-xacc)) (yacc (hbhp-i0-yacc))
                     (acc (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x))))
          (:instance hbhp-r-point-listp-of-nthcdr (q (+ 1 m)))
          (:instance hbhp-i0-nonzero-listp-of-nthcdr (q (+ 1 m)))
          (:instance hbhp-i-len-of-nthcdr (x vb) (n (* 3 (- w c))))
          (:instance hbhp-i-len-of-nthcdr (x gens) (n (+ 1 m)))
          (:instance hbhp-i0-consp-nthcdr-len (x vb) (n (* 3 (- w c))))
          (:instance hbhp-i0-len-arith (lg (len gens)) (lv (len vb))))
    :in-theory '(hbhp-iter0-out hbhp-iter0-wires-okp natp posp nfix
                 car-cons cdr-cons hbhp-iter0-gadget
                 r1cs::r1cs-constraints-holdp-of-append
                 hbhp-len-of-lk-list hbhp-i0-true-listp-when-bit-listp (:t len))))

(defruled hbhp-iter0-sound
  (implies (and (hbhp-iter0-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-iter0-gadget cbits vb wins gens w m c p) asg p))
           (b* ((out (hbhp-iter0-out cbits vb wins gens w m c)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-hasher-sum (hbhp-pad (append cbits (hbhp-lk-list vb asg)))
                                     gens w (ecurve::twisted-edwards-zero)))))
  :use (hbhp-i0-sound-short hbhp-i0-sound-long)
  :in-theory nil)

(defruled hbhp-i0-window-complete
  (implies (and (hbhp-iter0-hyps)
                (hbhp-iter0-canon cbits vb wins gens w m c asg))
           (r1cs::r1cs-constraints-holdp (hbhp-i0-mw-gadget) asg p))
  :use ((:instance hbhp-gen-okp-of-nth (q m))
        (:instance hbhp-cwin-start-correct (bits (hbhp-i0-cm)) (g (hbhp-i0-g)))
        (:instance hbhp-nchunks-of-3k (x (hbhp-i0-cm)) (k c))
        (:instance hbhp-i-len-of-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-i-bit-listp-nthcdr (x cbits) (n (* 3 w m)))
        (:instance hbhp-i0-nums (n (len vb)))
        (:instance hbhp-i0-len-pos (x vb))
        (:instance hbhp-i0-consp-take (k (min (* 3 (- w c)) (len vb))) (x vb))
        (:instance hbhp-ph-len-of-take (n (min (* 3 (- w c)) (len vb))) (x vb))
        (:instance hbhp-mwindow-complete
                   (vb (hbhp-i0-vm)) (ws (nth 0 (hbhp-i0-r))) (g (hbhp-i0-g))
                   (sc (hbhp-window-scalar (hbhp-i0-cm) 0))
                   (cu (car (hbhp-i0-cuv))) (cv (cdr (hbhp-i0-cuv)))
                   (ex (nth 1 (hbhp-i0-r))) (ey (nth 2 (hbhp-i0-r)))))
  :in-theory '(hbhp-iter0-wires-okp hbhp-iter0-canon natp posp nfix
               car-cons cdr-cons (:t len)))

(defruled hbhp-i0-kadd-complete
  (implies (and (hbhp-iter0-hyps)
                (hbhp-iter0-canon cbits vb wins gens w m c asg)
                (not (hbhp-i0-zp)))
           (r1cs::r1cs-constraints-holdp (hbhp-i0-k-gadget) asg p))
  :use (hbhp-i0-window-complete hbhp-i0-window-sound hbhp-i0-a-is-spec
        (:instance hbhp-kadd-complete
                   (acc (hbhp-i0-a)) (pt (hbhp-i0-x))
                   (cx (ecurve::point-finite->x (hbhp-i0-a)))
                   (cy (ecurve::point-finite->y (hbhp-i0-a)))
                   (x1 (nth 1 (hbhp-i0-r))) (y1 (nth 2 (hbhp-i0-r)))
                   (v01 (nth 3 (hbhp-i0-r))) (x3 (nth 4 (hbhp-i0-r)))
                   (y3 (nth 5 (hbhp-i0-r)))))
  :in-theory '(hbhp-iter0-wires-okp hbhp-mwindow-wires-okp hbhp-iter0-canon))

(defruledl hbhp-i0-holdp-nil
  (r1cs::r1cs-constraints-holdp nil asg p)
  :enable r1cs::r1cs-constraints-holdp)

(defruled hbhp-iter0-complete
  (implies (and (hbhp-iter0-hyps)
                (hbhp-iter0-canon cbits vb wins gens w m c asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-iter0-gadget cbits vb wins gens w m c p) asg p))
  :use (hbhp-i0-window-complete hbhp-i0-kadd-complete hbhp-i0-acc-point
        (:instance hbhp-rest-full-complete
                   (bits (hbhp-i0-vr)) (wins (cdr wins))
                   (gens (nthcdr (+ 1 m) gens))
                   (xacc (hbhp-i0-xacc)) (yacc (hbhp-i0-yacc))
                   (acc (ecurve::edwards-bls12-add (hbhp-i0-a) (hbhp-i0-x))))
        (:instance hbhp-r-point-listp-of-nthcdr (q (+ 1 m)))
        (:instance hbhp-i0-nonzero-listp-of-nthcdr (q (+ 1 m)))
        (:instance hbhp-i-len-of-nthcdr (x vb) (n (* 3 (- w c))))
        (:instance hbhp-i-len-of-nthcdr (x gens) (n (+ 1 m)))
        (:instance hbhp-i0-consp-nthcdr-len (x vb) (n (* 3 (- w c))))
        (:instance hbhp-i0-len-arith (lg (len gens)) (lv (len vb)))
        (:instance hbhp-i0-nums (n (len vb)))
        (:instance hbhp-i0-len-pos (x vb)))
  :in-theory '(hbhp-iter0-gadget r1cs::r1cs-constraints-holdp-of-append
               hbhp-iter0-canon hbhp-iter0-wires-okp hbhp-i0-holdp-nil
               natp posp nfix (:t len)))
