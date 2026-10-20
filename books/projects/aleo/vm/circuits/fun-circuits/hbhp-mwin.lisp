; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Gadgets of the window that straddles the boundary between the constant
; prefix (domain || length) and the variable bits of the first iteration of
; BHP::hash_uncompressed: its variable chunks start from a constant
; Montgomery accumulator, and its Edwards point is added to the constant
; sum of the earlier windows with Group::add on a constant `that'.

(in-package "ALEOVM")

(include-book "hbhp-wrap")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group::add with `this' = (x1, y1) variable and `that' = (cx, cy) constant.
;; u = u1 * (cx + cy), v0 = cy x1 and v1 = cx y1 are scalings of wires
;; (linear combinations); v0 * v1 is the only product of two variables.

(define hbhp-kadd-gadget ((x1 symbolp) (y1 symbolp) cx cy
                          (v01 symbolp) (x3 symbolp) (y3 symbolp) (p posp))
  :verify-guards nil
  (b* ((a (ecurve::edwards-bls12-a))
       (d (ecurve::edwards-bls12-d))
       (s (pfield::add cx cy p))
       (u (list (list (pfield::mul (pfield::neg a p) s p) x1) (list s y1)))
       (v0 (list (list cy x1)))
       (v1 (list (list cx y1))))
    (list (r1cs::make-r1cs-constraint
           :a v0 :b v1 :c (list (list 1 v01)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 x3))
           :b (list (list 1 1) (list d v01))
           :c (append v0 v1))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 y3))
           :b (list (list 1 1) (list (pfield::neg d p) v01))
           :c (append u (list (list (pfield::mul cy a p) x1))
                      (list (list (pfield::neg cx p) y1)))))))

(defruled hbhp-kadd-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (pfield::fep cx p) (pfield::fep cy p)
                (hbhp-wire-okp x1) (hbhp-wire-okp y1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3))
           (b* ((x1$ (hbhp-lk x1)) (y1$ (hbhp-lk y1))
                (v01$ (hbhp-lk v01)) (x3$ (hbhp-lk x3)) (y3$ (hbhp-lk y3))
                (d (ecurve::edwards-bls12-d))
                (u (pfield::mul (pfield::add x1$ y1$ p) (pfield::add cx cy p) p))
                (v0 (pfield::mul x1$ cy p))
                (v1 (pfield::mul cx y1$ p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (hbhp-kadd-gadget x1 y1 cx cy v01 x3 y3 p) asg p)
                    (and (equal v01$ (pfield::mul v0 v1 p))
                         (equal (pfield::mul x3$
                                             (pfield::add 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::add v0 v1 p))
                         (equal (pfield::mul y3$
                                             (pfield::sub 1 (pfield::mul d v01$ p) p)
                                             p)
                                (pfield::sub (pfield::sub u v0 p) v1 p))))))
  :use (hbhp-base-prime-facts curve-fep-of-edwards-bls12-d
        curve-fep-of-edwards-bls12-a)
  :enable (hbhp-kadd-gadget r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           hbhp-dot-cons hbhp-dot-nil r1cs::dot-product-of-append
           pfield::sub crv-edwards-a-is-neg-one)
  :disable (r1cs::dot-product))

(defruled hbhp-kadd-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp acc)
                (equal cx (ecurve::point-finite->x acc))
                (equal cy (ecurve::point-finite->y acc))
                (ecurve::edwards-bls12-pointp pt)
                (hbhp-wire-okp x1) (hbhp-wire-okp y1)
                (equal (ecurve::point-finite (hbhp-lk x1) (hbhp-lk y1)) pt)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-kadd-gadget x1 y1 cx cy v01 x3 y3 p) asg p))
           (equal (ecurve::point-finite (hbhp-lk x3) (hbhp-lk y3))
                  (ecurve::edwards-bls12-add acc pt)))
  :use ((:instance crv-fep-of-edwards-bls12-coords (pt acc))
        hbhp-kadd-gadget-to-eqns
        (:instance crv-group-add-from-equations
                   (p1 pt) (p2 acc)
                   (x1 (hbhp-lk x1)) (y1 (hbhp-lk y1)) (x2 cx) (y2 cy)
                   (u (pfield::mul (pfield::add (hbhp-lk x1) (hbhp-lk y1) p)
                                   (pfield::add cx cy p) p))
                   (v0 (pfield::mul (hbhp-lk x1) cy p))
                   (v1 (pfield::mul cx (hbhp-lk y1) p))
                   (v01 (hbhp-lk v01))
                   (x3 (hbhp-lk x3)) (y3 (hbhp-lk y3)))
        (:instance hbhp-add-comm (a acc) (b pt))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x1)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y1)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x3)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y3)
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(hbhp-base-prime-facts ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite pfield::mul-commutative
               pfield::fep nfix natp))

(defmacro hbhp-kadd-canon (x1 y1 cx cy v01 x3 y3 sum)
  `(and (equal (hbhp-lk ,v01)
               (pfield::mul (pfield::mul (hbhp-lk ,x1) ,cy p)
                            (pfield::mul ,cx (hbhp-lk ,y1) p) p))
        (equal (hbhp-lk ,x3) (ecurve::point-finite->x ,sum))
        (equal (hbhp-lk ,y3) (ecurve::point-finite->y ,sum))))

(defruled hbhp-kadd-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (ecurve::edwards-bls12-pointp acc)
                (equal cx (ecurve::point-finite->x acc))
                (equal cy (ecurve::point-finite->y acc))
                (ecurve::edwards-bls12-pointp pt)
                (hbhp-wire-okp x1) (hbhp-wire-okp y1)
                (equal (ecurve::point-finite (hbhp-lk x1) (hbhp-lk y1)) pt)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (hbhp-kadd-canon x1 y1 cx cy v01 x3 y3
                                 (ecurve::edwards-bls12-add acc pt)))
           (r1cs::r1cs-constraints-holdp
            (hbhp-kadd-gadget x1 y1 cx cy v01 x3 y3 p) asg p))
  :use ((:instance crv-fep-of-edwards-bls12-coords (pt acc))
        hbhp-kadd-gadget-to-eqns
        (:instance crv-group-add-equations-complete (p1 pt) (p2 acc))
        (:instance hbhp-add-comm (a acc) (b pt))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var x1)
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var y1)
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(hbhp-base-prime-facts ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite pfield::mul-commutative
               pfield::fep nfix natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The variable chunks of the window that straddles the boundary.  The
;; accumulator entering the first variable chunk (chunk position c >= 1)
;; is the constant (cu, cv), i.e. the linear combinations cu * 1 and cv * 1.
;; A tail of 1 or 2 bits is padded with constant false bits.

(define hbhp-mwindow-gadget (vb ws g (c natp) cu cv (ex symbolp) (ey symbolp)
                                (p posp))
  :verify-guards nil
  (b* ((k (hbhp-pwindow-k vb))
       (full (take (* 3 k) vb))
       (tl (nthcdr (* 3 k) vb))
       (u0 (list (list cu 1)))
       (v0 (list (list cv 1)))
       (out (hbhp-window-steps-out full ws u0 v0))
       (r (nth k ws))
       (j (+ (lnfix c) k)))
    (if (consp tl)
        (append (hbhp-window-steps full ws g c u0 v0 p)
                (hbhp-pchunk-gadget tl (nth 0 r) (nth 1 r) (hbhp-tab-y g j) p)
                (hbhp-mont-add-gadget (car out) (cdr out)
                                      (hbhp-plc tl (nth 0 r) (hbhp-tab-x g j) p)
                                      (list (list 1 (nth 1 r)))
                                      (nth 2 r) (nth 3 r) (nth 4 r) p)
                (hbhp-to-edwards-gadget (list (list 1 (nth 3 r)))
                                        (list (list 1 (nth 4 r)))
                                        ex ey p))
      (append (hbhp-window-steps full ws g c u0 v0 p)
              (hbhp-to-edwards-gadget (car out) (cdr out) ex ey p)))))

(define hbhp-mwindow-wires-okp (vb ws ex ey asg)
  :verify-guards nil
  (b* ((k (hbhp-pwindow-k vb))
       (full (take (* 3 k) vb))
       (tl (nthcdr (* 3 k) vb))
       (r (nth k ws)))
    (and (hbhp-steps-wires-okp full ws asg)
         (implies (consp tl)
                  (and (hbhp-ptl-okp tl (nth 0 r) asg)
                       (hbhp-wire-okp (nth 1 r)) (hbhp-wire-okp (nth 2 r))
                       (hbhp-wire-okp (nth 3 r)) (hbhp-wire-okp (nth 4 r))))
         (hbhp-wire-okp ex) (hbhp-wire-okp ey))))

(define hbhp-mwindow-scalar (vb (c natp) asg)
  :verify-guards nil
  (b* ((k (hbhp-pwindow-k vb))
       (full (take (* 3 k) vb))
       (tl (nthcdr (* 3 k) vb)))
    (+ (hbhp-steps-scalar full c asg)
       (if (consp tl) (* (hbhp-pc tl) (expt 16 (+ (lnfix c) k))) 0))))

(defruled hbhp-dot-const
  (implies (and (equal p (base-prime)) (pfield::fep x p))
           (equal (r1cs::dot-product (list (list x 1)) asg p) x))
  :use hbhp-base-prime-facts
  :in-theory '(hbhp-dot-cons hbhp-dot-nil pfield::mul-of-1-arg2
               pfield::add-of-0-arg2 pfield::fep pfield::mod-when-fep
               (:e equal) natp acl2::mod-when-<)
  :enable (pfield::fep))

(defruled hbhp-m-k-facts
  (implies (and (natp c) (< (+ (* 3 c) (len vb)) 190))
           (b* ((k (hbhp-pwindow-k vb)))
             (and (natp k)
                  (<= (* 3 k) (len vb))
                  (equal (len (take (* 3 k) vb)) (* 3 k))
                  (implies (consp (nthcdr (* 3 k) vb))
                           (and (<= (+ c k) 62)
                                (< (len (nthcdr (* 3 k) vb)) 3)))
                  (<= (+ c k) 63))))
  :enable (hbhp-pwindow-k hbhp-m-len-of-nthcdr)
  :prep-lemmas
  ((defruled hbhp-m-len-of-nthcdr
     (implies (natp n)
              (equal (len (nthcdr n x)) (nfix (- (len x) n))))
     :induct (nthcdr n x)
     :enable nthcdr)
   (defruled hbhp-m-consp-len
     (equal (consp x) (< 0 (len x)))))
  :hints (("Goal" :in-theory (enable hbhp-m-consp-len)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defmacro hbhp-mwindow-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (hbhp-gen-okp g)
        (natp c) (<= 1 c)
        (hbhp-acc-okp sc c)
        (equal cu (hbhp-mu (hbhp-gp sc g)))
        (equal cv (hbhp-mv (hbhp-gp sc g)))
        (consp vb)
        (< (+ (* 3 c) (len vb)) 190)
        (hbhp-mwindow-wires-okp vb ws ex ey asg)))

(defruledl hbhp-m-fep-mu-mv
  (and (pfield::fep (hbhp-mu pt) (base-prime))
       (pfield::fep (hbhp-mv pt) (base-prime)))
  :use hbhp-base-prime-facts
  :in-theory '(hbhp-mu hbhp-mv pfield::fep-of-div))

(defmacro hbhp-m-k () '(hbhp-pwindow-k vb))
(defmacro hbhp-m-full () '(take (* 3 (hbhp-pwindow-k vb)) vb))
(defmacro hbhp-m-tl () '(nthcdr (* 3 (hbhp-pwindow-k vb)) vb))
(defmacro hbhp-m-r () '(nth (hbhp-pwindow-k vb) ws))
(defmacro hbhp-m-out ()
  '(hbhp-window-steps-out (hbhp-m-full) ws (list (list cu 1)) (list (list cv 1))))
(defmacro hbhp-m-s1 () '(+ sc (hbhp-steps-scalar (hbhp-m-full) c asg)))

(defruled hbhp-m-steps
  (implies (and (hbhp-mwindow-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-steps (hbhp-m-full) ws g c
                                    (list (list cu 1)) (list (list cv 1)) p)
                 asg p))
           (and (equal (hbhp-dot (car (hbhp-m-out))) (hbhp-mu (hbhp-gp (hbhp-m-s1) g)))
                (equal (hbhp-dot (cdr (hbhp-m-out))) (hbhp-mv (hbhp-gp (hbhp-m-s1) g)))
                (hbhp-acc-okp (hbhp-m-s1) (+ c (hbhp-m-k)))))
  :use (hbhp-m-k-facts
        (:instance hbhp-m-fep-mu-mv (pt (hbhp-gp sc g)))
        (:instance hbhp-dot-const (x cu))
        (:instance hbhp-dot-const (x cv))
        (:instance hbhp-nchunks-of-3k (x (hbhp-m-full)) (k (hbhp-m-k)))
        (:instance hbhp-window-steps-sound
                   (bs (hbhp-m-full)) (j c) (s sc)
                   (u1 (list (list cu 1))) (v1 (list (list cv 1)))))
  :in-theory '(hbhp-mwindow-wires-okp natp))

(defruled hbhp-m-plus-assoc
  (equal (+ x (+ y z)) (+ (+ x y) z)))

(defruled hbhp-m-plus-0
  (implies (acl2-numberp x) (equal (+ x 0) x)))

(defruled hbhp-m-padded
  (implies (and (hbhp-mwindow-hyps)
                (consp (hbhp-m-tl))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-steps (hbhp-m-full) ws g c
                                    (list (list cu 1)) (list (list cv 1)) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-pchunk-gadget (hbhp-m-tl) (nth 0 (hbhp-m-r)) (nth 1 (hbhp-m-r))
                                     (hbhp-tab-y g (+ c (hbhp-m-k))) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget (car (hbhp-m-out)) (cdr (hbhp-m-out))
                                       (hbhp-plc (hbhp-m-tl) (nth 0 (hbhp-m-r))
                                                 (hbhp-tab-x g (+ c (hbhp-m-k))) p)
                                       (list (list 1 (nth 1 (hbhp-m-r))))
                                       (nth 2 (hbhp-m-r)) (nth 3 (hbhp-m-r))
                                       (nth 4 (hbhp-m-r)) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-to-edwards-gadget (list (list 1 (nth 3 (hbhp-m-r))))
                                         (list (list 1 (nth 4 (hbhp-m-r))))
                                         ex ey p)
                 asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (+ (hbhp-m-s1) (* (hbhp-pc (hbhp-m-tl))
                                             (expt 16 (+ c (hbhp-m-k)))))
                           g)))
  :use (hbhp-m-k-facts hbhp-m-steps
        (:instance hbhp-pstep-sound
                   (tl (hbhp-m-tl)) (j (+ c (hbhp-m-k))) (s (hbhp-m-s1))
                   (u1 (car (hbhp-m-out))) (v1 (cdr (hbhp-m-out)))
                   (b01 (nth 0 (hbhp-m-r))) (my (nth 1 (hbhp-m-r)))
                   (lam (nth 2 (hbhp-m-r))) (u3 (nth 3 (hbhp-m-r)))
                   (v3 (nth 4 (hbhp-m-r))))
        (:instance hbhp-dot-one-wire (w (nth 3 (hbhp-m-r))))
        (:instance hbhp-dot-one-wire (w (nth 4 (hbhp-m-r))))
        (:instance hbhp-edwards-final-sound
                   (s (+ (hbhp-m-s1) (* (hbhp-pc (hbhp-m-tl))
                                        (expt 16 (+ c (hbhp-m-k))))))
                   (j (+ 1 (+ c (hbhp-m-k))))
                   (u (list (list 1 (nth 3 (hbhp-m-r)))))
                   (v (list (list 1 (nth 4 (hbhp-m-r)))))))
  :in-theory '(hbhp-mwindow-wires-okp hbhp-base-prime-facts natp))

(defruled hbhp-m-unpadded
  (implies (and (hbhp-mwindow-hyps)
                (not (consp (hbhp-m-tl)))
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-steps (hbhp-m-full) ws g c
                                    (list (list cu 1)) (list (list cv 1)) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-to-edwards-gadget (car (hbhp-m-out)) (cdr (hbhp-m-out)) ex ey p)
                 asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (hbhp-m-s1) g)))
  :use (hbhp-m-k-facts hbhp-m-steps
        (:instance hbhp-edwards-final-sound
                   (s (hbhp-m-s1)) (j (+ c (hbhp-m-k)))
                   (u (car (hbhp-m-out))) (v (cdr (hbhp-m-out)))))
  :in-theory '(hbhp-mwindow-wires-okp hbhp-base-prime-facts natp))

(defruled hbhp-mwindow-sound
  (implies (and (hbhp-mwindow-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mwindow-gadget vb ws g c cu cv ex ey p) asg p))
           (equal (ecurve::point-finite (hbhp-lk ex) (hbhp-lk ey))
                  (hbhp-gp (+ sc (hbhp-mwindow-scalar vb c asg)) g)))
  :cases ((consp (hbhp-m-tl)))
  :hints (("Subgoal 1"
           :use hbhp-m-padded
           :in-theory '(hbhp-mwindow-gadget hbhp-mwindow-scalar
                        r1cs::r1cs-constraints-holdp-of-append
                        natp lnfix nfix hbhp-m-plus-assoc))
          ("Subgoal 2"
           :use hbhp-m-unpadded
           :in-theory '(hbhp-mwindow-gadget hbhp-mwindow-scalar
                        r1cs::r1cs-constraints-holdp-of-append
                        natp lnfix nfix hbhp-m-plus-0 (:t hbhp-steps-scalar)))))

(define hbhp-mwindow-canon (vb ws g (c natp) sc ex ey asg)
  :verify-guards nil
  (b* ((p (base-prime))
       (k (hbhp-pwindow-k vb))
       (full (take (* 3 k) vb))
       (tl (nthcdr (* 3 k) vb))
       (r (nth k ws))
       (j (+ (lnfix c) k))
       (s1 (+ sc (hbhp-steps-scalar full c asg)))
       (pt (hbhp-gp (+ sc (hbhp-mwindow-scalar vb c asg)) g)))
    (and (hbhp-steps-canon full ws g c sc asg)
         (implies (consp tl)
                  (and (hbhp-pchunk-canon tl (nth 0 r) (nth 1 r) (hbhp-tab-y g j))
                       (hbhp-mont-canon (hbhp-gp s1 g)
                                        (hbhp-gp (* (hbhp-pc tl) (expt 16 j)) g)
                                        (nth 2 r) (nth 3 r) (nth 4 r))))
         (equal (hbhp-lk ex) (hbhp-x pt))
         (equal (hbhp-lk ey) (hbhp-y pt)))))

(defruled hbhp-m-steps-complete
  (implies (and (hbhp-mwindow-hyps)
                (hbhp-steps-canon (hbhp-m-full) ws g c sc asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-window-steps (hbhp-m-full) ws g c
                               (list (list cu 1)) (list (list cv 1)) p)
            asg p))
  :use (hbhp-m-k-facts
        (:instance hbhp-m-fep-mu-mv (pt (hbhp-gp sc g)))
        (:instance hbhp-dot-const (x cu))
        (:instance hbhp-dot-const (x cv))
        (:instance hbhp-nchunks-of-3k (x (hbhp-m-full)) (k (hbhp-m-k)))
        (:instance hbhp-window-steps-complete
                   (bs (hbhp-m-full)) (j c) (s sc)
                   (u1 (list (list cu 1))) (v1 (list (list cv 1)))))
  :in-theory '(hbhp-mwindow-wires-okp natp))

(defruled hbhp-m-padded-complete
  (implies (and (hbhp-mwindow-hyps)
                (consp (hbhp-m-tl))
                (hbhp-mwindow-canon vb ws g c sc ex ey asg))
           (and (r1cs::r1cs-constraints-holdp
                 (hbhp-pchunk-gadget (hbhp-m-tl) (nth 0 (hbhp-m-r)) (nth 1 (hbhp-m-r))
                                     (hbhp-tab-y g (+ c (hbhp-m-k))) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-mont-add-gadget (car (hbhp-m-out)) (cdr (hbhp-m-out))
                                       (hbhp-plc (hbhp-m-tl) (nth 0 (hbhp-m-r))
                                                 (hbhp-tab-x g (+ c (hbhp-m-k))) p)
                                       (list (list 1 (nth 1 (hbhp-m-r))))
                                       (nth 2 (hbhp-m-r)) (nth 3 (hbhp-m-r))
                                       (nth 4 (hbhp-m-r)) p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-to-edwards-gadget (list (list 1 (nth 3 (hbhp-m-r))))
                                         (list (list 1 (nth 4 (hbhp-m-r))))
                                         ex ey p)
                 asg p)))
  :use (hbhp-m-k-facts hbhp-m-steps hbhp-m-steps-complete
        (:instance hbhp-pstep-complete
                   (tl (hbhp-m-tl)) (j (+ c (hbhp-m-k))) (s (hbhp-m-s1))
                   (u1 (car (hbhp-m-out))) (v1 (cdr (hbhp-m-out)))
                   (b01 (nth 0 (hbhp-m-r))) (my (nth 1 (hbhp-m-r)))
                   (lam (nth 2 (hbhp-m-r))) (u3 (nth 3 (hbhp-m-r)))
                   (v3 (nth 4 (hbhp-m-r))))
        (:instance hbhp-pstep-sound
                   (tl (hbhp-m-tl)) (j (+ c (hbhp-m-k))) (s (hbhp-m-s1))
                   (u1 (car (hbhp-m-out))) (v1 (cdr (hbhp-m-out)))
                   (b01 (nth 0 (hbhp-m-r))) (my (nth 1 (hbhp-m-r)))
                   (lam (nth 2 (hbhp-m-r))) (u3 (nth 3 (hbhp-m-r)))
                   (v3 (nth 4 (hbhp-m-r))))
        (:instance hbhp-dot-one-wire (w (nth 3 (hbhp-m-r))))
        (:instance hbhp-dot-one-wire (w (nth 4 (hbhp-m-r))))
        (:instance hbhp-edwards-final-complete
                   (s (+ (hbhp-m-s1) (* (hbhp-pc (hbhp-m-tl))
                                        (expt 16 (+ c (hbhp-m-k))))))
                   (j (+ 1 (+ c (hbhp-m-k))))
                   (u (list (list 1 (nth 3 (hbhp-m-r)))))
                   (v (list (list 1 (nth 4 (hbhp-m-r)))))))
  :in-theory '(hbhp-mwindow-wires-okp hbhp-mwindow-canon hbhp-mwindow-scalar
               hbhp-base-prime-facts natp lnfix nfix hbhp-m-plus-assoc))

(defruled hbhp-m-unpadded-complete
  (implies (and (hbhp-mwindow-hyps)
                (not (consp (hbhp-m-tl)))
                (hbhp-mwindow-canon vb ws g c sc ex ey asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-to-edwards-gadget (car (hbhp-m-out)) (cdr (hbhp-m-out)) ex ey p)
            asg p))
  :use (hbhp-m-k-facts hbhp-m-steps hbhp-m-steps-complete
        (:instance hbhp-edwards-final-complete
                   (s (hbhp-m-s1)) (j (+ c (hbhp-m-k)))
                   (u (car (hbhp-m-out))) (v (cdr (hbhp-m-out)))))
  :in-theory '(hbhp-mwindow-wires-okp hbhp-mwindow-canon hbhp-mwindow-scalar
               hbhp-base-prime-facts natp lnfix nfix hbhp-m-plus-0
               (:t hbhp-steps-scalar)))

(defruled hbhp-mwindow-complete
  (implies (and (hbhp-mwindow-hyps)
                (hbhp-mwindow-canon vb ws g c sc ex ey asg))
           (r1cs::r1cs-constraints-holdp
            (hbhp-mwindow-gadget vb ws g c cu cv ex ey p) asg p))
  :cases ((consp (hbhp-m-tl)))
  :hints (("Subgoal 1"
           :use (hbhp-m-padded-complete hbhp-m-steps-complete
                 (:instance hbhp-mwindow-canon))
           :in-theory '(hbhp-mwindow-gadget r1cs::r1cs-constraints-holdp-of-append
                        natp lnfix nfix))
          ("Subgoal 2"
           :use (hbhp-m-unpadded-complete hbhp-m-steps-complete
                 (:instance hbhp-mwindow-canon))
           :in-theory '(hbhp-mwindow-gadget r1cs::r1cs-constraints-holdp-of-append
                        natp lnfix nfix))))

