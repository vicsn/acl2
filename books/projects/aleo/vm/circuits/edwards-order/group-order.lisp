; The order of the Edwards-BLS12 group
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; Proof that 4 r Q = 0 for every Edwards-BLS12 point Q, hence 4Q is in the
;; order-r subgroup.
;;
;; 1. exponent.lisp: N Q = 0 for every point Q, where N is the length of a
;;    duplicate-free list of all curve points (translation by Q permutes the
;;    list, so its sum S satisfies S = S + N Q).
;; 2. point-list.lisp: each abscissa carries at most two points, so N <= 2q.
;; 3. bls12-points.lisp: the generator G has r G = 0 and G /= 0, so r | N
;;    (r is prime); T4 = (sqrt(-1), 0) has order 4, so 4 | N.  Since
;;    0 < N <= 2q < 12 r, N is 4r or 8r, so 8 r Q = 0 for every Q.
;; 4. no-order-8.lisp, doubling.lisp: if 8T = 0 then U = 4T has 2U = 0, so U
;;    is (0,1) or (0,-1); U = (0,-1) would make V = 2T a point with 2V =
;;    (0,-1), so V has ordinate 0, but no double has ordinate 0 because
;;    1 + d is not a square.  So 4T = 0, and with T = r Q, 4 r Q = 0.

(include-book "exponent")
(include-book "doubling")
(include-book "no-order-8")

(local (include-book "arithmetic-3/top" :dir :system))

(defruledl curve-p-fact
  (equal (twisted-edwards-curve->p (edwards-bls12-curve))
         (edwards-bls12-q))
  :in-theory '((:e twisted-edwards-curve->p)
               (:e edwards-bls12-curve)
               (:e edwards-bls12-q)))

(defruledl curve-facts
  (and (twisted-edwards-curve-completep (edwards-bls12-curve))
       (dm::primep (edwards-bls12-r))
       (equal (twisted-edwards-curve->p (edwards-bls12-curve))
              (edwards-bls12-q)))
  :in-theory '(edwards-bls12-curve-completep
               primep-of-edwards-bls12-r
               curve-p-fact))

(defruledl twisted-edwards-mul-2
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp pt)
                (point-on-twisted-edwards-p pt curve))
           (equal (twisted-edwards-mul 2 pt curve)
                  (twisted-edwards-add pt pt curve)))
  :use (:instance twisted-edwards-mul-succ (point pt) (n 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl r-divides-count
  (dm::divides (edwards-bls12-r) (te-point-count (edwards-bls12-curve)))
  :use (curve-facts
        (:instance twisted-edwards-zero-when-coprime-multiples-zero
                   (point (bls12-order-g))
                   (curve (edwards-bls12-curve))
                   (r (edwards-bls12-r))
                   (k (te-point-count (edwards-bls12-curve))))
        (:instance twisted-edwards-mul-of-te-point-count
                   (q (bls12-order-g))
                   (curve (edwards-bls12-curve))))
  :enable te-point-count)

(defruledl t4-order-4
  (twisted-edwards-point-orderp (bls12-order-t4) 4 (edwards-bls12-curve))
  :enable (twisted-edwards-point-orderp twisted-edwards-point-order-leastp)
  :use (bls12-order-t4-multiples
        (:instance lemma
                   (w (twisted-edwards-point-order-leastp-witness
                       (bls12-order-t4) 4 (edwards-bls12-curve)))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (natp w) (< 0 w) (< w 4))
              (or (equal w 1) (equal w 2) (equal w 3)))
     :rule-classes nil)))

(defruledl count-mod-4
  (equal (mod (te-point-count (edwards-bls12-curve)) 4) 0)
  :use (curve-facts
        t4-order-4
        bls12-order-t4-multiples
        (:instance twisted-edwards-mul-of-te-point-count
                   (q (bls12-order-t4))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mod-order
                   (point (bls12-order-t4))
                   (curve (edwards-bls12-curve))
                   (order 4)
                   (scalar (te-point-count (edwards-bls12-curve))))
        (:instance lemma (n (te-point-count (edwards-bls12-curve)))))
  :enable te-point-count
  :disable twisted-edwards-mul-of-mod-order
  :prep-lemmas
  ((defrule lemma
     (implies (natp n)
              (or (equal (mod n 4) 0) (equal (mod n 4) 1)
                  (equal (mod n 4) 2) (equal (mod n 4) 3)))
     :rule-classes nil)))

(defruledl len-positive-when-member
  (implies (member-equal a l)
           (< 0 (len l))))

(defruledl count-positive
  (< 0 (te-point-count (edwards-bls12-curve)))
  :use (curve-facts
        (:instance member-te-all-pts
                   (pt (twisted-edwards-zero))
                   (curve (edwards-bls12-curve)))
        (:instance len-positive-when-member
                   (a (twisted-edwards-zero))
                   (l (te-all-pts (edwards-bls12-curve)))))
  :enable te-point-count)

(defruledl count-arith
  (implies (and (integerp j)
                (< 0 (* (edwards-bls12-r) j))
                (<= (* (edwards-bls12-r) j) (* 2 (edwards-bls12-q)))
                (equal (mod (* (edwards-bls12-r) j) 4) 0))
           (or (equal j 4) (equal j 8)))
  :cases ((equal j 1) (equal j 2) (equal j 3) (equal j 4)
          (equal j 5) (equal j 6) (equal j 7) (equal j 8))
  :in-theory (enable (:e edwards-bls12-r) (:e edwards-bls12-q)))

(defruledl count-arith2
  (implies (and (natp n)
                (dm::divides (edwards-bls12-r) n)
                (< 0 n)
                (<= n (* 2 (edwards-bls12-q)))
                (equal (mod n 4) 0))
           (or (equal n (* 4 (edwards-bls12-r)))
               (equal n (* 8 (edwards-bls12-r)))))
  :use (:instance count-arith (j (/ n (edwards-bls12-r))))
  :in-theory (enable dm::divides (:e edwards-bls12-r) (:e edwards-bls12-q)))

(defruledl natp-of-te-point-count
  (natp (te-point-count curve))
  :enable te-point-count)

(defruled te-point-count-of-edwards-bls12
  (or (equal (te-point-count (edwards-bls12-curve)) (* 4 (edwards-bls12-r)))
      (equal (te-point-count (edwards-bls12-curve)) (* 8 (edwards-bls12-r))))
  :use (r-divides-count
        count-mod-4
        count-positive
        curve-facts
        (:instance te-point-count-upper-bound (curve (edwards-bls12-curve)))
        (:instance count-arith2
                   (n (te-point-count (edwards-bls12-curve)))))
  :in-theory '(curve-p-fact natp-of-te-point-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl mul-8r-zero
  (implies (and (pointp q)
                (point-on-twisted-edwards-p q (edwards-bls12-curve)))
           (equal (twisted-edwards-mul (* 8 (edwards-bls12-r)) q
                                       (edwards-bls12-curve))
                  (twisted-edwards-zero)))
  :use (curve-facts
        te-point-count-of-edwards-bls12
        (:instance twisted-edwards-mul-of-te-point-count
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 2)
                   (scalar1 (te-point-count (edwards-bls12-curve)))
                   (point q)
                   (curve (edwards-bls12-curve))))
  :disable (twisted-edwards-mul-of-mul twisted-edwards-mul-of-te-point-count))

(defruledl zero-or-minus-one-when-double-zero
  (implies (and (pointp u)
                (point-on-twisted-edwards-p u (edwards-bls12-curve))
                (equal (twisted-edwards-add u u (edwards-bls12-curve))
                       (twisted-edwards-zero)))
           (or (equal u (twisted-edwards-zero))
               (equal u (point-finite 0 (neg 1 (edwards-bls12-q))))))
  :use (curve-facts
        (:instance twisted-edwards-double-x-zero
                   (pt u) (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-double-when-y-zero
                   (pt u) (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-only-points-with-x-0-or-y-1
                   (point u) (curve (edwards-bls12-curve))))
  :in-theory '(twisted-edwards-zero
               point-finite->x-of-point-finite
               (:e point-finite) (:e nfix) (:e neg) (:e edwards-bls12-q)
               (:e point-finite->x) (:e point-finite->y) curve-p-fact
               (:e equal)))

(defruledl y-zero-when-double-minus-one
  (implies (and (pointp v)
                (point-on-twisted-edwards-p v (edwards-bls12-curve))
                (equal (twisted-edwards-add v v (edwards-bls12-curve))
                       (point-finite 0 (neg 1 (edwards-bls12-q)))))
           (equal (point-finite->y v) 0))
  :use (curve-facts
        bls12-double-of-minus-one
        (:instance twisted-edwards-double-x-zero
                   (pt v) (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-only-points-with-x-0-or-y-1
                   (point v) (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-add-of-twisted-edwards-zero-left
                   (point (twisted-edwards-zero))
                   (curve (edwards-bls12-curve))))
  :in-theory '(point-finite->x-of-point-finite
               (:e twisted-edwards-zero)
               (:e point-finite) (:e nfix) (:e neg) (:e edwards-bls12-q)
               (:e point-finite->x) (:e point-finite->y) curve-p-fact
               (:e point-fix)
               (:e point-on-twisted-edwards-p)
               (:e equal)))

(defruledl mul-4-zero-when-mul-8-zero
  (implies (and (pointp tt)
                (point-on-twisted-edwards-p tt (edwards-bls12-curve))
                (equal (twisted-edwards-mul 8 tt (edwards-bls12-curve))
                       (twisted-edwards-zero)))
           (equal (twisted-edwards-mul 4 tt (edwards-bls12-curve))
                  (twisted-edwards-zero)))
  :use (curve-facts
        (:instance zero-or-minus-one-when-double-zero
                   (u (twisted-edwards-mul 4 tt (edwards-bls12-curve))))
        (:instance twisted-edwards-mul-2
                   (pt (twisted-edwards-mul 4 tt (edwards-bls12-curve)))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 2) (scalar1 4) (point tt)
                   (curve (edwards-bls12-curve)))
        (:instance y-zero-when-double-minus-one
                   (v (twisted-edwards-mul 2 tt (edwards-bls12-curve))))
        (:instance twisted-edwards-mul-2
                   (pt (twisted-edwards-mul 2 tt (edwards-bls12-curve)))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 2) (scalar1 2) (point tt)
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-2
                   (pt tt)
                   (curve (edwards-bls12-curve)))
        (:instance edwards-bls12-double-y-not-zero (pt tt)))
  :in-theory '(point-on-twisted-edwards-p-of-twisted-edwards-mul
               pointp-of-twisted-edwards-mul
               twisted-edwards-add-associativity-holds
               (:e acl2::binary-*) (:e integerp)))

(defruled edwards-bls12-mul-4r-zero
  (implies (and (pointp q)
                (point-on-twisted-edwards-p q (edwards-bls12-curve)))
           (equal (twisted-edwards-mul (* 4 (edwards-bls12-r)) q
                                       (edwards-bls12-curve))
                  (twisted-edwards-zero)))
  :use (curve-facts
        mul-8r-zero
        (:instance mul-4-zero-when-mul-8-zero
                   (tt (twisted-edwards-mul (edwards-bls12-r) q
                                            (edwards-bls12-curve))))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 8) (scalar1 (edwards-bls12-r)) (point q)
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 4) (scalar1 (edwards-bls12-r)) (point q)
                   (curve (edwards-bls12-curve))))
  :disable twisted-edwards-mul-of-mul)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule edwards-bls12-r-pointp-of-4q
  (implies (edwards-bls12-pointp q)
           (b* ((q2 (edwards-bls12-add q q)))
             (edwards-bls12-r-pointp (edwards-bls12-add q2 q2))))
  :use (curve-facts
        edwards-bls12-mul-4r-zero
        (:instance twisted-edwards-mul-2 (pt q) (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-2
                   (pt (twisted-edwards-mul 2 q (edwards-bls12-curve)))
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar 2) (scalar1 2) (point q)
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-mul-of-mul
                   (scalar (edwards-bls12-r)) (scalar1 4) (point q)
                   (curve (edwards-bls12-curve)))
        (:instance twisted-edwards-point-orderp-when-prime-kills
                   (point (twisted-edwards-mul 4 q (edwards-bls12-curve)))
                   (curve (edwards-bls12-curve))
                   (r (edwards-bls12-r))))
  :enable (edwards-bls12-r-pointp edwards-bls12-pointp edwards-bls12-add)
  :disable twisted-edwards-mul-of-mul)
