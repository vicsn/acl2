; A duplicate-free list of all points of a complete twisted Edwards curve
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; For each abscissa x the curve equation fixes y^2 = (1 - a x^2) / (1 - d x^2),
;; so the points with abscissa x are (x, s) and (x, -s) for the square root s
;; of that value, if any.  The list is never computed; it is used to bound
;; the number of points by 2p.

(include-book "field-lemmas")


(define te-y2 ((x natp) (curve twisted-edwards-curvep))
  :verify-guards nil
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve))
       (xx (mul x x p)))
    (mul (add 1 (neg (mul a xx p) p) p)
         (pfield::inv (add 1 (neg (mul d xx p) p) p) p)
         p)))

(define te-pts-at-x ((x natp) (curve twisted-edwards-curvep))
  :verify-guards nil
  (b* ((p (twisted-edwards-curve->p curve))
       (c (te-y2 x curve)))
    (if (pfield-squarep c p)
        (b* ((s (pfield-square->root c p)))
          (if (equal s 0)
              (list (point-finite x 0))
            (list (point-finite x s) (point-finite x (neg s p)))))
      nil)))

(define te-pts-below ((n natp) (curve twisted-edwards-curvep))
  :verify-guards nil
  (if (zp n)
      nil
    (append (te-pts-at-x (1- n) curve)
            (te-pts-below (1- n) curve))))

(define te-all-pts ((curve twisted-edwards-curvep))
  :verify-guards nil
  (te-pts-below (twisted-edwards-curve->p curve) curve))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl curve-components
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve)))
    (and (dm::primep p)
         (posp p)
         (< 2 p)
         (fep a p)
         (fep d p)))
  :enable (twisted-edwards-curve->p
           twisted-edwards-curve->a
           twisted-edwards-curve->d))

(defruledl member-equal-of-cons-local
  (equal (member-equal a (cons b l))
         (if (equal a b) (cons b l) (member-equal a l))))

(defruledl member-equal-of-nil-local
  (equal (member-equal a nil) nil))

(defruledl fep-bounds-local
  (implies (fep x p)
           (and (natp x) (< x p)))
  :enable fep)

(defruledl neg-bounds-local
  (implies (posp p)
           (and (natp (neg x p)) (< (neg x p) p)))
  :use ((:instance pfield::fep-of-neg (pfield::p p) (pfield::x x))
        (:instance fep-bounds-local (x (neg x p))))
  :in-theory '(posp))

(defruledl fep-when-natp-lt
  (implies (and (natp x) (< x p))
           (fep x p))
  :enable fep)

(defruledl on-curve-iff-y2
  (implies (and (twisted-edwards-curve-completep curve)
                (natp x) (natp y)
                (< x (twisted-edwards-curve->p curve))
                (< y (twisted-edwards-curve->p curve)))
           (equal (point-on-twisted-edwards-p (point-finite x y) curve)
                  (equal (mul y y (twisted-edwards-curve->p curve))
                         (te-y2 x curve))))
  :in-theory '(point-on-twisted-edwards-p te-y2 twisted-edwards-curve-completep
               fep-when-natp-lt (:compound-recognizer acl2::natp-compound-recognizer) point-finite->x-of-point-finite point-finite->y-of-point-finite
               point-kind-of-point-finite nfix pfield::fep-of-mul
               pfield::fep-of-add pfield::fep-of-neg)
  :use (curve-components
        (:instance pfield-curve-equation-rearrange
                   (p (twisted-edwards-curve->p curve))
                   (a (twisted-edwards-curve->a curve))
                   (d (twisted-edwards-curve->d curve))
                   (xx (mul x x (twisted-edwards-curve->p curve)))
                   (yy (mul y y (twisted-edwards-curve->p curve))))
        (:instance pfield-solve-mul
                   (p (twisted-edwards-curve->p curve))
                   (yy (mul y y (twisted-edwards-curve->p curve)))
                   (n (add 1 (neg (mul (twisted-edwards-curve->a curve)
                                       (mul x x (twisted-edwards-curve->p curve))
                                       (twisted-edwards-curve->p curve))
                                  (twisted-edwards-curve->p curve))
                           (twisted-edwards-curve->p curve)))
                   (den (add 1 (neg (mul (twisted-edwards-curve->d curve)
                                         (mul x x (twisted-edwards-curve->p curve))
                                         (twisted-edwards-curve->p curve))
                                    (twisted-edwards-curve->p curve))
                             (twisted-edwards-curve->p curve))))
        (:instance pfield-not-square-one-minus-not-zero
                   (p (twisted-edwards-curve->p curve))
                   (d (twisted-edwards-curve->d curve)))))

(defruledl fep-of-te-y2
  (fep (te-y2 x curve) (twisted-edwards-curve->p curve))
  :enable te-y2
  :use curve-components)

(defruledl x-of-member-te-pts-at-x
  (implies (member-equal pt (te-pts-at-x x curve))
           (equal (point-finite->x pt) (nfix x)))
  :enable te-pts-at-x)

(defruledl on-curve-when-member-te-pts-at-x
  (implies (and (twisted-edwards-curve-completep curve)
                (natp x)
                (< x (twisted-edwards-curve->p curve))
                (member-equal pt (te-pts-at-x x curve)))
           (point-on-twisted-edwards-p pt curve))
  :use (curve-components
        fep-of-te-y2
        (:instance fep-of-pfield-square->root
                   (x (te-y2 x curve))
                   (p (twisted-edwards-curve->p curve)))
        (:instance on-curve-iff-y2
                   (y (pfield-square->root (te-y2 x curve)
                                           (twisted-edwards-curve->p curve))))
        (:instance on-curve-iff-y2
                   (y (neg (pfield-square->root
                            (te-y2 x curve)
                            (twisted-edwards-curve->p curve))
                           (twisted-edwards-curve->p curve))))
        (:instance pfield-squarep
                   (x (te-y2 x curve))
                   (p (twisted-edwards-curve->p curve))))
  :in-theory '(te-pts-at-x member-equal-of-cons-local member-equal-of-nil-local
               fep-bounds-local fep-of-pfield-square->root
               pfield-mul-neg-neg-same pfield::fep-of-neg neg-bounds-local))

(defruledl member-te-pts-at-x-when-on-curve-xy
  (implies (and (twisted-edwards-curve-completep curve)
                (natp x) (natp y)
                (< x (twisted-edwards-curve->p curve))
                (< y (twisted-edwards-curve->p curve))
                (point-on-twisted-edwards-p (point-finite x y) curve))
           (member-equal (point-finite x y) (te-pts-at-x x curve)))
  :use (curve-components
        fep-of-te-y2
        on-curve-iff-y2
        (:instance pfield-squarep-suff
                   (r y)
                   (x (te-y2 x curve))
                   (p (twisted-edwards-curve->p curve)))
        (:instance pfield-squarep
                   (x (te-y2 x curve))
                   (p (twisted-edwards-curve->p curve)))
        (:instance pfield-equal-squares
                   (p (twisted-edwards-curve->p curve))
                   (s (pfield-square->root (te-y2 x curve)
                                           (twisted-edwards-curve->p curve)))))
  :in-theory '(te-pts-at-x member-equal-of-cons-local member-equal-of-nil-local fep pfield::neg-of-0))

(defruled member-te-pts-at-x
  (implies (and (twisted-edwards-curve-completep curve)
                (natp x)
                (< x (twisted-edwards-curve->p curve))
                (pointp pt))
           (iff (member-equal pt (te-pts-at-x x curve))
                (and (point-on-twisted-edwards-p pt curve)
                     (equal (point-finite->x pt) x))))
  :use (on-curve-when-member-te-pts-at-x
        x-of-member-te-pts-at-x
        (:instance member-te-pts-at-x-when-on-curve-xy
                   (y (point-finite->y pt)))
        (:instance point-fix-when-finite (p pt)))
  :enable point-on-twisted-edwards-p
  :disable point-finite-of-point-finite->x/y)

(defrulel natp-of-point-finite->x-local
  (natp (point-finite->x p))
  :rule-classes :type-prescription)

(defruled member-te-pts-below
  (implies (and (twisted-edwards-curve-completep curve)
                (natp n)
                (<= n (twisted-edwards-curve->p curve))
                (pointp pt))
           (iff (member-equal pt (te-pts-below n curve))
                (and (point-on-twisted-edwards-p pt curve)
                     (< (point-finite->x pt) n))))
  :induct (te-pts-below n curve)
  :enable (te-pts-below member-te-pts-at-x)
)

(defrule member-te-all-pts
  (implies (and (twisted-edwards-curve-completep curve)
                (pointp pt))
           (iff (member-equal pt (te-all-pts curve))
                (point-on-twisted-edwards-p pt curve)))
  :enable (te-all-pts member-te-pts-below point-on-twisted-edwards-p))

(defrule pointp-when-member-te-all-pts
  (implies (member-equal pt (te-pts-below n curve))
           (pointp pt))
  :enable (te-pts-below te-pts-at-x))

(defruledl x-of-member-te-pts-below
  (implies (member-equal pt (te-pts-below n curve))
           (< (point-finite->x pt) (nfix n)))
  :enable (te-pts-below x-of-member-te-pts-at-x))

(defruledl no-duplicates-te-pts-at-x
  (implies (twisted-edwards-curve-completep curve)
           (no-duplicatesp-equal (te-pts-at-x x curve)))
  :enable (te-pts-at-x equal-of-point-finite)
  :use (curve-components
        (:instance pfield-neg-equal-self
                   (p (twisted-edwards-curve->p curve))
                   (s (pfield-square->root (te-y2 x curve)
                                           (twisted-edwards-curve->p curve))))
        (:instance fep-of-pfield-square->root
                   (x (te-y2 x curve))
                   (p (twisted-edwards-curve->p curve)))))

(defruledl no-duplicates-of-append
  (implies (and (no-duplicatesp-equal a)
                (no-duplicatesp-equal b)
                (not (intersectp-equal a b)))
           (no-duplicatesp-equal (append a b)))
  :induct (len a)
  :expand ((intersectp-equal a b))
  :prep-books ((include-book "std/lists/top" :dir :system)))

(defruledl not-intersectp-te-pts-sub
  (implies (and (natp n)
                (subsetp-equal a (te-pts-at-x n curve)))
           (not (intersectp-equal a (te-pts-below n curve))))
  :induct (len a)
  :enable (x-of-member-te-pts-at-x x-of-member-te-pts-below)
  :hints (("Subgoal *1/1"
           :use ((:instance x-of-member-te-pts-at-x (pt (car a)) (x n))
                 (:instance x-of-member-te-pts-below (pt (car a))))))
  :prep-books ((include-book "std/lists/top" :dir :system)))

(defruledl not-intersectp-te-pts
  (implies (natp n)
           (not (intersectp-equal (te-pts-at-x n curve)
                                  (te-pts-below n curve))))
  :use (:instance not-intersectp-te-pts-sub (a (te-pts-at-x n curve)))
  :prep-books ((include-book "std/lists/top" :dir :system)))

(defrule no-duplicates-te-all-pts
  (implies (twisted-edwards-curve-completep curve)
           (no-duplicatesp-equal (te-all-pts curve)))
  :enable te-all-pts
  :prep-lemmas
  ((defrule lemma
     (implies (twisted-edwards-curve-completep curve)
              (no-duplicatesp-equal (te-pts-below n curve)))
     :induct (te-pts-below n curve)
     :enable (te-pts-below no-duplicates-te-pts-at-x no-duplicates-of-append)
     :hints (("Subgoal *1/2" :use (:instance not-intersectp-te-pts
                                             (n (1- n))))))))

(defrule len-te-all-pts
  (<= (len (te-all-pts curve))
      (* 2 (twisted-edwards-curve->p curve)))
  :rule-classes :linear
  :enable te-all-pts
  :use (:instance lemma (n (twisted-edwards-curve->p curve)))
  :prep-lemmas
  ((defrule lemma
     (<= (len (te-pts-below n curve)) (* 2 (nfix n)))
     :rule-classes nil
     :induct (te-pts-below n curve)
     :enable (te-pts-below te-pts-at-x))))
