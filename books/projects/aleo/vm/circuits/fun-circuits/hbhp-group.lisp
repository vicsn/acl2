; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Multiples of a nonzero point G of the prime-order subgroup r.
;
;   n G = 0          iff  r | n
;   x(n G) = 0       iff  r | n        ((0, -1) has order 2, so it is not in r)
;   y(m G) = y(n G)  =>   r | m - n  or  r | m + n
;
; These discharge the non-exceptional conditions of the Montgomery addition
; (hbhp-mont.lisp) from bounds on the scalars, see hbhp-window-bounds.

(in-package "ALEOVM")

(include-book "hbhp-mont")
(include-book "../fun-specs/hash-bhp")

(local (include-book "../edwards-assoc/edwards-bls12-associativity"))
(local (include-book "../edwards-order/bls12-points"))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve))))

(defmacro hbhp-zero () '(ecurve::twisted-edwards-zero))

(defruledl hbhp-curve-ok
  (and (ecurve::twisted-edwards-curve-completep (ecurve::edwards-bls12-curve))
       (ecurve::twisted-edwards-add-associativity))
  :use (ecurve::edwards-bls12-curve-completep
        ecurve::twisted-edwards-add-associativity-holds))

(defruled hbhp-g-mul-add
  (implies (ecurve::edwards-bls12-pointp g)
           (equal (ecurve::edwards-bls12-add (ecurve::edwards-bls12-mul m g)
                                             (ecurve::edwards-bls12-mul n g))
                  (ecurve::edwards-bls12-mul (+ (ifix m) (ifix n)) g)))
  :use (hbhp-curve-ok
        (:instance ecurve::twisted-edwards-mul-of-scalar-addition-converse
                   (ecurve::scalar1 (ifix m)) (ecurve::scalar2 (ifix n))
                   (ecurve::point g) (ecurve::curve (ecurve::edwards-bls12-curve))))
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-mul
           ecurve::edwards-bls12-pointp)
  :disable (ecurve::twisted-edwards-mul-of-scalar-addition-converse))

(defruled hbhp-g-neg-mul
  (implies (ecurve::edwards-bls12-pointp g)
           (equal (ecurve::edwards-bls12-neg (ecurve::edwards-bls12-mul n g))
                  (ecurve::edwards-bls12-mul (- (ifix n)) g)))
  :use (hbhp-curve-ok
        (:instance ecurve::twisted-edwards-neg-of-mul
                   (ecurve::scalar n) (ecurve::point g)
                   (ecurve::curve (ecurve::edwards-bls12-curve))))
  :enable (ecurve::edwards-bls12-neg ecurve::edwards-bls12-mul
           ecurve::edwards-bls12-pointp))

(defruled hbhp-g-mul-zero-iff
  (implies (and (ecurve::edwards-bls12-r-pointp g)
                (not (equal g (hbhp-zero)))
                (integerp n))
           (equal (equal (ecurve::edwards-bls12-mul n g) (hbhp-zero))
                  (equal (mod n (ecurve::edwards-bls12-r)) 0)))
  :use (hbhp-curve-ok
        (:instance ecurve::twisted-edwards-mul-of-mod-order
                   (ecurve::scalar n) (ecurve::point g)
                   (ecurve::order (ecurve::edwards-bls12-r))
                   (ecurve::curve (ecurve::edwards-bls12-curve)))
        (:instance ecurve::twisted-edwards-point-order-leastp-necc
                   (ecurve::order1 (mod n (ecurve::edwards-bls12-r)))
                   (ecurve::point g)
                   (ecurve::order (ecurve::edwards-bls12-r))
                   (ecurve::curve (ecurve::edwards-bls12-curve))))
  :enable (ecurve::edwards-bls12-mul ecurve::edwards-bls12-r-pointp
           ecurve::edwards-bls12-pointp ecurve::twisted-edwards-point-orderp)
  :disable (ecurve::twisted-edwards-mul-of-mod-order
            ecurve::twisted-edwards-point-order-leastp-necc))

(defruled hbhp-minus-one-point-not-r
  (not (ecurve::edwards-bls12-r-pointp
        (ecurve::point-finite 0 (pfield::neg 1 (base-prime)))))
  :use ((:instance hbhp-g-mul-zero-iff
                   (g (ecurve::point-finite 0 (pfield::neg 1 (base-prime))))
                   (n 2)))
  :in-theory '((:e ecurve::edwards-bls12-r) (:e base-prime) (:e mod) (:e equal)
               (:e ecurve::twisted-edwards-zero) (:e pfield::neg)
               (:e ecurve::point-finite) (:e ecurve::edwards-bls12-mul)
               (:e integerp)))

(defrulel hbhp-sq-one
  (implies (and (primep p) (< 2 p) (pfield::fep y p)
                (equal (pfield::mul y y p) 1))
           (or (equal y 1) (equal y (pfield::neg 1 p))))
  :rule-classes nil
  :use (:instance pfield::equal-of-0-and-mul
                  (pfield::x (pfield::sub y 1 p)) (pfield::y (pfield::add y 1 p))
                  (pfield::p p))
  :disable (pfield::equal-of-0-and-mul))

(defruled hbhp-x-zero-r-point
  (implies (and (ecurve::edwards-bls12-r-pointp pt)
                (not (equal pt (hbhp-zero))))
           (not (equal (hbhp-x pt) 0)))
  :use ((:instance hbhp-point-facts (p (base-prime)))
        (:instance hbhp-sq-one (y (hbhp-y pt)) (p (base-prime)))
        hbhp-minus-one-point-not-r)
  :enable (hbhp-base-prime-facts ecurve::twisted-edwards-zero))

(defrulel hbhp-add-zero-neg
  (implies (and (pfield::fep x1 p) (pfield::fep x2 p) (primep p)
                (equal (pfield::add x1 x2 p) 0))
           (equal (pfield::neg x2 p) x1))
  :rule-classes nil
  :use hbhp-helper
  :in-theory (enable hbhp-posp-of-primep)
  :prep-lemmas
  ((defruled hbhp-posp-of-primep
     (implies (primep p) (posp p))
     :enable primep)
   (defruled hbhp-helper
     (implies (and (pfield::fep x1 p) (pfield::fep x2 p) (primep p))
              (equal (pfield::add (pfield::add x1 x2 p) (pfield::neg x2 p) p) x1)))))

(defrule hbhp-same-y-points
  (implies (and (ecurve::edwards-bls12-pointp p1)
                (ecurve::edwards-bls12-pointp p2)
                (equal (hbhp-y p1) (hbhp-y p2)))
           (or (equal p1 p2)
               (equal p1 (ecurve::edwards-bls12-neg p2))))
  :rule-classes nil
  :use ((:instance hbhp-point-facts (pt p1) (p (base-prime)))
        (:instance hbhp-point-facts (pt p2) (p (base-prime)))
        (:instance hbhp-neg-coords (pt p2) (p (base-prime)))
        (:instance hbhp-same-y-abstract
                   (a (ecurve::edwards-bls12-a)) (d (ecurve::edwards-bls12-d))
                   (x1 (hbhp-x p1)) (x2 (hbhp-x p2)) (y (hbhp-y p2))
                   (p (base-prime)))
        (:instance hbhp-add-zero-neg (x1 (hbhp-x p1)) (x2 (hbhp-x p2))
                   (p (base-prime))))
  :enable (hbhp-base-prime-facts)
  :disable (pfield::equal-of-0-and-add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro hbhp-gp (n g) `(ecurve::edwards-bls12-mul ,n ,g))

(defmacro hbhp-r () '(ecurve::edwards-bls12-r))

(defmacro hbhp-gen-okp (g)
  `(and (ecurve::edwards-bls12-r-pointp ,g)
        (not (equal ,g (hbhp-zero)))))

(defruled hbhp-x-of-mul-nonzero
  (implies (and (hbhp-gen-okp g)
                (integerp n)
                (not (equal (mod n (hbhp-r)) 0)))
           (not (equal (hbhp-x (hbhp-gp n g)) 0)))
  :use (hbhp-g-mul-zero-iff
        (:instance hbhp-x-zero-r-point (pt (hbhp-gp n g)))
        (:instance hbhp-r-pointp-of-mul (p1 g) (k n)))
  :in-theory nil)

(defruled hbhp-add-neg-self
  (implies (ecurve::edwards-bls12-pointp pt)
           (and (equal (ecurve::edwards-bls12-add pt (ecurve::edwards-bls12-neg pt))
                       (hbhp-zero))
                (equal (ecurve::edwards-bls12-add (ecurve::edwards-bls12-neg pt) pt)
                       (hbhp-zero))))
  :use hbhp-curve-ok
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-neg
           ecurve::edwards-bls12-pointp))

(defruled hbhp-y-of-muls-differ
  (implies (and (hbhp-gen-okp g)
                (integerp m) (integerp n)
                (not (equal (mod (- m n) (hbhp-r)) 0))
                (not (equal (mod (+ m n) (hbhp-r)) 0)))
           (not (equal (hbhp-y (hbhp-gp m g)) (hbhp-y (hbhp-gp n g)))))
  :use ((:instance hbhp-same-y-points (p1 (hbhp-gp m g)) (p2 (hbhp-gp n g)))
        (:instance hbhp-g-mul-zero-iff (n (- m n)))
        (:instance hbhp-g-mul-zero-iff (n (+ m n)))
        (:instance hbhp-g-mul-add (m m) (n (- n)))
        (:instance hbhp-g-mul-add (m m) (n n))
        (:instance hbhp-g-mul-add (m (- n)) (n n))
        (:instance hbhp-g-neg-mul (n n))
        (:instance hbhp-g-mul-zero-iff (n 0))
        (:instance hbhp-add-neg-self (pt (hbhp-gp m g)))
        (:instance hbhp-add-neg-self (pt (hbhp-gp n g)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g)))
  :in-theory (disable ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                      ecurve::edwards-bls12-neg (:e ecurve::edwards-bls12-r)))
