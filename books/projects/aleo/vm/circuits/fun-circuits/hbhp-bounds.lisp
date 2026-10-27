; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar bounds for one BHP window.  After j chunks the accumulated scalar
; s = sum_{i<j} c_i 16^i, with |c_i| in [1, 4], satisfies
;   0 < |s| <= B_j = 4 (16^j - 1) / 15   (j >= 1),
; and adding c 16^j keeps every quantity the Montgomery addition needs
; (s, c 16^j, s + c 16^j, s - c 16^j) nonzero and at most B_{j+1} in
; absolute value.  B_63 < r (B_63 / r ~ 0.914), and snarkVM's BHP requires
; WINDOW_SIZE <= 63 (BHP_LOOKUP_SIZE / max_window_size checks in
; console/algorithms/src/bhp/hasher/mod.rs), so none of them is a multiple
; of r.  With hbhp-group.lisp this discharges all exceptional cases.

(in-package "ALEOVM")

(include-book "hbhp-group")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defruledl hbhp-expt16-succ
  (implies (natp j)
           (and (equal (expt 16 (+ 1 j)) (* 16 (expt 16 j)))
                (< 0 (expt 16 j))
                (integerp (expt 16 j))))
  :enable expt)

(define hbhp-wbound ((j natp))
  :returns (b natp)
  (if (zp j) 0 (+ (hbhp-wbound (1- j)) (* 4 (expt 16 (1- j))))))

(defruled hbhp-wbound-lt-expt
  (< (hbhp-wbound j) (expt 16 (nfix j)))
  :induct (hbhp-wbound j)
  :enable hbhp-wbound
  :hints (("Subgoal *1/2" :use (:instance hbhp-expt16-succ (j (1- j))))))

(defruled hbhp-wbound-of-succ
  (implies (natp j)
           (equal (hbhp-wbound (+ 1 j))
                  (+ (hbhp-wbound j) (* 4 (expt 16 j)))))
  :expand ((hbhp-wbound (+ 1 j))))

(defruled hbhp-wbound-monotone
  (implies (and (natp i) (natp j) (<= i j))
           (<= (hbhp-wbound i) (hbhp-wbound j)))
  :induct (hbhp-wbound j)
  :enable hbhp-wbound)

(defruled hbhp-wbound-63-lt-r
  (< (hbhp-wbound 63) (ecurve::edwards-bls12-r))
  :in-theory '((:e hbhp-wbound) (:e ecurve::edwards-bls12-r) (:e <)))

(defruled hbhp-mod-r-nonzero
  (implies (and (integerp x)
                (not (equal x 0))
                (< x (ecurve::edwards-bls12-r))
                (< (- x) (ecurve::edwards-bls12-r)))
           (not (equal (mod x (ecurve::edwards-bls12-r)) 0)))
  :use (hbhp-r-pos (:instance hbhp-mod-small (r (ecurve::edwards-bls12-r))))
  :prep-lemmas
  ((defruled hbhp-mod-small
     (implies (and (integerp x) (integerp r) (< 0 r)
                   (not (equal x 0)) (< x r) (< (- x) r))
              (not (equal (mod x r) 0)))
     :cases ((< 0 x))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defruled hbhp-r-pos
     (and (< 2 (ecurve::edwards-bls12-r)) (integerp (ecurve::edwards-bls12-r)))
     :in-theory '((:e ecurve::edwards-bls12-r) (:e <) (:e integerp)))))

(define hbhp-acc-okp (s (j natp))
  :returns (yes/no booleanp)
  :short "Invariant of the accumulated window scalar after @('j') chunks."
  (and (integerp s)
       (<= s (hbhp-wbound j))
       (<= (- s) (hbhp-wbound j))
       (implies (< 0 (nfix j)) (not (equal s 0)))))

(defruled hbhp-chunk-scalar-range
  (and (integerp (hbhp-chunk-scalar b0 b1 b2))
       (<= 1 (abs (hbhp-chunk-scalar b0 b1 b2)))
       (<= (abs (hbhp-chunk-scalar b0 b1 b2)) 4))
  :enable (hbhp-chunk-scalar acl2::bfix))

(defruled hbhp-acc-okp-first
  (hbhp-acc-okp (hbhp-chunk-scalar b0 b1 b2) 1)
  :use hbhp-chunk-scalar-range
  :enable (hbhp-acc-okp hbhp-wbound))

(defruled hbhp-ce-bounds
  (implies (and (integerp c) (integerp e) (< 0 e)
                (<= 1 (abs c)) (<= (abs c) 4))
           (and (integerp (* c e))
                (implies (< 0 c) (and (<= e (* c e)) (<= (* c e) (* 4 e))))
                (implies (< c 0) (and (<= (* c e) (- e)) (<= (- (* 4 e)) (* c e))))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-chunk-mult-bound
  (implies (and (natp j) (integerp c) (<= 1 (abs c)) (<= (abs c) 4))
           (and (integerp (* c (expt 16 j)))
                (not (equal (* c (expt 16 j)) 0))
                (<= (abs (* c (expt 16 j))) (hbhp-wbound (+ 1 j)))))
  :use (hbhp-wbound-of-succ hbhp-expt16-succ
        (:instance hbhp-ce-bounds (e (expt 16 j))))
  :cases ((<= 0 c)))

(defruled hbhp-acc-step
  :short "Adding a chunk keeps the invariant and the step quantities small."
  (implies (and (natp j)
                (hbhp-acc-okp s j)
                (integerp c) (<= 1 (abs c)) (<= (abs c) 4))
           (b* ((cc (* c (expt 16 j))))
             (and (hbhp-acc-okp (+ s cc) (+ 1 j))
                  (integerp cc)
                  (not (equal cc 0))
                  (<= (abs cc) (hbhp-wbound (+ 1 j)))
                  (not (equal (+ s cc) 0))
                  (<= (abs (+ s cc)) (hbhp-wbound (+ 1 j)))
                  (not (equal (- s cc) 0))
                  (<= (abs (- s cc)) (hbhp-wbound (+ 1 j))))))
  :use (hbhp-wbound-lt-expt hbhp-wbound-of-succ hbhp-expt16-succ
        (:instance hbhp-ce-bounds (e (expt 16 j))))
  :enable (hbhp-acc-okp)
  :cases ((<= 0 c)))

(defruled hbhp-small-scalar-mod
  (implies (and (integerp x) (not (equal x 0))
                (natp k) (<= k 63)
                (<= (abs x) (hbhp-wbound k)))
           (not (equal (mod x (ecurve::edwards-bls12-r)) 0)))
  :use (hbhp-wbound-63-lt-r
        (:instance hbhp-wbound-monotone (i k) (j 63))
        hbhp-mod-r-nonzero))
