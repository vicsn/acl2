; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Arithmetic for the 128-bit signed shr_wrapped circuit: the arithmetic
; shift floor(x, d) is the truncated quotient of |x| by d for x >= 0, its
; negation for x < 0 with zero remainder, and the negation minus one
; otherwise.

(in-package "ALEOVM")

(include-book "int-support")

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-ss128-quot-split
  (implies (and (natp a) (posp d))
           (equal (/ a d)
                  (+ (floor a d) (/ (mod a d) d))))
  :enable mod)

(defruledl int-divshift-ss128-frac-bounds
  (implies (and (natp a) (posp d))
           (and (<= 0 (/ (mod a d) d))
                (< (/ (mod a d) d) 1)
                (implies (not (equal (mod a d) 0))
                         (< 0 (/ (mod a d) d)))))
  :use ((:instance acl2::<-of-*-and-*-cancel-gen
                   (x1 (mod a d)) (x2 d) (y (/ d))))
  :disable acl2::<-of-*-and-*-cancel-gen
  :hints (("Goal" :nonlinearp t)))

(defruled int-divshift-ss128-floor-of-neg
  (implies (and (natp a) (posp d))
           (equal (floor (- a) d)
                  (if (equal (mod a d) 0)
                      (- (floor a d))
                    (+ -1 (- (floor a d))))))
  :do-not-induct t
  :use ((:instance int-divshift-ss128-quot-split)
        (:instance int-divshift-ss128-frac-bounds)
        (:instance acl2::floor-unique
                   (i (- a)) (j d)
                   (n (if (equal (mod a d) 0)
                          (- (floor a d))
                        (+ -1 (- (floor a d)))))))
  :in-theory (disable int-divshift-ss128-quot-split
                      int-divshift-ss128-frac-bounds
                      floor mod))

(defruled int-divshift-sshr128-floor-cases
  :short "@('floor(x, d)') from the truncated division of @('|x|') by @('d')."
  (implies (and (integerp x) (posp d))
           (equal (floor x d)
                  (if (< x 0)
                      (if (equal (rem (abs x) d) 0)
                          (- (truncate (abs x) d))
                        (+ -1 (- (truncate (abs x) d))))
                    (truncate (abs x) d))))
  :do-not-induct t
  :use ((:instance int-divshift-ss128-floor-of-neg (a (- x))))
  :enable (acl2::truncate-becomes-floor acl2::rem-becomes-mod)
  :disable (floor mod truncate rem))
