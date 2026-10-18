; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed truncating division and remainder in terms of the unsigned
; division of the absolute values, as used by snarkVM's signed
; div_wrapped and rem_wrapped circuits.

(in-package "ALEOVM")

(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

(defruled int-divshift-truncate-via-abs
  (implies (and (integerp x) (integerp y) (not (equal y 0)))
           (equal (truncate x y)
                  (if (equal (< x 0) (< y 0))
                      (truncate (abs x) (abs y))
                    (- (truncate (abs x) (abs y))))))
  :cases ((< x 0) (< y 0)))

(defruled int-divshift-rem-via-abs
  (implies (and (integerp x) (integerp y) (not (equal y 0)))
           (equal (rem x y)
                  (if (< x 0)
                      (- (rem (abs x) (abs y)))
                    (rem (abs x) (abs y)))))
  :cases ((< x 0) (< y 0)))

(defruled int-divshift-truncate-abs-bounds
  (implies (and (natp a) (natp b) (not (equal b 0)))
           (and (natp (truncate a b))
                (<= (truncate a b) a)))
  :hints (("Goal" :cases ((equal b 1)))
          (and stable-under-simplificationp '(:nonlinearp t))))

(defruled int-divshift-rem-abs-bounds
  (implies (and (natp a) (natp b) (not (equal b 0)))
           (and (natp (rem a b))
                (< (rem a b) b))))

(defruledl int-divshift-truncate-shrinks
  (implies (and (natp a) (< 0 a) (integerp b) (<= 2 b))
           (< (truncate a b) a))
  :hints (("Goal" :nonlinearp t)))

(defruled int-divshift-truncate-fits
  (implies (and (posp k)
                (integerp x) (integerp y) (not (equal y 0))
                (<= (- k) x) (< x k)
                (<= (- k) y) (< y k)
                (not (and (equal x (- k)) (equal y -1))))
           (and (<= (- k) (truncate x y))
                (< (truncate x y) k)))
  :use (int-divshift-truncate-via-abs
        (:instance int-divshift-truncate-abs-bounds (a (abs x)) (b (abs y)))
        (:instance int-divshift-truncate-shrinks (a (abs x)) (b (abs y))))
  :cases ((equal (abs y) 1))
  :disable (truncate acl2::rewrite-truncate-to-floor))

(defruled int-divshift-integerp-of-rem
  (implies (and (integerp x) (integerp y))
           (integerp (rem x y))))
