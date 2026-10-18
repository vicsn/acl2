; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bits of the signed right shift.  With R the big-endian value of the
; n value bits B and m the sign bit, the low n bits of (R + m) * 2^s - m,
; reversed, are B shifted down by s with m shifted in, and their signed
; value is floor(x / 2^s).

(in-package "ALEOVM")

(include-book "int-divshift-shr-unsigned")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel int-divshift-sshr-plus-cancel
  (implies (acl2-numberp x)
           (equal (+ s (- s) x) x)))

(defruledl int-divshift-sshr-val-repeat
  (implies (and (natp s) (bitp mv))
           (equal (lebits=>nat (repeat s mv))
                  (* mv (+ -1 (expt 2 s)))))
  :induct (repeat s mv)
  :enable (repeat acl2::lebits=>nat-of-cons bitp expt))

(defruledl int-divshift-sshr-bitlist-repeat
  (implies (bitp mv) (bit-listp (repeat s mv)))
  :enable repeat)

(defruledl int-divshift-sshr-mod-shift
  (implies (and (integerp a) (integerp c) (posp mm)
                (equal (mod a mm) aa)
                (<= 0 (+ aa c)) (< (+ aa c) mm))
           (equal (mod (+ a c) mm) (+ aa c)))
  :use ((:instance acl2::mod-of-+-of-mod-arg1 (acl2::x1 a) (acl2::x2 c) (acl2::y mm)))
  :enable acl2::mod-when-<
  :disable acl2::mod-of-+-of-mod-arg1)

(defruledl int-divshift-sshr-low-value
  (implies (and (bit-listp b) (natp n) (equal (len b) n)
                (natp s) (<= s n) (bitp mv))
           (equal (mod (+ (* (lebits=>nat (rev b)) (expt 2 s))
                          (* mv (+ -1 (expt 2 s))))
                       (expt 2 n))
                  (lebits=>nat (append (repeat s mv) (rev (nthcdr s b))))))
  :do-not-induct t
  :use ((:instance int-shr-mod-is-rev-floor-bits (bits b) (e s))
        (:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (repeat s mv))
                   (acl2::hidigits (rev (nthcdr s b))))
        (:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (repeat s 0))
                   (acl2::hidigits (rev (nthcdr s b))))
        (:instance val-bound)
        (:instance int-divshift-sshr-mod-shift
                   (a (* (lebits=>nat (rev b)) (expt 2 s)))
                   (c (* mv (+ -1 (expt 2 s))))
                   (mm (expt 2 n))
                   (aa (* (expt 2 s) (lebits=>nat (rev (nthcdr s b)))))))
  :in-theory (e/d (int-divshift-sshr-val-repeat
                   lebits=>nat-of-repeat-0
                   acl2::rev-of-append acl2::rev-of-repeat)
                  (int-shr-mod-is-rev-floor-bits
                   acl2::lebits=>nat-of-append acl2::lebits=>nat-upper-bound
                   int-divshift-sshr-mod-shift
                   take nthcdr repeat mod rev))
  :prep-lemmas
  ((defruled val-bound
     (implies (and (bit-listp b) (equal (len b) n)
                   (natp s) (<= s n) (bitp mv))
              (< (lebits=>nat (append (repeat s mv) (rev (nthcdr s b))))
                 (expt 2 n)))
     :use (:instance acl2::lebits=>nat-upper-bound
                     (digits (append (repeat s mv) (rev (nthcdr s b)))))
     :enable bitp
     :disable (acl2::lebits=>nat-upper-bound acl2::lebits=>nat-of-append))))

(defruledl int-divshift-sshr-take-bits-1
  (implies (and (bit-listp b) (natp n) (equal (len b) n)
                (natp s) (<= s n) (bitp mv))
           (equal (take n (int->lebits (+ (* (lebits=>nat (rev b))
                                             (expt 2 s))
                                          (* mv (+ -1 (expt 2 s))))
                                       (* 2 n)))
                  (append (repeat s mv) (rev (nthcdr s b)))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-low-value)
        (:instance int-lebits-take-is-mod
                   (bits (int->lebits (+ (* (lebits=>nat (rev b))
                                            (expt 2 s))
                                         (* mv (+ -1 (expt 2 s))))
                                      (* 2 n)))
                   (n n))
        (:instance lebits=>nat-of-int->lebits
                   (x (+ (* (lebits=>nat (rev b)) (expt 2 s))
                         (* mv (+ -1 (expt 2 s)))))
                   (n (* 2 n)))
        (:instance mod-mod-2n
                   (x (+ (* (lebits=>nat (rev b)) (expt 2 s))
                         (* mv (+ -1 (expt 2 s))))))
        (:instance int-divshift-shr-bits-from-nat-copy
                   (bits (take n (int->lebits
                                  (+ (* (lebits=>nat (rev b)) (expt 2 s))
                                     (* mv (+ -1 (expt 2 s))))
                                  (* 2 n))))
                   (v (lebits=>nat (append (repeat s mv)
                                           (rev (nthcdr s b))))))
        (:instance int-divshift-shr-bits-from-nat-copy
                   (bits (append (repeat s mv) (rev (nthcdr s b))))
                   (v (lebits=>nat (append (repeat s mv)
                                           (rev (nthcdr s b)))))))
  :in-theory (e/d (int-divshift-sshr-bitlist-repeat
                   int-bit-listp-of-nthcdr
                   len-of-int->lebits bit-listp-of-int->lebits-explicit
                   acl2::len-of-take acl2::ifix-when-integerp bitp)
                  (int->lebits int-divshift-sshr-low-value
                   int-lebits-take-is-mod lebits=>nat-of-int->lebits
                   mod-mod-2n int-divshift-shr-bits-from-nat-copy
                   take nthcdr repeat mod rev lebits=>nat
                   acl2::lebits=>nat-of-append))
  :prep-lemmas
  ((defruled mod-mod-2n
     (implies (and (integerp x) (natp n))
              (equal (mod (mod x (expt 2 (* 2 n))) (expt 2 n))
                     (mod x (expt 2 n))))
     :use ((:instance acl2::mod-of-mod-when-mult
                      (x x) (y1 (* (expt 2 n) (expt 2 n))) (y2 (expt 2 n)))
           (:instance expt-square-copy (a n)))
     :prep-lemmas
     ((defruled expt-square-copy
        (implies (natp a)
                 (equal (* (expt 2 a) (expt 2 a)) (expt 2 (* 2 a))))
        :use (:instance acl2::expt-of-+ (r 2) (i1 a) (i2 a))
        :disable acl2::expt-of-+)))
   (defruled int-divshift-shr-bits-from-nat-copy
     (implies (and (bit-listp bits)
                   (equal (len bits) n)
                   (equal (lebits=>nat bits) v))
              (equal (int->lebits v n) bits))
     :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
     :enable (int->lebits acl2::mod-when-<))))

(defruled int-divshift-sshr-take-bits
  :short "The low @('n') bits of @('(R + m) * 2^s - m'), as a list, are
          the reversed arithmetic-shift bits."
  (implies (and (bit-listp b) (natp n) (equal (len b) n)
                (natp s) (<= s n) (bitp mv))
           (equal (take n (int->lebits (+ (* (+ (lebits=>nat (rev b)) mv)
                                             (expt 2 s))
                                          (- mv))
                                       (* 2 n)))
                  (rev (append (nthcdr s b) (repeat s mv)))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-take-bits-1))
  :in-theory (e/d (acl2::rev-of-append acl2::rev-of-repeat bitp)
                  (int-divshift-sshr-take-bits-1 int->lebits
                   take nthcdr repeat rev lebits=>nat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-sshr-floor-facts
  (implies (and (integerp x) (posp a) (posp h) (<= (- h) x) (< x h))
           (and (<= (- h) (floor x a))
                (< (floor x a) h)
                (equal (< (floor x a) 0) (< x 0))))
  :do-not-induct t
  :use ((:instance acl2::<-of-floor-arg1 (i x) (j a) (k h))
        (:instance acl2::<-of-floor-arg1 (i x) (j a) (k (- h)))
        (:instance acl2::<-of-floor-arg1 (i x) (j a) (k 0))
        (:instance h-le-ha))
  :disable (acl2::<-of-floor-arg1 floor)
  :prep-lemmas
  ((defruled h-le-ha
     (implies (and (posp a) (posp h))
              (<= h (* h a)))
     :hints (("Goal" :nonlinearp t)))))

(defruledl int-divshift-sshr-signed-mod
  (implies (and (posp n)
                (integerp x)
                (<= (- (expt 2 (1- n))) x)
                (< x (expt 2 (1- n))))
           (equal (mod x (expt 2 n))
                  (if (< x 0)
                      (+ x (expt 2 n))
                    x)))
  :cases ((< x 0))
  :use (:instance acl2::expt-of-+ (r 2) (i1 1) (i2 (1- n)))
  :enable (acl2::mod-when-<-of-0 acl2::mod-when-<)
  :disable acl2::expt-of-+)

(defruledl int-divshift-sshr-expt-split
  (implies (and (natp s) (natp n) (<= s n))
           (equal (* (expt 2 s) (expt 2 (+ n (- s))))
                  (expt 2 n)))
  :use (:instance acl2::expt-of-+ (r 2) (i1 s) (i2 (+ n (- s))))
  :disable acl2::expt-of-+)

(defruled int-divshift-sshr-bits-value
  (implies (and (posp n) (int-valuep x t n) (natp s) (< s n))
           (equal (lebits=>nat
                   (append (nthcdr s (int->lebits x n))
                           (repeat s (car (last (int->lebits x n))))))
                  (+ (floor x (expt 2 s))
                     (if (< x 0) (expt 2 n) 0))))
  :do-not-induct t
  :cases ((< x 0))
  :use ((:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (nthcdr s (int->lebits x n)))
                   (acl2::hidigits (repeat s (car (last (int->lebits x n))))))
        (:instance int-floor-lebits-nthcdr (bits (int->lebits x n)) (e s))
        (:instance lebits=>nat-of-int->lebits)
        (:instance int-signed-msb)
        (:instance int-divshift-sshr-signed-mod)
        (:instance int-divshift-sshr-expt-split)
        (:instance split-2)
        (:instance floor-plus-mult
                   (a (expt 2 s)) (b (expt 2 (+ n (- s))))))
  :in-theory (e/d (int-divshift-sshr-val-repeat
                   len-of-int->lebits bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max acl2::ifix-when-integerp)
                  (acl2::lebits=>nat-of-append int-floor-lebits-nthcdr
                   lebits=>nat-of-int->lebits int-signed-msb
                   int-divshift-sshr-signed-mod int-divshift-sshr-expt-split
                   floor-plus-mult split-2
                   int->lebits floor mod nthcdr repeat))
  :prep-lemmas
  ((defruled split-2
     (implies (and (natp s) (natp n) (<= s n))
              (equal (* (+ -1 (expt 2 s)) (expt 2 (+ n (- s))))
                     (+ (expt 2 n) (- (expt 2 (+ n (- s)))))))
     :use (int-divshift-sshr-expt-split
           (:instance gen (a (expt 2 s)) (b (expt 2 (+ n (- s))))))
     :in-theory (union-theories '((:type-prescription expt))
                                (theory 'minimal-theory))
     :prep-lemmas
     ((defruled gen
        (implies (and (acl2-numberp a) (acl2-numberp b))
                 (equal (* (+ -1 a) b) (+ (* a b) (- b)))))))
   (defruled floor-plus-mult
     (implies (and (integerp x) (posp a) (integerp b))
              (equal (floor (+ x (* a b)) a) (+ b (floor x a))))
     :use (:instance acl2::floor-of-+-when-mult-arg2
                     (i1 x) (i2 (* a b)) (j a) (i b))
     :disable acl2::floor-of-+-when-mult-arg2)))

(defruled int-divshift-sshr-bits-signed
  :short "The arithmetic-shift bits have signed value @('floor(x / 2^s)')."
  (implies (and (posp n) (int-valuep x t n) (natp s) (< s n))
           (equal (lebits->int
                   (append (nthcdr s (int->lebits x n))
                           (repeat s (car (last (int->lebits x n)))))
                   t)
                  (floor x (expt 2 s))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-bits-value)
        (:instance int-divshift-sshr-floor-facts
                   (a (expt 2 s)) (h (expt 2 (1- n))))
        (:instance acl2::expt-of-+ (r 2) (i1 1) (i2 (1- n))))
  :in-theory (e/d (lebits->int len-of-int->lebits
                   int-valuep int-min int-max)
                  (int-divshift-sshr-bits-value int-divshift-sshr-floor-facts
                   acl2::expt-of-+
                   int->lebits floor nthcdr repeat lebits=>nat)))
