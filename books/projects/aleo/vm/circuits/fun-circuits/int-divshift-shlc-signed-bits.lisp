; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bit facts for the signed shl_checked overflow check: the 2n-bit image of
; V has bits n..2n-1 equal to the msb of its low n bits exactly when V is
; congruent modulo 2^(2n) to the signed value of its low n bits.

(in-package "ALEOVM")

(include-book "int-divshift-sshr-bits")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel int-divshift-slc-plus-cancel
  (implies (acl2-numberp x)
           (equal (+ s (- s) x) x)))

(defruledl int-divshift-slc-bits-from-nat
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (equal (lebits=>nat bits) v))
           (equal (int->lebits v n) bits))
  :use (:instance acl2::nat=>lebits-of-lebits=>nat (digits bits))
  :enable (int->lebits acl2::mod-when-<))

(defruledl int-divshift-slc-mod-mod
  (implies (and (integerp v) (natp k) (natp w) (<= k w))
           (equal (mod (mod v (expt 2 w)) (expt 2 k))
                  (mod v (expt 2 k))))
  :use ((:instance acl2::mod-of-mod-when-mult
                   (x v) (y1 (* (expt 2 k) (expt 2 (- w k)))) (y2 (expt 2 k)))
        (:instance acl2::expt-of-+ (r 2) (i1 k) (i2 (- w k))))
  :disable acl2::expt-of-+)

(defruled int-divshift-take-of-int->lebits
  (implies (and (integerp v) (natp k) (natp w) (<= k w))
           (equal (take k (int->lebits v w))
                  (int->lebits v k)))
  :do-not-induct t
  :use ((:instance int-lebits-take-is-mod (bits (int->lebits v w)) (n k))
        (:instance lebits=>nat-of-int->lebits (x v) (n w))
        (:instance int-divshift-slc-mod-mod)
        (:instance lebits=>nat-of-int->lebits (x v) (n k))
        (:instance int-divshift-slc-bits-from-nat
                   (bits (take k (int->lebits v w)))
                   (n k)
                   (v (mod v (expt 2 k))))
        (:instance acl2::lebits=>nat-of-nat=>lebits-copy (n k)))
  :in-theory (e/d (len-of-int->lebits bit-listp-of-int->lebits-explicit
                   acl2::ifix-when-integerp)
                  (int->lebits int-lebits-take-is-mod lebits=>nat-of-int->lebits
                   int-divshift-slc-mod-mod int-divshift-slc-bits-from-nat
                   take mod))
  :prep-lemmas
  ((defruled acl2::lebits=>nat-of-nat=>lebits-copy
     (implies (and (integerp v) (natp n))
              (equal (int->lebits (mod v (expt 2 n)) n)
                     (int->lebits v n)))
     :enable int->lebits)))

(defruledl int-divshift-slc-val-repeat
  (implies (and (natp s) (bitp c))
           (equal (lebits=>nat (repeat s c))
                  (* c (+ -1 (expt 2 s)))))
  :induct (repeat s c)
  :enable (repeat acl2::lebits=>nat-of-cons bitp expt))

(defruledl int-divshift-slc-split-2n
  (implies (and (bit-listp y) (natp n) (equal (len y) (* 2 n)))
           (equal (lebits=>nat y)
                  (+ (lebits=>nat (take n y))
                     (* (expt 2 n) (lebits=>nat (nthcdr n y))))))
  :use ((:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (take n y))
                   (acl2::hidigits (nthcdr n y))))
  :disable acl2::lebits=>nat-of-append)

(defruled int-divshift-slc-signed-low
  :short "The low @('n') bits of @('V') are the bits of their signed
          value @('z'), whose unsigned value is @('z + c 2^n')."
  (implies (and (posp n) (integerp v))
           (b* ((z (lebits->int (int->lebits v n) t))
                (c (car (last (int->lebits v n)))))
             (and (int-valuep z t n)
                  (equal (int->lebits z n) (int->lebits v n))
                  (equal c (if (< z 0) 1 0))
                  (equal (mod v (expt 2 n))
                         (+ z (* c (expt 2 n)))))))
  :do-not-induct t
  :use ((:instance int-valuep-of-lebits->int
                   (bits (int->lebits v n)) (signedp t))
        (:instance lebits->int-of-int->lebits-inv)
        (:instance int-signed-msb (x (lebits->int (int->lebits v n) t)))
        (:instance lebits=>nat-of-int->lebits (x v) (n n))
        (:instance lebits=>nat-of-int->lebits
                   (x (lebits->int (int->lebits v n) t)) (n n))
        (:instance int-divshift-sshr-signed-mod-copy
                   (x (lebits->int (int->lebits v n) t))))
  :in-theory (e/d (len-of-int->lebits bit-listp-of-int->lebits-explicit
                   int-valuep int-min int-max acl2::ifix-when-integerp)
                  (int-valuep-of-lebits->int int-signed-msb
                   lebits=>nat-of-int->lebits int->lebits lebits->int mod))
  :prep-lemmas
  ((defruled lebits->int-of-int->lebits-inv
     (implies (and (posp n) (integerp v))
              (equal (int->lebits (lebits->int (int->lebits v n) t) n)
                     (int->lebits v n)))
     :enable (int->lebits lebits->int lebits=>nat-of-int->lebits
              len-of-int->lebits acl2::mod-when-<)
     :use ((:instance acl2::lebits=>nat-upper-bound
                      (digits (int->lebits v n)))
           (:instance lebits=>nat-of-int->lebits (x v) (n n))
           (:instance acl2::mod-of-+-of-mod-arg1-copy
                      (a (mod v (expt 2 n))) (m (expt 2 n))))
     :disable (acl2::lebits=>nat-upper-bound)
     :prep-lemmas
     ((defruled acl2::mod-of-+-of-mod-arg1-copy
        (implies (and (integerp a) (posp m))
                 (equal (mod (+ a (- m)) m) (mod a m)))
        :enable acl2::mod-when-<)))
   (defruled int-divshift-sshr-signed-mod-copy
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
     :disable acl2::expt-of-+)))

(defruledl int-divshift-slc-expt-square
  (implies (natp a)
           (equal (* (expt 2 a) (expt 2 a)) (expt 2 (* 2 a))))
  :use (:instance acl2::expt-of-+ (r 2) (i1 a) (i2 a))
  :disable acl2::expt-of-+)

(defruled int-divshift-slc-check-value
  (implies (and (posp n)
                (integerp v)
                (equal (nthcdr n (int->lebits v (* 2 n)))
                       (repeat n (car (last (int->lebits v n))))))
           (equal (mod v (expt 2 (* 2 n)))
                  (+ (lebits->int (int->lebits v n) t)
                     (* (car (last (int->lebits v n)))
                        (expt 2 (* 2 n))))))
  :do-not-induct t
  :use ((:instance int-divshift-slc-split-2n (y (int->lebits v (* 2 n))))
        (:instance lebits=>nat-of-int->lebits (x v) (n (* 2 n)))
        (:instance lebits=>nat-of-int->lebits (x v) (n n))
        (:instance int-divshift-take-of-int->lebits (k n) (w (* 2 n)))
        (:instance int-divshift-slc-signed-low)
        (:instance high-val (c (car (last (int->lebits v n)))))
        (:instance int-divshift-slc-expt-square (a n)))
  :in-theory (e/d (len-of-int->lebits bit-listp-of-int->lebits-explicit
                   acl2::ifix-when-integerp bitp)
                  (int-divshift-slc-split-2n lebits=>nat-of-int->lebits
                   int-divshift-take-of-int->lebits int-divshift-slc-signed-low
                   int-divshift-slc-val-repeat int-divshift-slc-expt-square
                   high-val
                   int->lebits lebits->int take nthcdr repeat mod))
  :prep-lemmas
  ((defruled high-val
     (implies (and (natp n) (bitp c))
              (equal (* (expt 2 n) (lebits=>nat (repeat n c)))
                     (* c (+ (expt 2 (* 2 n)) (- (expt 2 n))))))
     :use ((:instance int-divshift-slc-val-repeat (s n))
           (:instance int-divshift-slc-expt-square (a n)))
     :in-theory (e/d (bitp) (int-divshift-slc-val-repeat
                             int-divshift-slc-expt-square)))))

(defruled int-divshift-slc-check-sound
  :short "If the high bits agree with the msb, a small @('y') congruent
          to @('V') is the signed value of the low bits of @('V')."
  (implies (and (posp n)
                (integerp v)
                (integerp y)
                (<= (* 4 y) (expt 2 (* 2 n)))
                (<= (- (expt 2 (* 2 n))) (* 4 y))
                (equal (mod v (expt 2 (* 2 n)))
                       (mod y (expt 2 (* 2 n))))
                (equal (nthcdr n (int->lebits v (* 2 n)))
                       (repeat n (car (last (int->lebits v n))))))
           (and (equal (lebits->int (int->lebits v n) t) y)
                (int-valuep y t n)))
  :do-not-induct t
  :cases ((< y 0))
  :use ((:instance int-divshift-slc-check-value)
        (:instance int-divshift-slc-signed-low)
        (:instance int-divshift-slc-expt-square (a n))
        (:instance two-pow-le (a (expt 2 n)))
        (:instance acl2::expt-of-+ (r 2) (i1 1) (i2 (1- n))))
  :in-theory (e/d (int-valuep int-min int-max acl2::mod-when-<
                   acl2::mod-when-<-of-0-copy)
                  (int-divshift-slc-check-value int-divshift-slc-signed-low
                   int-divshift-slc-expt-square acl2::expt-of-+
                   int->lebits lebits->int))
  :prep-lemmas
  ((defruled two-pow-le
     (implies (and (integerp a) (<= 2 a))
              (<= (* 2 a) (* a a)))
     :hints (("Goal" :nonlinearp t)))
   (defruled acl2::mod-when-<-of-0-copy
     (implies (and (integerp y) (< y 0) (posp m) (<= (- m) y))
              (equal (mod y m) (+ y m)))
     :use (:instance acl2::floor-unique (i y) (j m) (n -1))
     :enable mod)))

(defruledl int-divshift-slc-int->lebits-of-mod
  (implies (and (integerp v) (natp n))
           (equal (int->lebits (mod v (expt 2 n)) n)
                  (int->lebits v n)))
  :enable int->lebits)

(defruledl int-divshift-slc-bitlist-repeat
  (implies (bitp mv) (bit-listp (repeat s mv)))
  :enable repeat)

(defruledl int-divshift-slc-le-sq
  (implies (and (integerp a) (<= 1 a)) (<= a (* a a)))
  :hints (("Goal" :nonlinearp t)))

(defruledl int-divshift-slc-signed-mod-2
  (implies (and (posp n) (integerp x)
                (<= (- (expt 2 (1- n))) x)
                (< x (expt 2 (1- n))))
           (and (equal (mod x (expt 2 n))
                       (if (< x 0) (+ x (expt 2 n)) x))
                (equal (mod x (expt 2 (* 2 n)))
                       (if (< x 0) (+ x (expt 2 (* 2 n))) x))))
  :cases ((< x 0))
  :use ((:instance acl2::expt-of-+ (r 2) (i1 1) (i2 (1- n)))
        (:instance int-divshift-slc-expt-square (a n))
        (:instance int-divshift-slc-le-sq (a (expt 2 n))))
  :enable (acl2::mod-when-<-of-0 acl2::mod-when-<)
  :disable (acl2::expt-of-+ int-divshift-slc-expt-square))

(defruled int-divshift-slc-sext-bits
  :short "Sign extension: the @('2n')-bit image of a signed @('n')-bit
          value is its @('n') bits followed by @('n') copies of the msb."
  (implies (and (posp n) (int-valuep y t n))
           (equal (append (int->lebits y n)
                          (repeat n (car (last (int->lebits y n)))))
                  (int->lebits y (* 2 n))))
     :do-not-induct t
     :use ((:instance acl2::lebits=>nat-of-append
                      (acl2::lodigits (int->lebits y n))
                      (acl2::hidigits (repeat n (car (last (int->lebits y n))))))
           (:instance int-signed-msb (x y))
           (:instance lebits=>nat-of-int->lebits (x y) (n n))
           (:instance int-divshift-slc-val-repeat
                      (s n) (c (car (last (int->lebits y n)))))
           (:instance int-divshift-slc-expt-square (a n))
           (:instance int-divshift-slc-signed-mod-2 (x y))
           (:instance int-divshift-slc-bits-from-nat
                      (bits (append (int->lebits y n)
                                    (repeat n (car (last (int->lebits y n))))))
                      (n (* 2 n))
                      (v (mod y (expt 2 (* 2 n)))))
           (:instance int-divshift-slc-int->lebits-of-mod (v y) (n (* 2 n)))
           )
     :in-theory (e/d (len-of-int->lebits bit-listp-of-int->lebits-explicit
                      acl2::ifix-when-integerp int-valuep int-min int-max bitp
                      int-divshift-slc-bitlist-repeat)
                     (acl2::lebits=>nat-of-append int-signed-msb
                      lebits=>nat-of-int->lebits int-divshift-slc-val-repeat
                      int-divshift-slc-expt-square int-divshift-slc-signed-mod-2
                      int-divshift-slc-bits-from-nat
                      int-divshift-slc-int->lebits-of-mod
                      int->lebits nthcdr repeat mod)))

(defruled int-divshift-slc-check-complete
  :short "An in-range @('y') congruent to @('V') gives high bits equal to
          the msb, and the low bits of @('V') decode to @('y')."
  (implies (and (posp n)
                (integerp v)
                (int-valuep y t n)
                (equal (mod v (expt 2 (* 2 n)))
                       (mod y (expt 2 (* 2 n)))))
           (and (equal (nthcdr n (int->lebits v (* 2 n)))
                       (repeat n (car (last (int->lebits v n)))))
                (equal (lebits->int (int->lebits v n) t) y)))
  :do-not-induct t
  :use ((:instance int-divshift-slc-int->lebits-of-mod (n (* 2 n)))
        (:instance int-divshift-slc-int->lebits-of-mod (v y) (n (* 2 n)))
        (:instance int-divshift-slc-int->lebits-of-mod (n n))
        (:instance int-divshift-slc-int->lebits-of-mod (v y) (n n))
        (:instance int-divshift-slc-mod-mod (k n) (w (* 2 n)))
        (:instance int-divshift-slc-mod-mod (v y) (k n) (w (* 2 n)))
        (:instance int-signed-msb (x y))
        (:instance lebits->int-of-int->lebits (x y) (signedp t))
        (:instance whole-bits))
  :in-theory (e/d (acl2::ifix-when-integerp int-valuep)
                  (int-divshift-slc-int->lebits-of-mod
                   int-divshift-slc-mod-mod int-signed-msb
                   lebits->int-of-int->lebits
                   whole-bits
                   int->lebits lebits->int nthcdr repeat mod))
  :prep-lemmas
  ((defruled whole-bits
     (implies (and (posp n) (int-valuep y t n))
              (equal (nthcdr n (int->lebits y (* 2 n)))
                     (repeat n (car (last (int->lebits y n))))))
     :do-not-induct t
     :use ((:instance int-divshift-slc-sext-bits)
           (:instance nthcdr-app (a (int->lebits y n))
                      (r (repeat n (car (last (int->lebits y n)))))))
     :in-theory (e/d (len-of-int->lebits)
                     (int-divshift-slc-sext-bits int->lebits nthcdr repeat))
     :prep-lemmas
     ((defruled nthcdr-app
        (implies (and (equal (len a) n) (true-listp r))
                 (equal (nthcdr n (append a r)) r)))))))
