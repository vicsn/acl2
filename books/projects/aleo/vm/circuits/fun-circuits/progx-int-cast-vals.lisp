; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value-level facts for the eight Integer-to-Integer arms of Integer::cast
; (snarkVM circuit/program/src/data/literal/cast/integer.rs).  bs are the n0
; input bits, m = (car (last bs)) their most significant bit, x their
; integer value with source signedness s0; s1 and n1 are the destination
; signedness and width.  For each case:
;   progx-icast-predp  what the case's constraints impose on bs
;   progx-icast-obits  the bits Integer::from_bits_le receives (constant
;                      false padding bits are omitted: they add no value)
; and the theorems show predp holds exactly when x fits the destination,
; and that then the from_bits_le reading of obits is x.
;   (u,u)          assert_bits_are_zero on bits n1..        obits bs or take n1
;   (u,s) n0 < n1  nothing                                   obits bs
;   (u,s) else     assert_bits_are_zero on bits n1-1..       obits take n1
;   (s,u) n0 <= n1 assert(!m)                                obits bs
;   (s,u) else     assert_bits_are_zero on bits n1..         obits take n1
;   (s,s) n0 <= n1 nothing                       obits bs ++ (n1-n0) copies of m
;   (s,s) else     assert_eq(m, b) for bits b in n1-1..n0-2  obits take n1-1 ++ m

(in-package "ALEOVM")

(include-book "progx-int-cast-bits")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define progx-icast-zerop ((k natp) (bs true-listp))
  :short "The bits of bs from position k on are all zero."
  (equal (nthcdr k bs) (repeat (len (nthcdr k bs)) 0)))

(defruled progx-icast-zerop-iff
  (implies (and (bit-listp bs) (natp k))
           (equal (progx-icast-zerop k bs)
                  (< (lebits=>nat bs) (expt 2 k))))
  :use ((:instance int-lebits-below-pow2-when-excess-zero (bits bs) (n k))
        (:instance int-excess-zero-when-lebits-below (bits bs) (n k)))
  :enable progx-icast-zerop)

(defruled progx-lebits-of-take-when-small
  (implies (and (bit-listp bs) (natp k) (<= k (len bs))
                (< (lebits=>nat bs) (expt 2 k)))
           (equal (lebits=>nat (take k bs)) (lebits=>nat bs)))
  :use (progx-lebits-split
        (:instance int-excess-zero-when-lebits-below (bits bs) (n k))
        (:instance progx-lebits-of-repeat-0 (j (len (nthcdr k bs))))))

(define progx-icast-predp ((bs true-listp) s0 s1 (n1 posp))
  (b* ((n0 (len bs)) (m (car (last bs))))
    (cond ((and s0 s1)
           (or (<= n0 n1)
               (equal (nthcdr (1- n1) bs) (repeat (- n0 (1- n1)) m))))
          (s1 (progx-icast-zerop (1- n1) bs))
          (s0 (and (equal m 0) (progx-icast-zerop n1 bs)))
          (t (progx-icast-zerop n1 bs)))))

(define progx-icast-obits ((bs true-listp) s0 s1 (n1 posp))
  (b* ((n0 (len bs)) (m (car (last bs))))
    (cond ((and s0 s1)
           (if (<= n0 n1)
               (append bs (repeat (- n1 n0) m))
             (append (take (1- n1) bs) (list m))))
          ((and s1 (< n0 n1)) bs)
          ((<= n0 n1) bs)
          (t (take n1 bs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unsigned source.

(defruled progx-icast-unsigned-source
  (implies (and (bit-listp bs) (consp bs) (posp n1) (not s0))
           (and (equal (progx-icast-predp bs s0 s1 n1)
                       (int-valuep (lebits->int bs s0) s1 n1))
                (implies (progx-icast-predp bs s0 s1 n1)
                         (equal (int-wrap
                                 (lebits=>nat (progx-icast-obits bs s0 s1 n1))
                                 s1 n1)
                                (lebits->int bs s0)))))
  :do-not-induct t
  :use ((:instance progx-icast-zerop-iff (k n1))
        (:instance progx-icast-zerop-iff (k (1- n1)))
        (:instance progx-lebits-of-take-when-small (k n1))
        (:instance progx-lebits-bound)
        (:instance progx-int-wrap-small (u (lebits=>nat bs)) (s s1) (n n1)))
  :enable (progx-icast-predp progx-icast-obits lebits->int-when-unsigned
           int-valuep int-min int-max)
  :disable (progx-icast-zerop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Signed source, unsigned destination.

(defruled progx-icast-signed-unsigned
  (implies (and (bit-listp bs) (consp bs) (posp n1) s0 (not s1))
           (and (equal (progx-icast-predp bs s0 s1 n1)
                       (int-valuep (lebits->int bs s0) s1 n1))
                (implies (progx-icast-predp bs s0 s1 n1)
                         (equal (int-wrap
                                 (lebits=>nat (progx-icast-obits bs s0 s1 n1))
                                 s1 n1)
                                (lebits->int bs s0)))))
  :do-not-induct t
  :use ((:instance progx-icast-zerop-iff (k n1))
        (:instance progx-lebits-of-take-when-small (k n1))
        progx-lebits-bound
        progx-lebits->int-cases
        progx-msb-0-or-1
        (:instance progx-int-wrap-small (u (lebits=>nat bs)) (s s1) (n n1)))
  :enable (progx-icast-predp progx-icast-obits
           int-valuep int-min int-max)
  :disable (progx-icast-zerop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Signed to signed, widening.

(defruled progx-expt-2-split
  (implies (and (natp a) (natp b))
           (equal (expt 2 (+ a b)) (* (expt 2 a) (expt 2 b)))))

(defruled progx-expt-2-mono
  (implies (and (integerp a) (integerp b) (<= a b))
           (<= (expt 2 a) (expt 2 b))))

(defruled progx-expt-2-double-half
  (implies (posp n)
           (equal (expt 2 n) (* 2 (expt 2 (+ -1 n)))))
  :use (:instance progx-expt-2-unfold (j n)))

(defruled progx-integerp-expt-2
  (implies (natp n) (integerp (expt 2 n))))

(defruled progx-icast-widen-high
  (implies (and (posp n0) (integerp n1) (<= n0 n1) (natp u)
                (<= (expt 2 (1- n0)) u) (< u (expt 2 n0)))
           (equal (int-wrap (+ u (expt 2 n1) (- (expt 2 n0))) t n1)
                  (- u (expt 2 n0))))
  :do-not-induct t
  :use ((:instance progx-int-wrap-high
                   (v (+ u (expt 2 n1) (- (expt 2 n0))))
                   (n n1))
        (:instance progx-expt-2-mono (a (+ -1 n0)) (b (+ -1 n1)))
        (:instance progx-expt-2-double-half (n n0))
        (:instance progx-expt-2-double-half (n n1))
        (:instance progx-integerp-expt-2 (n n0))
        (:instance progx-integerp-expt-2 (n n1)))
  :in-theory '(natp posp (:t expt)))

(defruled progx-lebits-of-append-repeat-1
  (implies (natp d)
           (equal (lebits=>nat (append bs (repeat d 1)))
                  (+ (lebits=>nat bs)
                     (- (expt 2 (+ (len bs) d)) (expt 2 (len bs))))))
  :use ((:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits bs) (acl2::hidigits (repeat d 1)))
        (:instance progx-lebits-of-repeat-1 (j d))
        (:instance progx-expt-2-split (a (len bs)) (b d)))
  :disable acl2::lebits=>nat-of-append)

(defruled progx-int-valuep-signed-widen
  (implies (and (int-valuep x t n0) (posp n0) (integerp n1) (<= n0 n1))
           (int-valuep x t n1))
  :use (:instance progx-expt-2-mono (a (+ -1 n0)) (b (+ -1 n1)))
  :in-theory '(int-valuep int-min int-max acl2::pos-fix posp natp))

(defruled progx-int-wrap-when-nat-valuep
  (implies (and (natp u) (posp n) (int-valuep u s n))
           (equal (int-wrap u s n) u))
  :use progx-int-wrap-small
  :in-theory '(int-valuep int-min int-max acl2::pos-fix posp natp))

(defruled progx-icast-signed-widen
  (implies (and (bit-listp bs) (consp bs) (posp n1)
                (equal s0 t) (equal s1 t) (<= (len bs) n1))
           (and (progx-icast-predp bs s0 s1 n1)
                (int-valuep (lebits->int bs s0) s1 n1)
                (equal (int-wrap
                        (lebits=>nat (progx-icast-obits bs s0 s1 n1))
                        s1 n1)
                       (lebits->int bs s0))))
  :do-not-induct t
  :use (progx-lebits-bound
        progx-lebits->int-cases
        progx-msb-0-or-1
        progx-msb-0-iff-small
        (:instance int-valuep-of-lebits->int (bits bs) (signedp s0)
                   (n (len bs)))
        (:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits bs)
                   (acl2::hidigits (repeat (- n1 (len bs)) (car (last bs)))))
        (:instance progx-lebits-of-append-repeat-1 (d (- n1 (len bs))))
        (:instance progx-lebits-of-repeat-0 (j (- n1 (len bs))))
        (:instance progx-expt-2-mono (a (1- (len bs))) (b (1- n1)))
        (:instance progx-int-valuep-signed-widen
                   (x (lebits->int bs s0)) (n0 (len bs)))
        (:instance progx-int-wrap-when-nat-valuep
                   (u (lebits=>nat bs)) (s t) (n n1))
        (:instance progx-icast-widen-high (u (lebits=>nat bs)) (n0 (len bs))))
  :enable (progx-icast-predp progx-icast-obits)
  :disable (acl2::lebits=>nat-of-append int-wrap lebits->int int-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Signed to signed, narrowing: k = n1 - 1 low bits are kept, and the
;; n0 - k bits from position k on must all equal m.

(defruled progx-lebits-of-take-append-bit
  (implies (and (natp k) (<= k (len bs)) (bitp m))
           (equal (lebits=>nat (append (take k bs) (list m)))
                  (+ (lebits=>nat (take k bs)) (* (expt 2 k) m))))
  :use ((:instance acl2::lebits=>nat-of-append
                   (acl2::lodigits (take k bs)) (acl2::hidigits (list m)))
        (:instance acl2::lebits=>nat-of-cons
                   (acl2::lodigit m) (acl2::hidigits nil)))
  :enable bitp
  :disable (acl2::lebits=>nat-of-append acl2::lebits=>nat-of-cons))

(defruled progx-lebits-when-high-repeat
  (implies (and (natp k) (<= k (len bs))
                (equal (nthcdr k bs) (repeat (- (len bs) k) m)))
           (equal (lebits=>nat bs)
                  (if (equal m 1)
                      (+ (lebits=>nat (take k bs))
                         (- (expt 2 (len bs)) (expt 2 k)))
                    (if (equal m 0) (lebits=>nat (take k bs))
                      (lebits=>nat bs)))))
  :use ((:instance acl2::append-of-take-and-nthcdr (acl2::n k) (acl2::x bs))
        (:instance progx-lebits-of-append-repeat-1
                   (bs (take k bs)) (d (- (len bs) k)))
        (:instance progx-lebits-split)
        (:instance progx-lebits-of-repeat-0 (j (- (len bs) k))))
  :disable (acl2::append-of-take-and-nthcdr))

(defruled progx-icast-narrow-sound
  (implies (and (bit-listp bs) (natp k) (< (+ 1 k) (len bs))
                (bitp m)
                (equal (nthcdr k bs) (repeat (- (len bs) k) m)))
           (and (int-valuep (- (lebits=>nat bs) (* m (expt 2 (len bs))))
                            t (+ 1 k))
                (equal (int-wrap
                        (lebits=>nat (append (take k bs) (list m)))
                        t (+ 1 k))
                       (- (lebits=>nat bs) (* m (expt 2 (len bs)))))))
  :do-not-induct t
  :use (progx-lebits-when-high-repeat
        progx-lebits-of-take-append-bit
        progx-lebits-take-bound
        (:instance progx-expt-2-succ)
        (:instance progx-int-wrap-small
                   (u (lebits=>nat (take k bs))) (s t) (n (+ 1 k)))
        (:instance progx-int-wrap-high
                   (v (+ (lebits=>nat (take k bs)) (expt 2 k))) (n (+ 1 k))))
  :enable (int-valuep int-min int-max bitp)
  :disable (int-wrap))

(defrule progx-high-max-core
  (implies (and (integerp hi) (integerp p) (rationalp lo) (rationalp k2)
                (< 0 k2) (< lo k2)
                (<= (- (* k2 p) k2) (+ lo (* k2 hi))))
           (<= (- p 1) hi))
  :rule-classes nil
  :hints (("Goal" :cases ((<= hi (- p 2))))
          ("Subgoal 1" :nonlinearp t)))

(defrule progx-squeeze-to-max
  (implies (and (natp l) (integerp hi)
                (< hi (expt 2 l)) (<= (expt 2 l) (+ 1 hi)))
           (equal hi (1- (expt 2 l))))
  :rule-classes nil
  :use (:instance progx-integerp-expt-2 (n l)))

(defruled progx-icast-narrow-complete
  (implies (and (bit-listp bs) (natp k) (< (+ 1 k) (len bs))
                (equal m (car (last bs)))
                (int-valuep (- (lebits=>nat bs) (* m (expt 2 (len bs))))
                            t (+ 1 k)))
           (equal (nthcdr k bs) (repeat (- (len bs) k) m)))
  :do-not-induct t
  :use (progx-msb-0-or-1
        (:instance progx-icast-zerop-iff)
        progx-lebits-split
        progx-lebits-take-bound
        (:instance progx-lebits-bound (bs (nthcdr k bs)))
        (:instance progx-high-max-core
                   (hi (lebits=>nat (nthcdr k bs)))
                   (lo (lebits=>nat (take k bs)))
                   (k2 (expt 2 k))
                   (p (expt 2 (- (len bs) k))))
        (:instance progx-repeat-1-when-lebits-max (bs (nthcdr k bs)))
        (:instance progx-squeeze-to-max
                   (l (- (len bs) k)) (hi (lebits=>nat (nthcdr k bs))))
        (:instance progx-expt-2-split (a k) (b (- (len bs) k))))
  :enable (int-valuep int-min int-max progx-icast-zerop
           acl2::bit-listp-of-nthcdr)
  :disable (progx-icast-zerop-iff))

(defruled progx-icast-signed-narrow
  (implies (and (bit-listp bs) (posp n1) (equal s0 t) (equal s1 t)
                (< n1 (len bs)))
           (and (equal (progx-icast-predp bs s0 s1 n1)
                       (int-valuep (lebits->int bs s0) s1 n1))
                (implies (progx-icast-predp bs s0 s1 n1)
                         (equal (int-wrap
                                 (lebits=>nat (progx-icast-obits bs s0 s1 n1))
                                 s1 n1)
                                (lebits->int bs s0)))))
  :do-not-induct t
  :use (progx-lebits->int-cases
        progx-msb-0-or-1
        (:instance progx-icast-narrow-sound
                   (k (1- n1)) (m (car (last bs))))
        (:instance progx-icast-narrow-complete
                   (k (1- n1)) (m (car (last bs)))))
  :enable (progx-icast-predp progx-icast-obits bitp)
  :disable (int-wrap int-valuep lebits->int))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled progx-icast-value
  :short "For all eight sign/width cases: the case's constraint condition
          holds iff the input integer fits the destination type, and then
          the from_bits_le reading of the output bits is the input integer."
  (implies (and (bit-listp bs) (consp bs) (posp n1)
                (booleanp s0) (booleanp s1))
           (and (equal (progx-icast-predp bs s0 s1 n1)
                       (int-valuep (lebits->int bs s0) s1 n1))
                (implies (progx-icast-predp bs s0 s1 n1)
                         (equal (int-wrap
                                 (lebits=>nat (progx-icast-obits bs s0 s1 n1))
                                 s1 n1)
                                (lebits->int bs s0)))))
  :do-not-induct t
  :use (progx-icast-signed-narrow progx-icast-signed-widen
        progx-icast-signed-unsigned progx-icast-unsigned-source)
  :in-theory '(booleanp (:t progx-icast-predp) (:t int-valuep)))
