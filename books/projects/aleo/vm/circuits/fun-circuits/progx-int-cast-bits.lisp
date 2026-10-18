; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bit-list facts for the Integer-to-Integer arms of Integer::cast (snarkVM
; circuit/program/src/data/literal/cast/integer.rs), over symbolic widths.
; bs is the n0 input bits, u their unsigned value, m = (car (last bs)) the
; most significant bit, and x = (lebits->int bs s0) the input integer.
; For each sign/width case, progx-icast-obits gives the bits that
; Integer::from_bits_le receives, progx-icast-predp the condition the
; case's constraints impose on bs, and the theorems show that the condition
; holds exactly when x is in range of the destination, and that the
; from_bits_le reading of the bits is then x.

(in-package "ALEOVM")

(include-book "int-bits")
(include-book "../library-extensions/digits")
(include-book "../library-extensions/bit-lists")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General lemmas.

(defruled progx-lebits-split
  (implies (and (natp k) (<= k (len bs)))
           (equal (lebits=>nat bs)
                  (+ (lebits=>nat (take k bs))
                     (* (expt 2 k) (lebits=>nat (nthcdr k bs))))))
  :use (:instance acl2::lebits=>nat-of-append
                  (acl2::lodigits (take k bs))
                  (acl2::hidigits (nthcdr k bs)))
  :in-theory (e/d (acl2::append-of-take-and-nthcdr) (acl2::lebits=>nat-of-append)))

(defruled progx-lebits-take-bound
  (implies (natp k)
           (< (lebits=>nat (take k bs)) (expt 2 k)))
  :use (:instance acl2::lebits=>nat-upper-bound (acl2::digits (take k bs))))

(defruled progx-lebits-bound
  (< (lebits=>nat bs) (expt 2 (len bs)))
  :use (:instance acl2::lebits=>nat-upper-bound (acl2::digits bs)))

(defruled progx-expt-2-unfold
  (implies (posp j)
           (equal (expt 2 (+ -1 j)) (* 1/2 (expt 2 j))))
  :enable expt)

(defruled progx-expt-2-succ
  (implies (natp k)
           (equal (expt 2 (+ 1 k)) (* 2 (expt 2 k))))
  :hints (("Goal" :expand ((expt 2 (+ 1 k))))))

(defruled progx-expt-2-step
  (implies (and (posp j) (equal (expt 2 (+ -1 j)) (+ 1 r)))
           (equal (+ 2 (* 2 r)) (expt 2 j)))
  :hints (("Goal" :expand ((expt 2 j))
           :in-theory '(zip zp fix posp commutativity-of-+ distributivity
                        (:e binary-*) (:e binary-+)))))

(defruled progx-lebits-of-repeat-1
  (equal (lebits=>nat (repeat j 1)) (1- (expt 2 (nfix j))))
  :induct (repeat j 1)
  :enable (repeat acl2::lebits=>nat-of-cons)
  :hints (("Subgoal *1/2''"
           :use (:instance progx-expt-2-step
                           (r (lebits=>nat (repeat (+ -1 j) 1)))))))

(defruled progx-lebits-of-repeat-0
  (equal (lebits=>nat (repeat j 0)) 0)
  :use (:instance lebits=>nat-of-repeat-0 (n j)))

(defruled progx-lebits-of-consp
  (implies (consp bs)
           (equal (lebits=>nat bs)
                  (+ (bfix (car bs)) (* 2 (lebits=>nat (cdr bs))))))
  :use (:instance acl2::lebits=>nat-of-cons
                  (acl2::lodigit (car bs)) (acl2::hidigits (cdr bs)))
  :enable acl2::bfix)

(defruled progx-bit-listp-of-repeat-1
  (bit-listp (repeat j 1))
  :induct (repeat j 1)
  :enable repeat)

(defrule progx-repeat-1-when-lebits-max
  (implies (and (bit-listp bs)
                (equal (lebits=>nat bs) (1- (expt 2 (len bs)))))
           (equal bs (repeat (len bs) 1)))
  :rule-classes nil
  :use ((:instance acl2::nat=>lebits-of-lebits=>nat (acl2::digits bs))
        (:instance acl2::nat=>lebits-of-lebits=>nat
                   (acl2::digits (repeat (len bs) 1)))
        (:instance progx-lebits-of-repeat-1 (j (len bs)))
        (:instance progx-bit-listp-of-repeat-1 (j (len bs))))
  :in-theory '(acl2::len-of-repeat nfix natp (:t len)
               acl2::bit-list-fix-when-bit-listp))

(defruled progx-msb-0-or-1
  (implies (and (bit-listp bs) (consp bs))
           (or (equal (car (last bs)) 0) (equal (car (last bs)) 1)))
  :rule-classes ((:forward-chaining :trigger-terms ((car (last bs)))))
  :use (:instance bitp-of-car-of-last-when-bit-listp (bits bs))
  :enable bitp)

(defruled progx-msb-0-iff-small
  (implies (and (bit-listp bs) (consp bs))
           (equal (equal (car (last bs)) 0)
                  (< (lebits=>nat bs) (expt 2 (1- (len bs))))))
  :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits bs))
        (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits bs))
        progx-msb-0-or-1)
  :do-not-induct t
  :enable (bitp bit-listp))

(defruled progx-lebits->int-cases
  (implies (and (bit-listp bs) (consp bs))
           (equal (lebits->int bs s0)
                  (if (and s0 (equal (car (last bs)) 1))
                      (- (lebits=>nat bs) (expt 2 (len bs)))
                    (lebits=>nat bs))))
  :use (progx-msb-0-iff-small progx-msb-0-or-1)
  :enable (lebits->int bitp))

(defrule progx-expt-2-half-lt
  (implies (posp n)
           (< (expt 2 (+ -1 n)) (expt 2 n)))
  :rule-classes :linear
  :hints (("Goal" :expand ((expt 2 n)))))

(defruled progx-int-wrap-small
  (implies (and (natp u) (posp n)
                (if s (< u (expt 2 (1- n))) (< u (expt 2 n))))
           (equal (int-wrap u s n) u))
  :enable int-wrap)

(defruled progx-int-wrap-high
  (implies (and (natp v) (posp n)
                (<= (expt 2 (1- n)) v) (< v (expt 2 n)))
           (equal (int-wrap v t n) (- v (expt 2 n))))
  :enable int-wrap)
