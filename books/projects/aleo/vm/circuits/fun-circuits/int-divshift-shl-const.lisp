; Aleo Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

(in-package "ALEOVM")

; shl_wrapped with a constant exponent: snarkVM emits no constraint and the
; result bits are the value bits shifted up by (e mod n) with zero fill,
; truncated to n bits.

(include-book "int-shift-pfcs")
(local (include-book "int-support"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))

(defund int-divshift-shl-const-bits (bits k)
  (append (repeat (nfix k) 0) bits))

(local
 (defrule int-divshift-lebits=>nat-of-repeat-0
   (equal (acl2::lebits=>nat (repeat k 0)) 0)
   :induct (repeat k 0)
   :enable (repeat acl2::lebits=>nat acl2::lendian=>nat)))

(local
 (defrule int-divshift-bit-listp-of-repeat-0
   (bit-listp (repeat k 0))
   :induct (repeat k 0)
   :enable repeat))

(local
 (defrule int-divshift-shl-const-bits-facts
   (implies (integer-widthp n)
            (and (bit-listp (int-divshift-shl-const-bits (int->lebits x n) k))
                 (equal (len (int-divshift-shl-const-bits (int->lebits x n) k))
                        (+ (nfix k) n))))
   :enable (int-divshift-shl-const-bits int->lebits)))

(local
 (defruled int-divshift-shl-const-nat
   (implies (and (integer-widthp n)
                 (natp k))
            (equal (acl2::lebits=>nat
                    (int-divshift-shl-const-bits (int->lebits x n) k))
                   (* (expt 2 k) (int-spec-unsigned x n))))
   :do-not-induct t
   :use ((:instance acl2::lebits=>nat-of-append
                    (lodigits (repeat k 0))
                    (hidigits (int->lebits x n))))
   :hints (("Goal" :in-theory (enable int-divshift-shl-const-bits int->lebits
                                      int-spec-unsigned integer-widthp posp-when-integer-widthp)))))

(local
 (defruled int-divshift-int-wrap-of-mod
   (implies (and (integer-widthp n) (integerp v))
            (equal (int-wrap (mod v (expt 2 n)) signedp n)
                   (int-wrap v signedp n)))
   :hints (("Goal" :in-theory (enable int-wrap integer-widthp posp-when-integer-widthp)))))

(defruled int-divshift-shl-wrapped-const-sound
  :short "Constant exponent: the rewired low @('n') bits are @('shl_wrapped')."
  (implies (and (integer-widthp n)
                (booleanp signedp)
                (int-valuep x signedp n)
                (natp e))
           (equal (lebits->int
                   (take n (int-divshift-shl-const-bits (int->lebits x n)
                                                         (mod e n)))
                   signedp)
                  (int-shl-wrapped-spec x e signedp n)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance lebits->int-is-int-wrap
                            (bits (take n (int-divshift-shl-const-bits
                                           (int->lebits x n) (mod e n)))))
                 (:instance int-lebits-take-is-mod
                            (bits (int-divshift-shl-const-bits
                                   (int->lebits x n) (mod e n))))
                 (:instance int-divshift-shl-const-nat (k (mod e n)))
                 (:instance int-divshift-int-wrap-of-mod
                            (v (* (expt 2 (mod e n)) (int-spec-unsigned x n))))
                 (:instance int-shl-wrapped-is-wrap-of-pattern))
           :in-theory (e/d (posp-when-integer-widthp)
                           (lebits->int int-divshift-shl-const-bits take
                            integer-widthp)))))
