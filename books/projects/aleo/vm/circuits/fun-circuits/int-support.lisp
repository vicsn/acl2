; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shared lemmas for the integer circuit specifications.
; Integer values in the funspecs are the two's-complement reading of the
; little-endian bits that snarkVM stores on Integer<E, I>.

(in-package "ALEOVM")

(include-book "../fun-specs/integers")
(include-book "../library-extensions/digits")
(include-book "../library-extensions/lookup-equal-list")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-xor")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled integer-length-of-base-prime
  (equal (integer-length (base-prime)) 253)
  :enable base-prime
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     base-prime))))

(defruled posp-when-integer-widthp
  (implies (integer-widthp n)
           (posp n))
  :rule-classes :forward-chaining
  :enable integer-widthp)

(defruled int-width-lt-prime-bits
  (implies (integer-widthp n)
           (< n (integer-length (base-prime))))
  :enable (integer-widthp integer-length-of-base-prime)
  :hints (("Goal" :cases ((equal n 8)
                          (equal n 16)
                          (equal n 32)
                          (equal n 64)
                          (equal n 128)))))

(defruled int-width-add-fits
  :short "Every integer width, including 128, satisfies the small-add
          hypothesis @($n+1 < \\mathit{integer\\mbox{-}length}(p)$)."
  (implies (integer-widthp n)
           (< (+ 1 n) (integer-length (base-prime))))
  :enable (integer-widthp integer-length-of-base-prime)
  :hints (("Goal" :cases ((equal n 8)
                          (equal n 16)
                          (equal n 32)
                          (equal n 64)
                          (equal n 128)))))

(defruled int-width-double-fits
  :short "Field product of two values below @($2^n$) fits in the base
          field iff the width is not 128."
  (implies (and (integer-widthp n)
                (not (equal n 128)))
           (< (* 2 n) (integer-length (base-prime))))
  :enable (integer-widthp integer-length-of-base-prime)
  :hints (("Goal" :cases ((equal n 8)
                          (equal n 16)
                          (equal n 32)
                          (equal n 64)))))

(defruled int-width-div-fits
  :short "The unsigned-small-div hypothesis @($2n+1 < \\mathit{integer\\mbox{-}length}(p)$)."
  (implies (and (integer-widthp n)
                (not (equal n 128)))
           (< (+ 1 (* 2 n)) (integer-length (base-prime))))
  :enable (integer-widthp integer-length-of-base-prime)
  :hints (("Goal" :cases ((equal n 8)
                          (equal n 16)
                          (equal n 32)
                          (equal n 64)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled len-of-int->lebits
  (implies (natp n)
           (equal (len (int->lebits x n)) n))
  :enable (int->lebits acl2::len-of-nat=>lebits))

(defruled bit-listp-of-int->lebits-explicit
  (bit-listp (int->lebits x n))
  :enable int->lebits)

(defruled lebits=>nat-of-int->lebits
  (implies (natp n)
           (equal (lebits=>nat (int->lebits x n))
                  (mod (ifix x) (expt 2 n))))
  :enable (int->lebits acl2::lebits=>nat-of-nat=>lebits))

(defruled lebits->int-is-lebits=>int
  (implies (bit-listp bits)
           (equal (lebits->int bits t)
                  (lebits=>int bits)))
  :hints (("Goal"
           :in-theory (enable lebits->int lebits=>int)
           :cases ((consp bits)))
          ("Subgoal 1"
           :use ((:instance lebits=>nat-lower-bound-when-msb-is-1
                            (bits bits))
                 (:instance lebits=>nat-upper-bound-when-msb-is-0
                            (bits bits))
                 (:instance bitp-of-car-of-last-when-bit-listp
                            (bits bits))))))

(defruled lebits->int-when-unsigned
  (equal (lebits->int bits nil)
         (lebits=>nat bits))
  :enable lebits->int)

(defruled int->lebits-of-int-wrap
  (implies (posp n)
           (equal (int->lebits (int-wrap x signedp n) n)
                  (int->lebits x n)))
  :enable (int->lebits int-wrap))

(defruled lebits->int-of-int->lebits
  (implies (and (posp n)
                (int-valuep x signedp n))
           (equal (lebits->int (int->lebits x n) signedp)
                  (ifix x)))
  :hints (("Goal"
           :cases ((and signedp (< (ifix x) 0))
                   (and signedp (<= 0 (ifix x)))
                   (not signedp))
           :in-theory (e/d (lebits->int
                            lebits=>nat-of-int->lebits
                            len-of-int->lebits
                            int-valuep
                            int-min
                            int-max)
                           (int->lebits)))))

(defruled int-valuep-of-lebits->int
  (implies (and (bit-listp bits)
                (equal (len bits) n)
                (posp n))
           (int-valuep (lebits->int bits signedp) signedp n))
  :enable (lebits->int int-valuep int-min int-max)
  :use (:instance acl2::lebits=>nat-upper-bound (digits bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun int-bitlist-ind (xs ys)
   (if (or (atom xs) (atom ys))
       nil
     (int-bitlist-ind (cdr xs) (cdr ys)))))

(defruled bitand-is-b-and
  (implies (and (bitp x) (bitp y))
           (equal (bitand x y) (b-and x y)))
  :enable (bitand b-and))

(defruled bitor-is-b-ior
  (implies (and (bitp x) (bitp y))
           (equal (bitor x y) (b-ior x y)))
  :enable (bitor b-ior))

(defruled bitxor-is-b-xor
  (implies (and (bitp x) (bitp y))
           (equal (bitxor x y) (b-xor x y)))
  :enable (bitxor b-xor))

(defruled lebits=>nat-of-bitand-list
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (equal (len ys) (len xs)))
           (equal (lebits=>nat (bitand-list xs ys))
                  (logand (lebits=>nat xs) (lebits=>nat ys))))
  :hints (("Goal"
           :induct (int-bitlist-ind xs ys)
           :in-theory (e/d (bitand-list
                            bitand-is-b-and
                            acl2::lebits=>nat-of-cons
                            logand*
                            logcar-i+2*j
                            logcdr-i+2*j
                            logcons)
                           (logand)))))

(defruled lebits=>nat-of-bitor-list
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (equal (len ys) (len xs)))
           (equal (lebits=>nat (bitor-list xs ys))
                  (logior (lebits=>nat xs) (lebits=>nat ys))))
  :hints (("Goal"
           :induct (int-bitlist-ind xs ys)
           :in-theory (e/d (bitor-list
                            bitor-is-b-ior
                            acl2::lebits=>nat-of-cons
                            logior*
                            logcar-i+2*j
                            logcdr-i+2*j
                            logcons)
                           (logior)))))

(defruled lebits=>nat-of-bitxor-list
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (equal (len ys) (len xs)))
           (equal (lebits=>nat (bitxor-list xs ys))
                  (logxor (lebits=>nat xs) (lebits=>nat ys))))
  :hints (("Goal"
           :induct (int-bitlist-ind xs ys)
           :in-theory (e/d (bitxor-list
                            bitxor-is-b-xor
                            acl2::lebits=>nat-of-cons
                            logxor*
                            logcar-i+2*j
                            logcdr-i+2*j
                            logcons)
                           (logxor)))))

(defruled bitand-list-of-int->lebits
  (implies (and (natp n)
                (equal (len (int->lebits x n)) n)
                (equal (len (int->lebits y n)) n))
           (equal (bitand-list (int->lebits x n)
                               (int->lebits y n))
                  (int->lebits (logand (ifix x) (ifix y)) n)))
  :hints (("Goal"
           :in-theory (e/d (lebits=>nat-of-bitand-list
                            lebits=>nat-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits)
                           (int->lebits
                            bitand-list))
           :use ((:instance acl2::lebits=>nat-injectivity
                            (digits1 (bitand-list (int->lebits x n)
                                                  (int->lebits y n)))
                            (digits2 (int->lebits (logand (ifix x) (ifix y))
                                                  n)))
                 (:instance mod-of-logand-and-expt
                            (i (ifix x))
                            (j (ifix y))
                            (n n))))))

(defruled bitor-list-of-int->lebits
  (implies (natp n)
           (equal (bitor-list (int->lebits x n)
                              (int->lebits y n))
                  (int->lebits (logior (ifix x) (ifix y)) n)))
  :hints (("Goal"
           :in-theory (e/d (lebits=>nat-of-bitor-list
                            lebits=>nat-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits)
                           (int->lebits
                            bitor-list))
           :use ((:instance acl2::lebits=>nat-injectivity
                            (digits1 (bitor-list (int->lebits x n)
                                                 (int->lebits y n)))
                            (digits2 (int->lebits (logior (ifix x) (ifix y))
                                                  n)))
                 (:instance mod-of-logior-expt
                            (i (ifix x))
                            (j (ifix y))
                            (n n))))))

(defruled bitxor-list-of-int->lebits
  (implies (natp n)
           (equal (bitxor-list (int->lebits x n)
                               (int->lebits y n))
                  (int->lebits (logxor (ifix x) (ifix y)) n)))
  :hints (("Goal"
           :in-theory (e/d (lebits=>nat-of-bitxor-list
                            lebits=>nat-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits)
                           (int->lebits
                            bitxor-list))
           :use ((:instance acl2::lebits=>nat-injectivity
                            (digits1 (bitxor-list (int->lebits x n)
                                                  (int->lebits y n)))
                            (digits2 (int->lebits (logxor (ifix x) (ifix y))
                                                  n)))
                 (:instance mod-of-logxor-and-expt
                            (i (ifix x))
                            (j (ifix y))
                            (n n))))))

(defruled int->lebits-of-int-bitand-spec
  (implies (and (natp n)
                (posp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int->lebits (int-bitand-spec x y signedp n) n)
                  (bitand-list (int->lebits x n)
                               (int->lebits y n))))
  :enable (int-bitand-spec
           int->lebits-of-int-wrap
           bitand-list-of-int->lebits
           len-of-int->lebits))

(defruled int->lebits-of-int-bitor-spec
  (implies (and (posp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int->lebits (int-bitor-spec x y signedp n) n)
                  (bitor-list (int->lebits x n)
                              (int->lebits y n))))
  :enable (int-bitor-spec
           int->lebits-of-int-wrap
           bitor-list-of-int->lebits))

(defruled int->lebits-of-int-bitxor-spec
  (implies (and (posp n)
                (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int->lebits (int-bitxor-spec x y signedp n) n)
                  (bitxor-list (int->lebits x n)
                               (int->lebits y n))))
  :enable (int-bitxor-spec
           int->lebits-of-int-wrap
           bitxor-list-of-int->lebits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Comparisons of the funspecs.  Boolean negation is @($1-b$), not a constraint.

(defruled int-is-greater-than-spec-is-swapped-lt
  (equal (int-is-greater-than-spec x y signedp n)
         (int-is-less-than-spec y x signedp n))
  :enable (int-is-greater-than-spec
           int-is-less-than-spec
           int-spec-bool))

(defruled int-is-greater-than-or-equal-spec-is-not-lt
  (implies (and (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int-is-greater-than-or-equal-spec x y signedp n)
                  (if (equal (int-is-less-than-spec x y signedp n) 1)
                      0
                    1)))
  :enable (int-is-greater-than-or-equal-spec
           int-is-less-than-spec
           int-spec-bool))

(defruled int-is-less-than-or-equal-spec-is-not-swapped-lt
  (implies (and (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int-is-less-than-or-equal-spec x y signedp n)
                  (int-is-greater-than-or-equal-spec y x signedp n)))
  :enable (int-is-less-than-or-equal-spec
           int-is-greater-than-or-equal-spec
           int-spec-bool))

(defruled int-is-not-equal-spec-is-not-equal
  (implies (and (int-valuep x signedp n)
                (int-valuep y signedp n))
           (equal (int-is-not-equal-spec x y signedp n)
                  (if (equal (int-is-equal-spec x y signedp n) 1)
                      0
                    1)))
  :enable (int-is-not-equal-spec
           int-is-equal-spec
           int-spec-bool))

(defruled int-is-zero-spec-is-equal-zero
  (implies (int-valuep x signedp n)
           (equal (int-is-zero-spec x signedp n)
                  (int-is-equal-spec x 0 signedp n)))
  :enable (int-is-zero-spec
           int-is-equal-spec
           int-spec-bool))

(defruled int-is-one-spec-is-equal-one
  (implies (int-valuep x signedp n)
           (equal (int-is-one-spec x signedp n)
                  (int-is-equal-spec x 1 signedp n)))
  :enable (int-is-one-spec
           int-is-equal-spec
           int-spec-bool))

(defruled int-modulo-spec-agrees
  (equal (int-modulo-spec x y signedp n)
         (if signedp
             (spec-error)
           (int-rem-wrapped-spec x y signedp n)))
  :enable int-modulo-spec)
