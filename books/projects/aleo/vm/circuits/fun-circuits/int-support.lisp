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

(local (include-book "../library-extensions/bit-lists"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

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

(defruled int-width-is-power-of-two
  :short "Every integer width is a power of two, and
          @($2^{\\mathit{integer\\mbox{-}length}(n)-1} = n$)."
  (implies (integer-widthp n)
           (equal (expt 2 (1- (integer-length n))) n))
  :enable integer-widthp
  :hints (("Goal" :cases ((equal n 8)
                          (equal n 16)
                          (equal n 32)
                          (equal n 64)
                          (equal n 128)))))

; Carry of the unsigned reading of a signed sum:
; N(x) + N(y) = N(x+y) + carry * 2^n, with carry a bit.
; The same identity is the low/high split of a subtraction offset by 2^n:
; N(x) - N(y) + 2^n = N(x-y) + carry * 2^n.

(defruledl mod-sum-and-carry
  (implies (and (natp a)
                (natp b)
                (posp m)
                (< a m)
                (< b m))
           (equal (+ a b)
                  (+ (mod (+ a b) m)
                     (* (if (< (+ a b) m) 0 1) m))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((< (+ a b) m))
           :use ((:instance acl2::mod-sum-cases (k a) (x b) (y m)))
           :in-theory (disable acl2::mod))))

(defruledl mod-diff-and-carry
  (implies (and (natp a)
                (natp b)
                (posp m)
                (< a m)
                (< b m))
           (equal (+ a (- b) m)
                  (+ (mod (- a b) m)
                     (* (if (<= b a) 1 0) m))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((<= b a))
           :in-theory (enable acl2::mod-when-<-of-0 acl2::mod-when-<))))

(define int-add-carry ((x integerp) (y integerp) (n posp))
  :returns (c bitp :rule-classes :type-prescription)
  :short "The bit @('carry') in @($N(x)+N(y) = N(x+y) + \\mathit{carry}\\,2^n$)."
  (if (posp n)
      (if (< (+ (mod (ifix x) (expt 2 n))
                (mod (ifix y) (expt 2 n)))
             (expt 2 n))
          0
        1)
    0)
  ///
  (defruled int-add-carry-equation
    (implies (posp n)
             (equal (+ (mod (ifix x) (expt 2 n))
                       (mod (ifix y) (expt 2 n)))
                    (+ (mod (+ (ifix x) (ifix y)) (expt 2 n))
                       (* (int-add-carry x y n) (expt 2 n)))))
    :enable int-add-carry
    :use (:instance mod-sum-and-carry
                    (a (mod (ifix x) (expt 2 n)))
                    (b (mod (ifix y) (expt 2 n)))
                    (m (expt 2 n)))))

(define int-sub-carry ((x integerp) (y integerp) (n posp))
  :returns (c bitp :rule-classes :type-prescription)
  :short "The bit @('carry') in
          @($N(x)-N(y)+2^n = N(x-y) + \\mathit{carry}\\,2^n$)."
  (if (posp n)
      (if (<= (mod (ifix y) (expt 2 n))
              (mod (ifix x) (expt 2 n)))
          1
        0)
    0)
  ///
  (defruled int-sub-carry-equation
    (implies (posp n)
             (equal (+ (mod (ifix x) (expt 2 n))
                       (- (mod (ifix y) (expt 2 n)))
                       (expt 2 n))
                    (+ (mod (- (ifix x) (ifix y)) (expt 2 n))
                       (* (int-sub-carry x y n) (expt 2 n)))))
    :enable int-sub-carry
    :use ((:instance mod-diff-and-carry
                     (a (mod (ifix x) (expt 2 n)))
                     (b (mod (ifix y) (expt 2 n)))
                     (m (expt 2 n))))))

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

(defruledl car-of-last-is-bit
  (implies (and (bit-listp bits) (consp bits))
           (or (equal (car (last bits)) 0)
               (equal (car (last bits)) 1)))
  :hints (("Goal"
           :use (:instance bitp-of-car-of-last-when-bit-listp (bits bits))
           :in-theory (e/d (bitp)
                           (acl2::bitp-when-member-equal-of-bit-listp
                            acl2::bitp-of-car-when-bit-listp)))))

(defruled lebits->int-is-lebits=>int
  (implies (bit-listp bits)
           (equal (lebits->int bits t)
                  (lebits=>int bits)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance car-of-last-is-bit (bits bits))
                 (:instance lebits=>nat-lower-bound-when-msb-is-1
                            (bits bits))
                 (:instance lebits=>nat-upper-bound-when-msb-is-0
                            (bits bits)))
           :in-theory (e/d (lebits->int lebits=>int bfix)
                           (acl2::bitp-when-member-equal-of-bit-listp
                            acl2::bitp-of-car-when-bit-listp)))))

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

; Sign bit of a signed integer, and the consequences used by checked
; addition, checked subtraction, and signed comparison.
; The most significant bit is 1 exactly when the value is negative.

(defruledl int-signed-mod-2n
  (implies (and (posp n)
                (integerp x)
                (<= (- (expt 2 (1- n))) x)
                (< x (expt 2 (1- n))))
           (equal (mod x (expt 2 n))
                  (if (< x 0)
                      (+ x (expt 2 n))
                    x)))
  :hints (("Goal"
           :cases ((< x 0))
           :in-theory (enable acl2::mod-when-<-of-0 acl2::mod-when-<))))

(defruledl consp-of-int->lebits
  (implies (posp n)
           (consp (int->lebits x n)))
  :hints (("Goal" :in-theory (enable int->lebits acl2::nat=>lebits))))

(defruled int-signed-msb
  (implies (and (posp n)
                (int-valuep x t n))
           (equal (car (last (int->lebits x n)))
                  (if (< x 0) 1 0)))
  :do-not-induct t
  :hints (("Goal"
           :cases ((< x 0))
           :use ((:instance car-of-last-is-bit
                            (bits (int->lebits x n)))
                 (:instance lebits=>nat-lower-bound-when-msb-is-1
                            (bits (int->lebits x n)))
                 (:instance lebits=>nat-upper-bound-when-msb-is-0
                            (bits (int->lebits x n))))
           :in-theory (e/d (int-valuep int-min int-max
                            lebits=>nat-of-int->lebits
                            len-of-int->lebits
                            bit-listp-of-int->lebits-explicit
                            int-signed-mod-2n
                            consp-of-int->lebits)
                           (acl2::bitp-when-member-equal-of-bit-listp
                            acl2::bitp-of-car-when-bit-listp)))))

(defruled int-signed-lt-iff
  :short "Signed order is unsigned order of the bit patterns when the
          sign bits agree, and is the negative-versus-nonnegative test
          when they differ."
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n))
           (equal (< x y)
                  (if (equal (car (last (int->lebits x n)))
                             (car (last (int->lebits y n))))
                      (< (lebits=>nat (int->lebits x n))
                         (lebits=>nat (int->lebits y n)))
                    (and (equal (car (last (int->lebits x n))) 1)
                         (equal (car (last (int->lebits y n))) 0)))))
  :enable (int-signed-msb
           int-signed-mod-2n
           lebits=>nat-of-int->lebits
           int-valuep int-min int-max))

(defruled int-add-signed-overflow-bit-is-zero
  :short "The checked-add overflow bit is 0 whenever @('x+y') is in range.
          That bit is 1 exactly when @('x') and @('y') have the same sign
          and the sum has the other sign."
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (int-valuep (+ x y) t n))
           (equal (if (and (equal (car (last (int->lebits x n)))
                                  (car (last (int->lebits y n))))
                           (not (equal (car (last (int->lebits (+ x y) n)))
                                       (car (last (int->lebits x n))))))
                      1
                    0)
                  0))
  :enable int-signed-msb
  :hints (("Goal" :cases ((< x 0) (< y 0)))))

(defruled int-add-signed-overflow-bitxor-is-zero
  :short "The same overflow fact, written with @('bitxor') so it matches
          @('boolean-and-notleft-gadget-to-booland-boolnot')."
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (int-valuep (+ x y) t n))
           (equal (if (and (equal (bitxor (car (last (int->lebits x n)))
                                          (car (last (int->lebits y n))))
                                  0)
                           (equal (bitxor (car (last (int->lebits (+ x y) n)))
                                          (car (last (int->lebits x n))))
                                  1))
                      1
                    0)
                  0))
  :enable (bitxor int-signed-msb)
  :hints (("Goal" :cases ((< x 0) (< y 0)))))

(defruled int-sub-signed-overflow-bit-is-zero
  :short "The checked-sub overflow bit is 0 whenever @('x-y') is in range.
          That bit is 1 exactly when @('x') and @('y') have different signs
          and the difference has @('y')'s sign."
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (int-valuep (- x y) t n))
           (equal (if (and (not (equal (car (last (int->lebits x n)))
                                       (car (last (int->lebits y n)))))
                           (equal (car (last (int->lebits (- x y) n)))
                                  (car (last (int->lebits y n)))))
                      1
                    0)
                  0))
  :enable int-signed-msb
  :hints (("Goal" :cases ((< x 0) (< y 0)))))

(defruled int-sub-signed-overflow-bitxor-is-zero
  :short "The same overflow fact, written with @('bitxor') so it matches
          @('boolean-and-notright-gadget-to-booland-boolnot')."
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (int-valuep (- x y) t n))
           (equal (if (and (equal (bitxor (car (last (int->lebits x n)))
                                          (car (last (int->lebits y n))))
                                  1)
                           (equal (bitxor (car (last (int->lebits (- x y) n)))
                                          (car (last (int->lebits y n))))
                                  0))
                      1
                    0)
                  0))
  :enable (bitxor int-signed-msb)
  :hints (("Goal" :cases ((< x 0) (< y 0)))))

(defruled not-spec-error-when-integerp
  (implies (integerp x)
           (not (equal x (spec-error))))
  :enable (spec-error reserr reserrp))

(defruled int-add-checked-spec-when-not-error
  (implies (and (int-valuep x signedp n)
                (int-valuep y signedp n)
                (not (equal (int-add-checked-spec x y signedp n)
                            (spec-error))))
           (and (equal (int-add-checked-spec x y signedp n)
                       (+ (ifix x) (ifix y)))
                (int-valuep (+ (ifix x) (ifix y)) signedp n)))
  :enable (int-add-checked-spec
           not-spec-error-when-integerp
           int-valuep))

(defruled int-sub-checked-spec-when-not-error
  (implies (and (int-valuep x signedp n)
                (int-valuep y signedp n)
                (not (equal (int-sub-checked-spec x y signedp n)
                            (spec-error))))
           (and (equal (int-sub-checked-spec x y signedp n)
                       (- (ifix x) (ifix y)))
                (int-valuep (- (ifix x) (ifix y)) signedp n)))
  :enable (int-sub-checked-spec
           not-spec-error-when-integerp
           int-valuep))

(defruled int-add-carry-on-lebits
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n))
           (equal (+ (lebits=>nat (int->lebits x n))
                     (lebits=>nat (int->lebits y n)))
                  (+ (lebits=>nat (int->lebits (+ (ifix x) (ifix y)) n))
                     (* (int-add-carry x y n) (expt 2 n)))))
  :enable (lebits=>nat-of-int->lebits
           int-valuep)
  :hints (("Goal" :use (:instance int-add-carry-equation))))

(defruled int-sub-carry-on-lebits
  (implies (and (posp n)
                (int-valuep x t n)
                (int-valuep y t n))
           (equal (+ (lebits=>nat (int->lebits x n))
                     (- (lebits=>nat (int->lebits y n)))
                     (expt 2 n))
                  (+ (lebits=>nat (int->lebits (- (ifix x) (ifix y)) n))
                     (* (int-sub-carry x y n) (expt 2 n)))))
  :enable (lebits=>nat-of-int->lebits
           int-valuep)
  :hints (("Goal" :use (:instance int-sub-carry-equation))))

(defruled int-unsigned-lt-offset
  :short "Low @('n') bits and high bit of @($2^n + x - y$), for unsigned @('x') and @('y')."
  (implies (and (natp x)
                (natp y)
                (posp n)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (equal (+ (lebits=>nat (int->lebits (+ (expt 2 n) x (- y)) n))
                     (* (if (< x y) 0 1) (expt 2 n)))
                  (+ (expt 2 n) x (- y))))
  :enable lebits=>nat-of-int->lebits
  :hints (("Goal" :cases ((< x y))))
  :use (:instance mod-diff-and-carry
                  (a x)
                  (b y)
                  (m (expt 2 n))))

(local
 (defun int-last-ind (xs)
   (if (or (atom xs) (atom (cdr xs)))
       xs
     (int-last-ind (cdr xs)))))

(defruled member-equal-of-car-of-last
  (implies (and (consp xs) (true-listp xs))
           (member-equal (car (last xs)) xs))
  :hints (("Goal"
           :induct (int-last-ind xs)
           :in-theory (enable last))))

(defruled symbolp-of-car-of-last
  (implies (and (symbol-listp xs) (consp xs))
           (symbolp (car (last xs))))
  :hints (("Goal"
           :induct (int-last-ind xs)
           :in-theory (enable symbol-listp last))))

(defruled true-listp-when-symbol-listp
  (implies (symbol-listp xs)
           (true-listp xs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-listp))))

(defruled consp-of-last-when-consp-true-listp
  (implies (and (consp xs) (true-listp xs))
           (consp (last xs)))
  :hints (("Goal" :in-theory (enable last))))

(defruled symbol-listp-of-append-of-symbol
  (implies (and (symbol-listp xs) (symbolp s))
           (symbol-listp (append xs (list s))))
  :hints (("Goal" :in-theory (enable symbol-listp append))))

(defruled bit-listp-of-append-of-bit
  (implies (and (bit-listp xs) (bitp b))
           (bit-listp (append xs (list b))))
  :hints (("Goal" :in-theory (enable bit-listp append))))

(defruled len-of-append-of-singleton
  (equal (len (append xs (list a)))
         (+ (len xs) 1))
  :hints (("Goal" :in-theory (enable append))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun int-bitlist-ind (xs ys)
   (if (or (atom xs) (atom ys))
       nil
     (int-bitlist-ind (cdr xs) (cdr ys)))))

(defruledl logcar-of-bit
  (implies (bitp x)
           (equal (acl2::logcar x) x))
  :hints (("Goal" :cases ((equal x 0) (equal x 1)) :in-theory (enable bitp))))

(defruledl logcdr-of-bit
  (implies (bitp x)
           (equal (acl2::logcdr x) 0))
  :hints (("Goal" :cases ((equal x 0) (equal x 1)) :in-theory (enable bitp))))

(defruledl lebits=>nat-when-len-zero
  (implies (and (bit-listp xs)
                (equal (len xs) 0))
           (equal (lebits=>nat xs) 0))
  :hints (("Goal" :in-theory (enable bit-listp len acl2::lebits=>nat))))

(defruled bitand-is-b-and
  (implies (and (bitp x) (bitp y))
           (equal (bitand x y) (acl2::b-and x y)))
  :enable (bitand acl2::b-and))

(defruled bitor-is-b-ior
  (implies (and (bitp x) (bitp y))
           (equal (bitor x y) (acl2::b-ior x y)))
  :enable (bitor acl2::b-ior))

(defruled bitxor-is-b-xor
  (implies (and (bitp x) (bitp y))
           (equal (bitxor x y) (acl2::b-xor x y)))
  :enable (bitxor acl2::b-xor))

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
                            lebits=>nat-when-len-zero
                            acl2::lebits=>nat-of-cons
                            acl2::logand*
                            acl2::logcar-i+2*j
                            acl2::logcdr-i+2*j
                            acl2::logcons)
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
                            lebits=>nat-when-len-zero
                            logcar-of-bit
                            logcdr-of-bit
                            acl2::lebits=>nat-of-cons
                            acl2::logcar-i+2*j
                            acl2::logcdr-i+2*j
                            acl2::logcons
                            acl2::b-ior
                            bitp)
                           (logior acl2::logcar acl2::logcdr floor)))
          ("Subgoal *1/2"
           :do-not-induct t
           :use ((:instance acl2::logior*
                            (i (lebits=>nat xs))
                            (j (lebits=>nat ys)))
                 (:instance acl2::lebits=>nat-of-cons
                            (lodigit (car xs))
                            (hidigits (cdr xs)))
                 (:instance acl2::lebits=>nat-of-cons
                            (lodigit (car ys))
                            (hidigits (cdr ys)))))))

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
                            lebits=>nat-when-len-zero
                            logcar-of-bit
                            logcdr-of-bit
                            acl2::lebits=>nat-of-cons
                            acl2::logcar-i+2*j
                            acl2::logcdr-i+2*j
                            acl2::logcons
                            acl2::b-xor
                            bitp)
                           (logxor acl2::logcar acl2::logcdr floor)))
          ("Subgoal *1/2"
           :do-not-induct t
           :use ((:instance acl2::logxor*
                            (i (lebits=>nat xs))
                            (j (lebits=>nat ys)))
                 (:instance acl2::lebits=>nat-of-cons
                            (lodigit (car xs))
                            (hidigits (cdr xs)))
                 (:instance acl2::lebits=>nat-of-cons
                            (lodigit (car ys))
                            (hidigits (cdr ys)))))))

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
                 (:instance acl2::mod-of-logand-and-expt
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
                 (:instance acl2::mod-of-logior-expt
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
                 (:instance acl2::mod-of-logxor-and-expt
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
