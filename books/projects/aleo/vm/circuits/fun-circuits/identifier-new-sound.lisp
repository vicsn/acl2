; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND for IdentifierLiteral::new.
;
; id-byte-gadget-to-equations reads one validate_byte as field equations.
; The lemmas below turn those equations into the integer checks of
; validate-byte, one product at a time, then lift the result across the
; byte list and the trailing-null constraints.

(in-package "ALEOVM")

(include-book "identifier-new-r1cs")

(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable lookup-equal-of-nth
                           (:e base-prime)
                           pfield::mul-commutative
                           (:definition pfield::sub)
                           (:definition pfield::add)
                           (:definition pfield::mul)
                           (:definition pfield::neg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule id-bit-upper
  (implies (bitp x)
           (<= x 1))
  :hints (("Goal" :in-theory (enable bitp))))

(defrule id-bitp-of-one-minus
  (implies (bitp b)
           (bitp (- 1 b)))
  :hints (("Goal" :cases ((equal b 0)) :in-theory (enable bitp))))

(defrule id-bitp-of-if-01
  (bitp (if a 1 0))
  :hints (("Goal" :in-theory (enable bitp))))

(defrule id-bitp-of-bitand
  (implies (and (bitp x) (bitp y))
           (bitp (bitand x y)))
  :hints (("Goal"
           :cases ((and (equal x 0) (equal y 0))
                   (and (equal x 0) (equal y 1))
                   (and (equal x 1) (equal y 0))
                   (and (equal x 1) (equal y 1)))
           :in-theory (enable bitp bitand))))

(defrule id-bitp-of-bitor
  (implies (and (bitp x) (bitp y))
           (bitp (bitor x y)))
  :hints (("Goal"
           :cases ((and (equal x 0) (equal y 0))
                   (and (equal x 0) (equal y 1))
                   (and (equal x 1) (equal y 0))
                   (and (equal x 1) (equal y 1)))
           :in-theory (enable bitp bitor))))

(defrule id-bitp-of-bitxor
  (implies (and (bitp x) (bitp y))
           (bitp (bitxor x y)))
  :hints (("Goal"
           :cases ((and (equal x 0) (equal y 0))
                   (and (equal x 0) (equal y 1))
                   (and (equal x 1) (equal y 0))
                   (and (equal x 1) (equal y 1)))
           :in-theory (enable bitp bitxor))))

(defrule id-five-lt-base-prime
  (implies (equal p (base-prime))
           (< 5 p))
  :hints (("Goal" :in-theory (enable (:e base-prime) (:e <)))))

(defrule id-low5-int-natp
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4))
           (natp (+ b0 b1 b2 b3 b4)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bitp))))

(defrule id-low5-int-lt-prime
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal p (base-prime)))
           (< (+ b0 b1 b2 b3 b4) p))
  :hints (("Goal" :in-theory (enable bitp (:e base-prime) (:e <)))))

(defruled id-not-is-one-minus
  (implies (bitp b)
           (equal (values-b-not b) (- 1 b)))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (enable values-b-not bitp acl2::bfix-when-bitp))))

(defruled id-not-not
  (implies (bitp b)
           (equal (values-b-not (values-b-not b)) b))
  :hints (("Goal"
           :cases ((equal b 0))
           :in-theory (enable values-b-not bitp acl2::bfix-when-bitp))))

(defruled id-sub1-is-one-minus
  (implies (and (bitp b) (equal p (base-prime)))
           (equal (pfield::sub 1 b p) (- 1 b)))
  :hints (("Goal"
           :in-theory (enable id-sub1-of-bit id-not-is-one-minus))))

(defruled id-add-sub1-bit
  (implies (and (bitp b) (bitp k) (equal p (base-prime)))
           (equal (pfield::add (pfield::sub 1 b p) k p)
                  (+ (- 1 b) k)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (id-sub1-is-one-minus
                            id-add-of-bits
                            id-bitp-of-one-minus)
                           ((:definition pfield::add)
                            (:definition pfield::sub)
                            (:definition pfield::mul)
                            (:definition pfield::mul))))))

(defruled id-two-bit-sum-small
  (implies (and (bitp a) (bitp b))
           (and (natp (+ a b))
                (< (+ a b) 3)))
  :hints (("Goal" :in-theory (enable bitp))))

(defruled id-one-minus-sum-small
  (implies (and (bitp b) (bitp k))
           (and (natp (+ (- 1 b) k))
                (< (+ (- 1 b) k) 3)))
  :hints (("Goal" :in-theory (enable bitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-bitp-of-r-when-neq
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p) m p) r)
                (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (bitp r))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-r-when-neq
                            (s (+ b0 b1 b2 b3 b4))
                            (m m) (r r) (p p)))
           :in-theory (e/d (id-low5-sum-is-plus
                            id-low5-int-natp
                            id-low5-int-lt-prime
                            bitp)
                           (id-r-when-neq
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition pfield::add))))))

(defruled id-r-is-not-all-zero
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p) m p) r)
                (equal (pfield::mul (id-low5-sum b0 b1 b2 b3 b4 p)
                                    (pfield::sub 1 r p)
                                    p)
                       0))
           (equal (values-b-not
                   (byte-validation-data->all-zero-5
                    (byte-validation-data-new b0 b1 b2 b3 b4)))
                  r))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-r-when-neq
                            (s (+ b0 b1 b2 b3 b4))
                            (m m) (r r) (p p)))
           :in-theory (e/d (id-bitp-of-r-when-neq
                            id-low5-sum-is-plus
                            id-low5-int-natp
                            id-low5-int-lt-prime
                            byte-validation-data-new
                            byte-validation-data->all-zero-5
                            values-bool-to-bit
                            values-b-not
                            acl2::bfix-when-bitp
                            id-bitp-of-if-01
                            bitp)
                           (id-r-when-neq
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            (:definition pfield::add))))))

(defruled id-null-is-spec
  (implies (and (bitp b6) (bitp b5) (equal p (base-prime))
                (equal null
                       (pfield::mul (pfield::sub 1 b6 p)
                                    (pfield::sub 1 b5 p)
                                    p)))
           (equal (values-b-and (values-b-not b6) (values-b-not b5))
                  null))
  :do-not-induct t
  :hints (("Goal"
           :cases ((and (equal b6 0) (equal b5 0))
                   (and (equal b6 0) (equal b5 1))
                   (and (equal b6 1) (equal b5 0))
                   (and (equal b6 1) (equal b5 1)))
           :in-theory (enable values-b-and values-b-not
                              pfield::mul pfield::sub pfield::add pfield::neg
                              bitp acl2::bfix-when-bitp
                              (:e base-prime)))))

(defruled id-bits-product-zero
  (implies (and (bitp x) (bitp y) (equal p (base-prime))
                (equal (pfield::mul x y p) 0))
           (equal (* x y) 0))
  :hints (("Goal"
           :in-theory (e/d (id-mul-of-bits)
                           ((:definition pfield::mul)
                            (:definition pfield::mul))))))

(defruled id-null-check-int
  (implies (and (bitp b5) (bitp b6) (bitp r)
                (equal p (base-prime))
                (equal (pfield::mul
                        (pfield::mul (pfield::sub 1 b6 p)
                                     (pfield::sub 1 b5 p)
                                     p)
                        r
                        p)
                       0))
           (equal (* (values-b-and (values-b-not b6) (values-b-not b5))
                     r)
                  0))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-bits-product-zero
                            (x (values-b-and (values-b-not b6)
                                             (values-b-not b5)))
                            (y r)
                            (p p)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-null-mul-is-spec
                         bitp-of-values-b-and
                         (:executable-counterpart equal)
                         (:executable-counterpart iff)
                         (:executable-counterpart not))))))

(defruled id-lower-is-and
  (implies (and (bitp b6) (bitp b5)
                (equal lower (bitand b6 b5)))
           (equal (values-b-and b6 b5) lower))
  :hints (("Goal" :in-theory (enable values-b-and-is-bitand))))

(defruled id-idig-is-offset
  (implies (and (bitp b1) (bitp b2) (bitp b3)
                (equal dor (bitor b2 b1))
                (equal idig (bitand b3 dor)))
           (equal (is-invalid-digit-offset b1 b2 b3) idig))
  :hints (("Goal"
           :in-theory (enable is-invalid-digit-offset
                              values-b-and-is-bitand
                              values-b-or-is-bitor))))

(defruled id-bu-is-upper
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal b4b3 (bitand b4 b3))
                (equal b1b0 (bitand b1 b0))
                (equal xor (bitxor b2 b1b0))
                (equal bu (bitand b4b3 xor)))
           (equal (is-invalid-uppercase-offset
                   (byte-validation-data-new b0 b1 b2 b3 b4)
                   b2)
                  bu))
  :hints (("Goal"
           :in-theory (e/d (is-invalid-uppercase-offset
                            byte-validation-data-new
                            values-b-and-is-bitand
                            values-b-xor-is-bitxor
                            acl2::bfix-when-bitp)
                           ((:definition byte-validation-data->b4b3$inline)
                            (:definition byte-validation-data->b1b0$inline))))))

(defruled id-bl-is-lower-offset
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (equal b4b3 (bitand b4 b3))
                (equal b1b0 (bitand b1 b0))
                (equal lor (bitor b2 b1b0))
                (equal bl (bitand b4b3 lor)))
           (equal (is-invalid-lowercase-offset
                   (byte-validation-data-new b0 b1 b2 b3 b4)
                   b2)
                  bl))
  :hints (("Goal"
           :in-theory (e/d (is-invalid-lowercase-offset
                            byte-validation-data-new
                            values-b-and-is-bitand
                            values-b-or-is-bitor
                            acl2::bfix-when-bitp)
                           ((:definition byte-validation-data->b4b3$inline)
                            (:definition byte-validation-data->b1b0$inline))))))

(defruled id-diff-check-int
  :short "A field product (a - b) * ((1 - c) + k) = 0 is the same integer product."
  (implies (and (bitp a) (bitp b) (bitp c) (bitp k)
                (equal p (base-prime))
                (equal (pfield::mul (pfield::sub a b p)
                                    (pfield::add (pfield::sub 1 c p) k p)
                                    p)
                       0))
           (equal (* (- a b) (+ (- 1 c) k)) 0))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-diff-prod-when-bits
                            (a a) (b b)
                            (k (+ (- 1 c) k))
                            (p p))
                 (:instance id-one-minus-sum-small
                            (b c) (k k)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-add-sub1-bit
                         bitp
                         (:executable-counterpart equal)
                         (:executable-counterpart iff)
                         (:executable-counterpart not))))))

(defruled id-bit-check-int
  :short "A field product a * ((1 - r) + k) = 0 is the same integer product."
  (implies (and (bitp a) (bitp r) (bitp k)
                (equal p (base-prime))
                (equal (pfield::mul a
                                    (pfield::add (pfield::sub 1 r p) k p)
                                    p)
                       0))
           (equal (* a (+ (- 1 r) k)) 0))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance id-bit-times-small-is-int
                            (a a)
                            (k (+ (- 1 r) k))
                            (p p))
                 (:instance id-one-minus-sum-small
                            (b r) (k k)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-add-sub1-bit
                         bitp
                         (:executable-counterpart equal)
                         (:executable-counterpart iff)
                         (:executable-counterpart not))))))

(defruled id-all-zero-is-sub1-r
  (implies (and (bitp z) (bitp r) (equal p (base-prime))
                (equal r (values-b-not z)))
           (equal (pfield::sub 1 r p) z))
  :hints (("Goal"
           :in-theory (enable id-sub1-of-bit id-not-not))))

(defruled id-all-zero-is-one-minus-r
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4)
                (bitp r)
                (equal (values-b-not
                        (byte-validation-data->all-zero-5
                         (byte-validation-data-new b0 b1 b2 b3 b4)))
                       r))
           (equal (byte-validation-data->all-zero-5
                   (byte-validation-data-new b0 b1 b2 b3 b4))
                  (- 1 r)))
  :hints (("Goal"
           :use (:instance id-not-not
                           (b (byte-validation-data->all-zero-5
                               (byte-validation-data-new b0 b1 b2 b3 b4))))
           :in-theory (e/d (id-not-is-one-minus
                            byte-validation-data-new
                            byte-validation-data->all-zero-5
                            values-bool-to-bit
                            values-b-not
                            acl2::bfix-when-bitp
                            bitp)
                           (id-not-not)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-equations-imply-validate-rest
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (id-byte-equations b0 b1 b2 b3 b4 b5 b6 b7
                                   b4b3 b1b0 m r null lower
                                   dor idig xor bu lor bl p))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) nil)
                  (values-b-and (values-b-not b6) (values-b-not b5))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-validate-byte-rest-when-checks
                 id-bitp-of-r-when-neq
                 id-r-is-not-all-zero
                 (:instance id-null-check-int
                            (r r) (b5 b5) (b6 b6) (p p))
                 id-lower-is-and
                 id-idig-is-offset
                 id-bu-is-upper
                 id-bl-is-lower-offset
                 (:instance id-diff-check-int
                            (a b5) (b lower) (c b4) (k idig) (p p))
                 (:instance id-diff-check-int
                            (a b6) (b lower) (c r) (k bu) (p p))
                 (:instance id-bit-check-int
                            (a lower) (r r) (k bl) (p p))
                 id-all-zero-is-one-minus-r)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-byte-equations
                         id-bitp-of-bitand
                         id-bitp-of-bitor
                         id-bitp-of-bitxor
                         bitp-of-is-invalid-digit-offset
                         bitp-of-is-invalid-uppercase-offset
                         bitp-of-is-invalid-lowercase-offset
                         bitp-of-values-b-and
                         bitp-of-values-b-not
                         bitp-of-byte-validation-data->all-zero-5
                         (:executable-counterpart bitp)
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff)
                         (:executable-counterpart cons)))
           :do-not '(generalize fertilize eliminate-destructors))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-letter-mul-is-and
  (implies (and (bitp b6) (bitp uscore) (equal p (base-prime))
                (equal islet
                       (pfield::mul b6 (pfield::sub 1 uscore p) p)))
           (equal (values-b-and b6 (values-b-not uscore))
                  islet))
  :do-not-induct t
  :hints (("Goal"
           :cases ((and (equal b6 0) (equal uscore 0))
                   (and (equal b6 0) (equal uscore 1))
                   (and (equal b6 1) (equal uscore 0))
                   (and (equal b6 1) (equal uscore 1)))
           :in-theory (enable values-b-and values-b-not
                              pfield::mul pfield::sub pfield::add pfield::neg
                              bitp acl2::bfix-when-bitp
                              (:e base-prime)))))

(defthm id-assert-bit-one
  (implies (and (bitp b) (equal p (base-prime))
                (assert-funspec b))
           (equal b 1))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal b 0))
           :in-theory (enable assert-funspec enforce-funspec
                              pfield::mul bitp
                              (:e base-prime)))))

(defruled id-first-letter-one
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3) (bitp b4) (bitp b6)
                (bitp b4b3) (bitp b1b0) (bitp partial) (bitp uscore)
                (equal p (base-prime))
                (equal b4b3 (bitand b4 b3))
                (equal b1b0 (bitand b1 b0))
                (equal partial (bitand b4b3 b1b0))
                (equal uscore (bitand partial b2))
                (equal islet
                       (pfield::mul b6 (pfield::sub 1 uscore p) p))
                (assert-funspec islet))
           (equal (values-b-and
                   b6
                   (values-b-not
                    (values-b-and
                     (values-b-and
                      (byte-validation-data->b4b3
                       (byte-validation-data-new b0 b1 b2 b3 b4))
                      (byte-validation-data->b1b0
                       (byte-validation-data-new b0 b1 b2 b3 b4)))
                     b2)))
                  1))
  :do-not-induct t
  :hints (("Goal"
           :use (id-letter-mul-is-and id-assert-bit-one)
           :in-theory (e/d (values-b-and-is-bitand
                            byte-validation-data-new
                            acl2::bfix-when-bitp
                            id-bitp-of-bitand)
                           ((:definition byte-validation-data->b4b3$inline)
                            (:definition byte-validation-data->b1b0$inline)
                            (:definition pfield::mul)
                            (:definition pfield::sub))))))

(defruled id-equations-imply-validate-first
  (implies (and (bitp b0) (bitp b1) (bitp b2) (bitp b3)
                (bitp b4) (bitp b5) (bitp b6) (bitp b7)
                (bitp partial) (bitp uscore)
                (equal p (base-prime))
                (pfield::fep m p)
                (pfield::fep r p)
                (id-byte-equations b0 b1 b2 b3 b4 b5 b6 b7
                                   b4b3 b1b0 m r null lower
                                   dor idig xor bu lor bl p)
                (id-first-extra-equations b4b3 b1b0 b2 b6
                                          partial uscore islet p))
           (equal (validate-byte (list b0 b1 b2 b3 b4 b5 b6 b7) t)
                  (values-b-and (values-b-not b6) (values-b-not b5))))
  :do-not-induct t
  :hints (("Goal"
           :use (id-validate-byte-first-when-checks
                 id-bitp-of-r-when-neq
                 id-r-is-not-all-zero
                 (:instance id-null-check-int
                            (r r) (b5 b5) (b6 b6) (p p))
                 id-lower-is-and
                 id-idig-is-offset
                 id-bu-is-upper
                 id-bl-is-lower-offset
                 (:instance id-diff-check-int
                            (a b5) (b lower) (c b4) (k idig) (p p))
                 (:instance id-diff-check-int
                            (a b6) (b lower) (c r) (k bu) (p p))
                 (:instance id-bit-check-int
                            (a lower) (r r) (k bl) (p p))
                 id-all-zero-is-one-minus-r
                 id-first-letter-one)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(id-byte-equations
                         id-first-extra-equations
                         id-bitp-of-bitand
                         id-bitp-of-bitor
                         id-bitp-of-bitxor
                         bitp-of-is-invalid-digit-offset
                         bitp-of-is-invalid-uppercase-offset
                         bitp-of-is-invalid-lowercase-offset
                         bitp-of-values-b-and
                         bitp-of-values-b-not
                         bitp-of-byte-validation-data->all-zero-5
                         (:executable-counterpart bitp)
                         (:executable-counterpart equal)
                         (:executable-counterpart not)
                         (:executable-counterpart iff)
                         (:executable-counterpart cons)))
           :do-not '(generalize fertilize eliminate-destructors))))
