; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS for Field::write_bits_le and write_bits_be.
;
; The gadget is boolean checks, a powers-of-two sum, and the
; bits-lte-const range fold against p - 1, closed by a unit-zero.
; A 3-bit list has the same shape as that gadget at prime 5
; (p - 1 = bits (0 0 1), fold length 2): OR of the two low bits,
; AND with the high bit, and (u - z1) = 1 with u = 1.
; Interpreted in the base field, the fold accepts only values below 5.
; For those values the three bits are the low three bits of the
; 253-bit funspec (the other 250 bits are zero).  Values 5, 6, and 7
; have canonical low bits but fail the fold, so the equivalence
; includes that bound.

(in-package "ALEOVM")

(include-book "fb2-field-bits")
(include-book "../r1cs/boolean-xor")
(include-book "kestrel/prime-fields/bitp-idioms" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthmd fb3-base-prime-above-16-exec
   (< 16 (base-prime))
   :hints (("Goal" :in-theory (enable (:e base-prime)
                                      (:e ecurve::edwards-bls12-q))))))

; (:e base-prime) is on in the world, so a ground (< 16 (base-prime))
; evaluates to T and cannot be stored as a linear rule.  Disable the
; executable counterpart only while the rule is built, then restore it.
(local (in-theory (disable (:e base-prime))))

(defrule fb3-base-prime-above-16
  (< 16 (base-prime))
  :rule-classes ((:linear :trigger-terms ((base-prime))))
  :hints (("Goal" :use fb3-base-prime-above-16-exec)))

(local (in-theory (enable (:e base-prime))))

(defruled fb3-bool-check-is-bitp
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep b p))
           (equal (equal (pfield::mul (pfield::sub (mod 1 p) b p) b p)
                         (mod 0 p))
                  (bitp b)))
  :enable (pfield::sub
           pfield::bitp-idiom-2-alt
           acl2::mod-of-0-arg1
           acl2::mod-of-1-arg1
           fb3-base-prime-above-16)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2
            (:rewrite pfield::bitp-idiom-2)))

(defruled fb3-neg-is-zero
  (implies (and (pfield::fep z p)
                (integerp p))
           (equal (equal (pfield::neg z p) 0)
                  (equal z 0)))
  :hints (("Goal"
           :cases ((equal z 0))
           :in-theory (e/d (pfield::neg pfield::neg-of-neg pfield::fep
                                        acl2::mod-of-0-arg1)
                           (pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-sub1-iff-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep z p))
           (equal (equal (pfield::sub 1 z p) 1)
                  (equal z 0)))
  :enable (pfield::sub fb3-neg-is-zero pfield::fep-holds
                       fb3-base-prime-above-16)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance pfield::equal-of-add-cancel-1
                  (x 1)
                  (y (pfield::neg z (base-prime)))
                  (p (base-prime))))

(defruled fb3-sub1-iff-one
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep z p))
           (equal (equal (pfield::sub 1 z p) 0)
                  (equal z 1)))
  :enable (pfield::sub
           pfield::fep-holds
           fb3-base-prime-above-16
           pfield::equal-of-0-and-add-of-neg-arg1
           pfield::add-commutative)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2
            pfield::mul-of-sub-arg1
            pfield::mul-of-sub-arg2)
  :use (:instance pfield::equal-of-0-and-add-of-neg-arg1
                  (x z)
                  (y 1)
                  (p (base-prime))))

(defruled fb3-unit-is-one
  (implies (and (equal p (base-prime))
                (primep p)
                (pfield::fep u p))
           (equal (equal (pfield::mul u (mod 1 p) p)
                         (mod 1 p))
                  (equal u 1)))
  :enable (acl2::mod-of-1-arg1
           pfield::mul-of-1-arg2
           fb3-base-prime-above-16))

(defruled fb3-zero-unit-is-zero
  (implies (and (equal p (base-prime))
                (primep p)
                (equal u 1)
                (pfield::fep z p))
           (equal (equal (pfield::mul (pfield::sub u z p) (mod 1 p) p)
                         (mod 1 p))
                  (equal z 0)))
  :enable (fb3-unit-is-one fb3-sub1-iff-zero pfield::mul-of-1-arg2
           acl2::mod-of-1-arg1))

(defruled fb3-weighted-3
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (pfield::fep x p))
           (equal (equal (pfield::mul x (mod 1 p) p)
                         (pfield::add
                          (pfield::add b0
                                       (pfield::mul (mod 2 p) b1 p)
                                       p)
                          (pfield::mul (mod 4 p) b2 p)
                          p))
                  (equal x (+ b0 (* 2 b1) (* 4 b2)))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            acl2::mod-of-1-arg1
                            acl2::mod-when-<
                            pfield::mul-of-1-arg2
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::add)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

(defruled fb3-weighted-2
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp b0)
                (bitp b1)
                (pfield::fep x p))
           (equal (equal (pfield::mul x (mod 1 p) p)
                         (pfield::add b0
                                      (pfield::mul (mod 2 p) b1 p)
                                      p))
                  (equal x (+ b0 (* 2 b1)))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            acl2::mod-of-1-arg1
                            acl2::mod-when-<
                            pfield::mul-of-1-arg2
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::add)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))))

(defruled fb3-two-bits-below-4
  (implies (and (bitp b0)
                (bitp b1)
                (equal x (+ b0 (* 2 b1))))
           (< x 4))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (enable bitp))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))))

(defruled fb3-bits-match-2
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp b0)
                (bitp b1)
                (equal x (+ b0 (* 2 b1))))
           (equal (list b0 b1)
                  (take 2 (field-bits-le x))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            field-bits-le
                            fieldp
                            pfield::fep-fix-when-fep
                            base-field-size-in-bits
                            base-prime
                            (:e ecurve::edwards-bls12-q)
                            (:e acl2::nat=>lebits)
                            (:e take))
                           nil))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))))

(defruled fb3-or-is-bitor
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp a)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul (pfield::sub (mod 1 p) a p)
                                      (pfield::sub (mod 1 p) b p)
                                      p)
                         (pfield::sub (mod 1 p) z p))
                  (equal z (bitor a b))))
  :hints (("Goal"
           :cases ((equal a 0) (equal a 1))
           :in-theory (e/d (bitp bitor
                            pfield::sub
                            acl2::mod-of-1-arg1
                            fb3-sub1-iff-zero
                            fb3-sub1-iff-one
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e pfield::add)
                            (:e pfield::neg)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b 0) (equal b 1)))
          ("Subgoal 2" :cases ((equal b 0) (equal b 1)))))

(defruled fb3-xor-is-bitxor
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp a)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul (pfield::mul (mod 2 p) a p) b p)
                         (pfield::sub (pfield::add a b p) z p))
                  (equal z (bitxor a b))))
  :hints (("Goal"
           :cases ((equal a 0) (equal a 1))
           :in-theory (e/d (bitp bitxor
                            pfield::sub
                            pfield::add
                            acl2::mod-when-<
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e pfield::add)
                            (:e pfield::neg)
                            (:e pfield::sub)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))
          ("Subgoal 1" :cases ((equal b 0) (equal b 1)))
          ("Subgoal 2" :cases ((equal b 0) (equal b 1)))))

(defruled fb3-if0-is-if0
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp d)
                (bitp y)
                (pfield::fep r p))
           (equal (equal (pfield::mul d y p) r)
                  (equal r (if (equal d 1) y 0))))
  :hints (("Goal"
           :cases ((equal d 0) (equal d 1))
           :in-theory (e/d (bitp
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))))

(defruled fb3-if-is-if
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp d)
                (pfield::fep y p)
                (pfield::fep r p)
                (pfield::fep b p))
           (equal (equal (pfield::mul d (pfield::sub y r p) p)
                         (pfield::sub b r p))
                  (equal b (if (equal d 1) y r))))
  :hints (("Goal"
           :cases ((equal d 0) (equal d 1))
           :use ((:instance pfield::equal-of-0-and-add-of-neg-arg2
                            (x b)
                            (y r)
                            (p p))
                 (:instance pfield::equal-of-add-and-add-cancel-4
                            (y y)
                            (x (pfield::neg r p))
                            (z b)
                            (p p)))
           :in-theory (e/d (bitp
                            pfield::sub
                            pfield::mul-of-0-arg1
                            pfield::mul-of-1-arg1
                            pfield::equal-of-0-and-add-of-neg-arg2
                            fb3-base-prime-above-16)
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-not-is-boolean-not
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul z (mod 1 p) p)
                         (pfield::sub (mod 1 p) b p))
                  (equal z (if (equal b 1) 0 1))))
  :hints (("Goal"
           :cases ((equal b 0) (equal b 1))
           :in-theory (e/d (bitp
                            pfield::sub
                            acl2::mod-of-1-arg1
                            pfield::mul-of-1-arg2
                            fb3-sub1-iff-zero
                            fb3-sub1-iff-one
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::add)
                            (:e pfield::neg)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2)))))

(defruled fb3-mul-is-bitand
  (implies (and (equal p (base-prime))
                (primep p)
                (bitp a)
                (bitp b)
                (pfield::fep z p))
           (equal (equal (pfield::mul a b p) z)
                  (equal z (bitand a b))))
  :hints (("Goal"
           :cases ((equal a 0) (equal a 1))
           :in-theory (e/d (bitp bitand
                            fb3-base-prime-above-16
                            (:e base-prime)
                            (:e ecurve::edwards-bls12-q)
                            (:e pfield::mul)
                            (:e mod))
                           (pfield::mul-of-add-arg1
                            pfield::mul-of-add-arg2)))
          ("Subgoal 1" :cases ((equal b 0) (equal b 1)))
          ("Subgoal 2" :cases ((equal b 0) (equal b 1)))))

(defruled fb3-bits-match-write-bits-le
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal x (+ b0 (* 2 b1) (* 4 b2))))
           (equal (list b0 b1 b2)
                  (take 3 (field-write-bits-le-funspec nil x))))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (e/d (bitp
                            field-write-bits-le-funspec
                            field-bits-le
                            fieldp
                            pfield::fep-fix-when-fep
                            base-field-size-in-bits
                            base-prime
                            (:e ecurve::edwards-bls12-q)
                            (:e acl2::nat=>lebits)
                            (:e take)
                            (:e append))
                           nil))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

(defruled fb3-bits-match-write-bits-be
  (implies (and (equal p (base-prime))
                (fieldp x)
                (bitp w0)
                (bitp w1)
                (bitp w2)
                (equal x (+ w2 (* 2 w1) (* 4 w0))))
           (equal (list w0 w1 w2)
                  (nthcdr 250 (field-write-bits-be-funspec nil x))))
  :hints (("Goal"
           :cases ((equal w2 0) (equal w2 1))
           :in-theory (e/d (bitp
                            field-write-bits-be-funspec
                            field-write-bits-le-funspec
                            field-bits-le
                            fieldp
                            pfield::fep-fix-when-fep
                            base-field-size-in-bits
                            base-prime
                            (:e ecurve::edwards-bls12-q)
                            (:e acl2::nat=>lebits)
                            (:e rev)
                            (:e nthcdr)
                            (:e append))
                           nil))
          ("Subgoal 1" :cases ((equal w1 0) (equal w1 1)))
          ("Subgoal 2" :cases ((equal w1 0) (equal w1 1)))
          ("Subgoal 1.1" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 1.2" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 2.1" :cases ((equal w0 0) (equal w0 1)))
          ("Subgoal 2.2" :cases ((equal w0 0) (equal w0 1)))))

(defruled fb3-three-bits-below-5
  (implies (and (bitp b0)
                (bitp b1)
                (bitp b2)
                (equal z0 (bitor b1 b0))
                (equal z1 (bitand b2 z0))
                (equal z1 0)
                (equal x (+ b0 (* 2 b1) (* 4 b2))))
           (< x 5))
  :hints (("Goal"
           :cases ((equal b0 0) (equal b0 1))
           :in-theory (enable bitp bitor bitand))
          ("Subgoal 1" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 2" :cases ((equal b1 0) (equal b1 1)))
          ("Subgoal 1.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 1.2" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.1" :cases ((equal b2 0) (equal b2 1)))
          ("Subgoal 2.2" :cases ((equal b2 0) (equal b2 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fb3-mod-when-fieldp
  (implies (fieldp x)
           (equal (mod x primes::*bls12-377-scalar-field-prime*) x))
  :enable (fieldp base-prime))

(defruled fb3-integerp-when-fieldp
  (implies (fieldp x)
           (integerp x))
  :enable fieldp)

(define fb3-field-write-bits-le-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for @('Field::write_bits_le').
          @('u = 1') forces the range bit @('z1') to 0."
  (pfcs::parse-def
   "field_write_bits_le_3(x, b0, b1, b2, z0, z1, u) := {
    (1 - b0) * (b0) == (0),
    (1 - b1) * (b1) == (0),
    (1 - b2) * (b2) == (0),
    (u) * (1) == (1),
    (u - z1) * (1) == (1),
    (x) * (1) == (b0 + 2 * b1 + 4 * b2),
    (1 - b1) * (1 - b0) == (1 - z0),
    (b2) * (z0) == (z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-write-bits-le-3-circuit)
            :pred fb3-field-write-bits-le-3-pred
            :prime prime)

(defruled fb3-field-write-bits-le-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep b0 prime)
                (pfield::fep b1 prime)
                (pfield::fep b2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime))
           (equal (fb3-field-write-bits-le-3-pred
                   x b0 b1 b2 z0 z1 u prime)
                  (and (bitp b0)
                       (bitp b1)
                       (bitp b2)
                       (equal u 1)
                       (equal z1 0)
                       (equal x (+ b0 (* 2 b1) (* 4 b2)))
                       (equal z0 (bitor b1 b0))
                       (equal z1 (bitand b2 z0))
                       (equal (list b0 b1 b2)
                              (take 3 (field-write-bits-le-funspec nil x)))
                       (< x 5))))
  :enable (fb3-field-write-bits-le-3-pred
           fb3-bool-check-is-bitp
           fb3-unit-is-one
           fb3-zero-unit-is-zero
           fb3-weighted-3
           fb3-or-is-bitor
           fb3-mul-is-bitand
           fb3-bits-match-write-bits-le
           fb3-three-bits-below-5
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp)
  :disable (bitp fieldp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fb3-field-write-bits-be-3-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Three-bit PFCS for @('Field::write_bits_be').
          @('w0') is the most significant of the three low bits."
  (pfcs::parse-def
   "field_write_bits_be_3(x, w0, w1, w2, z0, z1, u) := {
    (1 - w2) * (w2) == (0),
    (1 - w1) * (w1) == (0),
    (1 - w0) * (w0) == (0),
    (u) * (1) == (1),
    (u - z1) * (1) == (1),
    (x) * (1) == (w2 + 2 * w1 + 4 * w0),
    (1 - w1) * (1 - w2) == (1 - z0),
    (w0) * (z0) == (z1)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (fb3-field-write-bits-be-3-circuit)
            :pred fb3-field-write-bits-be-3-pred
            :prime prime)

(defruled fb3-field-write-bits-be-3-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (fieldp x)
                (pfield::fep w0 prime)
                (pfield::fep w1 prime)
                (pfield::fep w2 prime)
                (pfield::fep z0 prime)
                (pfield::fep z1 prime)
                (pfield::fep u prime))
           (equal (fb3-field-write-bits-be-3-pred
                   x w0 w1 w2 z0 z1 u prime)
                  (and (bitp w2)
                       (bitp w1)
                       (bitp w0)
                       (equal u 1)
                       (equal z1 0)
                       (equal x (+ w2 (* 2 w1) (* 4 w0)))
                       (equal z0 (bitor w1 w2))
                       (equal z1 (bitand w0 z0))
                       (equal (list w0 w1 w2)
                              (nthcdr 250
                                      (field-write-bits-be-funspec nil x)))
                       (< x 5))))
  :enable (fb3-field-write-bits-be-3-pred
           fb3-bool-check-is-bitp
           fb3-unit-is-one
           fb3-zero-unit-is-zero
           fb3-weighted-3
           fb3-or-is-bitor
           fb3-mul-is-bitand
           fb3-bits-match-write-bits-be
           fb3-three-bits-below-5
           fb3-mod-when-fieldp
           fb3-integerp-when-fieldp)
  :disable (bitp fieldp))
