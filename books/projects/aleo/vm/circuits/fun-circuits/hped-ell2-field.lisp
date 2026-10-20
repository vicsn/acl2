; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field facts for the Elligator2 circuit: inverse witnesses, the values of
; snarkVM's Legendre power (Euler, from Fermat's little theorem), the
; uniqueness of the even square root, and the case forms of x and y.

(in-package "ALEOVM")

(include-book "../fun-specs/hash-elligator2")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defrule hped-ell2-inv-witness
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep w p)
                (equal (pfield::mul x w p) 1))
           (and (not (equal x 0))
                (equal (pfield::inv x p) w)))
  :rule-classes nil
  :do-not-induct t
  :cases ((equal x 0))
  :hints (("Subgoal 1"
           :use ((:instance pfield::equal-of-inv (pfield::a x) (pfield::b w) (pfield::p p))))))

(defrule hped-ell2-square-one
  (implies (and (primep p)
                (pfield::fep x p)
                (equal (pfield::mul x x p) 1))
           (or (equal x 1)
               (equal x (pfield::neg 1 p))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance pfield::equal-of-0-and-mul
                   (pfield::p p)
                   (pfield::x (pfield::sub x 1 p))
                   (pfield::y (pfield::add x 1 p))))
  :disable pfield::equal-of-0-and-mul)

(defruled hped-ell2-q-facts
  (and (primep (ecurve::edwards-bls12-q))
       (oddp (ecurve::edwards-bls12-q))
       (equal (+ (hped-ell2-legendre-exp) (hped-ell2-legendre-exp))
              (pfield::minus1 (ecurve::edwards-bls12-q)))
       (posp (hped-ell2-legendre-exp)))
  :enable (hped-ell2-legendre-exp ecurve::edwards-bls12-q pfield::minus1))

(defruled hped-ell2-legendre-cases
  :short "snarkVM's Legendre power is 0 exactly at 0, and otherwise 1 or -1."
  (implies (pfield::fep g (ecurve::edwards-bls12-q))
           (b* ((e (hped-ell2-legendre g)))
             (and (equal (equal e 0) (equal g 0))
                  (implies (not (equal g 0))
                           (or (equal e 1)
                               (equal e (pfield::neg 1 (ecurve::edwards-bls12-q))))))))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance hped-ell2-square-one
                   (p (ecurve::edwards-bls12-q))
                   (x (hped-ell2-legendre g)))
        (:instance pfield::pow-of-+
                   (pfield::p (ecurve::edwards-bls12-q))
                   (a g) (b (hped-ell2-legendre-exp)) (c (hped-ell2-legendre-exp)))
        (:instance pfield::my-fermat-little (a g) (p (ecurve::edwards-bls12-q))))
  :enable (hped-ell2-legendre)
  :disable (pfield::pow-of-+ pfield::my-fermat-little))

(defrule hped-ell2-squares-equal
  (implies (and (primep p)
                (pfield::fep r p)
                (pfield::fep q p)
                (equal (pfield::mul r r p) (pfield::mul q q p)))
           (or (equal r q)
               (equal r (pfield::neg q p))))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance pfield::equal-of-0-and-mul
                   (pfield::p p)
                   (pfield::x (pfield::sub r q p))
                   (pfield::y (pfield::add r q p))))
  :disable pfield::equal-of-0-and-mul)

(defruledl hped-ell2-odd-minus-even
  (implies (and (integerp m) (oddp m) (integerp q) (evenp q))
           (not (evenp (- m q))))
  :use ((:instance hped-ell2-integerp-sum
                   (a (+ (* 1/2 m) (- (* 1/2 q)))) (b (* 1/2 q))))
  :enable (oddp evenp)
  :prep-lemmas ((defrule hped-ell2-integerp-sum
                  (implies (and (integerp a) (integerp b)) (integerp (+ a b)))))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled hped-ell2-neg-of-even-is-odd
  (implies (and (pfield::fep q (ecurve::edwards-bls12-q))
                (evenp q)
                (not (equal q 0)))
           (not (evenp (pfield::neg q (ecurve::edwards-bls12-q)))))
  :use (hped-ell2-q-facts
        (:instance hped-ell2-odd-minus-even (m (ecurve::edwards-bls12-q))))
  :enable (pfield::neg pfield::fep)
  :disable evenp)

(defruled hped-ell2-even-root
  :short "The even square root is unique: a field element that is even
          (as a natural below p) and squares to @('rhs') is snarkVM's root."
  (implies (and (pfield::fep q (ecurve::edwards-bls12-q))
                (evenp q)
                (equal (pfield::mul q q (ecurve::edwards-bls12-q)) rhs))
           (and (ecurve::pfield-even-squarep rhs (ecurve::edwards-bls12-q))
                (equal (pfield::fep-fix (ecurve::pfield-square->even-root
                                         rhs (ecurve::edwards-bls12-q))
                                        (ecurve::edwards-bls12-q))
                       q)))
  :do-not-induct t
  :use (hped-ell2-q-facts
        (:instance ecurve::pfield-even-squarep-suff
                   (ecurve::r q) (ecurve::x rhs) (ecurve::p (ecurve::edwards-bls12-q)))
        (:instance hped-ell2-squares-equal
                   (p (ecurve::edwards-bls12-q))
                   (r (ecurve::pfield-square->even-root rhs (ecurve::edwards-bls12-q))))
        (:instance hped-ell2-neg-of-even-is-odd))
  :enable ecurve::pfield-even-squarep)
