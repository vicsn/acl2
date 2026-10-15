; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Compare::{is_less_than, is_greater_than, is_less_than_or_equal,
;           is_greater_than_or_equal}.
;
; Unsigned less-than is r1cs/unsigned-small-lt.  Its result bit z is 0 iff
; x < y, so the boolean snarkVM returns is the linear combination 1 - z.
; The hypothesis n+1 < integer-length(p) holds for every width, including 128.
;
; is_greater_than is less-than with the operands swapped.
; is_greater_than_or_equal is boolean not of less-than (a linear combination).
; is_less_than_or_equal is greater-than-or-equal with the operands swapped.
;
; Signed less-than, which the library does not cover, is the snarkVM circuit:
; the same high bit of 2^n + xu - yu, plus a sign test
;   same-sign = not (msb x xor msb y)     ; not is a linear combination
;   neg-pos   = msb x and not msb y
;   result    = same-sign ? not high-bit : neg-pos

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-lt")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-and-notright")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-is-less-than-unsigned-gadget ((xs symbol-listp)
                                          (ys symbol-listp)
                                          (zs symbol-listp)
                                          (z symbolp)
                                          (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Unsigned @('is_less_than').  The returned boolean is @($1 - z$)."
  (unsigned-small-lt-gadget xs ys zs z p))

(define int-is-greater-than-unsigned-gadget ((xs symbol-listp)
                                             (ys symbol-listp)
                                             (zs symbol-listp)
                                             (z symbolp)
                                             (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('is_greater_than(x, y)') is @('is_less_than(y, x)')."
  (int-is-less-than-unsigned-gadget ys xs zs z p))

(define int-is-greater-than-or-equal-unsigned-gadget
  ((xs symbol-listp)
   (ys symbol-listp)
   (zs symbol-listp)
   (z symbolp)
   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Same constraints as less-than.  The result boolean is @('z')
          itself, because @('z = 0') iff @('x < y'), so @('z = 1') iff
          @('x >= y').  Boolean not is not a constraint."
  (int-is-less-than-unsigned-gadget xs ys zs z p))

(define int-is-less-than-or-equal-unsigned-gadget
  ((xs symbol-listp)
   (ys symbol-listp)
   (zs symbol-listp)
   (z symbolp)
   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "@('x <= y') is @('y >= x')."
  (int-is-greater-than-or-equal-unsigned-gadget ys xs zs z p))

(defruled int-is-less-than-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (not signedp)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-unsigned-gadget xs ys zs z p) asg p))
           (equal (if (equal (lookup-equal z asg) 0) 1 0)
                  (int-is-less-than-spec x y nil n)))
  :do-not-induct t
  :enable (int-is-less-than-unsigned-gadget
           int-is-less-than-spec
           int-spec-bool
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           int-valuep
           int-min
           int-max
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use unsigned-small-lt-gadget-soundness)

(defruled int-is-less-than-unsigned-result-bit
  :short "The less-than high bit is the boolean negation of the funspec."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (not signedp)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (bitp (lookup-equal z asg))
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-unsigned-gadget xs ys zs z p) asg p))
           (equal (lookup-equal z asg)
                  (if (equal (int-is-less-than-spec x y nil n) 1)
                      0
                    1)))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-gadget-sound (signedp nil))
  :enable bitp)

(defruled int-is-greater-than-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-unsigned-gadget xs ys zs z p) asg p))
           (equal (if (equal (lookup-equal z asg) 0) 1 0)
                  (int-is-greater-than-spec x y nil n)))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-gadget-sound
                  (xs ys) (ys xs) (x y) (y x) (signedp nil))
  :enable (int-is-greater-than-unsigned-gadget
           int-is-greater-than-spec-is-swapped-lt))

(defruled int-is-greater-than-or-equal-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp (lookup-equal z asg))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-or-equal-unsigned-gadget xs ys zs z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (int-is-greater-than-or-equal-spec x y nil n)))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-result-bit (signedp nil))
  :enable (int-is-greater-than-or-equal-unsigned-gadget
           int-is-greater-than-or-equal-spec-is-not-lt))

(defruled int-is-less-than-or-equal-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp (lookup-equal z asg))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-or-equal-unsigned-gadget xs ys zs z p)
                 asg p))
           (equal (lookup-equal z asg)
                  (int-is-less-than-or-equal-spec x y nil n)))
  :do-not-induct t
  :use (:instance int-is-greater-than-or-equal-unsigned-gadget-sound
                  (xs ys) (ys xs) (x y) (y x))
  :enable (int-is-less-than-or-equal-unsigned-gadget
           int-is-less-than-or-equal-spec-is-not-swapped-lt))

(defruledl int-valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)

; Completeness: the witness is the low n bits of 2^n + x - y and the high bit
; (0 iff x < y).  The same witness, with the operands swapped or with the
; high bit read as the boolean result, covers the other three comparisons.

(defruled int-is-less-than-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) x (- y)) n))
                (equal (lookup-equal z asg) (if (< x y) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-is-less-than-unsigned-gadget xs ys zs z p) asg p))
  :do-not-induct t
  :use (:instance unsigned-small-sub-opt-gadget-correct
                  (zs (append zs (list z))))
  :enable (int-is-less-than-unsigned-gadget
           integer-widthp
           integer-length-of-base-prime
           bit-listp-of-append-of-bit
           len-of-append-of-singleton
           int-valuation-binds-allp-of-nil
           unsigned-small-lt-gadget-to-unsigned-small-sub-opt-gadget
           unsigned-small-sub-opt-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list-of-cons
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           int-unsigned-lt-offset
           int-is-less-than-spec
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           int-width-add-fits
           posp-when-integer-widthp
           int-valuep int-min int-max
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-greater-than-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) y (- x)) n))
                (equal (lookup-equal z asg) (if (< y x) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-is-greater-than-unsigned-gadget xs ys zs z p) asg p))
  :do-not-induct t
  :use (:instance int-is-less-than-unsigned-gadget-complete
                  (xs ys) (ys xs) (x y) (y x))
  :enable int-is-greater-than-unsigned-gadget)

(defruled int-is-greater-than-or-equal-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) x (- y)) n))
                (equal (lookup-equal z asg) (if (< x y) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-is-greater-than-or-equal-unsigned-gadget xs ys zs z p)
            asg p))
  :do-not-induct t
  :use int-is-less-than-unsigned-gadget-complete
  :enable int-is-greater-than-or-equal-unsigned-gadget)

(defruled int-is-less-than-or-equal-unsigned-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys) (symbol-listp zs)
                (symbolp z)
                (equal n (len xs))
                (integer-widthp n)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n) y (- x)) n))
                (equal (lookup-equal z asg) (if (< y x) 0 1)))
           (r1cs::r1cs-constraints-holdp
            (int-is-less-than-or-equal-unsigned-gadget xs ys zs z p)
            asg p))
  :do-not-induct t
  :use (:instance int-is-greater-than-or-equal-unsigned-gadget-complete
                  (xs ys) (ys xs) (x y) (y x))
  :enable int-is-less-than-or-equal-unsigned-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 0 < 1 at width 2.  2^2 + 0 - 1 = 3 = bits (1 1 0), so z = 0 and zs = (1 1).

(defconst *int-is-less-than-sample*
  '((x0 . 0) (x1 . 0)
    (y0 . 1) (y1 . 0)
    (z0 . 1) (z1 . 1)
    (z . 0)))

(defruled int-is-less-than-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-less-than-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'z (base-prime))
   *int-is-less-than-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-is-less-than-unsigned-gadget
                                     unsigned-small-lt-gadget
                                     unsigned-small-lt-vector
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     pow2sum-vector
                                     pow2sum-neg-prime-vector
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

(defruled int-is-greater-than-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-greater-than-unsigned-gadget
    '(y0 y1) '(x0 x1) '(z0 z1) 'z (base-prime))
   *int-is-less-than-sample*
   (base-prime))
  :enable (int-is-greater-than-unsigned-gadget
           int-is-less-than-sample-holds))

(defruled int-is-greater-than-or-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-greater-than-or-equal-unsigned-gadget
    '(x0 x1) '(y0 y1) '(z0 z1) 'z (base-prime))
   *int-is-less-than-sample*
   (base-prime))
  :enable (int-is-greater-than-or-equal-unsigned-gadget
           int-is-less-than-sample-holds))

(defruled int-is-less-than-or-equal-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-is-less-than-or-equal-unsigned-gadget
    '(y0 y1) '(x0 x1) '(z0 z1) 'z (base-prime))
   *int-is-less-than-sample*
   (base-prime))
  :enable (int-is-less-than-or-equal-unsigned-gadget
           int-is-greater-than-or-equal-sample-holds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-is-less-than-signed-gadget ((xs symbol-listp)
                                        (ys symbol-listp)
                                        (zs symbol-listp)
                                        (z symbolp)
                                        (diff symbolp)
                                        (negpos symbolp)
                                        (out symbolp)
                                        (one symbolp)
                                        (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Signed @('is_less_than').  @('z') is the unsigned high bit
          (@('z = 0') iff the bit patterns satisfy @('xu < yu')).
          @('diff') is @('msb x xor msb y').  @('negpos') is
          @('msb x and not msb y').  @('out') is the result bit:
          if the signs agree it is @($1 - z$), otherwise it is @('negpos').
          Same-sign is the linear combination @($1 - \\mathit{diff}$)."
  (append (unsigned-small-lt-gadget xs ys zs z p)
          (boolean-xor-gadget (car (last xs)) (car (last ys)) diff p)
          (boolean-and-notright-gadget (car (last xs))
                                       (car (last ys))
                                       negpos one p)
          (list (r1cs::make-r1cs-constraint
                 :a (list (list 1 1)
                          (list (1- p) diff))
                 :b (list (list 1 1)
                          (list (1- p) z)
                          (list (1- p) negpos))
                 :c (list (list 1 out)
                          (list (1- p) negpos))))))

(defruled int-signed-lt-same-sign-case
  :short "When the sign bits agree, signed order is unsigned order of
          the bit patterns.  When they differ, the negative one is smaller."
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n)))))
           (equal (< (ifix x) (ifix y))
                  (if (equal sx sy)
                      (< (lebits=>nat (int->lebits x n))
                         (lebits=>nat (int->lebits y n)))
                    (and (equal sx 1)
                         (equal sy 0)))))
  :enable (int-signed-lt-iff
           posp-when-integer-widthp
           int-valuep))

; The signed ternary constraint, with bits d, z, n, o:
;   (1 - d) * (1 - z - n) = o - n
; forces o = (1 - z) when d = 0 and o = n when d = 1.

(defruledl int-signed-lt-ternary-holds
  (implies (and (primep p)
                (bitp d) (bitp z) (bitp n) (bitp o)
                (equal o (if (equal d 0)
                             (if (equal z 0) 1 0)
                           n)))
           (equal (pfield::mul (pfield::add 1 (pfield::mul (1- p) d p) p)
                               (pfield::add 1
                                            (pfield::add (pfield::mul (1- p) z p)
                                                         (pfield::mul (1- p) n p)
                                                         p)
                                            p)
                               p)
                  (pfield::add o (pfield::mul (1- p) n p) p)))
  :hints (("Goal"
           :cases ((equal d 0) (equal z 0) (equal n 0))
           :in-theory (enable pfield::add pfield::mul bitp))))

; Signed soundness is not claimed.  int-signed-lt-iff is the sign-bit
; criterion.  The ternary constraint still has to be tied to that
; criterion without opening bitxor into the field product.

(define int-is-less-than-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned less-than on field images.  @('s') is the low @('n')
          bits of @($2^n + x - y$) and @('r') is 1 iff @('x < y')
          (so the high bit is @($1 - r$)).  The product is @('(1-r) * n2'),
          which is an R1CS factor; the other side is the linear
          combination @('n2 + x - y - s')."
  (pfcs::parse-def
   "int_is_less_than(x, y, r, s, n2) := {
    (1 - r) * (n2) == (n2 + x - y - s)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-less-than-circuit)
            :pred int-is-less-than-pred
            :prime prime)

; The satisfying witness @($2^n + x - y = (1-r)2^n + s$) with
; @($0 \le s < 2^n$) forces @('r') to be the unsigned less-than bit.
; A boolean equality between the predicate and that equation, for an
; arbitrary @('s'), does not.

(defthm int-is-less-than-witness-is-spec
  (implies (and (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp r)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n))
                (equal (+ n2 x (- y))
                       (+ (* (- 1 r) n2) s)))
           (equal r (int-is-less-than-spec x y nil n)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< (ifix x) (ifix y)) (equal r 0))
           :do-not-induct t
           :in-theory (enable int-is-less-than-spec
                              int-spec-bool
                              int-valuep
                              int-min
                              int-max))))
