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
; Greater-than swaps the operands.  The or-equal forms read the negation
; of the opposite less-than bit; boolean not adds no constraint.

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

(defruledl int-lookup-equal-list-of-nil
  (equal (lookup-equal-list nil alist) nil)
  :enable lookup-equal-list)

(defruledl int-lebits=>nat-of-nil
  (equal (lebits=>nat nil) 0)
  :enable lebits=>nat)

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
  :use ((:instance unsigned-small-sub-opt-gadget-correct
                  (zs (append zs (list z))))
        int-unsigned-lt-offset)
  :enable (int-is-less-than-unsigned-gadget
           integer-widthp
           integer-length-of-base-prime
           bit-listp-of-append-of-bit
           symbol-listp-of-append-of-symbol
           len-of-append-of-singleton
           int-valuation-binds-allp-of-nil
           int-lookup-equal-list-of-nil
           int-lebits=>nat-of-nil
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

(defruledl int-consp-when-len-equal
  (implies (and (consp xs)
                (equal (len ys) (len xs)))
           (consp ys))
  :hints (("Goal" :expand ((len xs) (len ys)))))

(defruledl int-sign-bits-are-symbols
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (equal (len ys) (len xs)))
           (and (symbolp (car (last xs)))
                (symbolp (car (last ys)))))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           int-consp-when-len-equal))

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
  :guard-hints (("Goal" :in-theory (enable int-sign-bits-are-symbols)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard
                    :hints (("Goal"
                             :in-theory (enable int-sign-bits-are-symbols))))
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

(define int-is-greater-than-signed-gadget ((xs symbol-listp)
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
  :guard-hints (("Goal" :in-theory (enable int-consp-when-len-equal)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard
                    :hints (("Goal" :in-theory (enable int-consp-when-len-equal))))
  :short "@('is_greater_than(x, y)') is signed @('is_less_than(y, x)')."
  (int-is-less-than-signed-gadget ys xs zs z diff negpos out one p))

(define int-is-greater-than-or-equal-signed-gadget
  ((xs symbol-listp)
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
  :guard-hints (("Goal" :in-theory (enable int-sign-bits-are-symbols)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard
                    :hints (("Goal" :in-theory (enable int-sign-bits-are-symbols))))
  :short "Same constraints as signed less-than.  The result boolean is
          the linear combination @($1 - \\mathit{out}$)."
  (int-is-less-than-signed-gadget xs ys zs z diff negpos out one p))

(define int-is-less-than-or-equal-signed-gadget
  ((xs symbol-listp)
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
  :guard-hints (("Goal" :in-theory (enable int-consp-when-len-equal)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard
                    :hints (("Goal" :in-theory (enable int-consp-when-len-equal))))
  :short "@('x <= y') is signed @('y >= x')."
  (int-is-greater-than-or-equal-signed-gadget ys xs zs z diff negpos out one p))

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

; The sign-bit criterion is int-signed-lt-iff.  The circuit theorems
; below read the xor gadget as bitxor, then apply that criterion.
; They do not open the xor constraint into the field product.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signed comparison.  The result bit is the unsigned high bit's negation
; when the sign bits agree, and msb(x) AND NOT msb(y) when they differ.
; The witness is the low n bits of 2^n + N(x) - N(y), that high bit,
; the sign-bit xor and and-not, and the ternary selector 1 - diff.
; The output wire is that ternary value.  It is proved equal to the
; funspec; completeness does not assume the output wire is already the
; funspec.

(define int-signed-less-than-bit ((x integerp) (y integerp) (n natp))
  :returns (b bitp)
  :short "Signed less-than bit computed from the sign bits and the
          unsigned order of the bit patterns."
  (b* ((sx (car (last (int->lebits x n))))
       (sy (car (last (int->lebits y n))))
       (diff (if (equal sx sy) 0 1))
       (negpos (if (and (equal sx 1) (equal sy 0)) 1 0))
       (z (if (< (lebits=>nat (int->lebits x n))
                 (lebits=>nat (int->lebits y n)))
              0
            1)))
    (if (equal diff 0)
        (if (equal z 0) 1 0)
      negpos)))

(defruled int-signed-less-than-bit-is-spec
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n))
           (equal (int-signed-less-than-bit x y n)
                  (int-is-less-than-spec x y t n)))
  :enable (int-signed-less-than-bit
           int-is-less-than-spec
           int-spec-bool
           int-signed-lt-iff
           int-valuep
           posp-when-integer-widthp))

(deflabel int-compare-before-mod)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "../library-extensions/bit-lists"))

(defruledl equal-of-0-and-mod-of-o-minus-1
  (implies (and (primep p)
                (pfield::fep o p))
           (equal (equal 0 (mod (+ -1 o) p))
                  (equal o 1)))
  :hints (("Goal"
           :cases ((equal o 0) (equal o 1))
           :in-theory (enable pfield::fep))))

(defthmd add-of-minus1-equals-p-minus-1
  (implies (and (primep p)
                (< 1 p)
                (pfield::fep o p))
           (equal (equal (+ -1 p) (pfield::add -1 o p))
                  (equal o 0)))
  :hints (("Goal"
           :cases ((equal o 0))
           :in-theory (enable pfield::add pfield::fep))))

(defthm int-signed-lt-ternary-sound
  (implies (and (primep p)
                (< 4 p)
                (bitp d)
                (bitp z)
                (bitp n)
                (pfield::fep o p)
                (equal (pfield::mul (pfield::add 1 (pfield::mul (1- p) d p) p)
                                    (pfield::add 1
                                                 (pfield::add (pfield::mul (1- p) z p)
                                                              (pfield::mul (1- p) n p)
                                                              p)
                                                 p)
                                    p)
                       (pfield::add o (pfield::mul (1- p) n p) p)))
           (equal o
                  (if (equal d 0)
                      (if (equal z 0) 1 0)
                    n)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal d 0) (equal z 0) (equal n 0))
           :in-theory (enable pfield::add
                              pfield::mul
                              bitp
                              equal-of-0-and-mod-of-o-minus-1))))

(defruledl base-prime-greater-than-4
  (< 4 (base-prime))
  :hints (("Goal"
           :in-theory (enable (:e ecurve::edwards-bls12-q)
                              (:e base-prime)
                              base-prime))))

(defruled int-signed-lt-ternary-constraint-sound
  (implies (and (primep p)
                (< 4 p)
                (symbolp diff)
                (symbolp z)
                (symbolp negpos)
                (symbolp out)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal diff asg))
                (bitp (lookup-equal z asg))
                (bitp (lookup-equal negpos asg))
                (r1cs::r1cs-constraints-holdp
                 (list (r1cs::make-r1cs-constraint
                        :a (list (list 1 1)
                                 (list (1- p) diff))
                        :b (list (list 1 1)
                                 (list (1- p) z)
                                 (list (1- p) negpos))
                        :c (list (list 1 out)
                                 (list (1- p) negpos))))
                 asg p))
           (equal (lookup-equal out asg)
                  (if (equal (lookup-equal diff asg) 0)
                      (if (equal (lookup-equal z asg) 0)
                          1
                        0)
                    (lookup-equal negpos asg))))
  :use (:instance int-signed-lt-ternary-sound
                  (d (lookup-equal diff asg))
                  (z (lookup-equal z asg))
                  (n (lookup-equal negpos asg))
                  (o (lookup-equal out asg)))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::dot-product
           add-of-minus1-equals-p-minus-1))

(defruledl int->lebits-of-unsigned-reading
  (implies (natp n)
           (equal (int->lebits (lebits=>nat (int->lebits x n)) n)
                  (int->lebits x n)))
  :enable (int->lebits
           lebits=>nat-of-int->lebits
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           bit-list-fix
           acl2::mod-when-<)
  :use (:instance acl2::nat=>lebits-of-lebits=>nat
                  (digits (int->lebits x n))))

(defrule int-integer-below-is-leq-predecessor
  (implies (and (integerp a)
                (integerp b)
                (< a b))
           (<= a (+ -1 b)))
  :rule-classes nil)

(defthm int->lebits-consp
  (implies (posp n)
           (consp (int->lebits x n)))
  :hints (("Goal"
           :use (:instance len-of-int->lebits)
           :in-theory (e/d (len) (len-of-int->lebits)))))

(defruled bitxor-is-sign-diff
  (implies (and (bitp x) (bitp y))
           (equal (bitxor x y)
                  (if (equal x y) 0 1)))
  :enable bitxor)

(defruledl bitxor-of-self
  (equal (bitxor x x) 0)
  :enable bitxor)

(defruledl int-sign-bit-if-not-zero
  (implies (and (posp n)
                (not (equal (car (last (int->lebits x n))) 0)))
           (equal (car (last (int->lebits x n))) 1))
  :hints (("Goal"
           :do-not-induct t
           :use (:instance bitp-of-car-of-last-when-bit-listp
                           (bits (int->lebits x n)))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            int->lebits-consp
                            bitp)
                           (int->lebits last)))))

(defruledl int-signed-less-than-bit-is-ternary
  (implies (posp n)
           (equal (int-signed-less-than-bit x y n)
                  (if (equal (bitxor (car (last (int->lebits x n)))
                                     (car (last (int->lebits y n))))
                             0)
                      (if (< (lebits=>nat (int->lebits x n))
                             (lebits=>nat (int->lebits y n)))
                          1
                        0)
                    (if (and (equal (car (last (int->lebits x n))) 1)
                             (equal (car (last (int->lebits y n))) 0))
                        1
                      0))))
  :use ((:instance bitp-of-car-of-last-when-bit-listp
                   (bits (int->lebits x n)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (int->lebits y n))))
  :do-not-induct t
  :enable (int-signed-less-than-bit
           bitxor-is-sign-diff
           bit-listp-of-int->lebits-explicit
           int->lebits-consp)
  :disable (bitxor int->lebits last bitp))

(defthm int-signed-lt-wires-are-bit
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (bitp z)
                (bitp diff)
                (bitp negpos)
                (equal (equal z 0)
                       (< (lebits=>nat (int->lebits x n))
                          (lebits=>nat (int->lebits y n))))
                (equal diff (bitxor (car (last (int->lebits x n)))
                                    (car (last (int->lebits y n)))))
                (equal negpos
                       (if (and (equal (car (last (int->lebits x n))) 1)
                                (equal (car (last (int->lebits y n))) 0))
                           1
                         0))
                (equal out
                       (if (equal diff 0)
                           (if (equal z 0) 1 0)
                         negpos)))
           (equal (int-signed-less-than-bit x y n) out))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance bitp-of-car-of-last-when-bit-listp
                            (bits (int->lebits x n)))
                 (:instance bitp-of-car-of-last-when-bit-listp
                            (bits (int->lebits y n))))
           :in-theory (e/d (int-signed-less-than-bit
                            bitxor-is-sign-diff
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits
                            posp-when-integer-widthp
                            int->lebits-consp)
                           (last int->lebits bitxor)))))

(defruledl int-valuep-of-unsigned-reading
  (implies (and (integer-widthp n)
                (int-valuep x t n))
           (int-valuep (lebits=>nat (int->lebits x n)) nil n))
  :enable (int-valuep int-min int-max
           len-of-int->lebits
           bit-listp-of-int->lebits-explicit
           posp-when-integer-widthp
           integer-widthp)
  :disable lebits=>nat-of-int->lebits
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))))
  :use ((:instance acl2::lebits=>nat-upper-bound
                   (digits (int->lebits x n)))
        (:instance int-integer-below-is-leq-predecessor
                   (a (lebits=>nat (int->lebits x n)))
                   (b (expt 2 n)))))

(defruledl int-signed-lt-sign-wires
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp diff)
                (symbolp negpos)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget (car (last xs))
                                     (car (last ys))
                                     diff
                                     p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget (car (last xs))
                                              (car (last ys))
                                              negpos
                                              one
                                              p)
                 asg p))
           (and (equal (lookup-equal diff asg)
                       (bitxor (car (last (lookup-equal-list xs asg)))
                               (car (last (lookup-equal-list ys asg)))))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (lookup-equal-list xs asg)))
                                       1)
                                (equal (car (last (lookup-equal-list ys asg)))
                                       0))
                           1
                         0))))
  :do-not-induct t
  :use ((:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs)))
                   (y (car (last ys)))
                   (z diff))
        (:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x (car (last xs)))
                   (y (car (last ys)))
                   (z negpos))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars ys)
                   (var (car (last ys))))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance member-equal-of-car-of-last (xs xs))
        (:instance member-equal-of-car-of-last (xs ys)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last)
  :disable bitp)

(defruledl int-msb-xor-constraint-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp z)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal z asg)
                       (bitxor (car (last (lookup-equal-list xs asg)))
                               (car (last (lookup-equal-list ys asg))))))
           (r1cs::r1cs-constraints-holdp
            (boolean-xor-gadget (car (last xs))
                                (car (last ys))
                                z
                                p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-xor-gadget-to-bitxor
                   (x (car (last xs)))
                   (y (car (last ys))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars ys)
                   (var (car (last ys))))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance member-equal-of-car-of-last (xs xs))
        (:instance member-equal-of-car-of-last (xs ys)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :disable bitp)

(defruledl int-msb-and-notright-constraint-holds
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (consp xs)
                (consp ys)
                (symbolp negpos)
                (symbolp one)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ys asg))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (lookup-equal-list xs asg)))
                                       1)
                                (equal (car (last (lookup-equal-list ys asg)))
                                       0))
                           1
                         0)))
           (r1cs::r1cs-constraints-holdp
            (boolean-and-notright-gadget (car (last xs))
                                         (car (last ys))
                                         negpos
                                         one
                                         p)
            asg p))
  :do-not-induct t
  :use ((:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x (car (last xs)))
                   (y (car (last ys)))
                   (z negpos))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars xs)
                   (var (car (last xs))))
        (:instance r1cs::valuation-bindsp-when-valuation-binds-allp
                   (valuation asg)
                   (vars ys)
                   (var (car (last ys))))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance member-equal-of-car-of-last (xs xs))
        (:instance member-equal-of-car-of-last (xs ys)))
  :enable (symbolp-of-car-of-last
           true-listp-when-symbol-listp
           consp-of-last-when-consp-true-listp
           lookup-equal-of-car
           lookup-equal-list-of-last
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :disable bitp)

; The signed ternary constraint, with bits d, z, n, o:
;   (1 - d) * (1 - z - n) = o - n
; holds when o is (1 - z) if d = 0 and n if d = 1.

(defruledl int-signed-lt-ternary-holds
  (implies (and (primep p)
                (< 4 p)
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
           :in-theory (enable pfield::add
                              pfield::mul
                              bitp
                              equal-of-0-and-mod-of-o-minus-1))))

(defruledl int-signed-lt-ternary-constraint-complete
  (implies (and (primep p)
                (< 4 p)
                (symbolp diff)
                (symbolp z)
                (symbolp negpos)
                (symbolp out)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (bitp (lookup-equal diff asg))
                (bitp (lookup-equal z asg))
                (bitp (lookup-equal negpos asg))
                (bitp (lookup-equal out asg))
                (equal (lookup-equal out asg)
                       (if (equal (lookup-equal diff asg) 0)
                           (if (equal (lookup-equal z asg) 0)
                               1
                             0)
                         (lookup-equal negpos asg))))
           (r1cs::r1cs-constraints-holdp
            (list (r1cs::make-r1cs-constraint
                   :a (list (list 1 1)
                            (list (1- p) diff))
                   :b (list (list 1 1)
                            (list (1- p) z)
                            (list (1- p) negpos))
                   :c (list (list 1 out)
                            (list (1- p) negpos))))
            asg p))
  :do-not-induct t
  :use (:instance int-signed-lt-ternary-holds
                  (d (lookup-equal diff asg))
                  (z (lookup-equal z asg))
                  (n (lookup-equal negpos asg))
                  (o (lookup-equal out asg)))
  :enable (r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           r1cs::dot-product))

(defruledl int-r1cs-constraints-holdp-of-nil
  (r1cs::r1cs-constraints-holdp nil valuation prime)
  :enable r1cs::r1cs-constraints-holdp)

(defruledl int-consp-ys-and-zs
  (implies (and (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs)))
           (and (consp ys)
                (consp zs))))

(local
 (defthm int-signed-lt-out-is-selector
  (implies (and (posp n)
                (equal diff (bitxor (car (last (int->lebits x n)))
                                    (car (last (int->lebits y n)))))
                (equal z (if (< (lebits=>nat (int->lebits x n))
                                (lebits=>nat (int->lebits y n)))
                             0
                           1))
                (equal negpos
                       (if (and (equal (car (last (int->lebits x n))) 1)
                                (equal (car (last (int->lebits y n))) 0))
                           1
                         0))
                (equal out (int-signed-less-than-bit x y n)))
           (equal out
                  (if (equal diff 0)
                      (if (equal z 0) 1 0)
                    negpos)))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable int-signed-less-than-bit-is-ternary
                              bitxor-is-sign-diff)))))

(defruledl int-natp-of-len
  (natp (len x)))

(defruledl int->lebits-of-looked-up-unsigned-reading
  (implies (and (natp n)
                (equal bits (int->lebits x n)))
           (equal (int->lebits (lebits=>nat bits) n)
                  bits))
  :enable int->lebits-of-unsigned-reading)

(defruledl bit-listp-of-looked-up-int-bits
  (implies (equal bits (int->lebits x n))
           (bit-listp bits))
  :enable bit-listp-of-int->lebits-explicit)

(defruledl int-valuep-of-looked-up-unsigned-reading
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (equal bits (int->lebits x n)))
           (int-valuep (lebits=>nat bits) nil n))
  :enable int-valuep-of-unsigned-reading)

(local (in-theory (current-theory 'int-compare-before-mod)))

(with-prover-step-limit
 1000000
 (defruled int-is-less-than-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n)
                                       (lebits=>nat (int->lebits x n))
                                       (- (lebits=>nat (int->lebits y n))))
                                    n))
                (equal (lookup-equal z asg)
                       (if (< (lebits=>nat (int->lebits x n))
                              (lebits=>nat (int->lebits y n)))
                           0
                         1))
                (equal (lookup-equal diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (int->lebits x n))) 1)
                                (equal (car (last (int->lebits y n))) 0))
                           1
                         0))
                (equal (lookup-equal out asg)
                       (int-signed-less-than-bit x y n)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p)
                (equal (lookup-equal out asg)
                       (int-is-less-than-spec x y t n))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance int-is-less-than-unsigned-gadget-complete
                            (x (lebits=>nat (int->lebits x n)))
                            (y (lebits=>nat (int->lebits y n))))
                 (:instance int->lebits-of-looked-up-unsigned-reading
                            (n (len xs))
                            (bits (lookup-equal-list xs asg)))
                 (:instance int->lebits-of-looked-up-unsigned-reading
                            (x y)
                            (n (len xs))
                            (bits (lookup-equal-list ys asg)))
                 (:instance bit-listp-of-looked-up-int-bits
                            (n (len xs))
                            (bits (lookup-equal-list xs asg)))
                 (:instance bit-listp-of-looked-up-int-bits
                            (x y)
                            (n (len xs))
                            (bits (lookup-equal-list ys asg)))
                 (:instance int-valuep-of-looked-up-unsigned-reading
                            (n (len xs))
                            (bits (lookup-equal-list xs asg)))
                 (:instance int-valuep-of-looked-up-unsigned-reading
                            (x y)
                            (n (len xs))
                            (bits (lookup-equal-list ys asg)))
                 (:instance int-msb-xor-constraint-holds (z diff))
                 int-msb-and-notright-constraint-holds
                 int-signed-lt-ternary-constraint-complete
                 (:instance int-signed-lt-out-is-selector
                            (n (len xs))
                            (diff (lookup-equal diff asg))
                            (z (lookup-equal z asg))
                            (negpos (lookup-equal negpos asg))
                            (out (lookup-equal out asg)))
                 (:instance int-signed-less-than-bit-is-spec
                            (n (len xs))))
           :in-theory
           (union-theories
            '(int-natp-of-len
              int-is-less-than-signed-gadget
              int-is-less-than-unsigned-gadget
              int-is-less-than-spec
              r1cs::r1cs-constraint-holdsp
              r1cs::dot-product
              int->lebits-of-unsigned-reading
              base-prime-greater-than-4
              bitp-of-bitxor
              acl2::bitp-compound-recognizer
              posp-when-integer-widthp
              int-consp-when-len-equal
              r1cs::r1cs-constraints-holdp-of-append
              r1cs::r1cs-constraints-holdp-of-cons
              int-r1cs-constraints-holdp-of-nil)
            (theory 'minimal-theory))))))

(defruled int-is-less-than-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p))
           (equal (lookup-equal out asg)
                  (int-is-less-than-spec x y t n)))
  :do-not-induct t
  :use ((:instance unsigned-small-lt-gadget-soundness)
        int-consp-ys-and-zs
        (:instance int-signed-lt-sign-wires)
        (:instance int-signed-lt-ternary-constraint-sound)
        (:instance int-signed-lt-wires-are-bit
                   (z (lookup-equal z asg))
                   (diff (lookup-equal diff asg))
                   (negpos (lookup-equal negpos asg))
                   (out (lookup-equal out asg)))
        (:instance int-signed-less-than-bit-is-spec))
  :enable (int-is-less-than-signed-gadget
           int-is-less-than-spec
           int-spec-bool
           int-signed-less-than-bit-is-spec
           int-width-add-fits
           integer-length-of-base-prime
           integer-widthp
           int-valuep
           posp-when-integer-widthp
           bit-listp-of-int->lebits-explicit
           len-of-int->lebits
           lebits=>nat-of-int->lebits
           base-prime-greater-than-4
           int->lebits-consp
           bitxor-is-sign-diff
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :disable (bitp last unsigned-small-lt-gadget
                 boolean-xor-gadget
                 boolean-and-notright-gadget))


(defruled int-is-greater-than-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (consp ys)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p))
           (equal (lookup-equal out asg)
                  (int-is-greater-than-spec x y t n)))
  :do-not-induct t
  :use (:instance int-is-less-than-signed-gadget-sound
                  (xs ys) (ys xs) (x y) (y x))
  :enable (int-is-greater-than-signed-gadget
           int-is-greater-than-spec-is-swapped-lt
           int-is-less-than-spec
           int-is-greater-than-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-greater-than-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (consp ys)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n)
                                       (lebits=>nat (int->lebits y n))
                                       (- (lebits=>nat (int->lebits x n))))
                                    n))
                (equal (lookup-equal z asg)
                       (if (< (lebits=>nat (int->lebits y n))
                              (lebits=>nat (int->lebits x n)))
                           0
                         1))
                (equal (lookup-equal diff asg)
                       (bitxor (car (last (int->lebits y n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (int->lebits y n))) 1)
                                (equal (car (last (int->lebits x n))) 0))
                           1
                         0))
                (equal (lookup-equal out asg)
                       (int-signed-less-than-bit y x n)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p)
                (equal (lookup-equal out asg)
                       (int-is-greater-than-spec x y t n))))
  :do-not-induct t
  :use (:instance int-is-less-than-signed-gadget-complete
                  (xs ys) (ys xs) (x y) (y x))
  :enable (int-is-greater-than-signed-gadget
           int-is-greater-than-spec-is-swapped-lt
           int-is-greater-than-spec
           int-is-less-than-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-greater-than-or-equal-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-or-equal-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p))
           (equal (if (equal (lookup-equal out asg) 0) 1 0)
                  (int-is-greater-than-or-equal-spec x y t n)))
  :do-not-induct t
  :use int-is-less-than-signed-gadget-sound
  :enable (int-is-greater-than-or-equal-signed-gadget
           int-is-greater-than-or-equal-spec-is-not-lt
           int-is-less-than-spec
           int-is-greater-than-or-equal-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-greater-than-or-equal-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n)
                                       (lebits=>nat (int->lebits x n))
                                       (- (lebits=>nat (int->lebits y n))))
                                    n))
                (equal (lookup-equal z asg)
                       (if (< (lebits=>nat (int->lebits x n))
                              (lebits=>nat (int->lebits y n)))
                           0
                         1))
                (equal (lookup-equal diff asg)
                       (bitxor (car (last (int->lebits x n)))
                               (car (last (int->lebits y n)))))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (int->lebits x n))) 1)
                                (equal (car (last (int->lebits y n))) 0))
                           1
                         0))
                (equal (lookup-equal out asg)
                       (int-signed-less-than-bit x y n)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-greater-than-or-equal-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p)
                (equal (if (equal (lookup-equal out asg) 0) 1 0)
                       (int-is-greater-than-or-equal-spec x y t n))))
  :do-not-induct t
  :use int-is-less-than-signed-gadget-complete
  :enable (int-is-greater-than-or-equal-signed-gadget
           int-is-greater-than-or-equal-spec-is-not-lt
           int-is-less-than-spec
           int-is-greater-than-or-equal-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-less-than-or-equal-signed-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (consp ys)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-or-equal-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p))
           (equal (if (equal (lookup-equal out asg) 0) 1 0)
                  (int-is-less-than-or-equal-spec x y t n)))
  :do-not-induct t
  :use (:instance int-is-greater-than-or-equal-signed-gadget-sound
                  (xs ys) (ys xs) (x y) (y x))
  :enable (int-is-less-than-or-equal-signed-gadget
           int-is-less-than-or-equal-spec-is-not-swapped-lt
           int-is-less-than-or-equal-spec
           int-is-greater-than-or-equal-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled int-is-less-than-or-equal-signed-gadget-complete
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp diff)
                (symbolp negpos)
                (symbolp out)
                (symbolp one)
                (equal n (len xs))
                (integer-widthp n)
                (consp xs)
                (consp ys)
                (equal (len ys) n)
                (equal (len zs) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg diff)
                (r1cs::valuation-bindsp asg negpos)
                (r1cs::valuation-bindsp asg out)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (equal (lookup-equal-list zs asg)
                       (int->lebits (+ (expt 2 n)
                                       (lebits=>nat (int->lebits y n))
                                       (- (lebits=>nat (int->lebits x n))))
                                    n))
                (equal (lookup-equal z asg)
                       (if (< (lebits=>nat (int->lebits y n))
                              (lebits=>nat (int->lebits x n)))
                           0
                         1))
                (equal (lookup-equal diff asg)
                       (bitxor (car (last (int->lebits y n)))
                               (car (last (int->lebits x n)))))
                (equal (lookup-equal negpos asg)
                       (if (and (equal (car (last (int->lebits y n))) 1)
                                (equal (car (last (int->lebits x n))) 0))
                           1
                         0))
                (equal (lookup-equal out asg)
                       (int-signed-less-than-bit y x n)))
           (and (r1cs::r1cs-constraints-holdp
                 (int-is-less-than-or-equal-signed-gadget
                  xs ys zs z diff negpos out one p)
                 asg p)
                (equal (if (equal (lookup-equal out asg) 0) 1 0)
                       (int-is-less-than-or-equal-spec x y t n))))
  :do-not-induct t
  :use (:instance int-is-greater-than-or-equal-signed-gadget-complete
                  (xs ys) (ys xs) (x y) (y x))
  :enable (int-is-less-than-or-equal-signed-gadget
           int-is-less-than-or-equal-spec-is-not-swapped-lt
           int-is-less-than-or-equal-spec
           int-is-greater-than-or-equal-spec
           int-spec-bool
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS equivalences.  The unsigned predicate is the field equation
; (1-r)*2^n = 2^n + x - y - s.  Inside the bound 0 <= s < 2^n, with r a
; bit, that equation holds exactly when r is the unsigned less-than bit
; and s is the low half of 2^n + x - y.  It is not the signed spec:
; signed comparison is the sign-bit ternary on the unsigned readings.
; Greater-than swaps the operands.  The or-equal forms read the negation
; of the less-than bit.  Those rewrites are the funspec theorems
; int-is-greater-than-spec-is-swapped-lt,
; int-is-greater-than-or-equal-spec-is-not-lt, and
; int-is-less-than-or-equal-spec-is-not-swapped-lt.
; Every theorem is for every integer-widthp, including 128.

(defrule int-compare-two-widths-below-prime
  (implies (and (equal prime (base-prime))
                (integer-widthp n))
           (< (+ (expt 2 n) (expt 2 n)) prime))
  :hints (("Goal"
           :cases ((equal n 8)
                   (equal n 16)
                   (equal n 32)
                   (equal n 64)
                   (equal n 128))
           :in-theory (enable integer-widthp
                              (:e base-prime)
                              (:e ecurve::edwards-bls12-q)))))

(defrule int-compare-mod-when-inside
  (implies (and (integerp a)
                (integerp p)
                (< 0 p)
                (< (- p) a)
                (< a p))
           (equal (mod a p)
                  (if (< a 0) (+ a p) a)))
  :hints (("Goal"
           :cases ((< a 0))
           :in-theory (e/d (acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(with-prover-step-limit
 400000
 (defruled int-is-less-than-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp r)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n)))
           (equal (int-is-less-than-pred x y r s n2 prime)
                  (and (equal r (int-is-less-than-spec x y nil n))
                       (equal s (if (< x y)
                                    (+ n2 x (- y))
                                  (- x y))))))
  :do-not-induct t
  :hints (("Goal"
           :use int-compare-two-widths-below-prime
           :cases ((< x y) (equal r 0))
           :in-theory (e/d (int-is-less-than-pred
                            int-is-less-than-spec
                            int-spec-bool
                            int-valuep
                            int-min
                            int-max
                            integer-widthp
                            posp-when-integer-widthp
                            pfield::add
                            pfield::mul
                            pfield::neg
                            pfield::sub
                            bitp
                            int-compare-mod-when-inside
                            acl2::mod-when-<
                            acl2::mod-when-<-of-0)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants
                            pfield::add-of-mod-arg1
                            pfield::mod-when-fep))))))

(define int-is-greater-than-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned @('is_greater_than').  Less-than with the operands swapped."
  (pfcs::parse-def
   "int_is_greater_than(x, y, r, s, n2) := {
    (1 - r) * (n2) == (n2 + y - x - s)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-greater-than-circuit)
            :pred int-is-greater-than-pred
            :prime prime)

(define int-is-greater-than-or-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned @('is_greater_than_or_equal').  The result is the high bit."
  (pfcs::parse-def
   "int_is_greater_than_or_equal(x, y, r, s, n2) := {
    (r) * (n2) == (n2 + x - y - s)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-greater-than-or-equal-circuit)
            :pred int-is-greater-than-or-equal-pred
            :prime prime)

(define int-is-less-than-or-equal-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Unsigned @('is_less_than_or_equal').  Greater-than-or-equal
          with the operands swapped."
  (pfcs::parse-def
   "int_is_less_than_or_equal(x, y, r, s, n2) := {
    (r) * (n2) == (n2 + y - x - s)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-less-than-or-equal-circuit)
            :pred int-is-less-than-or-equal-pred
            :prime prime)

(defruled int-is-greater-than-pred-is-swapped-lt
  (equal (int-is-greater-than-pred x y r s n2 prime)
         (int-is-less-than-pred y x r s n2 prime))
  :enable (int-is-greater-than-pred int-is-less-than-pred))

(defruled int-is-greater-than-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp r)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n)))
           (equal (int-is-greater-than-pred x y r s n2 prime)
                  (and (equal r (int-is-greater-than-spec x y nil n))
                       (equal s (if (< y x)
                                    (+ n2 y (- x))
                                  (- y x))))))
  :do-not-induct t
  :enable (int-is-greater-than-pred-is-swapped-lt
           int-is-greater-than-spec-is-swapped-lt
           int-is-greater-than-spec
           int-is-less-than-spec
           int-spec-bool)
  :hints (("Goal"
           :use (:instance int-is-less-than-pred-to-funspec
                           (x y) (y x)))))

(defruled int-is-gte-pred-is-flipped-lt
  (implies (and (equal prime (base-prime))
                (primep prime)
                (bitp r)
                (integerp n2))
           (equal (int-is-greater-than-or-equal-pred x y r s n2 prime)
                  (int-is-less-than-pred x y (if (equal r 0) 1 0) s n2 prime)))
  :enable (int-is-greater-than-or-equal-pred
           int-is-less-than-pred
           pfield::add
           pfield::mul
           pfield::neg
           pfield::sub
           bitp
           int-compare-mod-when-inside)
  :disable (mod floor
            acl2::mod-of-+-of-constant
            acl2::mod-of-minus-arg1
            acl2::equal-of-mod-of-+-when-constants))


(defruled int-is-greater-than-or-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp r)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n)))
           (equal (int-is-greater-than-or-equal-pred x y r s n2 prime)
                  (and (equal r (int-is-greater-than-or-equal-spec x y nil n))
                       (equal s (if (< x y)
                                    (+ n2 x (- y))
                                  (- x y))))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-is-less-than-pred-to-funspec
                            (r (if (equal r 0) 1 0)))
                 (:instance int-is-gte-pred-is-flipped-lt))
           :in-theory (e/d (int-is-greater-than-or-equal-spec-is-not-lt
                            int-is-greater-than-or-equal-spec
                            int-is-less-than-spec
                            int-spec-bool
                            bitp)
                           (int-is-gte-pred-is-flipped-lt
                            int-is-less-than-pred-to-funspec
                            int-is-greater-than-or-equal-pred
                            int-is-less-than-pred)))))

(defruled int-is-less-than-or-equal-pred-is-swapped-gte
  (equal (int-is-less-than-or-equal-pred x y r s n2 prime)
         (int-is-greater-than-or-equal-pred y x r s n2 prime))
  :enable (int-is-less-than-or-equal-pred
           int-is-greater-than-or-equal-pred))


(defruled int-is-less-than-or-equal-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (not signedp)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (bitp r)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n)))
           (equal (int-is-less-than-or-equal-pred x y r s n2 prime)
                  (and (equal r (int-is-less-than-or-equal-spec x y nil n))
                       (equal s (if (< y x)
                                    (+ n2 y (- x))
                                  (- y x))))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-greater-than-or-equal-pred-to-funspec
                           (x y) (y x))
           :in-theory (e/d (int-is-less-than-or-equal-pred-is-swapped-gte
                            int-is-less-than-or-equal-spec-is-not-swapped-lt
                            int-is-less-than-or-equal-spec
                            int-is-greater-than-or-equal-spec
                            int-spec-bool)
                           (int-is-greater-than-or-equal-pred-to-funspec
                            int-is-less-than-or-equal-pred
                            int-is-greater-than-or-equal-pred)))))


(define int-is-less-than-signed-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Signed @('is_less_than').  Unsigned comparison of the bit
          patterns, then the sign-bit ternary."
  (pfcs::parse-def
   "int_is_less_than_signed(xu, yu, r, s, n2, sx, sy, diff, negpos, out, one) := {
    (1 - r) * (n2) == (n2 + xu - yu - s),
    (2 * sx) * (sy) == (sx + sy - diff),
    (sx) * (one - sy) == (negpos),
    (1 - diff) * (r - negpos) == (out - negpos)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-less-than-signed-circuit)
            :pred int-is-less-than-signed-pred
            :prime prime)

(defruled int-spec-unsigned-unsigned-valuep
  (implies (and (integer-widthp n)
                (int-valuep x signedp n))
           (int-valuep (int-spec-unsigned x n) nil n))
  :enable (int-valuep int-min int-max int-spec-unsigned
           integer-widthp posp-when-integer-widthp)
  :disable (mod floor))

(defthmd int-sign-bit-is-bitp
  (implies (and (integer-widthp n)
                (int-valuep x signedp n))
           (bitp (car (last (int->lebits x n)))))
  :hints (("Goal"
           :use ((:instance bitp-of-car-of-last-when-bit-listp
                            (bits (int->lebits x n)))
                 (:instance int->lebits-consp))
           :in-theory (e/d (bit-listp-of-int->lebits-explicit
                            posp-when-integer-widthp
                            integer-widthp)
                           (bitp)))))

(defthmd int-signed-xor-iff
  (implies (and (equal prime (base-prime))
                (primep prime)
                (bitp sx)
                (bitp sy)
                (bitp diff))
           (equal (equal (pfield::mul (pfield::mul (mod 2 prime) sx prime)
                                      sy
                                      prime)
                         (pfield::sub (pfield::add sx sy prime)
                                      diff
                                      prime))
                  (equal diff (if (equal sx sy) 0 1))))
  :hints (("Goal"
           :cases ((equal sx 0) (equal sy 0) (equal diff 0))
           :in-theory (e/d (pfield::add pfield::mul pfield::neg pfield::sub
                            bitp
                            int-compare-mod-when-inside)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defthmd int-signed-and-not-iff
  (implies (and (equal prime (base-prime))
                (primep prime)
                (equal one 1)
                (bitp sx)
                (bitp sy)
                (bitp negpos))
           (equal (equal (pfield::mul sx
                                      (pfield::sub one sy prime)
                                      prime)
                         negpos)
                  (equal negpos
                         (if (and (equal sx 1) (equal sy 0))
                             1
                           0))))
  :hints (("Goal"
           :cases ((equal sx 0) (equal sy 0) (equal negpos 0))
           :in-theory (e/d (pfield::add pfield::mul pfield::neg pfield::sub
                            bitp
                            int-compare-mod-when-inside)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defthmd int-signed-ternary-iff
  (implies (and (equal prime (base-prime))
                (primep prime)
                (bitp diff)
                (bitp r)
                (bitp negpos)
                (bitp out))
           (equal (equal (pfield::mul (pfield::sub (mod 1 prime) diff prime)
                                      (pfield::sub r negpos prime)
                                      prime)
                         (pfield::sub out negpos prime))
                  (equal out (if (equal diff 0) r negpos))))
  :hints (("Goal"
           :cases ((equal diff 0) (equal r 0) (equal negpos 0) (equal out 0))
           :in-theory (e/d (pfield::add pfield::mul pfield::neg pfield::sub
                            bitp
                            int-compare-mod-when-inside)
                           (mod floor
                            acl2::mod-of-+-of-constant
                            acl2::mod-of-minus-arg1
                            acl2::equal-of-mod-of-+-when-constants)))))

(defthm int-signed-out-is-bit
  (implies (and (natp n)
                (equal xu (lebits=>nat (int->lebits x n)))
                (equal yu (lebits=>nat (int->lebits y n)))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (equal r (if (< xu yu) 1 0))
                (equal diff (if (equal sx sy) 0 1))
                (equal negpos (if (and (equal sx 1) (equal sy 0)) 1 0))
                (equal out (if (equal diff 0) r negpos)))
           (equal out (int-signed-less-than-bit x y n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable int-signed-less-than-bit))))

(defthm int-signed-ternary-is-spec
  (implies (and (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (equal r (if (< xu yu) 1 0))
                (equal diff (if (equal sx sy) 0 1))
                (equal negpos (if (and (equal sx 1) (equal sy 0)) 1 0))
                (equal out (if (equal diff 0) r negpos)))
           (equal out (int-is-less-than-spec x y t n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance int-signed-out-is-bit)
                 (:instance int-signed-less-than-bit-is-spec))
           :in-theory (e/d (int-spec-unsigned
                            lebits=>nat-of-int->lebits
                            integer-widthp
                            posp-when-integer-widthp
                            int-valuep)
                           (int-signed-less-than-bit
                            int-is-less-than-spec)))))

(defruled int-is-less-than-signed-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (bitp r)
                (bitp diff)
                (bitp negpos)
                (bitp out)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n))
                (equal one 1))
           (equal (int-is-less-than-signed-pred
                   xu yu r s n2 sx sy diff negpos out one prime)
                  (and (equal r (if (< xu yu) 1 0))
                       (equal s (if (< xu yu)
                                    (+ n2 xu (- yu))
                                  (- xu yu)))
                       (equal diff (if (equal sx sy) 0 1))
                       (equal negpos (if (and (equal sx 1)
                                              (equal sy 0))
                                         1
                                       0))
                       (equal out (if (equal diff 0) r negpos))
                       (equal out (int-is-less-than-spec x y t n)))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-is-less-than-pred-to-funspec
                            (x xu) (y yu) (signedp nil))
                 (:instance int-signed-xor-iff)
                 (:instance int-signed-and-not-iff)
                 (:instance int-signed-ternary-iff)
                 (:instance int-signed-ternary-is-spec)
                 (:instance int-sign-bit-is-bitp (signedp t))
                 (:instance int-sign-bit-is-bitp (x y) (signedp t))
                 (:instance int-spec-unsigned-unsigned-valuep
                            (signedp t))
                 (:instance int-spec-unsigned-unsigned-valuep
                            (x y) (signedp t)))
           :in-theory (union-theories
                       '(int-is-less-than-signed-pred
                         int-is-less-than-pred
                         int-is-less-than-spec
                         int-spec-bool
                         int-spec-unsigned
                         int-valuep
                         int-min
                         int-max
                         bitp
                         ifix
                         natp)
                       (theory 'minimal-theory)))))

(define int-is-greater-than-signed-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Signed @('is_greater_than').  Signed less-than with the operands swapped."
  (pfcs::parse-def
   "int_is_greater_than_signed(xu, yu, r, s, n2, sx, sy, diff, negpos, out, one) := {
    (1 - r) * (n2) == (n2 + yu - xu - s),
    (2 * sy) * (sx) == (sy + sx - diff),
    (sy) * (one - sx) == (negpos),
    (1 - diff) * (r - negpos) == (out - negpos)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-greater-than-signed-circuit)
            :pred int-is-greater-than-signed-pred
            :prime prime)

(define int-is-greater-than-or-equal-signed-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Signed @('is_greater_than_or_equal').  Same constraints as
          signed less-than.  The result boolean is @($1 - \\mathit{out}$)."
  (pfcs::parse-def
   "int_is_greater_than_or_equal_signed(xu, yu, r, s, n2, sx, sy, diff, negpos, out, one) := {
    (1 - r) * (n2) == (n2 + xu - yu - s),
    (2 * sx) * (sy) == (sx + sy - diff),
    (sx) * (one - sy) == (negpos),
    (1 - diff) * (r - negpos) == (out - negpos)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-greater-than-or-equal-signed-circuit)
            :pred int-is-greater-than-or-equal-signed-pred
            :prime prime)

(define int-is-less-than-or-equal-signed-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Signed @('is_less_than_or_equal').  Signed greater-than-or-equal
          with the operands swapped."
  (pfcs::parse-def
   "int_is_less_than_or_equal_signed(xu, yu, r, s, n2, sx, sy, diff, negpos, out, one) := {
    (1 - r) * (n2) == (n2 + yu - xu - s),
    (2 * sy) * (sx) == (sy + sx - diff),
    (sy) * (one - sx) == (negpos),
    (1 - diff) * (r - negpos) == (out - negpos)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-is-less-than-or-equal-signed-circuit)
            :pred int-is-less-than-or-equal-signed-pred
            :prime prime)

(defruled int-is-greater-than-signed-pred-is-swapped-lt
  (equal (int-is-greater-than-signed-pred
          xu yu r s n2 sx sy diff negpos out one prime)
         (int-is-less-than-signed-pred
          yu xu r s n2 sy sx diff negpos out one prime))
  :enable (int-is-greater-than-signed-pred
           int-is-less-than-signed-pred))

(defruled int-is-greater-than-signed-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (bitp r)
                (bitp diff)
                (bitp negpos)
                (bitp out)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n))
                (equal one 1))
           (equal (int-is-greater-than-signed-pred
                   xu yu r s n2 sx sy diff negpos out one prime)
                  (and (equal r (if (< yu xu) 1 0))
                       (equal s (if (< yu xu)
                                    (+ n2 yu (- xu))
                                  (- yu xu)))
                       (equal diff (if (equal sy sx) 0 1))
                       (equal negpos (if (and (equal sy 1)
                                              (equal sx 0))
                                         1
                                       0))
                       (equal out (if (equal diff 0) r negpos))
                       (equal out (int-is-greater-than-spec x y t n)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-less-than-signed-pred-to-funspec
                           (x y) (y x)
                           (xu yu) (yu xu)
                           (sx sy) (sy sx))
           :in-theory (e/d (int-is-greater-than-signed-pred-is-swapped-lt
                            int-is-greater-than-spec-is-swapped-lt
                            int-is-greater-than-spec
                            int-is-less-than-spec
                            int-spec-bool)
                           (int-is-less-than-signed-pred-to-funspec
                            int-is-greater-than-signed-pred
                            int-is-less-than-signed-pred)))))

(defruled int-gte-signed-pred-is-lt
  (equal (int-is-greater-than-or-equal-signed-pred
          xu yu r s n2 sx sy diff negpos out one prime)
         (int-is-less-than-signed-pred
          xu yu r s n2 sx sy diff negpos out one prime))
  :enable (int-is-greater-than-or-equal-signed-pred
           int-is-less-than-signed-pred))

(defruled int-is-greater-than-or-equal-signed-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (bitp r)
                (bitp diff)
                (bitp negpos)
                (bitp out)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n))
                (equal one 1))
           (equal (int-is-greater-than-or-equal-signed-pred
                   xu yu r s n2 sx sy diff negpos out one prime)
                  (and (equal r (if (< xu yu) 1 0))
                       (equal s (if (< xu yu)
                                    (+ n2 xu (- yu))
                                  (- xu yu)))
                       (equal diff (if (equal sx sy) 0 1))
                       (equal negpos (if (and (equal sx 1)
                                              (equal sy 0))
                                         1
                                       0))
                       (equal out (if (equal diff 0) r negpos))
                       (equal (if (equal out 0) 1 0)
                              (int-is-greater-than-or-equal-spec x y t n)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-less-than-signed-pred-to-funspec)
           :in-theory (e/d (int-gte-signed-pred-is-lt
                            int-is-greater-than-or-equal-spec-is-not-lt
                            int-is-greater-than-or-equal-spec
                            int-is-less-than-spec
                            int-spec-bool
                            bitp)
                           (int-is-less-than-signed-pred-to-funspec
                            int-is-greater-than-or-equal-signed-pred
                            int-is-less-than-signed-pred)))))

(defruled int-lte-signed-pred-is-swapped-gte
  (equal (int-is-less-than-or-equal-signed-pred
          xu yu r s n2 sx sy diff negpos out one prime)
         (int-is-greater-than-or-equal-signed-pred
          yu xu r s n2 sy sx diff negpos out one prime))
  :enable (int-is-less-than-or-equal-signed-pred
           int-is-greater-than-or-equal-signed-pred))

(defruled int-is-less-than-or-equal-signed-pred-to-funspec
  (implies (and (equal prime (base-prime))
                (primep prime)
                (integer-widthp n)
                (int-valuep x t n)
                (int-valuep y t n)
                (equal xu (int-spec-unsigned x n))
                (equal yu (int-spec-unsigned y n))
                (equal sx (car (last (int->lebits x n))))
                (equal sy (car (last (int->lebits y n))))
                (bitp r)
                (bitp diff)
                (bitp negpos)
                (bitp out)
                (natp s)
                (< s (expt 2 n))
                (equal n2 (expt 2 n))
                (equal one 1))
           (equal (int-is-less-than-or-equal-signed-pred
                   xu yu r s n2 sx sy diff negpos out one prime)
                  (and (equal r (if (< yu xu) 1 0))
                       (equal s (if (< yu xu)
                                    (+ n2 yu (- xu))
                                  (- yu xu)))
                       (equal diff (if (equal sy sx) 0 1))
                       (equal negpos (if (and (equal sy 1)
                                              (equal sx 0))
                                         1
                                       0))
                       (equal out (if (equal diff 0) r negpos))
                       (equal (if (equal out 0) 1 0)
                              (int-is-less-than-or-equal-spec x y t n)))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-is-greater-than-or-equal-signed-pred-to-funspec
                           (x y) (y x)
                           (xu yu) (yu xu)
                           (sx sy) (sy sx))
           :in-theory (e/d (int-lte-signed-pred-is-swapped-gte
                            int-is-less-than-or-equal-spec-is-not-swapped-lt
                            int-is-less-than-or-equal-spec
                            int-is-greater-than-or-equal-spec
                            int-spec-bool
                            bitp)
                           (int-is-greater-than-or-equal-signed-pred-to-funspec
                            int-is-less-than-or-equal-signed-pred
                            int-is-greater-than-or-equal-signed-pred)))))
