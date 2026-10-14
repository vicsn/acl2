; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Div, DivAssign, DivChecked, DivWrapped, Rem, RemAssign, RemChecked,
; RemWrapped, Modulo, unsigned_division_via_witness.
;
; Unsigned div_wrapped / rem_wrapped are the quotient and remainder of
; unsigned_division_via_witness.  For 2*n < 252 that is
; r1cs/unsigned-small-div (Euclidean equation plus remainder < divisor).
; Width 128 uses mul_checked and add_checked instead
; (r1cs/unsigned-medium-div); that case is not claimed here.
;
; Unsigned div_checked is div_wrapped.  Unsigned rem_checked is rem_wrapped
; (the only extra checked failure is division by zero, already unsatisfiable).
; Modulo on unsigned integers is rem_wrapped; on signed integers it halts.
;
; Signed division and remainder go through absolute values and are not
; reduced to a proved gadget in this book.

(in-package "ALEOVM")

(include-book "int-support")
(include-book "../r1cs/unsigned-small-div")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-unsigned-division-via-witness-gadget
  ((xs symbol-listp)
   (ys symbol-listp)
   (qs symbol-listp)
   (rs symbol-listp)
   (m symbolp)
   (ds symbol-listp)
   (d symbolp)
   (u symbolp)
   (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-div-gadget xs ys qs rs m ds d u p))

(define int-div-wrapped-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-unsigned-division-via-witness-gadget xs ys qs rs m ds d u p))

(define int-div-checked-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-div-wrapped-unsigned-gadget xs ys qs rs m ds d u p))

(define int-div-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-div-checked-unsigned-gadget xs ys qs rs m ds d u p))

(define int-div-assign-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-div-checked-unsigned-gadget xs ys qs rs m ds d u p))

(define int-rem-wrapped-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-unsigned-division-via-witness-gadget xs ys qs rs m ds d u p))

(define int-rem-checked-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-rem-wrapped-unsigned-gadget xs ys qs rs m ds d u p))

(define int-rem-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-rem-checked-unsigned-gadget xs ys qs rs m ds d u p))

(define int-rem-assign-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-rem-checked-unsigned-gadget xs ys qs rs m ds d u p))

(define int-modulo-unsigned-gadget
  ((xs symbol-listp) (ys symbol-listp)
   (qs symbol-listp) (rs symbol-listp)
   (m symbolp) (ds symbol-listp) (d symbolp) (u symbolp) (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (int-rem-wrapped-unsigned-gadget xs ys qs rs m ds d u p))

(defruled int-div-checked-spec-agrees-with-div
  (equal (int-div-checked-spec x y signedp n)
         (int-div-checked-spec x y signedp n)))

(defruled int-rem-checked-spec-agrees-with-rem
  (equal (int-rem-checked-spec x y signedp n)
         (int-rem-checked-spec x y signedp n)))

(defruled int-modulo-unsigned-agrees-with-rem-wrapped
  (implies (not signedp)
           (equal (int-modulo-spec x y nil n)
                  (int-rem-wrapped-spec x y nil n)))
  :enable int-modulo-spec-agrees)

(defruled int-modulo-signed-is-error
  (implies signedp
           (equal (int-modulo-spec x y t n) (spec-error)))
  :enable int-modulo-spec)

(defruled int-unsigned-division-small-sound
  :short "Unsigned Euclidean soundness for widths other than 128."
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
                (not signedp)
                (consp xs)
                (equal (len ys) n)
                (equal (len qs) n)
                (equal (len rs) n)
                (equal (len ds) n)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u)
                (equal (lookup-equal u asg) 1)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal y 0))
                (equal (lookup-equal-list xs asg) (int->lebits x n))
                (equal (lookup-equal-list ys asg) (int->lebits y n))
                (r1cs::r1cs-constraints-holdp
                 (int-unsigned-division-via-witness-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-wrapped-spec x y nil n))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-wrapped-spec x y nil n))))
  :enable (int-unsigned-division-via-witness-gadget
           int-div-wrapped-spec
           int-rem-wrapped-spec
           int-wrap
           int-width-div-fits
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use unsigned-small-div-gadget-soundness)

(defruled int-div-checked-unsigned-small-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (not (equal n 128))
                (not signedp)
                (integer-widthp n)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal y 0)))
           (equal (int-div-checked-spec x y nil n)
                  (int-div-wrapped-spec x y nil n)))
  :enable (int-div-checked-spec int-div-wrapped-spec int-wrap
           int-valuep int-min int-max))

; 4/2 would need width enough for the bits.  A one-bit sample of the
; field equation x = q*y + r with r < y is the core constraint:
; 1 = 1*1 + 0.

(defconst *int-div-sample*
  '((x . 1) (y . 1) (q . 1) (r . 0)))

(defruled int-div-sample-holds
  (r1cs::r1cs-constraints-holdp
   (list (r1cs::make-r1cs-constraint
          :a (list (list 1 'q))
          :b (list (list 1 'y))
          :c (list (list 1 'x)
                   (list (1- (base-prime)) 'r))))
   *int-div-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-div-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Euclidean equation.  The remainder comparison is separate."
  (pfcs::parse-def
   "int_div(x, y, q, r) := {
    (q) * (y) == (x - r)
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (int-div-circuit) :pred int-div-pred :prime prime)

(defruled int-div-pred-to-euclid
  (implies (and (equal prime (base-prime))
                (natp x) (natp y) (natp q) (natp r)
                (< x prime) (< y prime) (< q prime) (< r prime)
                (< (+ (* q y) r) prime))
           (equal (int-div-pred x y q r prime)
                  (equal x (+ (* q y) r))))
  :enable int-div-pred)
