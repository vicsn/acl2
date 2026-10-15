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

(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))

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

(defthm int-div-checked-spec-agrees-with-div
  (equal (int-div-checked-spec x y signedp n)
         (int-div-checked-spec x y signedp n))
  :rule-classes nil)

(defthm int-rem-checked-spec-agrees-with-rem
  (equal (int-rem-checked-spec x y signedp n)
         (int-rem-checked-spec x y signedp n))
  :rule-classes nil)

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
                       (int-rem-wrapped-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :enable (int-unsigned-division-via-witness-gadget
           int-div-wrapped-spec
           int-rem-wrapped-spec
           int-wrap
           int-valuep
           int-min
           int-max
           integer-widthp
           integer-length-of-base-prime
           int-width-div-fits
           posp-when-integer-widthp
           lebits=>nat-of-int->lebits
           bit-listp-of-int->lebits-explicit)
  :use (unsigned-small-div-gadget-soundness
        unsigned-small-div-gadget-euclidian))

(defruled int-rem-checked-unsigned-agrees
  :short "For a nonzero unsigned divisor the checked remainder is the wrapped one."
  (implies (and (integer-widthp n)
                (int-valuep x nil n)
                (int-valuep y nil n)
                (not (equal y 0)))
           (equal (int-rem-checked-spec x y nil n)
                  (int-rem-wrapped-spec x y nil n)))
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-rem-checked-spec
                            int-rem-wrapped-spec
                            integer-widthp
                            int-valuep
                            int-min
                            int-max)
                           (truncate)))))

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
  :do-not-induct t
  :hints (("Goal"
           :in-theory (e/d (int-div-checked-spec
                            int-div-wrapped-spec
                            int-wrap
                            integer-widthp
                            int-valuep
                            int-min
                            int-max)
                           (truncate)))))

(defruled int-div-wrapped-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-div-wrapped-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-wrapped-spec x y nil n))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-wrapped-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use (:instance int-unsigned-division-small-sound (signedp nil))
  :enable int-div-wrapped-unsigned-gadget)

(defruled int-div-checked-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-div-checked-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-checked-spec x y nil n))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use (int-div-wrapped-unsigned-gadget-sound
        (:instance int-div-checked-unsigned-small-sound (signedp nil))
        int-rem-checked-unsigned-agrees)
  :enable int-div-checked-unsigned-gadget)

(defruled int-div-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-div-unsigned-gadget xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-checked-spec x y nil n))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use int-div-checked-unsigned-gadget-sound
  :enable int-div-unsigned-gadget)

(defruled int-div-assign-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-div-assign-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list qs asg))
                       (int-div-checked-spec x y nil n))
                (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use int-div-checked-unsigned-gadget-sound
  :enable int-div-assign-unsigned-gadget)

(defruled int-rem-wrapped-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-rem-wrapped-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-wrapped-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use (:instance int-unsigned-division-small-sound (signedp nil))
  :enable int-rem-wrapped-unsigned-gadget)

(defruled int-rem-checked-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-rem-checked-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use (int-rem-wrapped-unsigned-gadget-sound
        int-rem-checked-unsigned-agrees)
  :enable int-rem-checked-unsigned-gadget)

(defruled int-rem-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-rem-unsigned-gadget xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use int-rem-checked-unsigned-gadget-sound
  :enable int-rem-unsigned-gadget)

(defruled int-rem-assign-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-rem-assign-unsigned-gadget
                  xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-rem-checked-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use int-rem-checked-unsigned-gadget-sound
  :enable int-rem-assign-unsigned-gadget)

(defruled int-modulo-unsigned-gadget-sound
  (implies (and (equal p (base-prime))
                (primep p)
                (symbol-listp xs) (symbol-listp ys)
                (symbol-listp qs) (symbol-listp rs)
                (symbolp m) (symbol-listp ds) (symbolp d) (symbolp u)
                (equal n (len xs))
                (integer-widthp n)
                (not (equal n 128))
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
                 (int-modulo-unsigned-gadget xs ys qs rs m ds d u p)
                 asg p))
           (and (equal (lebits=>nat (lookup-equal-list rs asg))
                       (int-modulo-spec x y nil n))
                (< (lebits=>nat (lookup-equal-list rs asg))
                   (lebits=>nat (lookup-equal-list ys asg)))))
  :do-not-induct t
  :use (int-rem-wrapped-unsigned-gadget-sound
        (:instance int-modulo-unsigned-agrees-with-rem-wrapped
                   (signedp nil)
                   (n (len xs))))
  :enable (int-modulo-unsigned-gadget
           int-modulo-spec))

; One-bit witness of unsigned-small-div: 1 = 1*1 + 0, and
; 2^1 + 0 - 1 = 1 so the less-than low bit is 1 and the high bit is 0.
; The zero-unit variable on that high bit is 1.

(defconst *int-unsigned-div-sample*
  '((x0 . 1) (y0 . 1) (q0 . 1) (r0 . 0)
    (m . 1) (d0 . 1) (d . 0) (u . 1)))

(defruled int-unsigned-division-sample-holds
  (r1cs::r1cs-constraints-holdp
   (int-unsigned-division-via-witness-gadget
    '(x0) '(y0) '(q0) '(r0) 'm '(d0) 'd 'u (base-prime))
   *int-unsigned-div-sample*
   (base-prime))
  :hints (("Goal" :in-theory (enable (:e ecurve::edwards-bls12-q)
                                     (:e base-prime)
                                     int-unsigned-division-via-witness-gadget
                                     unsigned-small-div-gadget
                                     boolean-check-gadget-list
                                     boolean-check-gadget
                                     bits-mul-field-gadget
                                     pow2sum-vector
                                     field-bits-add-bits-gadget
                                     unsigned-small-lt-gadget
                                     unsigned-small-lt-vector
                                     pow2sum-neg-prime-vector
                                     vector-neg-prime
                                     zero-unit-gadget
                                     r1cs::r1cs-constraints-holdp
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::dot-product
                                     lookup-equal))))

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

(local
 (defthm int-div-reconstruct
   (implies (and (natp x) (natp r) (natp prod)
                 (posp p)
                 (< x p) (< r p)
                 (< (+ prod r) p)
                 (equal prod (mod (- x r) p)))
            (equal x (+ prod r)))
   :rule-classes nil
   :hints (("Goal"
            :cases ((< x r))
            :do-not-induct t
            :in-theory (disable mod floor))
           ("Subgoal 1"
            :use (:instance acl2::mod-when-<-of-0
                            (x (- x r))
                            (y p))
            :in-theory (disable mod floor acl2::mod-when-<-of-0))
           ("Subgoal 2"
            :use (:instance acl2::mod-when-<
                            (x (- x r))
                            (y p))
            :in-theory (disable mod floor acl2::mod-when-<)))))

(defruled int-div-pred-to-euclid
  (implies (and (equal prime (base-prime))
                (natp x) (natp y) (natp q) (natp r)
                (< x prime) (< y prime) (< q prime) (< r prime)
                (< (+ (* q y) r) prime))
           (equal (int-div-pred x y q r prime)
                  (equal x (+ (* q y) r))))
  :do-not-induct t
  :hints (("Goal"
           :use (:instance int-div-reconstruct
                           (prod (* q y))
                           (p prime))
           :in-theory (e/d (int-div-pred
                            pfield::mul
                            pfield::add
                            pfield::neg)
                           (floor mod)))))
