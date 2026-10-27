; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pedersen hash_uncompressed, commit_uncompressed and commit
; (circuit/algorithms/src/pedersen) on variable input bits, against
; fun-specs/hash-pedersen.lisp.
;
; The bases are circuit constants, so Group::ternary(bit, base, zero) is a
; pair of linear combinations (Field::ternary with constant operands):
;   x = Bx b,   y = 1 + (By - 1) b.
; Padding bits are constant false, so their terms are the constant zero, and
; Group::add with a constant zero operand returns the other operand without
; constraints.  The fold starts from the constant zero, so the first term is
; the accumulator for free; every later term costs one Group::add with
; this = term (the non-constant `other`) and that = accumulator:
;   (tx + ty) (ax + ay) = u      tx ay = v0      ax ty = v1      v0 v1 = v01
;   x3 (1 + d v01) = v0 + v1     y3 (1 - d v01) = u - v0 - v1    (a = -1)
; commit_uncompressed then runs Scalar::to_bits_le on the randomizer
; (scalar-write-bits-le-gadget, 251 bits) and folds the random-base terms
; onto the hash.  If the input is empty the hash is the constant zero, and
; the first randomizer term is again free.  commit is the x-coordinate of
; commit_uncompressed (no constraints).

(in-package "ALEOVM")

(include-book "hped-lc")
(include-book "scalar-write-bits-r1cs")
(include-book "crv-add-complete")
(include-book "../fun-specs/hash-pedersen")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable (:e hped-lc-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gadgets.

(define hped-ped-term-x (base b)
  :verify-guards nil
  :short "x-coordinate of @('Group::ternary(b, base, zero)')."
  (hped-lc-scale (ecurve::point-finite->x base) (hped-lc-v b)))

(define hped-ped-term-y (base b)
  :verify-guards nil
  :short "y-coordinate of @('Group::ternary(b, base, zero)')."
  (hped-lc-add (hped-lc-1)
               (hped-lc-scale (pfield::sub (ecurve::point-finite->y base) 1 (base-prime))
                              (hped-lc-v b))))

(define hped-ped-add-gadget (tx ty ax ay ws)
  :verify-guards nil
  :short "@('Group::add') of the term @('(tx, ty)') and the accumulator
          @('(ax, ay)'); @('ws') is @('(u v0 v1 v01 x3 y3)')."
  (b* ((d (ecurve::edwards-bls12-d))
       (u (nth 0 ws)) (v0 (nth 1 ws)) (v1 (nth 2 ws))
       (v01 (nth 3 ws)) (x3 (nth 4 ws)) (y3 (nth 5 ws))
       (dv (hped-lc-scale d (hped-lc-v v01))))
    (list (hped-c (hped-lc-add tx ty) (hped-lc-add ax ay) (hped-lc-v u))
          (hped-c tx ay (hped-lc-v v0))
          (hped-c ax ty (hped-lc-v v1))
          (hped-c (hped-lc-v v0) (hped-lc-v v1) (hped-lc-v v01))
          (hped-c (hped-lc-v x3) (hped-lc-add (hped-lc-1) dv)
                  (hped-lc-add (hped-lc-v v0) (hped-lc-v v1)))
          (hped-c (hped-lc-v y3) (hped-lc-sub (hped-lc-1) dv)
                  (hped-lc-sub (hped-lc-sub (hped-lc-v u) (hped-lc-v v0))
                               (hped-lc-v v1))))))

(define hped-ped-fold-gadget (bits bases wss ax ay)
  :verify-guards nil
  :short "Fold @('acc + ternary(bit, base, zero)') over variable bits,
          from a non-constant accumulator."
  (if (endp bits)
      nil
    (b* ((ws (car wss)))
      (append (hped-ped-add-gadget (hped-ped-term-x (car bases) (car bits))
                                   (hped-ped-term-y (car bases) (car bits))
                                   ax ay ws)
              (hped-ped-fold-gadget (cdr bits) (cdr bases) (cdr wss)
                                    (hped-lc-v (nth 4 ws))
                                    (hped-lc-v (nth 5 ws)))))))

(define hped-ped-fold-out (bits wss ax ay)
  :verify-guards nil
  :short "The accumulator after the fold, as @('(x . y)') linear combinations."
  (if (endp bits)
      (cons ax ay)
    (hped-ped-fold-out (cdr bits) (cdr wss)
                       (hped-lc-v (nth 4 (car wss)))
                       (hped-lc-v (nth 5 (car wss))))))

(define hped-ped-from-zero-gadget (bits bases wss)
  :verify-guards nil
  :short "The fold from the constant zero: the first term is free."
  (if (endp bits)
      nil
    (hped-ped-fold-gadget (cdr bits) (cdr bases) wss
                          (hped-ped-term-x (car bases) (car bits))
                          (hped-ped-term-y (car bases) (car bits)))))

(define hped-ped-from-zero-out (bits bases wss)
  :verify-guards nil
  (if (endp bits)
      (cons nil (hped-lc-1))
    (hped-ped-fold-out (cdr bits) wss
                       (hped-ped-term-x (car bases) (car bits))
                       (hped-ped-term-y (car bases) (car bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wire bookkeeping.

(define hped-ped-ws-okp (wss n asg)
  :verify-guards nil
  :short "The first @('n') wire tuples are six bound symbols each."
  (if (zp n)
      t
    (and (consp wss)
         (symbol-listp (car wss))
         (equal (len (car wss)) 6)
         (r1cs::valuation-binds-allp asg (car wss))
         (hped-ped-ws-okp (cdr wss) (1- n) asg))))

(defruledl hped-ped-nth-wire
  (implies (and (symbol-listp w)
                (r1cs::valuation-binds-allp asg w)
                (natp n)
                (< n (len w)))
           (and (symbolp (nth n w))
                (r1cs::valuation-bindsp asg (nth n w))))
  :induct (nth n w)
  :enable (nth r1cs::valuation-binds-allp))

(defruledl hped-ped-car-wire
  (implies (and (symbol-listp w)
                (r1cs::valuation-binds-allp asg w)
                (consp w))
           (and (symbolp (car w))
                (r1cs::valuation-bindsp asg (car w))))
  :enable r1cs::valuation-binds-allp)

(defruledl hped-ped-dot-of-nil
  (equal (r1cs::dot-product nil asg p) 0)
  :enable r1cs::dot-product)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group facts.

(defruledl hped-ped-primep
  (primep (base-prime)))

(defruledl hped-ped-coords
  (implies (ecurve::edwards-bls12-pointp pt)
           (and (pfield::fep (ecurve::point-finite->x pt) (base-prime))
                (pfield::fep (ecurve::point-finite->y pt) (base-prime))
                (equal (ecurve::point-finite (ecurve::point-finite->x pt)
                                             (ecurve::point-finite->y pt))
                       pt)))
  :use ((:instance crv-fep-of-edwards-bls12-coords (p (base-prime)))
        hped-ped-primep
        (:instance ecurve::point-on-twisted-edwards-is-finite
                   (ecurve::point pt) (ecurve::curve (ecurve::edwards-bls12-curve))))
  :enable (ecurve::edwards-bls12-pointp ecurve::point-finite-of-point-finite->x/y))

(define hped-ped-term-point (base b)
  :verify-guards nil
  (if (equal b 1) base (ecurve::twisted-edwards-zero)))

(defruledl hped-ped-pointp-of-zero
  (ecurve::edwards-bls12-pointp (ecurve::twisted-edwards-zero))
  :enable (ecurve::edwards-bls12-pointp))

(defruledl hped-ped-step-eq
  (implies (and (ecurve::edwards-bls12-pointp acc)
                (ecurve::edwards-bls12-pointp base))
           (equal (ecurve::edwards-bls12-add (hped-ped-term-point base b) acc)
                  (if (equal b 1) (ecurve::edwards-bls12-add acc base) acc)))
  :enable (hped-ped-term-point ecurve::edwards-bls12-add ecurve::edwards-bls12-pointp
           ecurve::point-fix-when-pointp))

(defruledl hped-ped-dot-of-term
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbolp b)
                (r1cs::valuation-bindsp asg b)
                (bitp (lookup-equal b asg))
                (ecurve::edwards-bls12-pointp base))
           (b* ((tp (hped-ped-term-point base (lookup-equal b asg))))
             (and (equal (r1cs::dot-product (hped-ped-term-x base b) asg (base-prime))
                         (ecurve::point-finite->x tp))
                  (equal (r1cs::dot-product (hped-ped-term-y base b) asg (base-prime))
                         (ecurve::point-finite->y tp)))))
  :do-not-induct t
  :use (hped-ped-primep (:instance hped-ped-coords (pt base)))
  :cases ((equal (lookup-equal b asg) 1))
  :enable (hped-ped-term-x hped-ped-term-y hped-ped-term-point bitp
           pfield::fep ecurve::twisted-edwards-zero))

(defruledl hped-ped-pointp-of-term
  (implies (ecurve::edwards-bls12-pointp base)
           (ecurve::edwards-bls12-pointp (hped-ped-term-point base b)))
  :enable (hped-ped-term-point hped-ped-pointp-of-zero))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(defruled hped-ped-add-gadget-sound
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbol-listp ws)
                (equal (len ws) 6)
                (r1cs::valuation-binds-allp asg ws)
                (ecurve::edwards-bls12-pointp tp)
                (ecurve::edwards-bls12-pointp acc)
                (equal (r1cs::dot-product tx asg (base-prime)) (ecurve::point-finite->x tp))
                (equal (r1cs::dot-product ty asg (base-prime)) (ecurve::point-finite->y tp))
                (equal (r1cs::dot-product ax asg (base-prime)) (ecurve::point-finite->x acc))
                (equal (r1cs::dot-product ay asg (base-prime)) (ecurve::point-finite->y acc))
                (r1cs::r1cs-constraints-holdp (hped-ped-add-gadget tx ty ax ay ws)
                                              asg (base-prime)))
           (equal (ecurve::point-finite (lookup-equal (nth 4 ws) asg)
                                        (lookup-equal (nth 5 ws) asg))
                  (ecurve::edwards-bls12-add tp acc)))
  :do-not-induct t
  :use (hped-ped-primep
        (:instance hped-ped-coords (pt tp))
        (:instance hped-ped-coords (pt acc))
        (:instance crv-group-add-from-equations
                   (p (base-prime)) (p1 tp) (p2 acc)
                   (x1 (ecurve::point-finite->x tp)) (y1 (ecurve::point-finite->y tp))
                   (x2 (ecurve::point-finite->x acc)) (y2 (ecurve::point-finite->y acc))
                   (u (lookup-equal (nth 0 ws) asg)) (v0 (lookup-equal (nth 1 ws) asg))
                   (v1 (lookup-equal (nth 2 ws) asg)) (v01 (lookup-equal (nth 3 ws) asg))
                   (x3 (lookup-equal (nth 4 ws) asg)) (y3 (lookup-equal (nth 5 ws) asg))))
  :in-theory (union-theories
              '(hped-ped-add-gadget
                r1cs::r1cs-constraints-holdp-of-cons
                hped-holdsp-of-c hped-dot-of-lc-v hped-dot-of-lc-1 hped-dot-of-lc-add
                hped-dot-of-lc-scale hped-dot-of-lc-sub
                hped-ped-nth-wire r1cs::fep-of-lookup-equal
                (:e len) (:e nth) (:e <) (:e natp) (:e base-prime)
                (:e ecurve::edwards-bls12-d) (:e pfield::fep)
                r1cs::r1cs-constraints-holdp)
              (theory 'minimal-theory)))

(defrulel hped-ped-coords-of-equal
  (implies (and (equal (ecurve::point-finite a b) pt)
                (natp a) (natp b))
           (and (equal a (ecurve::point-finite->x pt))
                (equal b (ecurve::point-finite->y pt))))
  :rule-classes nil)

(defmacro hped-ped-fold-hyps ()
  '(and (r1cs::r1cs-valuationp asg (base-prime))
        (symbol-listp bits)
        (r1cs::valuation-binds-allp asg bits)
        (bit-listp (lookup-equal-list bits asg))
        (hped-ped-r-point-listp bases)
        (<= (len bits) (len bases))
        (hped-ped-ws-okp wss (len bits) asg)
        (ecurve::edwards-bls12-r-pointp acc)
        (equal (r1cs::dot-product ax asg (base-prime)) (ecurve::point-finite->x acc))
        (equal (r1cs::dot-product ay asg (base-prime)) (ecurve::point-finite->y acc))))

(defmacro hped-ped-next-acc ()
  '(if (equal (lookup-equal (car bits) asg) 1)
       (ecurve::edwards-bls12-add acc (car bases))
     acc))

(defruledl hped-ped-fold-step-sound
  (implies (and (hped-ped-fold-hyps)
                (consp bits)
                (r1cs::r1cs-constraints-holdp (hped-ped-fold-gadget bits bases wss ax ay)
                                              asg (base-prime)))
           (b* ((ws (car wss))
                (acc1 (hped-ped-next-acc)))
             (and (ecurve::edwards-bls12-r-pointp acc1)
                  (equal (r1cs::dot-product (hped-lc-v (nth 4 ws)) asg (base-prime))
                         (ecurve::point-finite->x acc1))
                  (equal (r1cs::dot-product (hped-lc-v (nth 5 ws)) asg (base-prime))
                         (ecurve::point-finite->y acc1))
                  (r1cs::r1cs-constraints-holdp
                   (hped-ped-fold-gadget (cdr bits) (cdr bases) (cdr wss)
                                         (hped-lc-v (nth 4 ws)) (hped-lc-v (nth 5 ws)))
                   asg (base-prime)))))
  :do-not-induct t
  :use (hped-ped-primep
        (:instance hped-ped-add-gadget-sound
                   (ws (car wss))
                   (tx (hped-ped-term-x (car bases) (car bits)))
                   (ty (hped-ped-term-y (car bases) (car bits)))
                   (tp (hped-ped-term-point (car bases) (lookup-equal (car bits) asg))))
        (:instance hped-ped-dot-of-term (b (car bits)) (base (car bases)))
        (:instance hped-ped-pointp-of-term (b (lookup-equal (car bits) asg))
                   (base (car bases)))
        (:instance hped-ped-step-eq (b (lookup-equal (car bits) asg)) (base (car bases)))
        (:instance hped-ped-car-wire (w bits))
        (:instance hped-ped-nth-wire (w (car wss)) (n 4))
        (:instance hped-ped-nth-wire (w (car wss)) (n 5))
        (:instance hped-ped-coords-of-equal
                   (a (lookup-equal (nth 4 (car wss)) asg))
                   (b (lookup-equal (nth 5 (car wss)) asg))
                   (pt (hped-ped-next-acc))))
  :enable (hped-ped-fold-gadget hped-ped-ws-okp lookup-equal-list
           hped-ped-r-point-listp r1cs::valuation-binds-allp
           r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type)
  :disable (hped-ped-add-gadget hped-ped-term-x hped-ped-term-y hped-ped-step-eq
            hped-ped-dot-of-term hped-ped-pointp-of-term))

(defun hped-ped-fold-ind (bits bases wss ax ay acc asg)
  (declare (xargs :verify-guards nil))
  (if (endp bits)
      (list bases wss ax ay acc asg)
    (hped-ped-fold-ind (cdr bits) (cdr bases) (cdr wss)
                       (hped-lc-v (nth 4 (car wss)))
                       (hped-lc-v (nth 5 (car wss)))
                       (hped-ped-next-acc)
                       asg)))

(defruled hped-ped-fold-gadget-sound
  (implies (and (hped-ped-fold-hyps)
                (r1cs::r1cs-constraints-holdp (hped-ped-fold-gadget bits bases wss ax ay)
                                              asg (base-prime)))
           (b* ((out (hped-ped-fold-out bits wss ax ay)))
             (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                          (r1cs::dot-product (cdr out) asg (base-prime)))
                    (hped-ped-sum (lookup-equal-list bits asg) bases acc))))
  :induct (hped-ped-fold-ind bits bases wss ax ay acc asg)
  :hints (("Subgoal *1/1" :use hped-ped-fold-sound-base
           :expand ((hped-ped-fold-out bits wss ax ay)
                    (lookup-equal-list bits asg)
                    (hped-ped-sum nil bases acc)))
          ("Subgoal *1/2" :use hped-ped-fold-step-sound
           :expand ((hped-ped-fold-out bits wss ax ay)
                    (lookup-equal-list bits asg)
                    (hped-ped-ws-okp wss (len bits) asg)
                    (hped-ped-r-point-listp bases)
                    (r1cs::valuation-binds-allp asg bits))
           :in-theory (disable hped-ped-fold-step-sound hped-ped-fold-gadget)))
  :enable (hped-ped-sum hped-ped-fold-out lookup-equal-list)
  :prep-lemmas
  ((defrule hped-ped-fold-sound-base
     (implies (and (ecurve::edwards-bls12-r-pointp acc)
                   (equal (r1cs::dot-product ax asg (base-prime)) (ecurve::point-finite->x acc))
                   (equal (r1cs::dot-product ay asg (base-prime)) (ecurve::point-finite->y acc)))
              (equal (ecurve::point-finite (r1cs::dot-product ax asg (base-prime))
                                           (r1cs::dot-product ay asg (base-prime)))
                     acc))
     :use (:instance hped-ped-coords (pt acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Padding and the free first term.

(defruledl hped-ped-pointp-when-r-pointp
  (implies (ecurve::edwards-bls12-r-pointp pt)
           (ecurve::edwards-bls12-pointp pt))
  :enable ecurve::edwards-bls12-r-pointp)

(defruledl hped-ped-add-zero-left
  (implies (ecurve::edwards-bls12-pointp pt)
           (equal (ecurve::edwards-bls12-add (ecurve::twisted-edwards-zero) pt)
                  pt))
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-pointp))

(defruledl hped-ped-r-pointp-of-term
  (implies (ecurve::edwards-bls12-r-pointp base)
           (ecurve::edwards-bls12-r-pointp (hped-ped-term-point base b)))
  :enable hped-ped-term-point)

(defun hped-ped-zeros-ind (n bases acc)
  (if (or (zp n) (endp bases))
      acc
    (hped-ped-zeros-ind (1- n) (cdr bases) acc)))

(defruledl hped-ped-sum-of-zeros
  (equal (hped-ped-sum (repeat n 0) bases acc) acc)
  :induct (hped-ped-zeros-ind n bases acc)
  :enable (hped-ped-sum repeat))

(defruledl hped-ped-sum-of-append
  (implies (<= (len a) (len bases))
           (equal (hped-ped-sum (append a b) bases acc)
                  (hped-ped-sum b (nthcdr (len a) bases) (hped-ped-sum a bases acc))))
  :induct (hped-ped-sum a bases acc)
  :expand ((nthcdr (len a) bases))
  :enable (hped-ped-sum))

(defruledl hped-ped-sum-of-pad
  (implies (<= (len input) (len bases))
           (equal (hped-ped-sum (hped-ped-pad input n) bases acc)
                  (hped-ped-sum input bases acc)))
  :enable (hped-ped-pad hped-ped-sum-of-append hped-ped-sum-of-zeros))

(defmacro hped-ped-zero-hyps ()
  '(and (r1cs::r1cs-valuationp asg (base-prime))
        (symbol-listp bits)
        (r1cs::valuation-binds-allp asg bits)
        (bit-listp (lookup-equal-list bits asg))
        (hped-ped-r-point-listp bases)
        (<= (len bits) (len bases))
        (hped-ped-ws-okp wss (len (cdr bits)) asg)))

(defruledl hped-ped-from-zero-sound-empty
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (not (consp bits)))
           (b* ((out (hped-ped-from-zero-out bits bases wss)))
             (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                          (r1cs::dot-product (cdr out) asg (base-prime)))
                    (hped-ped-sum (lookup-equal-list bits asg) bases
                                  (ecurve::twisted-edwards-zero)))))
  :enable (hped-ped-from-zero-out hped-ped-sum lookup-equal-list hped-ped-dot-of-nil
           (:e ecurve::twisted-edwards-zero) hped-dot-of-lc-1))

(defruledl hped-ped-sum-first
  (implies (and (consp bits)
                (consp bases)
                (ecurve::edwards-bls12-r-pointp (car bases)))
           (equal (hped-ped-sum bits bases (ecurve::twisted-edwards-zero))
                  (hped-ped-sum (cdr bits) (cdr bases)
                                (hped-ped-term-point (car bases) (car bits)))))
  :expand ((hped-ped-sum bits bases (ecurve::twisted-edwards-zero)))
  :enable (hped-ped-term-point hped-ped-add-zero-left hped-ped-pointp-when-r-pointp))

(defruled hped-ped-from-zero-gadget-sound
  (implies (and (hped-ped-zero-hyps)
                (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                              asg (base-prime)))
           (b* ((out (hped-ped-from-zero-out bits bases wss)))
             (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                          (r1cs::dot-product (cdr out) asg (base-prime)))
                    (hped-ped-sum (lookup-equal-list bits asg) bases
                                  (ecurve::twisted-edwards-zero)))))
  :do-not-induct t
  :cases ((consp bits))
  :hints (("Subgoal 2" :use hped-ped-from-zero-sound-empty)
          ("Subgoal 1"
           :use ((:instance hped-ped-fold-gadget-sound
                            (bits (cdr bits)) (bases (cdr bases))
                            (ax (hped-ped-term-x (car bases) (car bits)))
                            (ay (hped-ped-term-y (car bases) (car bits)))
                            (acc (hped-ped-term-point (car bases)
                                                      (lookup-equal (car bits) asg))))
                 (:instance hped-ped-dot-of-term (b (car bits)) (base (car bases)))
                 (:instance hped-ped-r-pointp-of-term
                            (b (lookup-equal (car bits) asg)) (base (car bases)))
                 (:instance hped-ped-pointp-when-r-pointp (pt (car bases)))
                 (:instance hped-ped-car-wire (w bits))
                 (:instance hped-ped-sum-first (bits (lookup-equal-list bits asg))))
           :expand ((hped-ped-from-zero-out bits bases wss)
                    (hped-ped-from-zero-gadget bits bases wss)
                    (lookup-equal-list bits asg)
                    (hped-ped-r-point-listp bases)
                    (r1cs::valuation-binds-allp asg bits))
           :in-theory (disable hped-ped-fold-gadget-sound hped-ped-dot-of-term
                               hped-ped-sum-first))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; hash_uncompressed.

(defruled hped-pedersen-hash-uncompressed-gadget-sound
  (implies (and (hped-ped-zero-hyps)
                (equal (len bases) num-bits)
                (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                              asg (base-prime)))
           (b* ((out (hped-ped-from-zero-out bits bases wss)))
             (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                          (r1cs::dot-product (cdr out) asg (base-prime)))
                    (hped-pedersen-hash-uncompressed num-bits bases
                                                     (lookup-equal-list bits asg)))))
  :do-not-induct t
  :use (hped-ped-from-zero-gadget-sound
        (:instance hped-ped-sum-of-pad (input (lookup-equal-list bits asg)) (n num-bits)
                   (acc (ecurve::twisted-edwards-zero))))
  :enable hped-pedersen-hash-uncompressed
  :disable (hped-ped-from-zero-gadget-sound))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; commit_uncompressed and commit.

(define hped-ped-commit-gadget (bits bases wss s xs rs rbases rwss)
  :verify-guards nil
  :short "@('hash_uncompressed(input) + randomizer * random_base'):
          @('xs') are the randomizer's 251 bit wires (@('Scalar::to_bits_le')),
          @('rs') its comparison wires, @('rwss') the random-base fold wires."
  (append (hped-ped-from-zero-gadget bits bases wss)
          (scalar-write-bits-le-gadget s xs rs (base-prime))
          (if (consp bits)
              (b* ((h (hped-ped-from-zero-out bits bases wss)))
                (hped-ped-fold-gadget xs rbases rwss (car h) (cdr h)))
            (hped-ped-from-zero-gadget xs rbases rwss))))

(define hped-ped-commit-out (bits bases wss xs rbases rwss)
  :verify-guards nil
  (if (consp bits)
      (b* ((h (hped-ped-from-zero-out bits bases wss)))
        (hped-ped-fold-out xs rwss (car h) (cdr h)))
    (hped-ped-from-zero-out xs rbases rwss)))

(defun hped-ped-two-ind (m n wss)
  (if (or (zp m) (zp n) (endp wss))
      nil
    (hped-ped-two-ind (1- m) (1- n) (cdr wss))))

(defruledl hped-ped-ws-okp-mono
  (implies (and (hped-ped-ws-okp wss n asg)
                (<= (nfix m) (nfix n)))
           (hped-ped-ws-okp wss m asg))
  :induct (hped-ped-two-ind m n wss)
  :enable hped-ped-ws-okp)

(defruledl hped-ped-scalar-bits-is-randomizer-bits
  (equal (scalar-bits-le s) (hped-ped-randomizer-bits s))
  :enable (scalar-bits-le hped-ped-randomizer-bits scalar-prime
           scalar-field-size-in-bits (:e ecurve::edwards-bls12-r))
  :disable pfield::fep-fix)

(defmacro hped-ped-commit-hyps ()
  '(and (hped-ped-zero-hyps)
        (equal (len bases) num-bits)
        (symbolp s)
        (symbol-listp xs)
        (symbol-listp rs)
        (equal (len xs) 251)
        (equal (len rs) 250)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rs)
        (hped-ped-r-point-listp rbases)
        (equal (len rbases) 251)
        (hped-ped-ws-okp rwss 251 asg)))

(defmacro hped-ped-commit-concl ()
  '(b* ((out (hped-ped-commit-out bits bases wss xs rbases rwss)))
     (and (scalarp (lookup-equal s asg))
          (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                       (r1cs::dot-product (cdr out) asg (base-prime)))
                 (hped-pedersen-commit-uncompressed num-bits bases rbases
                                                    (lookup-equal-list bits asg)
                                                    (lookup-equal s asg))))))

(defruledl hped-ped-commit-sound-nonempty
  (implies (and (hped-ped-commit-hyps)
                (consp bits)
                (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime)))
           (hped-ped-commit-concl))
  :do-not-induct t
  :use (hped-ped-from-zero-gadget-sound
        hped-pedersen-hash-uncompressed-gadget-sound
        (:instance scalar-write-bits-le-gadget-sound (p (base-prime)) (acc nil))
        (:instance hped-ped-scalar-bits-is-randomizer-bits (s (lookup-equal s asg)))
        (:instance hped-ped-sum-of-pad (input (lookup-equal-list bits asg)) (n num-bits)
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hped-ped-coords-of-equal
                   (a (r1cs::dot-product (car (hped-ped-from-zero-out bits bases wss))
                                         asg (base-prime)))
                   (b (r1cs::dot-product (cdr (hped-ped-from-zero-out bits bases wss))
                                         asg (base-prime)))
                   (pt (hped-ped-sum (lookup-equal-list bits asg) bases
                                     (ecurve::twisted-edwards-zero))))
        (:instance hped-ped-fold-gadget-sound
                   (bits xs) (bases rbases) (wss rwss)
                   (ax (car (hped-ped-from-zero-out bits bases wss)))
                   (ay (cdr (hped-ped-from-zero-out bits bases wss)))
                   (acc (hped-ped-sum (lookup-equal-list bits asg) bases
                                      (ecurve::twisted-edwards-zero)))))
  :enable (hped-ped-commit-gadget hped-ped-commit-out hped-pedersen-commit-uncompressed
           hped-pedersen-hash-uncompressed r1cs::r1cs-constraints-holdp-of-append)
  :disable (hped-ped-from-zero-gadget-sound hped-pedersen-hash-uncompressed-gadget-sound
            scalar-write-bits-le-gadget-sound hped-ped-fold-gadget-sound
            hped-ped-from-zero-gadget hped-ped-fold-gadget hped-ped-from-zero-out
            hped-ped-fold-out scalar-write-bits-le-gadget))

(defruledl hped-ped-lookup-list-of-nil
  (equal (lookup-equal-list nil asg) nil)
  :enable lookup-equal-list)

(defruledl hped-ped-commit-sound-empty
  (implies (and (hped-ped-commit-hyps)
                (not (consp bits))
                (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime)))
           (hped-ped-commit-concl))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-sound (p (base-prime)) (acc nil))
        (:instance hped-ped-scalar-bits-is-randomizer-bits (s (lookup-equal s asg)))
        (:instance hped-ped-ws-okp-mono (wss rwss) (n 251) (m (len (cdr xs))))
        (:instance hped-ped-from-zero-gadget-sound
                   (bits xs) (bases rbases) (wss rwss)))
  :enable (hped-ped-commit-gadget hped-ped-commit-out hped-pedersen-commit-uncompressed
           hped-pedersen-hash-uncompressed hped-ped-pad hped-ped-sum-of-zeros
           r1cs::r1cs-constraints-holdp-of-append hped-ped-lookup-list-of-nil)
  :disable (hped-ped-from-zero-gadget-sound scalar-write-bits-le-gadget-sound
            hped-ped-from-zero-gadget hped-ped-from-zero-out scalar-write-bits-le-gadget))

(defruled hped-pedersen-commit-uncompressed-gadget-sound
  (implies (and (hped-ped-commit-hyps)
                (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime)))
           (hped-ped-commit-concl))
  :use (hped-ped-commit-sound-nonempty hped-ped-commit-sound-empty))

(defruledl hped-ped-not-reserrp-of-r-point
  (implies (ecurve::edwards-bls12-r-pointp x)
           (not (reserrp x)))
  :use (:instance hped-ped-pointp-when-r-pointp (pt x))
  :enable (reserrp ecurve::edwards-bls12-pointp ecurve::point-on-twisted-edwards-p
           ecurve::pointp ecurve::point-kind ecurve::point-finite->x))

(defruledl hped-ped-not-reserrp-of-commit
  (implies (and (hped-ped-r-point-listp bases)
                (hped-ped-r-point-listp rbases)
                (<= (len input) (nfix num-bits)))
           (not (reserrp (hped-pedersen-commit-uncompressed num-bits bases rbases
                                                            input randomizer))))
  :use ((:instance hped-ped-not-reserrp-of-r-point
                   (x (hped-ped-sum (hped-ped-pad input num-bits) bases
                                    (ecurve::twisted-edwards-zero))))
        (:instance hped-ped-not-reserrp-of-r-point
                   (x (hped-ped-sum (hped-ped-randomizer-bits randomizer) rbases
                                    (hped-ped-sum (hped-ped-pad input num-bits) bases
                                                  (ecurve::twisted-edwards-zero))))))
  :enable (hped-pedersen-commit-uncompressed hped-pedersen-hash-uncompressed))

(defruled hped-pedersen-commit-gadget-sound
  (implies (and (hped-ped-commit-hyps)
                (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime)))
           (b* ((out (hped-ped-commit-out bits bases wss xs rbases rwss)))
             (equal (r1cs::dot-product (car out) asg (base-prime))
                    (hped-pedersen-commit num-bits bases rbases
                                          (lookup-equal-list bits asg)
                                          (lookup-equal s asg)))))
  :do-not-induct t
  :use (hped-pedersen-commit-uncompressed-gadget-sound
        (:instance hped-ped-not-reserrp-of-commit
                   (input (lookup-equal-list bits asg)) (randomizer (lookup-equal s asg)))
        (:instance hped-ped-coords-of-equal
                   (a (r1cs::dot-product (car (hped-ped-commit-out bits bases wss xs rbases rwss))
                                         asg (base-prime)))
                   (b (r1cs::dot-product (cdr (hped-ped-commit-out bits bases wss xs rbases rwss))
                                         asg (base-prime)))
                   (pt (hped-pedersen-commit-uncompressed num-bits bases rbases
                                                          (lookup-equal-list bits asg)
                                                          (lookup-equal s asg)))))
  :enable hped-pedersen-commit
  :disable (hped-pedersen-commit-uncompressed-gadget-sound hped-ped-commit-out
            hped-ped-commit-gadget hped-pedersen-commit-uncompressed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defruledl hped-ped-add-gadget-complete
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbol-listp ws)
                (equal (len ws) 6)
                (r1cs::valuation-binds-allp asg ws)
                (ecurve::edwards-bls12-pointp tp)
                (ecurve::edwards-bls12-pointp acc)
                (equal (r1cs::dot-product tx asg (base-prime)) (ecurve::point-finite->x tp))
                (equal (r1cs::dot-product ty asg (base-prime)) (ecurve::point-finite->y tp))
                (equal (r1cs::dot-product ax asg (base-prime)) (ecurve::point-finite->x acc))
                (equal (r1cs::dot-product ay asg (base-prime)) (ecurve::point-finite->y acc))
                (equal (lookup-equal (nth 0 ws) asg)
                       (pfield::mul (pfield::add (ecurve::point-finite->x tp)
                                                 (ecurve::point-finite->y tp) (base-prime))
                                    (pfield::add (ecurve::point-finite->x acc)
                                                 (ecurve::point-finite->y acc) (base-prime))
                                    (base-prime)))
                (equal (lookup-equal (nth 1 ws) asg)
                       (pfield::mul (ecurve::point-finite->x tp)
                                    (ecurve::point-finite->y acc) (base-prime)))
                (equal (lookup-equal (nth 2 ws) asg)
                       (pfield::mul (ecurve::point-finite->x acc)
                                    (ecurve::point-finite->y tp) (base-prime)))
                (equal (lookup-equal (nth 3 ws) asg)
                       (pfield::mul (lookup-equal (nth 1 ws) asg)
                                    (lookup-equal (nth 2 ws) asg) (base-prime)))
                (equal (lookup-equal (nth 4 ws) asg)
                       (ecurve::point-finite->x (ecurve::edwards-bls12-add tp acc)))
                (equal (lookup-equal (nth 5 ws) asg)
                       (ecurve::point-finite->y (ecurve::edwards-bls12-add tp acc))))
           (r1cs::r1cs-constraints-holdp (hped-ped-add-gadget tx ty ax ay ws)
                                         asg (base-prime)))
  :do-not-induct t
  :use (hped-ped-primep
        (:instance crv-group-add-equations-complete
                   (p (base-prime)) (p1 tp) (p2 acc)))
  :in-theory (union-theories
              '(hped-ped-add-gadget
                r1cs::r1cs-constraints-holdp-of-cons
                hped-holdsp-of-c hped-dot-of-lc-v hped-dot-of-lc-1 hped-dot-of-lc-add
                hped-dot-of-lc-scale hped-dot-of-lc-sub
                hped-ped-nth-wire r1cs::fep-of-lookup-equal
                (:e len) (:e nth) (:e <) (:e natp) (:e base-prime)
                (:e ecurve::edwards-bls12-d) (:e pfield::fep)
                r1cs::r1cs-constraints-holdp)
              (theory 'minimal-theory)))

(define hped-ped-fold-canonp (bits bases wss acc asg)
  :verify-guards nil
  :short "The canonical @('Group::add') witnesses of the fold: the products
          and the coordinates of @('term + acc') at every step."
  (if (endp bits)
      t
    (b* ((ws (car wss))
         (p (base-prime))
         (tp (hped-ped-term-point (car bases) (lookup-equal (car bits) asg)))
         (x1 (ecurve::point-finite->x tp))
         (y1 (ecurve::point-finite->y tp))
         (x2 (ecurve::point-finite->x acc))
         (y2 (ecurve::point-finite->y acc))
         (s (ecurve::edwards-bls12-add tp acc)))
      (and (equal (lookup-equal (nth 0 ws) asg)
                  (pfield::mul (pfield::add x1 y1 p) (pfield::add x2 y2 p) p))
           (equal (lookup-equal (nth 1 ws) asg) (pfield::mul x1 y2 p))
           (equal (lookup-equal (nth 2 ws) asg) (pfield::mul x2 y1 p))
           (equal (lookup-equal (nth 3 ws) asg)
                  (pfield::mul (lookup-equal (nth 1 ws) asg)
                               (lookup-equal (nth 2 ws) asg) p))
           (equal (lookup-equal (nth 4 ws) asg) (ecurve::point-finite->x s))
           (equal (lookup-equal (nth 5 ws) asg) (ecurve::point-finite->y s))
           (hped-ped-fold-canonp (cdr bits) (cdr bases) (cdr wss) s asg)))))

(defmacro hped-ped-canon-acc ()
  '(ecurve::edwards-bls12-add
    (hped-ped-term-point (car bases) (lookup-equal (car bits) asg)) acc))

(defruledl hped-ped-fold-step-complete
  (implies (and (hped-ped-fold-hyps)
                (consp bits)
                (hped-ped-fold-canonp bits bases wss acc asg))
           (b* ((ws (car wss))
                (acc1 (hped-ped-canon-acc)))
             (and (r1cs::r1cs-constraints-holdp
                   (hped-ped-add-gadget (hped-ped-term-x (car bases) (car bits))
                                        (hped-ped-term-y (car bases) (car bits))
                                        ax ay ws)
                   asg (base-prime))
                  (ecurve::edwards-bls12-r-pointp acc1)
                  (equal (r1cs::dot-product (hped-lc-v (nth 4 ws)) asg (base-prime))
                         (ecurve::point-finite->x acc1))
                  (equal (r1cs::dot-product (hped-lc-v (nth 5 ws)) asg (base-prime))
                         (ecurve::point-finite->y acc1))
                  (hped-ped-fold-canonp (cdr bits) (cdr bases) (cdr wss) acc1 asg))))
  :do-not-induct t
  :use (hped-ped-primep
        (:instance hped-ped-add-gadget-complete
                   (ws (car wss))
                   (tx (hped-ped-term-x (car bases) (car bits)))
                   (ty (hped-ped-term-y (car bases) (car bits)))
                   (tp (hped-ped-term-point (car bases) (lookup-equal (car bits) asg))))
        (:instance hped-ped-dot-of-term (b (car bits)) (base (car bases)))
        (:instance hped-ped-r-pointp-of-term (b (lookup-equal (car bits) asg))
                   (base (car bases)))
        (:instance hped-ped-pointp-when-r-pointp
                   (pt (hped-ped-term-point (car bases) (lookup-equal (car bits) asg))))
        (:instance hped-ped-pointp-when-r-pointp (pt acc))
        (:instance hped-ped-pointp-when-r-pointp (pt (car bases)))
        (:instance hped-ped-car-wire (w bits))
        (:instance hped-ped-nth-wire (w (car wss)) (n 4))
        (:instance hped-ped-nth-wire (w (car wss)) (n 5)))
  :enable (hped-ped-fold-canonp hped-ped-ws-okp lookup-equal-list
           hped-ped-r-point-listp r1cs::valuation-binds-allp)
  :disable (hped-ped-add-gadget hped-ped-term-x hped-ped-term-y hped-ped-term-point
            hped-ped-dot-of-term hped-ped-add-gadget-complete))

(defun hped-ped-canon-ind (bits bases wss ax ay acc asg)
  (declare (xargs :verify-guards nil))
  (if (endp bits)
      (list bases wss ax ay acc asg)
    (hped-ped-canon-ind (cdr bits) (cdr bases) (cdr wss)
                        (hped-lc-v (nth 4 (car wss)))
                        (hped-lc-v (nth 5 (car wss)))
                        (hped-ped-canon-acc)
                        asg)))

(defruled hped-ped-fold-gadget-complete
  (implies (and (hped-ped-fold-hyps)
                (hped-ped-fold-canonp bits bases wss acc asg))
           (r1cs::r1cs-constraints-holdp (hped-ped-fold-gadget bits bases wss ax ay)
                                         asg (base-prime)))
  :induct (hped-ped-canon-ind bits bases wss ax ay acc asg)
  :hints (("Subgoal *1/2" :use hped-ped-fold-step-complete
           :expand ((hped-ped-fold-gadget bits bases wss ax ay)
                    (lookup-equal-list bits asg)
                    (hped-ped-ws-okp wss (len bits) asg)
                    (hped-ped-r-point-listp bases)
                    (r1cs::valuation-binds-allp asg bits))
           :in-theory (e/d (r1cs::r1cs-constraints-holdp-of-append)
                           (hped-ped-fold-step-complete hped-ped-fold-canonp
                            hped-ped-add-gadget))))
  :enable (hped-ped-fold-gadget))

(define hped-ped-from-zero-canonp (bits bases wss asg)
  :verify-guards nil
  :short "Canonical witnesses of the fold from the constant zero, whose
          accumulator after the free first term is that term."
  (or (endp bits)
      (hped-ped-fold-canonp (cdr bits) (cdr bases) wss
                            (hped-ped-term-point (car bases) (lookup-equal (car bits) asg))
                            asg)))

(defruled hped-ped-from-zero-gadget-complete
  (implies (and (hped-ped-zero-hyps)
                (hped-ped-from-zero-canonp bits bases wss asg))
           (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                         asg (base-prime)))
  :do-not-induct t
  :cases ((consp bits))
  :hints (("Subgoal 1"
           :use ((:instance hped-ped-fold-gadget-complete
                            (bits (cdr bits)) (bases (cdr bases))
                            (ax (hped-ped-term-x (car bases) (car bits)))
                            (ay (hped-ped-term-y (car bases) (car bits)))
                            (acc (hped-ped-term-point (car bases)
                                                      (lookup-equal (car bits) asg))))
                 (:instance hped-ped-dot-of-term (b (car bits)) (base (car bases)))
                 (:instance hped-ped-r-pointp-of-term
                            (b (lookup-equal (car bits) asg)) (base (car bases)))
                 (:instance hped-ped-pointp-when-r-pointp (pt (car bases)))
                 (:instance hped-ped-car-wire (w bits)))
           :expand ((hped-ped-from-zero-gadget bits bases wss)
                    (lookup-equal-list bits asg)
                    (hped-ped-r-point-listp bases)
                    (r1cs::valuation-binds-allp asg bits))
           :in-theory (e/d (hped-ped-from-zero-canonp)
                           (hped-ped-fold-gadget-complete hped-ped-dot-of-term))))
  :enable (hped-ped-from-zero-gadget))

(defruled hped-pedersen-hash-uncompressed-gadget-complete
  (implies (and (hped-ped-zero-hyps)
                (equal (len bases) num-bits)
                (hped-ped-from-zero-canonp bits bases wss asg))
           (b* ((out (hped-ped-from-zero-out bits bases wss)))
             (and (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                                asg (base-prime))
                  (equal (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                               (r1cs::dot-product (cdr out) asg (base-prime)))
                         (hped-pedersen-hash-uncompressed num-bits bases
                                                          (lookup-equal-list bits asg))))))
  :do-not-induct t
  :use (hped-ped-from-zero-gadget-complete hped-pedersen-hash-uncompressed-gadget-sound)
  :in-theory (theory 'minimal-theory))

(define hped-ped-commit-canonp (bits bases wss s xs rs rbases rwss asg)
  :verify-guards nil
  :short "Canonical witnesses of @('commit_uncompressed'): the hash fold,
          the randomizer's bits and @('bits-lte-const') fold, and the
          random-base fold from the hash."
  (b* ((sv (lookup-equal s asg)))
    (and (hped-ped-from-zero-canonp bits bases wss asg)
         (scalarp sv)
         (equal (lookup-equal-list xs asg) (scalar-bits-le sv))
         (equal (lookup-equal-list rs asg)
                (crv-bits-lte-const-witness (lookup-equal-list xs asg)
                                            (scalar-modulus-minus-one-bits)))
         (if (consp bits)
             (hped-ped-fold-canonp xs rbases rwss
                                   (hped-ped-sum (lookup-equal-list bits asg) bases
                                                 (ecurve::twisted-edwards-zero))
                                   asg)
           (hped-ped-from-zero-canonp xs rbases rwss asg)))))

(defruledl hped-ped-commit-holds-nonempty
  (implies (and (hped-ped-commit-hyps)
                (consp bits)
                (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
           (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                 rbases rwss)
                                         asg (base-prime)))
  :do-not-induct t
  :use (hped-ped-from-zero-gadget-complete
        hped-ped-from-zero-gadget-sound
        (:instance scalar-write-bits-le-gadget-complete (p (base-prime)) (acc nil))
        (:instance hped-ped-coords-of-equal
                   (a (r1cs::dot-product (car (hped-ped-from-zero-out bits bases wss))
                                         asg (base-prime)))
                   (b (r1cs::dot-product (cdr (hped-ped-from-zero-out bits bases wss))
                                         asg (base-prime)))
                   (pt (hped-ped-sum (lookup-equal-list bits asg) bases
                                     (ecurve::twisted-edwards-zero))))
        (:instance hped-ped-fold-gadget-complete
                   (bits xs) (bases rbases) (wss rwss)
                   (ax (car (hped-ped-from-zero-out bits bases wss)))
                   (ay (cdr (hped-ped-from-zero-out bits bases wss)))
                   (acc (hped-ped-sum (lookup-equal-list bits asg) bases
                                      (ecurve::twisted-edwards-zero)))))
  :enable (hped-ped-commit-gadget hped-ped-commit-canonp
           r1cs::r1cs-constraints-holdp-of-append)
  :disable (hped-ped-from-zero-gadget-complete hped-ped-from-zero-gadget-sound
            scalar-write-bits-le-gadget-complete hped-ped-fold-gadget-complete
            hped-ped-from-zero-gadget hped-ped-fold-gadget hped-ped-from-zero-out
            hped-ped-fold-out scalar-write-bits-le-gadget hped-ped-fold-canonp
            hped-ped-from-zero-canonp))

(defruledl hped-ped-commit-holds-empty
  (implies (and (hped-ped-commit-hyps)
                (not (consp bits))
                (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
           (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                 rbases rwss)
                                         asg (base-prime)))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-complete (p (base-prime)) (acc nil))
        (:instance hped-ped-ws-okp-mono (wss rwss) (n 251) (m (len (cdr xs))))
        (:instance hped-ped-from-zero-gadget-complete
                   (bits xs) (bases rbases) (wss rwss)))
  :enable (hped-ped-commit-gadget hped-ped-commit-canonp hped-ped-from-zero-gadget
           r1cs::r1cs-constraints-holdp-of-append)
  :disable (hped-ped-from-zero-gadget-complete scalar-write-bits-le-gadget-complete
            scalar-write-bits-le-gadget hped-ped-from-zero-canonp))

(defruled hped-pedersen-commit-uncompressed-gadget-complete
  (implies (and (hped-ped-commit-hyps)
                (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
           (and (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime))
                (hped-ped-commit-concl)))
  :use (hped-ped-commit-holds-nonempty hped-ped-commit-holds-empty
        hped-pedersen-commit-uncompressed-gadget-sound)
  :in-theory (theory 'minimal-theory))

(defruled hped-pedersen-commit-gadget-complete
  (implies (and (hped-ped-commit-hyps)
                (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
           (and (r1cs::r1cs-constraints-holdp (hped-ped-commit-gadget bits bases wss s xs rs
                                                                      rbases rwss)
                                              asg (base-prime))
                (b* ((out (hped-ped-commit-out bits bases wss xs rbases rwss)))
                  (equal (r1cs::dot-product (car out) asg (base-prime))
                         (hped-pedersen-commit num-bits bases rbases
                                               (lookup-equal-list bits asg)
                                               (lookup-equal s asg))))))
  :use (hped-ped-commit-holds-nonempty hped-ped-commit-holds-empty
        hped-pedersen-commit-gadget-sound)
  :in-theory (theory 'minimal-theory))
