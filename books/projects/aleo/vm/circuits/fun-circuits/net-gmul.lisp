; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Aleo::g_scalar_multiply (circuit/network/src/v0.rs):
;
;   bases.iter().zip_eq(&scalar.to_bits_le())
;     .fold(Group::zero(), |output, (base, bit)|
;           Group::ternary(bit, &(&output + base), &output))
;
; with bases[i] = 2^i G (constants, i < 251) and a variable scalar.
; Scalar::to_bits_le is scalar-write-bits-le-gadget (251 bit wires).
;
; Step 0: zero + G returns the constant G (zero shortcut of Group::add), and
; the ternary of two constants with a variable condition is the linear
; combination x = b0 Gx, y = 1 + b0 (Gy - 1) (hbhp-tern-x, hbhp-tern-y);
; no constraint.
;
; Step i >= 1, accumulator (ax, ay) as linear combinations, base B = 2^i G:
; Group::add with a constant `other' keeps the accumulator as `this'.
; u = (ax + ay)(Bx + By), v0 = By ax and v1 = Bx ay are constant scalings
; (no constraint, since ax, ay, Bx, By are non-zero and the accumulator is
; not constant), then
;   v0 * v1 = v01                             (Field::mul)
;   x3 * (1 + d v01) = v0 + v1                (Group::add x3)
;   y3 * (1 - d v01) = u - v0 - v1            (Group::add y3, a = -1)
;   (x3 - ax) * b = wx - ax                   (Field::ternary x)
;   (y3 - ay) * b = wy - ay                   (Field::ternary y)
; and (wx, wy) is the next accumulator.  250 steps: 5 constraints each.

(in-package "ALEOVM")

(include-book "hbhp-cu")
(include-book "crv-add-complete")
(include-book "compute-key-from-private-key")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-cancel" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r)
                           (:e curve-generator-g))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One step i >= 1.

(define net-gstep-gadget (ax ay (b symbolp) pt st (p posp))
  :verify-guards nil
  :short "Wires of @('st'): (v01 x3 y3 wx wy); @('pt') is the constant base."
  (b* ((bx (ecurve::point-finite->x pt))
       (by (ecurve::point-finite->y pt))
       (d (ecurve::edwards-bls12-d))
       (v01 (nth 0 st)) (x3 (nth 1 st)) (y3 (nth 2 st))
       (wx (nth 3 st)) (wy (nth 4 st))
       (v0 (hbhp-sv-scale by ax p))
       (v1 (hbhp-sv-scale bx ay p)))
    (list (r1cs::make-r1cs-constraint
           :a v0
           :b v1
           :c (list (list 1 v01)))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 x3))
           :b (list (list 1 1) (list d v01))
           :c (append v0 v1))
          (r1cs::make-r1cs-constraint
           :a (list (list 1 y3))
           :b (list (list 1 1) (list (pfield::neg d p) v01))
           :c (append (hbhp-sv-scale (pfield::add bx by p) (append ax ay) p)
                      (hbhp-sv-neg v0 p)
                      (hbhp-sv-neg v1 p)))
          (r1cs::make-r1cs-constraint
           :a (append (list (list 1 x3)) (hbhp-sv-neg ax p))
           :b (list (list 1 b))
           :c (append (list (list 1 wx)) (hbhp-sv-neg ax p)))
          (r1cs::make-r1cs-constraint
           :a (append (list (list 1 y3)) (hbhp-sv-neg ay p))
           :b (list (list 1 b))
           :c (append (list (list 1 wy)) (hbhp-sv-neg ay p))))))

(defmacro net-gstep-wires-okp (b st)
  `(and (hbhp-wire-okp ,b)
        (hbhp-wire-okp (nth 0 ,st)) (hbhp-wire-okp (nth 1 ,st))
        (hbhp-wire-okp (nth 2 ,st)) (hbhp-wire-okp (nth 3 ,st))
        (hbhp-wire-okp (nth 4 ,st))))

(defruled net-gstep-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (net-gstep-wires-okp b st))
           (b* ((ax$ (hbhp-dot ax)) (ay$ (hbhp-dot ay))
                (bx (ecurve::point-finite->x pt))
                (by (ecurve::point-finite->y pt))
                (b$ (hbhp-lk b))
                (v01$ (hbhp-lk (nth 0 st))) (x3$ (hbhp-lk (nth 1 st)))
                (y3$ (hbhp-lk (nth 2 st))) (wx$ (hbhp-lk (nth 3 st)))
                (wy$ (hbhp-lk (nth 4 st)))
                (d (ecurve::edwards-bls12-d))
                (v0 (pfield::mul ax$ by p))
                (v1 (pfield::mul bx ay$ p))
                (u (pfield::mul (pfield::add ax$ ay$ p) (pfield::add bx by p) p)))
             (equal (r1cs::r1cs-constraints-holdp
                     (net-gstep-gadget ax ay b pt st p) asg p)
                    (and (equal v01$ (pfield::mul v0 v1 p))
                         (equal (pfield::mul x3$ (pfield::add 1 (pfield::mul d v01$ p) p) p)
                                (pfield::add v0 v1 p))
                         (equal (pfield::mul y3$ (pfield::sub 1 (pfield::mul d v01$ p) p) p)
                                (pfield::sub (pfield::sub u v0 p) v1 p))
                         (equal (pfield::mul (pfield::sub x3$ ax$ p) b$ p)
                                (pfield::sub wx$ ax$ p))
                         (equal (pfield::mul (pfield::sub y3$ ay$ p) b$ p)
                                (pfield::sub wy$ ay$ p))))))
  :use (hbhp-base-prime-facts curve-fep-of-edwards-bls12-d)
  :enable (net-gstep-gadget r1cs::r1cs-constraint-holdsp
           r1cs::r1cs-constraints-holdp
           hbhp-dot-cons hbhp-dot-nil r1cs::dot-product-of-append
           pfield::sub)
  :disable (r1cs::dot-product))

(defruled net-tern-value
  (implies (and (primep p)
                (pfield::fep x3 p) (pfield::fep a p) (pfield::fep w p)
                (bitp b))
           (iff (equal (pfield::mul (pfield::sub x3 a p) b p) (pfield::sub w a p))
                (equal w (if (equal b 1) x3 a))))
  :cases ((equal b 0) (equal b 1))
  :enable bitp)

(defruled net-gstep-add-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (net-gstep-wires-okp b st)
                (ecurve::edwards-bls12-pointp pt)
                (ecurve::edwards-bls12-pointp acc)
                (equal (hbhp-dot ax) (ecurve::point-finite->x acc))
                (equal (hbhp-dot ay) (ecurve::point-finite->y acc))
                (r1cs::r1cs-constraints-holdp (net-gstep-gadget ax ay b pt st p) asg p))
           (equal (ecurve::point-finite (hbhp-lk (nth 1 st)) (hbhp-lk (nth 2 st)))
                  (ecurve::edwards-bls12-add acc pt)))
  :do-not-induct t
  :use (net-gstep-gadget-to-eqns
        hbhp-base-prime-facts
        (:instance crv-group-add-from-equations
                   (p1 acc) (p2 pt)
                   (x1 (ecurve::point-finite->x acc)) (y1 (ecurve::point-finite->y acc))
                   (x2 (ecurve::point-finite->x pt)) (y2 (ecurve::point-finite->y pt))
                   (x3 (hbhp-lk (nth 1 st))) (y3 (hbhp-lk (nth 2 st)))
                   (u (pfield::mul (pfield::add (ecurve::point-finite->x acc)
                                                (ecurve::point-finite->y acc) p)
                                   (pfield::add (ecurve::point-finite->x pt)
                                                (ecurve::point-finite->y pt) p) p))
                   (v0 (pfield::mul (ecurve::point-finite->x acc) (ecurve::point-finite->y pt) p))
                   (v1 (pfield::mul (ecurve::point-finite->x pt) (ecurve::point-finite->y acc) p))
                   (v01 (hbhp-lk (nth 0 st))))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 1 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 2 st))
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory nil)

(defruled net-gstep-tern-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (net-gstep-wires-okp b st)
                (bitp (hbhp-lk b))
                (r1cs::r1cs-constraints-holdp (net-gstep-gadget ax ay b pt st p) asg p))
           (and (equal (hbhp-lk (nth 3 st))
                       (if (equal (hbhp-lk b) 1) (hbhp-lk (nth 1 st)) (hbhp-dot ax)))
                (equal (hbhp-lk (nth 4 st))
                       (if (equal (hbhp-lk b) 1) (hbhp-lk (nth 2 st)) (hbhp-dot ay)))))
  :do-not-induct t
  :use (net-gstep-gadget-to-eqns
        hbhp-base-prime-facts
        (:instance net-tern-value
                   (x3 (hbhp-lk (nth 1 st))) (a (hbhp-dot ax))
                   (w (hbhp-lk (nth 3 st))) (b (hbhp-lk b)))
        (:instance net-tern-value
                   (x3 (hbhp-lk (nth 2 st))) (a (hbhp-dot ay))
                   (w (hbhp-lk (nth 4 st))) (b (hbhp-lk b)))
        (:instance r1cs::fep-of-dot-product (r1cs::vec ax) (r1cs::valuation asg) (r1cs::prime p))
        (:instance r1cs::fep-of-dot-product (r1cs::vec ay) (r1cs::valuation asg) (r1cs::prime p))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 1 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 2 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 3 st))
                   (r1cs::prime p) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var (nth 4 st))
                   (r1cs::prime p) (r1cs::valuation asg)))
  :in-theory '(posp))

(defruled net-gstep-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (net-gstep-wires-okp b st)
                (bitp (hbhp-lk b))
                (ecurve::edwards-bls12-pointp pt)
                (ecurve::edwards-bls12-pointp acc)
                (equal (ecurve::point-finite (hbhp-dot ax) (hbhp-dot ay)) acc)
                (r1cs::r1cs-constraints-holdp (net-gstep-gadget ax ay b pt st p) asg p))
           (equal (ecurve::point-finite (hbhp-lk (nth 3 st)) (hbhp-lk (nth 4 st)))
                  (group-ternary-funspec (hbhp-lk b) (group-add-funspec acc pt) acc)))
  :do-not-induct t
  :use (net-gstep-tern-sound
        hbhp-base-prime-facts
        (:instance net-gstep-add-sound)
        (:instance r1cs::fep-of-dot-product (r1cs::vec ax) (r1cs::valuation asg) (r1cs::prime p))
        (:instance r1cs::fep-of-dot-product (r1cs::vec ay) (r1cs::valuation asg) (r1cs::prime p)))
  :in-theory '(group-ternary-funspec group-add-funspec
               ecurve::point-finite->x-of-point-finite
               ecurve::point-finite->y-of-point-finite
               pfield::fep natp nfix posp))

(defmacro net-gstep-canon (b st acc pt)
  `(b* ((sum (ecurve::edwards-bls12-add ,acc ,pt)))
     (and (equal (hbhp-lk (nth 0 ,st))
                 (pfield::mul (pfield::mul (ecurve::point-finite->x ,acc)
                                           (ecurve::point-finite->y ,pt) p)
                              (pfield::mul (ecurve::point-finite->x ,pt)
                                           (ecurve::point-finite->y ,acc) p)
                              p))
          (equal (hbhp-lk (nth 1 ,st)) (ecurve::point-finite->x sum))
          (equal (hbhp-lk (nth 2 ,st)) (ecurve::point-finite->y sum))
          (equal (hbhp-lk (nth 3 ,st))
                 (if (equal (hbhp-lk ,b) 1)
                     (ecurve::point-finite->x sum)
                   (ecurve::point-finite->x ,acc)))
          (equal (hbhp-lk (nth 4 ,st))
                 (if (equal (hbhp-lk ,b) 1)
                     (ecurve::point-finite->y sum)
                   (ecurve::point-finite->y ,acc))))))

(defruled net-gstep-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (net-gstep-wires-okp b st)
                (bitp (hbhp-lk b))
                (ecurve::edwards-bls12-pointp pt)
                (ecurve::edwards-bls12-pointp acc)
                (equal (hbhp-dot ax) (ecurve::point-finite->x acc))
                (equal (hbhp-dot ay) (ecurve::point-finite->y acc))
                (net-gstep-canon b st acc pt))
           (r1cs::r1cs-constraints-holdp (net-gstep-gadget ax ay b pt st p) asg p))
  :do-not-induct t
  :use (net-gstep-gadget-to-eqns
        hbhp-base-prime-facts
        (:instance crv-group-add-equations-complete (p1 acc) (p2 pt))
        (:instance crv-fep-of-edwards-bls12-coords (pt acc))
        (:instance crv-fep-of-edwards-bls12-coords
                   (pt (ecurve::edwards-bls12-add acc pt)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 acc) (ecurve::point2 pt))
        (:instance net-tern-value
                   (x3 (hbhp-lk (nth 1 st))) (a (hbhp-dot ax))
                   (w (hbhp-lk (nth 3 st))) (b (hbhp-lk b)))
        (:instance net-tern-value
                   (x3 (hbhp-lk (nth 2 st))) (a (hbhp-dot ay))
                   (w (hbhp-lk (nth 4 st))) (b (hbhp-lk b))))
  :in-theory '(posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fold over steps i, i+1, ... with base 2^i G.

(define net-gbase ((i natp))
  :verify-guards nil
  (ecurve::edwards-bls12-mul (expt 2 (lnfix i)) (curve-generator-g)))

(defruled net-gbase-pointp
  (ecurve::edwards-bls12-pointp (net-gbase i))
  :enable net-gbase
  :use (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                  (ecurve::scalar (expt 2 (nfix i))) (point (curve-generator-g))))

(define net-gfold-gadget (bits sts (i natp) ax ay (p posp))
  :verify-guards nil
  (if (endp bits)
      nil
    (append (net-gstep-gadget ax ay (car bits) (net-gbase i) (car sts) p)
            (net-gfold-gadget (cdr bits) (cdr sts) (1+ (lnfix i))
                              (list (list 1 (nth 3 (car sts))))
                              (list (list 1 (nth 4 (car sts))))
                              p))))

(define net-gfold-out (bits sts ax ay)
  :verify-guards nil
  (if (endp bits)
      (cons ax ay)
    (net-gfold-out (cdr bits) (cdr sts)
                   (list (list 1 (nth 3 (car sts))))
                   (list (list 1 (nth 4 (car sts)))))))

(define net-gfold-wires-okp (bits sts asg)
  :verify-guards nil
  (if (endp bits)
      t
    (and (net-gstep-wires-okp (car bits) (car sts))
         (bitp (hbhp-lk (car bits)))
         (net-gfold-wires-okp (cdr bits) (cdr sts) asg))))

(define net-gfold-canonp (bits sts (i natp) acc asg)
  :verify-guards nil
  (if (endp bits)
      t
    (and (let ((p (base-prime))) (net-gstep-canon (car bits) (car sts) acc (net-gbase i)))
         (net-gfold-canonp (cdr bits) (cdr sts) (1+ (lnfix i))
                           (group-ternary-funspec
                            (hbhp-lk (car bits))
                            (group-add-funspec acc (net-gbase i))
                            acc)
                           asg))))

(defun net-gfold-induct (bits sts i ax ay acc asg)
  (declare (xargs :verify-guards nil))
  (if (endp bits)
      (list sts i ax ay acc asg)
    (net-gfold-induct (cdr bits) (cdr sts) (1+ (nfix i))
                      (list (list 1 (nth 3 (car sts))))
                      (list (list 1 (nth 4 (car sts))))
                      (group-ternary-funspec
                       (lookup-equal (car bits) asg)
                       (group-add-funspec acc (net-gbase i))
                       acc)
                      asg)))

(defruled net-pointp-of-ternary-add
  (implies (and (ecurve::edwards-bls12-pointp acc)
                (ecurve::edwards-bls12-pointp pt))
           (ecurve::edwards-bls12-pointp
            (group-ternary-funspec b (group-add-funspec acc pt) acc)))
  :enable (group-ternary-funspec group-add-funspec))

(defruled net-dot-one-wire
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-wire-okp w))
           (equal (r1cs::dot-product (list (list 1 w)) asg p) (hbhp-lk w)))
  :use (hbhp-base-prime-facts hbhp-dot-one-wire)
  :in-theory nil)

(defruled net-point-finite-of-coords
  (implies (ecurve::edwards-bls12-pointp acc)
           (equal (ecurve::point-finite (ecurve::point-finite->x acc)
                                        (ecurve::point-finite->y acc))
                  acc))
  :enable (ecurve::edwards-bls12-pointp ecurve::point-on-twisted-edwards-p
           ecurve::pointp))

(defruled net-gfold-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (natp i)
                (ecurve::edwards-bls12-pointp acc)
                (equal (ecurve::point-finite (hbhp-dot ax) (hbhp-dot ay)) acc)
                (net-gfold-wires-okp bits sts asg)
                (r1cs::r1cs-constraints-holdp (net-gfold-gadget bits sts i ax ay p) asg p))
           (b* ((out (net-gfold-out bits sts ax ay)))
             (equal (ecurve::point-finite (hbhp-dot (car out)) (hbhp-dot (cdr out)))
                    (g-scalar-window (lookup-equal-list bits asg) i acc))))
  :induct (net-gfold-induct bits sts i ax ay acc asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               (:induction net-gfold-induct) nfix lnfix natp endp
               car-cons cdr-cons (:t net-gbase))
  :hints (("Subgoal *1/2"
           :expand ((:free (ax ay i p) (net-gfold-gadget bits sts i ax ay p))
                    (:free (ax ay) (net-gfold-out bits sts ax ay))
                    (net-gfold-wires-okp bits sts asg)
                    (lookup-equal-list bits asg)
                    (:free (bs i acc) (g-scalar-window (cons (lookup-equal (car bits) asg) bs)
                                                       i acc)))
           :use ((:instance net-gstep-sound (b (car bits)) (pt (net-gbase i)) (st (car sts)))
                 (:instance net-gbase-pointp)
                 (:instance net-pointp-of-ternary-add (pt (net-gbase i))
                            (b (lookup-equal (car bits) asg)))
                 (:instance net-dot-one-wire (w (nth 3 (car sts))))
                 (:instance net-dot-one-wire (w (nth 4 (car sts))))
                 (:instance net-gbase-is-window-base)))
          ("Subgoal *1/1"
           :expand ((:free (ax ay) (net-gfold-out bits sts ax ay))
                    (lookup-equal-list bits asg)
                    (:free (i acc) (g-scalar-window nil i acc)))))
  :prep-lemmas
  ((defruled net-gbase-is-window-base
     (equal (ecurve::edwards-bls12-mul (expt 2 (nfix i)) (curve-generator-g))
            (net-gbase i))
     :enable net-gbase)))

(defruled net-ternary-add-coords
  (b* ((nxt (group-ternary-funspec b (group-add-funspec acc pt) acc))
       (sum (ecurve::edwards-bls12-add acc pt)))
    (and (equal (ecurve::point-finite->x nxt)
                (if (equal b 1) (ecurve::point-finite->x sum) (ecurve::point-finite->x acc)))
         (equal (ecurve::point-finite->y nxt)
                (if (equal b 1) (ecurve::point-finite->y sum) (ecurve::point-finite->y acc)))))
  :enable (group-ternary-funspec group-add-funspec))

(defruled net-gfold-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (natp i)
                (ecurve::edwards-bls12-pointp acc)
                (equal (hbhp-dot ax) (ecurve::point-finite->x acc))
                (equal (hbhp-dot ay) (ecurve::point-finite->y acc))
                (net-gfold-wires-okp bits sts asg)
                (net-gfold-canonp bits sts i acc asg))
           (r1cs::r1cs-constraints-holdp (net-gfold-gadget bits sts i ax ay p) asg p))
  :induct (net-gfold-induct bits sts i ax ay acc asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               (:induction net-gfold-induct) nfix lnfix natp endp
               car-cons cdr-cons (:t net-gbase))
  :hints (("Subgoal *1/2"
           :expand ((:free (ax ay i p) (net-gfold-gadget bits sts i ax ay p))
                    (net-gfold-wires-okp bits sts asg)
                    (:free (i acc) (net-gfold-canonp bits sts i acc asg)))
           :use ((:instance net-gstep-complete (b (car bits)) (pt (net-gbase i)) (st (car sts)))
                 (:instance net-gbase-pointp)
                 (:instance net-pointp-of-ternary-add (pt (net-gbase i))
                            (b (lookup-equal (car bits) asg)))
                 (:instance net-dot-one-wire (w (nth 3 (car sts))))
                 (:instance net-dot-one-wire (w (nth 4 (car sts))))
                 (:instance net-ternary-add-coords (pt (net-gbase i))
                            (b (lookup-equal (car bits) asg)))))
          ("Subgoal *1/1"
           :expand ((:free (p) (net-gfold-gadget bits sts i ax ay p)))
           :in-theory '(r1cs::r1cs-constraints-holdp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The whole circuit: Scalar::to_bits_le, step 0 as linear combinations,
;; then steps 1..250.

(define net-gmul-gadget ((s symbolp) rbits rs sts (p posp))
  :verify-guards nil
  (append (scalar-write-bits-le-gadget s rbits rs p)
          (net-gfold-gadget (cdr rbits) sts 1
                            (hbhp-tern-x (car rbits) (curve-generator-g))
                            (hbhp-tern-y (car rbits) (curve-generator-g) p)
                            p)))

(define net-gmul-out (rbits sts (p posp))
  :verify-guards nil
  (net-gfold-out (cdr rbits) sts
                 (hbhp-tern-x (car rbits) (curve-generator-g))
                 (hbhp-tern-y (car rbits) (curve-generator-g) p)))

(define net-gsts-okp (bits sts asg)
  :verify-guards nil
  :short "The five wires of every step are bound non-constant wires."
  (if (endp bits)
      t
    (b* ((st (car sts)))
      (and (hbhp-wire-okp (nth 0 st)) (hbhp-wire-okp (nth 1 st))
           (hbhp-wire-okp (nth 2 st)) (hbhp-wire-okp (nth 3 st))
           (hbhp-wire-okp (nth 4 st))
           (net-gsts-okp (cdr bits) (cdr sts) asg)))))

(defruled net-gfold-wires-okp-when-bits
  (implies (and (symbol-listp bits)
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg))
                (net-gsts-okp bits sts asg))
           (net-gfold-wires-okp bits sts asg))
  :induct (net-gsts-okp bits sts asg)
  :enable (net-gsts-okp net-gfold-wires-okp lookup-equal-list
           r1cs::valuation-binds-allp))

(defruled net-gmul-first-step
  (implies (and (bitp b) (ecurve::edwards-bls12-pointp g))
           (equal (group-ternary-funspec
                   b
                   (group-add-funspec (ecurve::twisted-edwards-zero)
                                      (ecurve::edwards-bls12-mul 1 g))
                   (ecurve::twisted-edwards-zero))
                  (ecurve::edwards-bls12-mul b g)))
  :cases ((equal b 0) (equal b 1))
  :use ((:instance hbhp-mul-0 (b g))
        (:instance hbhp-mul-1 (b g))
        (:instance hbhp-add-zero-left (pt g)))
  :in-theory '(bitp group-ternary-funspec group-add-funspec (:e equal)))

(defruled net-gmul-window-of-cons
  (implies (and (bitp b) (bit-listp bs))
           (equal (g-scalar-window (cons b bs) 0 (ecurve::twisted-edwards-zero))
                  (g-scalar-window bs 1 (ecurve::edwards-bls12-mul b (curve-generator-g)))))
  :expand ((g-scalar-window (cons b bs) 0 (ecurve::twisted-edwards-zero)))
  :use ((:instance net-gmul-first-step (g (curve-generator-g))))
  :in-theory '(edwards-bls12-pointp-of-curve-generator-g car-cons cdr-cons
               nfix (:e expt) (:e binary-+) (:e natp) (:e endp) endp))

(defmacro net-gmul-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (symbolp s)
        (symbol-listp rbits)
        (symbol-listp rs)
        (equal (len rbits) 251)
        (equal (len rs) 250)
        (r1cs::valuation-bindsp asg s)
        (r1cs::valuation-binds-allp asg rbits)
        (r1cs::valuation-binds-allp asg rs)
        (net-gsts-okp (cdr rbits) sts asg)))

(defruled net-lookup-equal-list-of-cons-split
  (implies (consp xs)
           (equal (lookup-equal-list xs asg)
                  (cons (lookup-equal (car xs) asg) (lookup-equal-list (cdr xs) asg))))
  :enable lookup-equal-list)
(defruled net-bit-listp-of-cons-split
  (equal (bit-listp (cons a b)) (and (bitp a) (bit-listp b))))
(defruled net-symbol-listp-of-cons-split
  (implies (and (symbol-listp xs) (consp xs))
           (and (symbolp (car xs)) (symbol-listp (cdr xs)))))
(defruled net-binds-allp-of-cons-split
  (implies (and (r1cs::valuation-binds-allp asg xs) (consp xs))
           (and (r1cs::valuation-bindsp asg (car xs))
                (r1cs::valuation-binds-allp asg (cdr xs))))
  :enable r1cs::valuation-binds-allp)
(defruled net-car-not-1-when-symbol-listp
  (implies (and (symbol-listp xs) (consp xs))
           (not (equal (car xs) 1))))
(defruled net-consp-when-len-251
  (implies (equal (len xs) 251) (consp xs)))

(defruled net-g-scalar-multiply-sound
  (implies (and (net-gmul-hyps)
                (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
           (b* ((out (net-gmul-out rbits sts p))
                (pt (ecurve::point-finite (hbhp-dot (car out)) (hbhp-dot (cdr out)))))
             (and (scalarp (lookup-equal s asg))
                  (ecurve::edwards-bls12-pointp pt)
                  (equal pt (aleo-g-scalar-multiply-funspec (lookup-equal s asg))))))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-sound (xs rbits) (acc nil))
        (:instance net-symbol-listp-of-cons-split (xs rbits))
        (:instance net-car-not-1-when-symbol-listp (xs rbits))
        (:instance net-consp-when-len-251 (xs rbits))
        (:instance hbhp-tern-values (b (car rbits)) (pt (curve-generator-g)))
        (:instance net-point-finite-of-coords
                   (acc (ecurve::edwards-bls12-mul (lookup-equal (car rbits) asg)
                                                   (curve-generator-g))))
        (:instance net-gfold-sound
                   (bits (cdr rbits)) (i 1)
                   (ax (hbhp-tern-x (car rbits) (curve-generator-g)))
                   (ay (hbhp-tern-y (car rbits) (curve-generator-g) p))
                   (acc (ecurve::edwards-bls12-mul (lookup-equal (car rbits) asg)
                                                   (curve-generator-g))))
        (:instance net-gfold-wires-okp-when-bits (bits (cdr rbits)))
        (:instance net-gmul-window-of-cons
                   (b (lookup-equal (car rbits) asg))
                   (bs (lookup-equal-list (cdr rbits) asg)))
        (:instance g-scalar-window-of-scalar-from-zero (s (lookup-equal s asg)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (lookup-equal (car rbits) asg))
                   (point (curve-generator-g)))
        (:instance edwards-bls12-pointp-of-aleo-g-scalar-multiply-funspec (s (lookup-equal s asg))))
  :in-theory '(net-gmul-gadget net-gmul-out r1cs::r1cs-constraints-holdp-of-append
               net-lookup-equal-list-of-cons-split net-bit-listp-of-cons-split
               net-symbol-listp-of-cons-split net-binds-allp-of-cons-split
               edwards-bls12-pointp-of-curve-generator-g net-consp-when-len-251
               (:e natp) (:e len) (:e bit-listp) (:e symbolp)))

(defruled net-g-scalar-multiply-complete
  (implies (and (net-gmul-hyps)
                (scalarp (lookup-equal s asg))
                (equal (lookup-equal-list rbits asg)
                       (scalar-bits-le (lookup-equal s asg)))
                (equal (lookup-equal-list rs asg)
                       (crv-bits-lte-const-witness (lookup-equal-list rbits asg)
                                                   (scalar-modulus-minus-one-bits)))
                (net-gfold-canonp (cdr rbits) sts 1
                                  (ecurve::edwards-bls12-mul (lookup-equal (car rbits) asg)
                                                             (curve-generator-g))
                                  asg))
           (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-complete (xs rbits) (acc nil))
        (:instance bit-listp-of-scalar-bits-le (a (lookup-equal s asg)))
        (:instance net-symbol-listp-of-cons-split (xs rbits))
        (:instance net-car-not-1-when-symbol-listp (xs rbits))
        (:instance net-consp-when-len-251 (xs rbits))
        (:instance hbhp-tern-values (b (car rbits)) (pt (curve-generator-g)))
        (:instance net-gfold-complete
                   (bits (cdr rbits)) (i 1)
                   (ax (hbhp-tern-x (car rbits) (curve-generator-g)))
                   (ay (hbhp-tern-y (car rbits) (curve-generator-g) p))
                   (acc (ecurve::edwards-bls12-mul (lookup-equal (car rbits) asg)
                                                   (curve-generator-g))))
        (:instance net-gfold-wires-okp-when-bits (bits (cdr rbits)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (lookup-equal (car rbits) asg))
                   (point (curve-generator-g))))
  :in-theory '(net-gmul-gadget r1cs::r1cs-constraints-holdp-of-append
               net-lookup-equal-list-of-cons-split net-bit-listp-of-cons-split
               net-symbol-listp-of-cons-split net-binds-allp-of-cons-split
               edwards-bls12-pointp-of-curve-generator-g net-consp-when-len-251
               (:e natp) (:e len) (:e bit-listp) (:e symbolp)))
