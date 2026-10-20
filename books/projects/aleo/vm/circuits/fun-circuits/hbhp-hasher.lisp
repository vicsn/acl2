; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHPHasher::hash_uncompressed on variable bits.
;
; The input is split into windows of 3w bits, window i using generator G_i
; (hbhp-window.lisp).  The window sums are folded with Group addition:
; Group::zero() + (first window) is constant-folded (no constraints), and
; every later window is added with the variable/variable Group::add gadget,
; with the new window as `this' and the accumulator as `that'.
;
; Modelled inputs: every bit is a variable (Boolean) wire and the input length
; is a multiple of 3, so no constant padding bits occur.  Inputs needing
; padding mix constant and variable bits in the last chunk, which snarkVM
; constant-folds differently; they are not covered here.

(in-package "ALEOVM")

(include-book "hbhp-window")
(include-book "crv-curve")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime)
                           (:e ecurve::edwards-bls12-q)
                           (:e ecurve::edwards-bls12-a)
                           (:e ecurve::edwards-bls12-d)
                           (:e ecurve::edwards-bls12-curve)
                           (:e ecurve::edwards-bls12-r))))

(defrulel hbhp-len-of-nthcdr
  (implies (natp n)
           (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :induct (nthcdr n x)
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group facts.

(defruled hbhp-add-comm
  (equal (ecurve::edwards-bls12-add a b) (ecurve::edwards-bls12-add b a))
  :enable ecurve::edwards-bls12-add)

(defruled hbhp-add-zero-left
  (implies (ecurve::edwards-bls12-pointp pt)
           (equal (ecurve::edwards-bls12-add (ecurve::twisted-edwards-zero) pt)
                  pt))
  :enable (ecurve::edwards-bls12-add ecurve::edwards-bls12-pointp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wires of a window without the length condition.

(define hbhp-wwires-okp (bs ws ex ey asg)
  :verify-guards nil
  (and (hbhp-wire-okp (nth 0 bs)) (hbhp-wire-okp (nth 1 bs))
       (hbhp-wire-okp (nth 2 bs))
       (bitp (hbhp-lk (nth 0 bs))) (bitp (hbhp-lk (nth 1 bs)))
       (bitp (hbhp-lk (nth 2 bs)))
       (hbhp-wire-okp (nth 0 (car ws))) (hbhp-wire-okp (nth 1 (car ws)))
       (hbhp-steps-wires-okp (nthcdr 3 bs) (cdr ws) asg)
       (hbhp-wire-okp ex) (hbhp-wire-okp ey)))

(defruled hbhp-window-wires-okp-from-wwires
  (implies (and (<= 3 (len bs)) (hbhp-wwires-okp bs ws ex ey asg))
           (hbhp-window-wires-okp bs ws ex ey asg))
  :enable (hbhp-wwires-okp hbhp-window-wires-okp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The gadget.  Each window record in `wins' is
;; (ws ex ey u v0 v1 v01 x3 y3): the window wires, its output, and the wires
;; of the Group::add into the accumulator (unused for the first window).

(defmacro hbhp-win-n (bits w)
  `(min (* 3 (acl2::pos-fix ,w)) (len ,bits)))

(define hbhp-hasher-rest (bits wins gens w xacc yacc (p posp))
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :in-theory (enable acl2::pos-fix)))
  (b* (((when (or (endp bits) (endp gens))) nil)
       (n (hbhp-win-n bits w))
       (r (car wins)))
    (append (hbhp-window-gadget (take n bits) (nth 0 r) (car gens)
                                (nth 1 r) (nth 2 r) p)
            (crv-group-add-gadget (nth 1 r) (nth 2 r) xacc yacc
                                  (nth 3 r) (nth 4 r) (nth 5 r) (nth 6 r)
                                  (nth 7 r) (nth 8 r) p)
            (hbhp-hasher-rest (nthcdr n bits) (cdr wins) (cdr gens) w
                              (nth 7 r) (nth 8 r) p))))

(define hbhp-hasher-rest-out (bits wins gens w xacc yacc)
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :in-theory (enable acl2::pos-fix)))
  (b* (((when (or (endp bits) (endp gens))) (cons xacc yacc))
       (n (hbhp-win-n bits w))
       (r (car wins)))
    (hbhp-hasher-rest-out (nthcdr n bits) (cdr wins) (cdr gens) w
                          (nth 7 r) (nth 8 r))))

(define hbhp-hasher-rest-wires-okp (bits wins gens w asg)
  :verify-guards nil
  :measure (len bits)
  :hints (("Goal" :in-theory (enable acl2::pos-fix)))
  (b* (((when (or (endp bits) (endp gens))) t)
       (n (hbhp-win-n bits w))
       (r (car wins)))
    (and (hbhp-wwires-okp (take n bits) (nth 0 r) (nth 1 r) (nth 2 r) asg)
         (hbhp-wire-okp (nth 3 r)) (hbhp-wire-okp (nth 4 r))
         (hbhp-wire-okp (nth 5 r)) (hbhp-wire-okp (nth 6 r))
         (hbhp-wire-okp (nth 7 r)) (hbhp-wire-okp (nth 8 r))
         (hbhp-hasher-rest-wires-okp (nthcdr n bits) (cdr wins) (cdr gens) w
                                     asg))))

(define hbhp-hasher-gadget (bits wins gens w (p posp))
  :verify-guards nil
  :short "The constraints of @('BHPHasher::hash_uncompressed') on the
          variable bit wires @('bits')."
  (b* ((n (hbhp-win-n bits w))
       (r (car wins)))
    (append (hbhp-window-gadget (take n bits) (nth 0 r) (car gens)
                                (nth 1 r) (nth 2 r) p)
            (hbhp-hasher-rest (nthcdr n bits) (cdr wins) (cdr gens) w
                              (nth 1 r) (nth 2 r) p))))

(define hbhp-hasher-out (bits wins gens w)
  :verify-guards nil
  :short "The output wires @('(x . y)') of the gadget."
  (b* ((n (hbhp-win-n bits w))
       (r (car wins)))
    (hbhp-hasher-rest-out (nthcdr n bits) (cdr wins) (cdr gens) w
                          (nth 1 r) (nth 2 r))))

(define hbhp-hasher-wires-okp (bits wins gens w asg)
  :verify-guards nil
  (b* ((n (hbhp-win-n bits w))
       (r (car wins)))
    (and (hbhp-wwires-okp (take n bits) (nth 0 r) (nth 1 r) (nth 2 r) asg)
         (hbhp-hasher-rest-wires-okp (nthcdr n bits) (cdr wins) (cdr gens) w
                                     asg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Window lengths.

(defruled hbhp-nchunks-bound
  (<= (* 3 (hbhp-nchunks bs)) (len bs))
  :induct (hbhp-nchunks bs)
  :enable hbhp-nchunks)

(defruled hbhp-win-n-facts
  (implies (and (natp len) (< 0 len) (equal (mod len 3) 0) (posp w))
           (and (<= 3 (min (* 3 w) len))
                (<= (min (* 3 w) len) len)
                (<= (min (* 3 w) len) (* 3 w))
                (natp (min (* 3 w) len))
                (equal (mod (- len (min (* 3 w) len)) 3) 0)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled hbhp-window-nchunks-ok
  (implies (and (posp w) (<= w 63) (<= n (* 3 w)) (natp n) (<= n (len bits)))
           (<= (hbhp-nchunks (take n bits)) 63))
  :use (:instance hbhp-nchunks-bound (bs (take n bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values.

(defruled hbhp-take-of-lk-list
  (implies (<= (nfix n) (len bs))
           (equal (take n (hbhp-lk-list bs asg)) (hbhp-lk-list (take n bs) asg)))
  :induct (take n bs)
  :enable (hbhp-lk-list take))

(defruled hbhp-consp-of-lk-list
  (equal (consp (hbhp-lk-list bs asg)) (consp bs))
  :expand (hbhp-lk-list bs asg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One window plus the addition into the accumulator.

(defruled hbhp-hasher-window-step
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gen-okp g)
                (posp w) (<= w 63)
                (natp n) (<= 3 n) (<= n (* 3 w)) (<= n (len bits))
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-wwires-okp (take n bits) ws ex ey asg)
                (hbhp-wire-okp u) (hbhp-wire-okp v0) (hbhp-wire-okp v1)
                (hbhp-wire-okp v01) (hbhp-wire-okp x3) (hbhp-wire-okp y3)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-window-gadget (take n bits) ws g ex ey p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (crv-group-add-gadget ex ey xacc yacc u v0 v1 v01 x3 y3 p)
                 asg p))
           (equal (ecurve::point-finite (hbhp-lk x3) (hbhp-lk y3))
                  (ecurve::edwards-bls12-add
                   acc
                   (hbhp-gp (hbhp-window-scalar
                             (take n (hbhp-lk-list bits asg)) 0)
                            g))))
  :use ((:instance hbhp-window-gadget-sound-spec (bs (take n bits)))
        (:instance hbhp-window-wires-okp-from-wwires (bs (take n bits)))
        (:instance hbhp-window-nchunks-ok)
        (:instance hbhp-take-of-lk-list (bs bits))
        (:instance crv-group-add-gadget-sound
                   (x1 ex) (y1 ey) (x2 xacc) (y2 yacc)
                   (p1 (hbhp-gp (hbhp-window-scalar
                                 (hbhp-lk-list (take n bits) asg) 0)
                                g))
                   (p2 acc))
        (:instance hbhp-add-comm
                   (a acc)
                   (b (hbhp-gp (hbhp-window-scalar
                                (hbhp-lk-list (take n bits) asg) 0)
                               g)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (hbhp-lk-list (take n bits) asg) 0))
                   (point g))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x g))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ex) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var ey) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var xacc) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var yacc) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :in-theory (e/d (group-add-funspec hbhp-wwires-okp hbhp-base-prime-facts
                   pfield::fep)
                  (ecurve::edwards-bls12-mul ecurve::edwards-bls12-add
                   hbhp-window-gadget crv-group-add-gadget
                   hbhp-window-wires-okp hbhp-steps-wires-okp
                   hbhp-window-scalar hbhp-lk-list hbhp-nchunks
                   ecurve::edwards-bls12-r-pointp
                   ecurve::edwards-bls12-pointp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fold.

(defun hbhp-rest-induct (bits wins gens w xacc yacc acc asg)
  (declare (xargs :measure (len bits) :verify-guards nil
                  :hints (("Goal" :in-theory (enable acl2::pos-fix)))))
  (b* (((when (or (endp bits) (endp gens))) (list wins xacc yacc acc asg))
       (n (hbhp-win-n bits w))
       (r (car wins)))
    (hbhp-rest-induct (nthcdr n bits) (cdr wins) (cdr gens) w
                      (nth 7 r) (nth 8 r)
                      (ecurve::edwards-bls12-add
                       acc
                       (hbhp-gp (hbhp-window-scalar
                                 (take n (hbhp-lk-list bits asg)) 0)
                                (car gens)))
                      asg)))

(defruledl hbhp-len-pos
  (implies (consp x) (< 0 (len x))))

(defruled hbhp-hasher-rest-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-r-point-listp gens) (hbhp-nonzero-listp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (ecurve::edwards-bls12-pointp acc)
                (hbhp-wire-okp xacc) (hbhp-wire-okp yacc)
                (equal (ecurve::point-finite (hbhp-lk xacc) (hbhp-lk yacc)) acc)
                (hbhp-hasher-rest-wires-okp bits wins gens w asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-rest bits wins gens w xacc yacc p) asg p))
           (b* ((out (hbhp-hasher-rest-out bits wins gens w xacc yacc)))
             (equal (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))
                    (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w acc))))
  :induct (hbhp-rest-induct bits wins gens w xacc yacc acc asg)
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append
               hbhp-nthcdr-of-lk-list hbhp-consp-of-lk-list hbhp-len-of-lk-list
               hbhp-r-point-listp hbhp-nonzero-listp acl2::pos-fix posp natp
               hbhp-len-of-nthcdr nfix hbhp-len-pos (:induction hbhp-rest-induct)
               endp atom not car-cons cdr-cons (:t min) (:t len))
  :hints (("Subgoal *1/2"
           :expand ((:free (gens xacc yacc p)
                     (hbhp-hasher-rest bits wins gens w xacc yacc p))
                    (:free (gens xacc yacc)
                     (hbhp-hasher-rest-out bits wins gens w xacc yacc))
                    (:free (gens) (hbhp-hasher-rest-wires-okp bits wins gens w asg))
                    (:free (gens acc)
                     (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w acc)))
           :use ((:instance hbhp-hasher-window-step
                            (g (car gens)) (n (hbhp-win-n bits w))
                            (ws (nth 0 (car wins)))
                            (ex (nth 1 (car wins))) (ey (nth 2 (car wins)))
                            (u (nth 3 (car wins))) (v0 (nth 4 (car wins)))
                            (v1 (nth 5 (car wins))) (v01 (nth 6 (car wins)))
                            (x3 (nth 7 (car wins))) (y3 (nth 8 (car wins))))
                 (:instance hbhp-win-n-facts (len (len bits)))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                            (ecurve::point1 acc)
                            (ecurve::point2
                             (hbhp-gp (hbhp-window-scalar
                                       (take (hbhp-win-n bits w)
                                             (hbhp-lk-list bits asg)) 0)
                                      (car gens))))
                 (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                            (ecurve::scalar
                             (hbhp-window-scalar
                              (take (hbhp-win-n bits w) (hbhp-lk-list bits asg)) 0))
                            (point (car gens)))
                 (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                            (ecurve::x (car gens)))))
          ("Subgoal *1/1"
           :expand ((:free (gens xacc yacc)
                     (hbhp-hasher-rest-out bits wins gens w xacc yacc))
                    (:free (gens acc)
                     (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w acc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top level.

(defrule hbhp-true-listp-of-lk-list
  (true-listp (hbhp-lk-list bs asg))
  :enable hbhp-lk-list)

(defruled hbhp-pad-when-mod-3
  (implies (and (true-listp x) (equal (mod (len x) 3) 0))
           (equal (hbhp-pad x) x))
  :enable hbhp-pad
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl hbhp-len-atom
  (implies (not (consp x)) (equal (len x) 0)))

(defruledl hbhp-len-of-take
  (equal (len (take n x)) (nfix n)))

(defruled hbhp-hasher-gadget-sound
  :short "Soundness of @('BHPHasher::hash_uncompressed') on variable bits."
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (hbhp-gens-okp gens)
                (posp w) (<= w 63)
                (equal (mod (len bits) 3) 0)
                (< (* 3 w) (len bits))
                (<= (len bits) (* 3 w (len gens)))
                (hbhp-hasher-wires-okp bits wins gens w asg)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hasher-gadget bits wins gens w p) asg p))
           (b* ((out (hbhp-hasher-out bits wins gens w)))
             (equal (hbhp-hasher-hash-uncompressed gens w (hbhp-lk-list bits asg))
                    (ecurve::point-finite (hbhp-lk (car out))
                                          (hbhp-lk (cdr out))))))
  :use ((:instance hbhp-window-gadget-sound-spec
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins))) (g (car gens))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-wires-okp-from-wwires
                   (bs (take (hbhp-win-n bits w) bits))
                   (ws (nth 0 (car wins)))
                   (ex (nth 1 (car wins))) (ey (nth 2 (car wins))))
        (:instance hbhp-window-nchunks-ok (n (hbhp-win-n bits w)))
        (:instance hbhp-take-of-lk-list (bs bits) (n (hbhp-win-n bits w)))
        (:instance hbhp-win-n-facts (len (len bits)))
        (:instance hbhp-hasher-rest-sound
                   (bits (nthcdr (hbhp-win-n bits w) bits))
                   (wins (cdr wins)) (gens (cdr gens))
                   (xacc (nth 1 (car wins))) (yacc (nth 2 (car wins)))
                   (acc (hbhp-gp (hbhp-window-scalar
                                  (take (hbhp-win-n bits w)
                                        (hbhp-lk-list bits asg)) 0)
                                 (car gens))))
        (:instance hbhp-add-zero-left
                   (pt (hbhp-gp (hbhp-window-scalar
                                 (take (hbhp-win-n bits w)
                                       (hbhp-lk-list bits asg)) 0)
                                (car gens))))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-mul
                   (ecurve::scalar (hbhp-window-scalar
                                    (take (hbhp-win-n bits w)
                                          (hbhp-lk-list bits asg)) 0))
                   (point (car gens)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x (car gens)))
        (:instance hbhp-pad-when-mod-3 (x (hbhp-lk-list bits asg))))
  :in-theory '(hbhp-hasher-hash-uncompressed hbhp-hasher-gadget hbhp-hasher-out
               hbhp-hasher-wires-okp hbhp-gens-okp hbhp-r-point-listp
               hbhp-nonzero-listp r1cs::r1cs-constraints-holdp-of-append
               hbhp-nthcdr-of-lk-list hbhp-consp-of-lk-list hbhp-len-of-lk-list
               hbhp-true-listp-of-lk-list acl2::pos-fix posp natp
               hbhp-len-of-nthcdr nfix hbhp-len-pos
               endp atom not car-cons cdr-cons (:t min) (:t len)
               (:t hbhp-lk-list) (:e ecurve::twisted-edwards-zero)
               hbhp-len-of-take hbhp-wwires-okp hbhp-len-atom)
  :hints (("Goal"
           :expand ((:free (gens acc)
                     (hbhp-hasher-sum (hbhp-lk-list bits asg) gens w acc))))))
