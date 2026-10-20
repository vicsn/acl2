; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete Elligator2 (snarkVM console/algorithms/src/elligator2/encode.rs).
;
; This book does not include base.lisp, so that base.lisp can include it:
; base.lisp's elligator2-encode is hped-elligator2-encode-total, and the
; failure condition used by curve-network.lisp is hped-elligator2-encode-validp.  The field is (ecurve::edwards-bls12-q),
; which is (base-prime).
;
; The console code is followed step by step.  The Legendre symbol is computed
; as snarkVM's fields compute it, s = g^((p-1)/2), with s = 0 the zero symbol,
; s = 1 a residue, and any other value a non-residue (s = p-1 by Euler; see
; hped-ell2-legendre-cases).  The console's LegendreSymbol::Zero arm of the x
; and y matches is unreachable, because e = 0 is rejected just before.
; The returned sign bit (the console returns (group, sign_high)) is not part
; of the result: the circuit does not compute it.
;
; Each console `ensure!`/`bail!` is a (reserr) result.  After the cofactor
; clear, the console also checks the curve and the subgroup; both always hold
; (hped-elligator2-encode-r-pointp), so the result is a subgroup point
; whenever it is not an error.

(in-package "ALEOVM")

(include-book "kestrel/crypto/ecurve/prime-field-squares" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "../edwards-order/group-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constants (snarkVM curves/src/edwards_bls12/parameters.rs).

(define hped-ell2-montgomery-a ()
  :returns (a natp :rule-classes (:rewrite :type-prescription))
  :short "@('MONTGOMERY_A')."
  3990301581132929505568273333084066329187552697088022219156688740916631500114)

(define hped-ell2-montgomery-b ()
  :returns (b natp :rule-classes (:rewrite :type-prescription))
  :short "@('MONTGOMERY_B')."
  4454160168295440918680551605697480202188346638066041608778544715000777738925)

(in-theory (disable (:e hped-ell2-montgomery-a) (:e hped-ell2-montgomery-b)))

(defrule hped-ell2-fep-of-montgomery-a
  (pfield::fep (hped-ell2-montgomery-a) (ecurve::edwards-bls12-q))
  :enable (hped-ell2-montgomery-a ecurve::edwards-bls12-q pfield::fep))

(defrule hped-ell2-fep-of-montgomery-b
  (pfield::fep (hped-ell2-montgomery-b) (ecurve::edwards-bls12-q))
  :enable (hped-ell2-montgomery-b ecurve::edwards-bls12-q pfield::fep))

(defrule hped-ell2-montgomery-b-not-zero
  (not (equal (hped-ell2-montgomery-b) 0))
  :enable hped-ell2-montgomery-b)

(define hped-ell2-a ()
  :returns (a (pfield::fep a (ecurve::edwards-bls12-q)) :hints (("Goal" :in-theory (enable ecurve::edwards-bls12-q pfield::fep))))
  :short "Weierstrass coefficient @($A / B$)."
  (b* ((q (ecurve::edwards-bls12-q)))
    (pfield::mul (hped-ell2-montgomery-a)
                 (pfield::inv (hped-ell2-montgomery-b) q)
                 q)))

(define hped-ell2-b ()
  :returns (b (pfield::fep b (ecurve::edwards-bls12-q)) :hints (("Goal" :in-theory (enable ecurve::edwards-bls12-q pfield::fep))))
  :short "Weierstrass coefficient @($1 / B^2$)."
  (b* ((q (ecurve::edwards-bls12-q))
       (binv (pfield::inv (hped-ell2-montgomery-b) q)))
    (pfield::mul binv binv q)))

(in-theory (disable (:e hped-ell2-a) (:e hped-ell2-b)))

(define hped-ell2-legendre-exp ()
  :returns (c natp :rule-classes (:rewrite :type-prescription))
  :short "@('MODULUS_MINUS_ONE_DIV_TWO')."
  (floor (1- (ecurve::edwards-bls12-q)) 2))

(define hped-ell2-legendre ((g (pfield::fep g (ecurve::edwards-bls12-q))))
  :returns (s (pfield::fep s (ecurve::edwards-bls12-q)))
  :short "snarkVM's Legendre computation @($g^{(p-1)/2}$);
          0, 1, and otherwise a non-residue."
  (pfield::pow g (hped-ell2-legendre-exp) (ecurve::edwards-bls12-q)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; console/algorithms/src/elligator2/encode.rs: encode_without_cofactor_clear
(define hped-elligator2-encode-without-cofactor-clear
  ((input (pfield::fep input (ecurve::edwards-bls12-q))))
  :returns (pt (implies (not (reserrp pt)) (ecurve::edwards-bls12-pointp pt)))
  :short "The twisted Edwards point before the cofactor clear, or an error."
  (b* ((q (ecurve::edwards-bls12-q))
       ((when (equal input 0)) (reserr :input-zero))
       (a (hped-ell2-a))
       (b (hped-ell2-b))
       (ur2 (pfield::mul (ecurve::edwards-bls12-d) (pfield::mul input input q) q))
       (one+ur2 (pfield::add 1 ur2 q))
       ((when (equal (pfield::mul (pfield::mul a a q) ur2 q)
                     (pfield::mul b (pfield::mul one+ur2 one+ur2 q) q)))
        (reserr :a2ur2-equals-b-one+ur2-squared))
       ((when (equal one+ur2 0)) (reserr :one+ur2-zero))
       (v (pfield::mul (pfield::neg a q) (pfield::inv one+ur2 q) q))
       ((when (equal v 0)) (reserr :v-zero))
       (v2 (pfield::mul v v q))
       (e (hped-ell2-legendre
           (pfield::add (pfield::add (pfield::mul v2 v q) (pfield::mul a v2 q) q)
                        (pfield::mul b v q)
                        q)))
       ((when (equal e 0)) (reserr :e-zero))
       (x (if (equal e 1) v (pfield::sub (pfield::neg v q) a q)))
       ((when (equal x 0)) (reserr :x-zero))
       (x2 (pfield::mul x x q))
       (rhs (pfield::add (pfield::add (pfield::mul x2 x q) (pfield::mul a x2 q) q)
                         (pfield::mul b x q)
                         q))
       ((unless (ecurve::pfield-even-squarep rhs q)) (reserr :no-even-sqrt))
       (value (pfield::fep-fix (ecurve::pfield-square->even-root rhs q) q))
       (y (if (equal e 1) (pfield::neg value q) value))
       ((when (equal y 0)) (reserr :y-zero))
       ((unless (equal (pfield::mul y y q) rhs)) (reserr :not-weierstrass))
       (mb (hped-ell2-montgomery-b))
       (ma (hped-ell2-montgomery-a))
       (u (pfield::mul mb x q))
       (vm (pfield::mul mb y q))
       (u2 (pfield::mul u u q))
       ((unless (equal (pfield::mul mb (pfield::mul vm vm q) q)
                       (pfield::add (pfield::add (pfield::mul u2 u q)
                                                 (pfield::mul ma u2 q)
                                                 q)
                                    u q)))
        (reserr :not-montgomery))
       ((when (equal vm 0)) (reserr :vm-zero))
       (xe (pfield::mul u (pfield::inv vm q) q))
       ((when (equal (pfield::add u 1 q) 0)) (reserr :u+1-zero))
       (ye (pfield::mul (pfield::sub u 1 q) (pfield::inv (pfield::add u 1 q) q) q))
       (pt (ecurve::point-finite xe ye))
       ((unless (ecurve::edwards-bls12-pointp pt)) (reserr :not-on-curve)))
    pt)
  :guard-hints (("Goal" :in-theory (enable ecurve::fep-of-pfield-square->root))))

; console/algorithms/src/elligator2/encode.rs: encode
(define hped-elligator2-encode ((input (pfield::fep input (ecurve::edwards-bls12-q))))
  :returns (pt (implies (not (reserrp pt)) (ecurve::edwards-bls12-r-pointp pt))
               :hints (("Goal" :use (:instance ecurve::edwards-bls12-r-pointp-of-4q
                                               (ecurve::q (hped-elligator2-encode-without-cofactor-clear input))))))
  :short "@('Elligator2::encode'): the cofactor-cleared point @($4 P$),
          computed as two doublings, or an error."
  (b* ((pt (hped-elligator2-encode-without-cofactor-clear input))
       ((when (reserrp pt)) pt)
       (pt2 (ecurve::edwards-bls12-add pt pt))
       (pt4 (ecurve::edwards-bls12-add pt2 pt2))
       ((unless (ecurve::edwards-bls12-r-pointp pt4)) (reserr :not-in-subgroup)))
    pt4))

(define hped-elligator2-encode-validp (input)
  :returns (yes/no booleanp)
  :short "Elligator2 succeeds on @('input')."
  (and (pfield::fep input (ecurve::edwards-bls12-q))
       (not (reserrp (hped-elligator2-encode input))))
  ///
  (defrule hped-elligator2-encode-validp-of-0
    (not (hped-elligator2-encode-validp 0))
    :enable (hped-elligator2-encode
             hped-elligator2-encode-without-cofactor-clear)))

(defruled hped-ell2-r-pointp-of-zero
  (ecurve::edwards-bls12-r-pointp (ecurve::twisted-edwards-zero))
  :enable (ecurve::edwards-bls12-r-pointp
           ecurve::edwards-bls12-pointp
           ecurve::edwards-bls12-mul))

(define hped-elligator2-encode-total (input)
  :returns (pt ecurve::edwards-bls12-r-pointp
               :hints (("Goal" :in-theory (enable hped-elligator2-encode-validp
                                                  hped-ell2-r-pointp-of-zero))))
  :short "Total version for base.lisp's @('elligator2-encode'):
          the zero point where @(tsee hped-elligator2-encode-validp) fails."
  (if (hped-elligator2-encode-validp input)
      (hped-elligator2-encode input)
    (ecurve::twisted-edwards-zero))
  :guard-hints (("Goal" :in-theory (enable hped-elligator2-encode-validp))))
