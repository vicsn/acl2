; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One 3-bit chunk of BHPHasher::hash_uncompressed on variable bits
; (circuit/algorithms/src/bhp/hasher/hash_uncompressed.rs):
;
;   b01 = b0 AND b1                              1 constraint
;   montgomery_x = x0 + b0 (x1 - x0) + b1 (x2 - x0)
;                  + b01 (x3 - x2 - x1 + x0)     linear combination
;   y            = the same over y0..y3          linear combination
;   (-2 y) * (b2 - 1/2) = montgomery_y           1 constraint
;
; where (xk, yk) is the constant lookup entry for multiplier k + 1.  With
; boolean b0, b1, b2 the outputs are (x_k, (-1)^b2 y_k) for k = b0 + 2 b1.

(in-package "ALEOVM")

(include-book "hbhp-mont")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sparse-vector helpers.

(define hbhp-sv-scale (c vec (p posp))
  :verify-guards nil
  :short "Multiply every coefficient of a sparse vector by @('c')."
  (if (endp vec)
      nil
    (cons (list (pfield::mul c (mod (ifix (first (car vec))) p) p)
                (second (car vec)))
          (hbhp-sv-scale c (cdr vec) p))))

(defrule hbhp-dot-product-of-sv-scale
  (implies (posp p)
           (equal (r1cs::dot-product (hbhp-sv-scale c vec p) asg p)
                  (pfield::mul c (r1cs::dot-product vec asg p) p)))
  :induct (len vec)
  :enable (hbhp-sv-scale r1cs::dot-product))

(define hbhp-lookup-lc (b0 b1 b01 tab (p posp))
  :verify-guards nil
  :short "The linear combination @('t0 + b0 (t1 - t0) + b1 (t2 - t0)
          + b01 (t3 - t2 - t1 + t0)') over a 4-entry constant table."
  (b* ((t0 (nth 0 tab)) (t1 (nth 1 tab)) (t2 (nth 2 tab)) (t3 (nth 3 tab)))
    (list (list t0 1)
          (list (pfield::sub t1 t0 p) b0)
          (list (pfield::sub t2 t0 p) b1)
          (list (pfield::add (pfield::sub (pfield::sub t3 t2 p) t1 p) t0 p) b01))))

(define hbhp-half ()
  :short "@('Field::half()') of the BLS12-377 base field."
  (/ (1+ (base-prime)) 2))

(defruled hbhp-half-facts
  (implies (equal p (base-prime))
           (and (pfield::fep (hbhp-half) p)
                (equal (pfield::mul 2 (hbhp-half) p) 1)
                (equal (pfield::sub 1 (hbhp-half) p) (hbhp-half))))
  :in-theory '((:e base-prime) (:e hbhp-half) (:e pfield::fep)
               (:e pfield::mul) (:e pfield::sub) (:e equal)))

(define hbhp-chunk-gadget ((b0 symbolp) (b1 symbolp) (b2 symbolp)
                           (b01 symbolp) (my symbolp)
                           ty (p posp))
  :verify-guards nil
  :short "The two constraints of a chunk with variable bits."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 b0))
         :b (list (list 1 b1))
         :c (list (list 1 b01)))
        (r1cs::make-r1cs-constraint
         :a (hbhp-sv-scale (pfield::neg 2 p) (hbhp-lookup-lc b0 b1 b01 ty p) p)
         :b (list (list 1 b2) (list (pfield::neg (hbhp-half) p) 1))
         :c (list (list 1 my)))))

(define hbhp-sel4 (tab (b0 bitp) (b1 bitp))
  :verify-guards nil
  (nth (+ (acl2::bfix b0) (* 2 (acl2::bfix b1))) tab))

(define hbhp-fep4p (tab (p posp))
  :verify-guards nil
  (and (pfield::fep (nth 0 tab) p) (pfield::fep (nth 1 tab) p)
       (pfield::fep (nth 2 tab) p) (pfield::fep (nth 3 tab) p)))

(defruled hbhp-lookup-lc-value
  (implies (and (primep p)
                (hbhp-fep4p tab p)
                (bitp b0$) (bitp b1$)
                (equal (lookup-equal b0 asg) b0$)
                (equal (lookup-equal b1 asg) b1$)
                (equal (lookup-equal b01 asg) (pfield::mul b0$ b1$ p))
                (not (equal b0 1)) (not (equal b1 1)) (not (equal b01 1)))
           (equal (r1cs::dot-product (hbhp-lookup-lc b0 b1 b01 tab p) asg p)
                  (hbhp-sel4 tab b0$ b1$)))
  :enable (hbhp-lookup-lc hbhp-sel4 hbhp-fep4p r1cs::dot-product bitp
           acl2::lookup-eq-becomes-lookup-equal)
  :cases ((and (equal b0$ 0) (equal b1$ 0))
          (and (equal b0$ 1) (equal b1$ 0))
          (and (equal b0$ 0) (equal b1$ 1))
          (and (equal b0$ 1) (equal b1$ 1))))

(defmacro hbhp-lk (w) `(lookup-equal ,w asg))

(defruled hbhp-dot-cons
  (equal (r1cs::dot-product (cons (list c v) vec) asg p)
         (pfield::add (pfield::mul (mod c p) (if (equal v 1) 1 (lookup-equal v asg)) p)
                      (r1cs::dot-product vec asg p)
                      p))
  :enable (r1cs::dot-product acl2::lookup-eq-becomes-lookup-equal))

(defruled hbhp-dot-nil
  (equal (r1cs::dot-product nil asg p) 0)
  :enable r1cs::dot-product)

(defruledl hbhp-simple-field
  (implies (and (primep p) (< 2 p))
           (and (equal (mod 1 p) 1)
                (implies (pfield::fep x p)
                         (and (equal (pfield::mul 1 x p) x)
                              (equal (pfield::mul x 1 p) x)
                              (equal (pfield::add x 0 p) x)
                              (equal (mod x p) x))))))

(defruled hbhp-chunk-gadget-to-eqns
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b01) (symbolp my)
                (not (equal b0 1)) (not (equal b1 1)) (not (equal b2 1))
                (not (equal b01 1)) (not (equal my 1))
                (r1cs::valuation-bindsp asg b0) (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2) (r1cs::valuation-bindsp asg b01)
                (r1cs::valuation-bindsp asg my))
           (equal (r1cs::r1cs-constraints-holdp
                   (hbhp-chunk-gadget b0 b1 b2 b01 my ty p) asg p)
                  (and (equal (pfield::mul (hbhp-lk b0) (hbhp-lk b1) p) (hbhp-lk b01))
                       (equal (pfield::mul
                               (pfield::mul (pfield::neg 2 p)
                                            (r1cs::dot-product
                                             (hbhp-lookup-lc b0 b1 b01 ty p) asg p)
                                            p)
                               (pfield::add (hbhp-lk b2) (pfield::neg (hbhp-half) p) p)
                               p)
                              (hbhp-lk my)))))
  :in-theory '(hbhp-chunk-gadget r1cs::r1cs-constraint-holdsp
               r1cs::r1cs-constraints-holdp
               r1cs::r1cs-constraint->a-of-r1cs-constraint
               r1cs::r1cs-constraint->b-of-r1cs-constraint
               r1cs::r1cs-constraint->c-of-r1cs-constraint
               hbhp-base-prime-facts r1cs::fep-of-lookup-equal
               hbhp-dot-cons hbhp-dot-nil hbhp-simple-field
               hbhp-dot-product-of-sv-scale
               pfield::fep-of-neg pfield::fep-of-mul pfield::fep-of-add
               car-cons cdr-cons (:e equal) endp atom))

(defruled hbhp-chunk-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbolp b0) (symbolp b1) (symbolp b2) (symbolp b01) (symbolp my)
                (not (equal b0 1)) (not (equal b1 1)) (not (equal b2 1))
                (not (equal b01 1)) (not (equal my 1))
                (r1cs::valuation-bindsp asg b0) (r1cs::valuation-bindsp asg b1)
                (r1cs::valuation-bindsp asg b2) (r1cs::valuation-bindsp asg b01)
                (r1cs::valuation-bindsp asg my)
                (bitp (hbhp-lk b0)) (bitp (hbhp-lk b1)) (bitp (hbhp-lk b2))
                (hbhp-fep4p tx p) (hbhp-fep4p ty p)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-chunk-gadget b0 b1 b2 b01 my ty p) asg p))
           (and (equal (r1cs::dot-product (hbhp-lookup-lc b0 b1 b01 tx p) asg p)
                       (hbhp-sel4 tx (hbhp-lk b0) (hbhp-lk b1)))
                (equal (hbhp-lk my)
                       (if (equal (hbhp-lk b2) 1)
                           (pfield::neg (hbhp-sel4 ty (hbhp-lk b0) (hbhp-lk b1)) p)
                         (hbhp-sel4 ty (hbhp-lk b0) (hbhp-lk b1))))))
  :use (hbhp-chunk-gadget-to-eqns
        (:instance hbhp-lookup-lc-value (tab tx)
                   (b0$ (hbhp-lk b0)) (b1$ (hbhp-lk b1)))
        (:instance hbhp-lookup-lc-value (tab ty)
                   (b0$ (hbhp-lk b0)) (b1$ (hbhp-lk b1)))
        (:instance hbhp-fep-of-sel4 (tab ty) (b0 (hbhp-lk b0)) (b1 (hbhp-lk b1)))
        (:instance hbhp-sign-lemma
                   (y (hbhp-sel4 ty (hbhp-lk b0) (hbhp-lk b1)))
                   (b (hbhp-lk b2))))
  :in-theory '(hbhp-base-prime-facts)
  :prep-lemmas
  ((defruled hbhp-two-half-y
     (implies (and (equal p (base-prime)) (pfield::fep y p))
              (equal (pfield::mul 2 (pfield::mul (hbhp-half) y p) p) y))
     :use (hbhp-half-facts
           (:instance pfield::mul-associative
                      (pfield::x 2) (pfield::y (hbhp-half)) (pfield::z y)
                      (pfield::p p)))
     :in-theory '(hbhp-base-prime-facts pfield::mul-of-1-arg1))
   (defruled hbhp-fep-of-sel4
     (implies (hbhp-fep4p tab p)
              (pfield::fep (hbhp-sel4 tab b0 b1) p))
     :enable (hbhp-sel4 hbhp-fep4p acl2::bfix))
   (defruled hbhp-sign-lemma
     (implies (and (equal p (base-prime))
                   (pfield::fep y p) (bitp b))
              (equal (pfield::mul (pfield::mul (pfield::neg 2 p) y p)
                                  (pfield::add b (pfield::neg (hbhp-half) p) p)
                                  p)
                     (if (equal b 1) (pfield::neg y p) y)))
     :use (hbhp-half-facts hbhp-two-half-y)
     :enable (bitp hbhp-base-prime-facts)
     :disable ((:e hbhp-half)))))
