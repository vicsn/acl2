; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PathHash::hash_children for BHP and Keccak against the funspec
; crypto-merkle-hash-children (fun-specs/crypto-merkle.lisp).
;
; BHP (circuit/collections/src/merkle_tree/helpers/path_hash.rs): the
; circuit of hbhp-hc.lisp, with hasher (:bhp . size) and children
; (list left right).
;
; Keccak (circuit/collections/src/kary_merkle_tree/helpers/path_hash.rs):
; the children are BooleanHash<VARIANT> values, i.e. lists of VARIANT bit
; wires; the circuit flattens them, hashes [true] ++ bits with
; hkec-g-hash-children (hkec-main.lisp) and keeps output[..VARIANT]
; (clone_from_slice, no constraint; it panics when VARIANT exceeds the
; output length).  The hasher is (:keccak instance . VARIANT) where
; instance = (TYPE . BITS) as in hkec-variant-p.

(in-package "ALEOVM")

(include-book "hbhp-hc")
(include-book "hkec-main")
(include-book "../fun-specs/crypto-merkle")

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHP.

(defruledl hmrk-crypto-field-bits-le-is-field-bits-le
  (implies (fieldp x)
           (equal (crypto-field-bits-le x) (field-bits-le x)))
  :enable (crypto-field-bits-le crypto-nat->lebits field-bits-le fieldp
           pfield::fep-fix pfield::fep base-field-size-in-bits))

(defruledl hmrk-bhp-children-bits
  (implies (and (equal (car ph) :bhp) (fieldp l) (fieldp r))
           (equal (crypto-merkle-hash-list-bits ph (list l r))
                  (append (field-bits-le l) (field-bits-le r))))
  :enable (crypto-merkle-hash-list-bits crypto-merkle-hash-bits
           crypto-keccak-hasher-p hmrk-crypto-field-bits-le-is-field-bits-le))

(defruledl hmrk-bhp-funspec
  (implies (and (fieldp l) (fieldp r))
           (equal (crypto-merkle-hash-children (cons :bhp size) (list l r))
                  (hbhp-bhp-hash size (cons 1 (append (field-bits-le l)
                                                      (field-bits-le r))))))
  :enable (crypto-merkle-hash-children crypto-hash-bhp crypto-group-x
           bhp-hash-uncompressed hbhp-bhp-hash
           ecurve::edwards-bls12-point->u
           ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp)
  :use ((:instance hmrk-bhp-children-bits (ph (cons :bhp size)))
        (:instance hbhp-r-pointp-of-bhp-hash-uncompressed
                   (bits (cons 1 (append (field-bits-le l) (field-bits-le r)))))))

(defruledl hmrk-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg x))
           (fieldp (lookup-equal x asg)))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var x)
                   (r1cs::prime (base-prime)) (r1cs::valuation asg))
        primep-of-base-prime)
  :in-theory '(fieldp))

(defruledl hmrk-hc-fieldp-of-children
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (hbhp-hc-wires-okp l r fl rl fr rr cbits wins0 its gens w m c max asg))
           (and (fieldp (lookup-equal l asg))
                (fieldp (lookup-equal r asg))))
  :use ((:instance hmrk-fieldp-of-lookup (x l))
        (:instance hmrk-fieldp-of-lookup (x r)))
  :in-theory '(hbhp-hc-wires-okp))

(defruledl hmrk-fieldp-of-bhp-children
  (fieldp (crypto-merkle-hash-children (cons :bhp size) children))
  :use (:instance fieldp-of-crypto-merkle-hash-children (ph (cons :bhp size)))
  :in-theory '(crypto-field-hasher-p (:e eq) car-cons))

; The output wire is read as (nfix (lookup-equal x asg)), the value of a
; possibly unbound wire, as in hbhp-bhp-hc-sound.
(defruled hmrk-bhp-hash-children-sound
  (implies (and (hbhp-bhp-hc-hyps)
                (r1cs::r1cs-constraints-holdp
                 (hbhp-hc-gadget l r fl rl fr rr cbits wins0 its gens w m c max u p)
                 asg p))
           (b* ((out (hbhp-hc-out fl fr cbits wins0 its gens w m c max))
                (h (nfix (lookup-equal (car out) asg))))
             (and (fieldp h)
                  (equal h (crypto-merkle-hash-children
                            (cons :bhp size)
                            (list (lookup-equal l asg) (lookup-equal r asg)))))))
  :use (hbhp-bhp-hc-sound
        hmrk-hc-fieldp-of-children
        (:instance hmrk-fieldp-of-bhp-children
                   (children (list (lookup-equal l asg) (lookup-equal r asg))))
        (:instance hmrk-bhp-funspec (l (lookup-equal l asg)) (r (lookup-equal r asg))))
  :in-theory nil)

(defruled hmrk-bhp-hash-children-complete
  (implies (and (hbhp-bhp-hc-hyps)
                (hbhp-hc-canon l r fl rl fr rr cbits wins0 its gens w m c max asg))
           (b* ((out (hbhp-hc-out fl fr cbits wins0 its gens w m c max)))
             (and (r1cs::r1cs-constraints-holdp
                   (hbhp-hc-gadget l r fl rl fr rr cbits wins0 its gens w m c max u p)
                   asg p)
                  (equal (nfix (lookup-equal (car out) asg))
                         (crypto-merkle-hash-children
                          (cons :bhp size)
                          (list (lookup-equal l asg) (lookup-equal r asg)))))))
  :use (hbhp-bhp-hc-complete hmrk-bhp-hash-children-sound)
  :in-theory nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keccak.

(defun hmrk-flatten (xss)
  (if (atom xss) nil (append (car xss) (hmrk-flatten (cdr xss)))))

(defun hmrk-eval-lists (xss asg p)
  (if (atom xss)
      nil
    (cons (hkec-eval-list (car xss) asg p)
          (hmrk-eval-lists (cdr xss) asg p))))

(defun hmrk-wires-lists-p (xss asg p)
  (if (atom xss)
      t
    (and (hkec-wires-p (car xss) asg p)
         (hmrk-wires-lists-p (cdr xss) asg p))))

(defruledl hmrk-eval-list-of-append
  (equal (hkec-eval-list (append a b) asg p)
         (append (hkec-eval-list a asg p) (hkec-eval-list b asg p))))

(defruledl hmrk-wires-p-of-append
  (equal (hkec-wires-p (append a b) asg p)
         (and (hkec-wires-p a asg p) (hkec-wires-p b asg p))))

(defrule hmrk-wires-p-of-flatten
  (equal (hkec-wires-p (hmrk-flatten xss) asg p)
         (hmrk-wires-lists-p xss asg p))
  :enable hmrk-wires-p-of-append)

(defrule hmrk-eval-list-of-flatten
  (implies (and (crypto-hasher-p ph)
                (equal (car ph) :keccak)
                (equal (hmrk-eval-lists xss asg p) children))
           (equal (hkec-eval-list (hmrk-flatten xss) asg p)
                  (crypto-merkle-hash-list-bits ph children)))
  :induct (hmrk-eval-lists xss asg p)
  :enable (hmrk-eval-list-of-append crypto-merkle-hash-list-bits
           crypto-merkle-hash-bits crypto-keccak-hasher-p))

(defruledl hmrk-not-reserrp-when-bit-listp
  (implies (bit-listp x) (not (reserrp x)))
  :enable (reserrp bit-listp))

(defruled hmrk-keccak-funspec
  (implies (and (hkec-variant-p variant)
                (posp v)
                (<= v (cdr variant)))
           (equal (crypto-merkle-hash-children (cons :keccak (cons variant v)) children)
                  (take v (hkec-keccak-family-hash
                           variant
                           (cons 1 (crypto-merkle-hash-list-bits
                                    (cons :keccak (cons variant v)) children))))))
  :enable (crypto-merkle-hash-children crypto-keccak-truncate crypto-hash-keccak
           keccak-family-hash crypto-keccak-variant)
  :use (:instance hmrk-not-reserrp-when-bit-listp
                  (x (hkec-keccak-family-hash
                      variant
                      (cons 1 (crypto-merkle-hash-list-bits
                               (cons :keccak (cons variant v)) children))))))

(defruled hmrk-keccak-funspec-error
  (implies (and (hkec-variant-p variant)
                (posp v)
                (< (cdr variant) v))
           (reserrp (crypto-merkle-hash-children (cons :keccak (cons variant v)) children)))
  :enable (crypto-merkle-hash-children crypto-keccak-truncate crypto-hash-keccak
           keccak-family-hash crypto-keccak-variant spec-error))

(defrule hmrk-eval-list-of-take
  (implies (<= (nfix n) (len xs))
           (equal (hkec-eval-list (take n xs) asg p)
                  (take n (hkec-eval-list xs asg p)))))

(defrule hmrk-len-of-eval-list
  (equal (len (hkec-eval-list xs asg p)) (len xs)))

(defrule hmrk-wires-p-of-take
  (implies (and (hkec-wires-p xs asg p) (<= (nfix n) (len xs)))
           (hkec-wires-p (take n xs) asg p)))

(defruled hmrk-keccak-hash-children-sound
  (b* ((ph (cons :keccak (cons variant v)))
       ((mv out cs) (hkec-g-hash-children variant (hmrk-flatten child-wires) p)))
    (implies (and (primep p)
                  (hkec-variant-p variant)
                  (posp v)
                  (<= v (cdr variant))
                  (hmrk-wires-lists-p child-wires asg p)
                  (equal (hmrk-eval-lists child-wires asg p) children)
                  (r1cs::r1cs-constraints-holdp cs asg p))
             (b* ((h (hkec-eval-list (take v out) asg p)))
               (and (hkec-wires-p (take v out) asg p)
                    (crypto-merkle-hash-p ph h)
                    (equal h (crypto-merkle-hash-children ph children))))))
  :use ((:instance hkec-g-hash-children-sound (children-bits (hmrk-flatten child-wires)))
        (:instance hmrk-len-of-eval-list
                   (xs (mv-nth 0 (hkec-g-hash-children variant (hmrk-flatten child-wires) p))))
        (:instance len-of-hkec-keccak-family-hash
                   (input-bits (cons 1 (hkec-eval-list (hmrk-flatten child-wires) asg p))))
        hmrk-keccak-funspec
        (:instance hmrk-eval-list-of-flatten
                   (ph (cons :keccak (cons variant v)))
                   (xss child-wires)))
  :enable (crypto-merkle-hash-p crypto-keccak-hasher-p crypto-keccak-variant
           crypto-hasher-p)
  :disable (hkec-g-hash-children-sound hmrk-eval-list-of-flatten
            hmrk-len-of-eval-list len-of-hkec-keccak-family-hash))

(defruled hmrk-keccak-hash-children-complete
  (b* ((ph (cons :keccak (cons variant v)))
       (bits (hmrk-flatten child-wires))
       ((mv out cs) (hkec-g-hash-children variant bits p))
       (asg2 (hkec-solve cs asg p)))
    (implies (and (primep p)
                  (hkec-variant-p variant)
                  (posp v)
                  (<= v (cdr variant))
                  (hkec-terms-ok bits 0)
                  (hmrk-wires-lists-p child-wires asg p)
                  (equal (hmrk-eval-lists child-wires asg p) children))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-list bits asg2 p) (hkec-eval-list bits asg p))
                  (equal (take v (hkec-eval-list out asg2 p))
                         (crypto-merkle-hash-children ph children)))))
  :use ((:instance hkec-g-hash-children-complete (children-bits (hmrk-flatten child-wires)))
        hmrk-keccak-funspec
        (:instance hmrk-eval-list-of-flatten
                   (ph (cons :keccak (cons variant v)))
                   (xss child-wires)))
  :enable crypto-hasher-p
  :disable (hkec-g-hash-children-complete hmrk-eval-list-of-flatten))
