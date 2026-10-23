; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Poseidon as a Merkle leaf / path hasher (merkle_tree/helpers/{leaf,path}_hash.rs):
; hash_leaf(leaf) = Hash::hash([0field] ++ leaf) and
; hash_children(l, r) = Hash::hash([1field, l, r]), Hash::hash being the
; first output of hash_many with one output.  The hasher is a constant
; Poseidon instance: a network one (rate 2, 4, 8, domain AleoPoseidon{rate})
; or Poseidon{rate}::setup(domain) for a pair (domain . rate) as in
; poseidon-hash-many (fun-specs/base.lisp).
;
; mrk-psd-hash-sound / -complete relate the hpos circuits to
; crypto-poseidon-hash-instance; mrk-psd-level-hash-sound discharges one level
; of mrk-levels-hash-soundp (mrk-pathv.lisp).

(in-package "ALEOVM")

(include-book "mrk-pathv")
(include-book "hpos-aleo")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defund mrk-psd-instance-p (inst)
  (declare (xargs :verify-guards nil))
  (if (consp inst)
      (and (stringp (car inst)) (hpos-aleo-rate-p (cdr inst)))
    (hpos-aleo-rate-p inst)))

; The circuit of Poseidon::hash_many(xs, nout) for the instance.
(defund mrk-psd-hash-many-circuit (inst xs nout vs asg)
  (declare (xargs :verify-guards nil))
  (if (consp inst)
      (hpos-c-hash-many (hpos-domain-fe (car inst)) xs nout (cdr inst)
                        (hpos-aleo-params (cdr inst)) (hpos-alpha-bits) vs asg)
    (hpos-c-poseidon-hash-many inst xs nout vs asg)))

(defruledl mrk-psd-fep-of-domain-fe
  (pfield::fep (hpos-domain-fe d) primes::*bls12-377-scalar-field-prime*)
  :enable (hpos-domain-fe pfield::fep))

(defruled mrk-psd-hash-many-sound
  (b* (((mv outs cs & &) (mrk-psd-hash-many-circuit inst xs nout vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (mrk-psd-instance-p inst)
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list outs asgx p)
                    (poseidon-hash-many inst (hpos-lc-eval-list xs asgx p) nout))))
  :use ((:instance hpos-aleo-params-facts (rate (cdr inst)))
        (:instance mrk-psd-fep-of-domain-fe (d (car inst)))
        hpos-primep-of-base
        (:instance hpos-c-hash-many-sound
                   (domain (hpos-domain-fe (car inst)))
                   (rate (cdr inst))
                   (params (hpos-aleo-params (cdr inst)))
                   (bits (hpos-alpha-bits))))
  :enable (mrk-psd-hash-many-circuit mrk-psd-instance-p poseidon-hash-many)
  :disable (hpos-c-hash-many-sound hpos-aleo-params-facts (:e dm::primep)))

(defruled mrk-psd-hash-many-complete
  (b* (((mv outs cs vs2 asg2) (mrk-psd-hash-many-circuit inst xs nout vs asg))
       (p primes::*bls12-377-scalar-field-prime*))
    (implies (and (mrk-psd-instance-p inst)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-hash-many-bound (if (consp inst) (cdr inst) inst)
                                            (len xs) nout
                                            (hpos-aleo-params
                                             (if (consp inst) (cdr inst) inst))
                                            (hpos-alpha-bits))
                      (len vs))
                  (hpos-lc-list-boundp xs asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp outs asg2))))
  :use ((:instance hpos-aleo-params-facts (rate (cdr inst)))
        hpos-primep-of-base
        (:instance hpos-c-hash-many-complete
                   (domain (hpos-domain-fe (car inst)))
                   (rate (cdr inst))
                   (params (hpos-aleo-params (cdr inst)))
                   (bits (hpos-alpha-bits))))
  :enable (mrk-psd-hash-many-circuit mrk-psd-instance-p hpos-poseidon-bound)
  :disable (hpos-c-hash-many-complete hpos-aleo-params-facts (:e dm::primep)))

;; Hash::hash: the first output, as an R1CS sparse vector.

(defund mrk-psd-hash-out (inst xs vs asg)
  (declare (xargs :verify-guards nil))
  (mv-let (outs cs vs2 asg2) (mrk-psd-hash-many-circuit inst xs 1 vs asg)
    (declare (ignore cs vs2 asg2))
    (hpos-lc-sv (car outs))))

(defund mrk-psd-hash-cs (inst xs vs asg)
  (declare (xargs :verify-guards nil))
  (mv-let (outs cs vs2 asg2) (mrk-psd-hash-many-circuit inst xs 1 vs asg)
    (declare (ignore outs vs2 asg2))
    cs))

(defrule mrk-psd-sparse-vectorp-of-hash-out
  (r1cs::sparse-vectorp (mrk-psd-hash-out inst xs vs asg))
  :enable mrk-psd-hash-out)

(defruledl mrk-car-of-hpos-lc-eval-list
  (equal (car (hpos-lc-eval-list lcs asg p))
         (if (consp lcs) (hpos-lc-eval (car lcs) asg p) nil))
  :enable hpos-lc-eval-list)

(defruled mrk-psd-hash-sound
  (implies (and (mrk-psd-instance-p inst)
                (r1cs::r1cs-constraints-holdp (mrk-psd-hash-cs inst xs vs asg)
                                              asgx (base-prime)))
           (equal (r1cs::dot-product (mrk-psd-hash-out inst xs vs asg) asgx (base-prime))
                  (crypto-poseidon-hash-instance inst
                                                 (hpos-lc-eval-list xs asgx (base-prime)))))
  :use ((:instance mrk-psd-hash-many-sound (nout 1))
        (:instance len-of-poseidon-hash-many
                   (rate inst) (num-outputs 1)
                   (inputs (hpos-lc-eval-list xs asgx (base-prime))))
        (:instance hpos-len-of-hpos-lc-eval-list
                   (lcs (mv-nth 0 (mrk-psd-hash-many-circuit inst xs 1 vs asg)))
                   (asg asgx) (p (base-prime)))
        (:instance mrk-car-of-hpos-lc-eval-list
                   (lcs (mv-nth 0 (mrk-psd-hash-many-circuit inst xs 1 vs asg)))
                   (asg asgx) (p (base-prime))))
  :cases ((consp (mv-nth 0 (mrk-psd-hash-many-circuit inst xs 1 vs asg))))
  :in-theory '(mrk-psd-hash-out mrk-psd-hash-cs crypto-poseidon-hash-instance
               hpos-lc-eval len (:e base-prime) (:e nfix) (:e equal)))

;; One level of MerklePath::verify: the inputs are 1field and the left /
;; right ternary wires.

(defund mrk-psd-children-xs (l r)
  (declare (xargs :verify-guards nil))
  (list (hpos-lc-const 1) (hpos-lc-var l) (hpos-lc-var r)))

(defruledl mrk-psd-eval-children-xs
  (implies (and (symbolp l) (symbolp r)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg l)
                (r1cs::valuation-bindsp asg r))
           (equal (hpos-lc-eval-list (mrk-psd-children-xs l r) asg (base-prime))
                  (list 1 (lookup-equal l asg) (lookup-equal r asg))))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var l)
                   (r1cs::prime (base-prime)) (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var r)
                   (r1cs::prime (base-prime)) (r1cs::valuation asg)))
  :enable (mrk-psd-children-xs hpos-lc-eval-list base-prime pfield::fep)
  :disable r1cs::fep-of-lookup-equal)

(defruled mrk-psd-children-funspec
  (equal (crypto-merkle-hash-children (cons :poseidon inst) (list x y))
         (crypto-poseidon-hash-instance inst (list 1 x y)))
  :enable crypto-merkle-hash-children)

(defruled mrk-psd-level-hash-sound
  (implies (and (mrk-psd-instance-p inst)
                (r1cs::r1cs-valuationp asg (base-prime))
                (symbolp (car ls)) (symbolp (car rs))
                (r1cs::valuation-bindsp asg (car ls))
                (r1cs::valuation-bindsp asg (car rs))
                (equal (car hcs)
                       (mrk-psd-hash-cs inst (mrk-psd-children-xs (car ls) (car rs))
                                        vs asg0))
                (equal (cadr cvs)
                       (mrk-psd-hash-out inst (mrk-psd-children-xs (car ls) (car rs))
                                         vs asg0)))
           (implies (r1cs::r1cs-constraints-holdp (car hcs) asg (base-prime))
                    (equal (r1cs::dot-product (cadr cvs) asg (base-prime))
                           (crypto-merkle-hash-children
                            (cons :poseidon inst)
                            (list (lookup-equal (car ls) asg)
                                  (lookup-equal (car rs) asg))))))
  :use ((:instance mrk-psd-hash-sound
                   (xs (mrk-psd-children-xs (car ls) (car rs)))
                   (asg asg0) (asgx asg))
        (:instance mrk-psd-eval-children-xs (l (car ls)) (r (car rs)))
        (:instance mrk-psd-children-funspec
                   (x (lookup-equal (car ls) asg))
                   (y (lookup-equal (car rs) asg))))
  :in-theory nil)

;; LeafHash::hash_leaf: the inputs are 0field and the leaf's fields.

(defund mrk-psd-leaf-xs (leaf-lcs)
  (declare (xargs :verify-guards nil))
  (cons (hpos-lc-const 0) leaf-lcs))

(defruled mrk-psd-leaf-funspec
  (equal (crypto-merkle-hash-leaf (cons :poseidon inst) leaf)
         (crypto-poseidon-hash-instance inst (cons 0 leaf)))
  :enable crypto-merkle-hash-leaf)

(defruled mrk-psd-leaf-hash-sound
  (implies (and (mrk-psd-instance-p inst)
                (equal leaf (hpos-lc-eval-list leaf-lcs asg (base-prime)))
                (r1cs::r1cs-constraints-holdp
                 (mrk-psd-hash-cs inst (mrk-psd-leaf-xs leaf-lcs) vs asg0)
                 asg (base-prime)))
           (equal (r1cs::dot-product
                   (mrk-psd-hash-out inst (mrk-psd-leaf-xs leaf-lcs) vs asg0)
                   asg (base-prime))
                  (crypto-merkle-hash-leaf (cons :poseidon inst) leaf)))
  :use ((:instance mrk-psd-hash-sound (xs (mrk-psd-leaf-xs leaf-lcs))
                   (asg asg0) (asgx asg))
        mrk-psd-leaf-funspec)
  :enable (mrk-psd-leaf-xs hpos-lc-eval-list base-prime))
