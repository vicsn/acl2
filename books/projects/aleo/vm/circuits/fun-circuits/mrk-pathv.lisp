; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MerklePath::verify (circuit/collections/src/merkle_tree/verify.rs) against
; crypto-merkle-path-verify (fun-specs/crypto-merkle.lisp), and
; PathHash::hash_empty (trait default, merkle_tree and kary_merkle_tree).
;
; A hash is a snarkVM Field, i.e. a linear combination: here an R1CS sparse
; vector whose value is r1cs::dot-product (BHP outputs are one variable,
; ((1 x)); Poseidon outputs are general linear combinations, hpos-lc-sv).
; Per level i the circuit takes the leaf-index bit wire b (a Boolean of the
; injected U64), the sibling wire s and the current hash C, and emits
;   left  = Field::ternary(!b, C, s):  (C - s) * (1 - b) = (left - s)
;   right = Field::ternary(!b, s, C):  (s - C) * (1 - b) = (right - C)
; (!b is the linear combination 1 - b; left and right are new witnesses),
; then the constraints HC of path_hasher.hash_children(left, right), whose
; output is the next current hash.  Finally root.is_equal(current) emits
;   (root - C) * (m) = (r)      (root - C) * (1 - r) = (0)
; and returns 1 - r (circuit/types/field/src/equal.rs).
;
; The leaf-hash and hash_children constraint lists are parameters; the
; theorems assume they are sound / complete at each level (discharged for
; BHP in mrk-pathv-bhp.lisp and Poseidon in mrk-pathv-psd.lisp).  The host
; halts (index >= 2^DEPTH, path length, DEPTH > 64) are hypotheses.

(in-package "ALEOVM")

(include-book "../fun-specs/crypto-merkle")
(include-book "../fun-specs/primitives-field")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Vectors.

(defun mrk-neg (v)
  (if (atom v)
      nil
    (cons (list (- (ifix (first (car v)))) (second (car v)))
          (mrk-neg (cdr v)))))

(defrule mrk-sparse-vectorp-of-neg
  (implies (r1cs::sparse-vectorp v)
           (r1cs::sparse-vectorp (mrk-neg v)))
  :enable r1cs::sparse-vectorp)

(defruledl mrk-mul-of-minus
  (implies (and (integerp c) (posp p))
           (equal (pfield::mul (- c) x p) (pfield::neg (pfield::mul c x p) p)))
  :enable (pfield::mul pfield::neg))

(defruledl mrk-add-of-minus
  (implies (and (integerp c) (posp p))
           (equal (pfield::add (- c) y p) (pfield::add (pfield::neg c p) y p)))
  :enable (pfield::add pfield::neg))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defruled mrk-mod-of-minus
    (implies (and (integerp c) (posp p))
             (equal (mod (- c) p) (pfield::neg (mod c p) p)))
    :enable pfield::neg))

(defrule mrk-dot-of-neg
  (implies (and (primep p) (r1cs::sparse-vectorp v))
           (equal (r1cs::dot-product (mrk-neg v) asg p)
                  (pfield::neg (r1cs::dot-product v asg p) p)))
  :induct (mrk-neg v)
  :enable (r1cs::dot-product r1cs::sparse-vectorp mrk-mod-of-minus
           pfield::neg-of-add))

(defun mrk-var (x) (list (list 1 x)))

(defrule mrk-dot-of-var
  (implies (and (primep p) (r1cs::r1cs-valuationp asg p)
                (symbolp x) (r1cs::valuation-bindsp asg x))
           (equal (r1cs::dot-product (mrk-var x) asg p)
                  (lookup-equal x asg)))
  :use (:instance r1cs::fep-of-lookup-equal (r1cs::var x) (r1cs::prime p)
                  (r1cs::valuation asg))
  :enable r1cs::dot-product)

(defrule mrk-sparse-vectorp-of-var
  (implies (symbolp x) (r1cs::sparse-vectorp (mrk-var x)))
  :enable r1cs::sparse-vectorp)

(defun mrk-vecs-p (vs)
  (if (atom vs)
      t
    (and (r1cs::sparse-vectorp (car vs)) (mrk-vecs-p (cdr vs)))))

(defun mrk-dots (vs asg p)
  (if (atom vs)
      nil
    (cons (r1cs::dot-product (car vs) asg p) (mrk-dots (cdr vs) asg p))))

(defun mrk-vals (xs asg)
  (if (endp xs) nil (cons (lookup-equal (car xs) asg) (mrk-vals (cdr xs) asg))))

(defrule mrk-len-of-vals
  (equal (len (mrk-vals xs asg)) (len xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field::ternary(!b, X, Y) with a fresh output wire.

(defun mrk-tern (b xv yv out p)
  (r1cs::make-r1cs-constraint
   :a (append xv (mrk-neg yv))
   :b (list (list 1 1) (list (1- p) b))
   :c (cons (list 1 out) (mrk-neg yv))))

(defruled mrk-tern-holds
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp b) (symbolp out)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg out)
                (r1cs::sparse-vectorp xv)
                (r1cs::sparse-vectorp yv)
                (bitp (lookup-equal b asg)))
           (equal (r1cs::r1cs-constraint-holdsp (mrk-tern b xv yv out p) asg p)
                  (equal (lookup-equal out asg)
                         (if (equal (lookup-equal b asg) 1)
                             (r1cs::dot-product yv asg p)
                           (r1cs::dot-product xv asg p)))))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var out) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :cases ((equal (lookup-equal b asg) 1))
  :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product bitp)
  :disable r1cs::fep-of-lookup-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field::is_equal(X, Y) on linear combinations; the bit is 1 - r.

(defun mrk-is-equal (xv yv m r p)
  (list (r1cs::make-r1cs-constraint
         :a (append xv (mrk-neg yv))
         :b (list (list 1 m))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (append xv (mrk-neg yv))
         :b (list (list 1 1) (list (1- p) r))
         :c nil)))

(local (defrule mrk-is-equal-vals
  (implies (and (primep p)
                (pfield::fep x p) (pfield::fep y p)
                (pfield::fep m p) (pfield::fep r p)
                (equal (pfield::mul (pfield::sub x y p) m p) r)
                (equal (pfield::mul (pfield::sub x y p) (pfield::sub 1 r p) p) 0))
           (equal r (if (equal x y) 0 1)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal x y))
           :in-theory (e/d ()
                           ((:definition pfield::sub)
                            pfield::mul-of-sub-arg1
                            pfield::mul-of-sub-arg2))
           :use ((:instance pfield::equal-of-0-and-mul
                            (x (pfield::sub x y p))
                            (y (pfield::sub 1 r p)))
                 (:instance pfield::equal-of-0-and-sub)
                 (:instance pfield::equal-of-0-and-sub (x 1) (y r))
                 (:instance pfield::mul-of-0-arg1 (y m)))))))

(defruledl mrk-is-equal-to-vals
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp m) (symbolp r)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::sparse-vectorp xv)
                (r1cs::sparse-vectorp yv))
           (b* ((x (r1cs::dot-product xv asg p))
                (y (r1cs::dot-product yv asg p))
                (m$ (lookup-equal m asg))
                (r$ (lookup-equal r asg)))
             (equal (r1cs::r1cs-constraints-holdp (mrk-is-equal xv yv m r p) asg p)
                    (and (equal (pfield::mul (pfield::sub x y p) m$ p) r$)
                         (equal (pfield::mul (pfield::sub x y p)
                                             (pfield::sub 1 r$ p) p)
                                0)))))
  :use ((:instance r1cs::fep-of-lookup-equal (r1cs::var m) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var r) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product pfield::sub)
  :disable r1cs::fep-of-lookup-equal)

(defruled mrk-is-equal-sound
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp m) (symbolp r)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::sparse-vectorp xv)
                (r1cs::sparse-vectorp yv)
                (r1cs::r1cs-constraints-holdp (mrk-is-equal xv yv m r p) asg p))
           (equal (pfield::sub 1 (lookup-equal r asg) p)
                  (if (equal (r1cs::dot-product xv asg p)
                             (r1cs::dot-product yv asg p))
                      1 0)))
  :use (mrk-is-equal-to-vals
        (:instance mrk-is-equal-vals
                   (x (r1cs::dot-product xv asg p))
                   (y (r1cs::dot-product yv asg p))
                   (m (lookup-equal m asg))
                   (r (lookup-equal r asg)))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var m) (r1cs::prime p)
                   (r1cs::valuation asg))
        (:instance r1cs::fep-of-lookup-equal (r1cs::var r) (r1cs::prime p)
                   (r1cs::valuation asg)))
  :disable (r1cs::fep-of-lookup-equal mrk-is-equal))

(defruled mrk-is-equal-complete
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbolp m) (symbolp r)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-bindsp asg r)
                (r1cs::sparse-vectorp xv)
                (r1cs::sparse-vectorp yv)
                (equal x (r1cs::dot-product xv asg p))
                (equal y (r1cs::dot-product yv asg p))
                (equal (lookup-equal r asg) (if (equal x y) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal x y) 1 (pfield::inv (pfield::sub x y p) p))))
           (and (r1cs::r1cs-constraints-holdp (mrk-is-equal xv yv m r p) asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (if (equal x y) 1 0))))
  :use mrk-is-equal-to-vals
  :cases ((equal x y))
  :hints (("Subgoal 2" :use ((:instance pfield::mul-of-inv-arg2
                                         (x (pfield::sub x y p)))
                              (:instance pfield::equal-of-0-and-sub)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Levels.  CVS has one more vector than BITS: (car cvs) is the leaf hash.

(defun mrk-levels-gadget (bits sibs cvs ls rs hcs p)
  (if (endp bits)
      nil
    (append (list (mrk-tern (car bits) (car cvs) (mrk-var (car sibs)) (car ls) p)
                  (mrk-tern (car bits) (mrk-var (car sibs)) (car cvs) (car rs) p))
            (car hcs)
            (mrk-levels-gadget (cdr bits) (cdr sibs) (cdr cvs) (cdr ls)
                               (cdr rs) (cdr hcs) p))))

(defun mrk-final (bits cvs)
  (if (endp bits) (car cvs) (mrk-final (cdr bits) (cdr cvs))))

(defun mrk-levels-wiresp (bits sibs cvs ls rs asg)
  (if (endp bits)
      (and (consp cvs) (r1cs::sparse-vectorp (car cvs)))
    (and (symbolp (car bits)) (symbolp (car sibs))
         (symbolp (car ls)) (symbolp (car rs))
         (r1cs::sparse-vectorp (car cvs))
         (r1cs::valuation-bindsp asg (car bits))
         (r1cs::valuation-bindsp asg (car sibs))
         (r1cs::valuation-bindsp asg (car ls))
         (r1cs::valuation-bindsp asg (car rs))
         (bitp (lookup-equal (car bits) asg))
         (mrk-levels-wiresp (cdr bits) (cdr sibs) (cdr cvs) (cdr ls)
                            (cdr rs) asg))))

(defun mrk-levels-hash-soundp (ph ls rs cvs hcs asg p)
  (if (endp ls)
      t
    (and (implies (r1cs::r1cs-constraints-holdp (car hcs) asg p)
                  (equal (r1cs::dot-product (cadr cvs) asg p)
                         (crypto-merkle-hash-children
                          ph (list (lookup-equal (car ls) asg)
                                   (lookup-equal (car rs) asg)))))
         (mrk-levels-hash-soundp ph (cdr ls) (cdr rs) (cdr cvs) (cdr hcs)
                                 asg p))))

(defun mrk-levels-hash-completep (ph ls rs cvs hcs asg p)
  (if (endp ls)
      t
    (and (r1cs::r1cs-constraints-holdp (car hcs) asg p)
         (equal (r1cs::dot-product (cadr cvs) asg p)
                (crypto-merkle-hash-children
                 ph (list (lookup-equal (car ls) asg)
                          (lookup-equal (car rs) asg))))
         (mrk-levels-hash-completep ph (cdr ls) (cdr rs) (cdr cvs) (cdr hcs)
                                    asg p))))

(defun mrk-levels-ternary-witnessp (bits sibs cvs ls rs asg p)
  (if (endp bits)
      t
    (and (equal (lookup-equal (car ls) asg)
                (if (equal (lookup-equal (car bits) asg) 1)
                    (lookup-equal (car sibs) asg)
                  (r1cs::dot-product (car cvs) asg p)))
         (equal (lookup-equal (car rs) asg)
                (if (equal (lookup-equal (car bits) asg) 1)
                    (r1cs::dot-product (car cvs) asg p)
                  (lookup-equal (car sibs) asg)))
         (mrk-levels-ternary-witnessp (cdr bits) (cdr sibs) (cdr cvs)
                                      (cdr ls) (cdr rs) asg p))))

(defun mrk-levels-induct (bits sibs cvs ls rs hcs)
  (if (endp bits)
      (list sibs cvs ls rs hcs)
    (mrk-levels-induct (cdr bits) (cdr sibs) (cdr cvs) (cdr ls) (cdr rs)
                       (cdr hcs))))

(defruled mrk-levels-sound
  (implies (and (equal p (base-prime))
                (crypto-field-hasher-p ph)
                (r1cs::r1cs-valuationp asg p)
                (equal (len ls) (len bits))
                (equal (len sibs) (len bits))
                (mrk-levels-wiresp bits sibs cvs ls rs asg)
                (mrk-levels-hash-soundp ph ls rs cvs hcs asg p)
                (r1cs::r1cs-constraints-holdp
                 (mrk-levels-gadget bits sibs cvs ls rs hcs p) asg p))
           (equal (r1cs::dot-product (mrk-final bits cvs) asg p)
                  (crypto-merkle-path-loop ph
                                           (mrk-vals bits asg)
                                           (mrk-vals sibs asg)
                                           (r1cs::dot-product (car cvs) asg p))))
  :induct (mrk-levels-induct bits sibs cvs ls rs hcs)
  :enable (mrk-tern-holds crypto-merkle-path-loop)
  :disable (mrk-tern mrk-var))

(defruled mrk-levels-complete
  (implies (and (equal p (base-prime))
                (crypto-field-hasher-p ph)
                (r1cs::r1cs-valuationp asg p)
                (equal (len ls) (len bits))
                (equal (len sibs) (len bits))
                (mrk-levels-wiresp bits sibs cvs ls rs asg)
                (mrk-levels-ternary-witnessp bits sibs cvs ls rs asg p)
                (mrk-levels-hash-completep ph ls rs cvs hcs asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (mrk-levels-gadget bits sibs cvs ls rs hcs p) asg p)
                (equal (r1cs::dot-product (mrk-final bits cvs) asg p)
                       (crypto-merkle-path-loop ph
                                                (mrk-vals bits asg)
                                                (mrk-vals sibs asg)
                                                (r1cs::dot-product (car cvs) asg p)))))
  :induct (mrk-levels-induct bits sibs cvs ls rs hcs)
  :enable (mrk-tern-holds crypto-merkle-path-loop)
  :disable (mrk-tern mrk-var))

(defruled mrk-sparse-vectorp-of-final
  (implies (mrk-levels-wiresp bits sibs cvs ls rs asg)
           (r1cs::sparse-vectorp (mrk-final bits cvs)))
  :induct (mrk-levels-induct bits sibs cvs ls rs hcs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The whole circuit: leaf-hash constraints LCS, levels, root.is_equal.

(defun mrk-pathv-gadget (lcs bits sibs cvs ls rs hcs root m r p)
  (append lcs
          (mrk-levels-gadget bits sibs cvs ls rs hcs p)
          (mrk-is-equal (mrk-var root) (mrk-final bits cvs) m r p)))

(defruled mrk-pathv-gadget-holdp
  (equal (r1cs::r1cs-constraints-holdp
          (mrk-pathv-gadget lcs bits sibs cvs ls rs hcs root m r p) asg p)
         (and (r1cs::r1cs-constraints-holdp lcs asg p)
              (r1cs::r1cs-constraints-holdp
               (mrk-levels-gadget bits sibs cvs ls rs hcs p) asg p)
              (r1cs::r1cs-constraints-holdp
               (mrk-is-equal (mrk-var root) (mrk-final bits cvs) m r p) asg p)))
  :in-theory '(mrk-pathv-gadget r1cs::r1cs-constraints-holdp-of-append))

(defruledl mrk-path-verify-spec-unfold
  (implies (and (natp idx)
                (< idx (expt 2 (nfix depth)))
                (equal (len sibs) (nfix depth))
                (<= (nfix depth) 64))
           (equal (crypto-merkle-path-verify lh ph depth (list idx sibs) root leaf)
                  (if (equal root
                             (crypto-merkle-path-loop
                              ph (take depth (crypto-nat->lebits 64 idx))
                              sibs (crypto-merkle-hash-leaf lh leaf)))
                      1 0)))
  :enable crypto-merkle-path-verify)

(defmacro mrk-pathv-hyps ()
  '(and (equal p (base-prime))
        (crypto-field-hasher-p lh)
        (crypto-field-hasher-p ph)
        (r1cs::r1cs-valuationp asg p)
        (natp depth)
        (<= depth 64)
        (natp idx)
        (< idx (expt 2 depth))
        (equal (len bits) depth)
        (equal (len sibs) depth)
        (equal (len ls) depth)
        (equal (mrk-vals bits asg)
               (take depth (crypto-nat->lebits 64 idx)))
        (mrk-levels-wiresp bits sibs cvs ls rs asg)
        (symbolp root) (symbolp m) (symbolp r)
        (r1cs::valuation-bindsp asg root)
        (r1cs::valuation-bindsp asg m)
        (r1cs::valuation-bindsp asg r)))

(defruled mrk-pathv-sound
  (implies (and (mrk-pathv-hyps)
                (implies (r1cs::r1cs-constraints-holdp lcs asg p)
                         (equal (r1cs::dot-product (car cvs) asg p)
                                (crypto-merkle-hash-leaf lh leaf)))
                (mrk-levels-hash-soundp ph ls rs cvs hcs asg p)
                (r1cs::r1cs-constraints-holdp
                 (mrk-pathv-gadget lcs bits sibs cvs ls rs hcs root m r p)
                 asg p))
           (and (bitp (pfield::sub 1 (lookup-equal r asg) p))
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (crypto-merkle-path-verify
                        lh ph depth (list idx (mrk-vals sibs asg))
                        (lookup-equal root asg) leaf))))
  :do-not-induct t
  :use (mrk-levels-sound
        mrk-pathv-gadget-holdp
        mrk-sparse-vectorp-of-final
        (:instance mrk-is-equal-sound (xv (mrk-var root)) (yv (mrk-final bits cvs)))
        (:instance mrk-path-verify-spec-unfold (sibs (mrk-vals sibs asg))
                   (root (lookup-equal root asg))))
  :enable bitp
  :disable (mrk-pathv-gadget mrk-levels-gadget mrk-final mrk-vals mrk-is-equal
            mrk-levels-wiresp mrk-levels-hash-soundp crypto-merkle-path-verify
            mrk-var))

(defruled mrk-pathv-complete
  (implies (and (mrk-pathv-hyps)
                (r1cs::r1cs-constraints-holdp lcs asg p)
                (equal (r1cs::dot-product (car cvs) asg p)
                       (crypto-merkle-hash-leaf lh leaf))
                (mrk-levels-ternary-witnessp bits sibs cvs ls rs asg p)
                (mrk-levels-hash-completep ph ls rs cvs hcs asg p)
                (equal fin (r1cs::dot-product (mrk-final bits cvs) asg p))
                (equal (lookup-equal r asg)
                       (if (equal (lookup-equal root asg) fin) 0 1))
                (equal (lookup-equal m asg)
                       (if (equal (lookup-equal root asg) fin)
                           1
                         (pfield::inv (pfield::sub (lookup-equal root asg) fin p) p))))
           (and (r1cs::r1cs-constraints-holdp
                 (mrk-pathv-gadget lcs bits sibs cvs ls rs hcs root m r p)
                 asg p)
                (equal (pfield::sub 1 (lookup-equal r asg) p)
                       (crypto-merkle-path-verify
                        lh ph depth (list idx (mrk-vals sibs asg))
                        (lookup-equal root asg) leaf))))
  :do-not-induct t
  :use (mrk-levels-complete
        mrk-pathv-gadget-holdp
        mrk-sparse-vectorp-of-final
        (:instance mrk-is-equal-complete (xv (mrk-var root)) (yv (mrk-final bits cvs))
                   (x (lookup-equal root asg)) (y fin))
        (:instance mrk-path-verify-spec-unfold (sibs (mrk-vals sibs asg))
                   (root (lookup-equal root asg))))
  :disable (mrk-pathv-gadget mrk-levels-gadget mrk-final mrk-vals mrk-is-equal
            mrk-levels-wiresp mrk-levels-hash-completep
            mrk-levels-ternary-witnessp crypto-merkle-path-verify mrk-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PathHash::hash_empty (trait default).  The hasher and the zero / default
;; children are constants, so hash_children folds at synthesis time: no
;; constraint, and the result is the constant the funspec computes.

(define mrk-hash-empty-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  nil)

(defruled mrk-hash-empty-sound
  (implies (and (crypto-field-hasher-p ph)
                (r1cs::r1cs-constraints-holdp (mrk-hash-empty-gadget) asg p))
           (and (fieldp (crypto-merkle-hash-empty ph))
                (equal (crypto-merkle-hash-empty ph)
                       (crypto-merkle-hash-children ph (list 0 0)))))
  :enable crypto-merkle-hash-empty)

(defruled mrk-hash-empty-complete
  (r1cs::r1cs-constraints-holdp (mrk-hash-empty-gadget) asg p)
  :enable mrk-hash-empty-gadget)

(defruled mrk-kary-hash-empty-sound
  (implies (and (crypto-hasher-p ph)
                (r1cs::r1cs-constraints-holdp (mrk-hash-empty-gadget) asg p))
           (equal (crypto-kary-merkle-hash-empty ph arity)
                  (crypto-merkle-hash-children
                   ph (repeat arity (crypto-merkle-hash-default ph)))))
  :enable crypto-kary-merkle-hash-empty)
