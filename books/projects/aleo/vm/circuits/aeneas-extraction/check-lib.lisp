; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Comparison of the constraints emitted by the extracted Rust (circuits.lisp)
; with a formal gadget.
;
; Extracted wire i is the symbol Wi, (wv i), and wire 0 is the constant 1, so a
; harness's inputs are W1, W2, ... and each fresh wire takes the next number.
; A gadget is called on those symbols. A gadget wire that snarkVM folds into a
; constant (a unit wire, the bits of a constant operand) is replaced by its
; value through SUBST.
;
; Each constraint is reduced to a canonical form over the base field:
; coefficients mod p and merged per wire; a triple of constants is dropped
; when it holds, as the host checks it; a triple with a constant A or B is the
; linear form B*a - c (or a*b - c), scaled to a leading coefficient of 1; any
; other triple has A and B scaled to leading coefficient 1 (C absorbs the
; factors) and ordered. Two constraint lists are the same circuit when their
; canonical forms are equal, in order.

(include-book "circuits")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "../fun-specs/base")

(local (include-book "arithmetic-5/top" :dir :system))

(set-ignore-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *fuel* 100000000)

(defun wv (i)
  (acl2::packn-pos (list "W" (nfix i)) 'wv))

(defun wvs (lo n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons (wv lo) (wvs (1+ (nfix lo)) (1- n)))))

(defun wvs-stride (lo n stride)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons (wv lo) (wvs-stride (+ (nfix lo) (nfix stride)) (1- n) stride))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extracted constraints as sparse R1CS constraints.

;; The constants of Cs::ks, evaluated mod p into a fast alist from index to
;; value. SYMS maps the index of a named constant to its value.
(defun ext-pow (b e p)
  (declare (xargs :measure (nfix e)))
  (cond ((zp e) (mod 1 p))
        ((evenp e) (ext-pow (mod (* b b) p) (floor e 2) p))
        (t (mod (* b (ext-pow b (1- e) p)) p))))

(defun ext-k-val (k vals)
  (if (zp k) 1 (ifix (cdr (hons-get k vals)))))

(defun ext-ks (ks i syms vals)
  (declare (xargs :measure (len ks)))
  (if (atom ks)
      vals
    (b* ((n (car ks))
         (p (base-prime))
         (op (acl2::circuits-konst->op n))
         (a (ext-k-val (acl2::circuits-konst->a n) vals))
         (b (ext-k-val (acl2::circuits-konst->b n) vals))
         (v (case op
              (0 (mod (ifix (cdr (assoc (acl2::circuits-konst->a n) syms))) p))
              (1 (mod (* a b) p))
              (2 (mod (+ a b) p))
              (3 (ext-pow (mod a p) (- p 2) p))
              (t (mod (* (ifix (acl2::circuits-konst->c n))
                         (expt 2 (nfix (acl2::circuits-konst->sh n))))
                      p)))))
      (ext-ks (cdr ks) (1+ i) syms (hons-acons i v vals)))))

(defun ext-vec (lc syms)
  (if (atom lc)
      nil
    (b* ((tm (car lc))
         (v (acl2::circuits-term->v tm)))
      (cons (list (* (ifix (acl2::circuits-term->c tm))
                     (expt 2 (nfix (acl2::circuits-term->sh tm)))
                     (ext-k-val (acl2::circuits-term->k tm) syms))
                  (if (equal v 0) 1 (wv v)))
            (ext-vec (cdr lc) syms)))))

(defun ext-constraints (cs syms)
  (if (atom cs)
      nil
    (cons (r1cs::make-r1cs-constraint
           :a (ext-vec (acl2::circuits-constraint->a (car cs)) syms)
           :b (ext-vec (acl2::circuits-constraint->b (car cs)) syms)
           :c (ext-vec (acl2::circuits-constraint->c (car cs)) syms))
          (ext-constraints (cdr cs) syms))))

; The constraints of a harness result, or :FAIL when the extracted code
; returned a Rust error (a panic or running out of fuel). EXT-RUN-SYMS takes
; the values of the named constants.
(defun ext-run-syms (res syms)
  (if (equal (acl2::result-kind res) :ok)
      (b* ((cs (acl2::result-ok->val res))
           (vals (ext-ks (acl2::circuits-cs->ks cs) 1 syms nil))
           (out (ext-constraints (acl2::circuits-cs->cs cs) vals)))
        (prog2$ (fast-alist-free vals) out))
    :fail))

(defun ext-run (res)
  (ext-run-syms res nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Canonical forms.

(defun mexpt (b e p)
  (declare (xargs :measure (nfix e)))
  (cond ((zp e) (mod 1 p))
        ((evenp e) (mexpt (mod (* b b) p) (floor e 2) p))
        (t (mod (* b (mexpt b (1- e) p)) p))))

(defun minv (x p) (mexpt (mod x p) (- p 2) p))

(defun sv-put (var coef alist p)
  (cond ((atom alist) (list (cons var (mod coef p))))
        ((equal (caar alist) var)
         (cons (cons var (mod (+ coef (cdar alist)) p)) (cdr alist)))
        (t (cons (car alist) (sv-put var coef (cdr alist) p)))))

(defun sv-acc (vec subst p acc)
  (if (atom vec)
      acc
    (b* ((coef (ifix (first (car vec))))
         (var (second (car vec)))
         (hit (assoc-equal var subst))
         ((mv var coef) (if hit (mv 1 (* coef (ifix (cdr hit)))) (mv var coef))))
      (sv-acc (cdr vec) subst p (sv-put var coef acc p)))))

(defun sv-nonzero (alist)
  (cond ((atom alist) nil)
        ((equal (cdar alist) 0) (sv-nonzero (cdr alist)))
        (t (cons (car alist) (sv-nonzero (cdr alist))))))

(defun sv-insert (pair alist)
  (cond ((atom alist) (list pair))
        ((lexorder (car pair) (caar alist)) (cons pair alist))
        (t (cons (car alist) (sv-insert pair (cdr alist))))))

(defun sv-sort (alist)
  (if (atom alist) nil (sv-insert (car alist) (sv-sort (cdr alist)))))

(defun sv-canon (vec subst p)
  (sv-sort (sv-nonzero (sv-acc vec subst p nil))))

(defun sv-scale (alist k p)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (mod (* k (cdar alist)) p))
          (sv-scale (cdr alist) k p))))

(defun pairlis$-sv (alist k p)
  (if (atom alist)
      nil
    (cons (list (mod (* k (cdar alist)) p) (caar alist))
          (pairlis$-sv (cdr alist) k p))))

(defun sv-sub (x y p)
  (sv-sort (sv-nonzero (sv-acc (append (pairlis$-sv x 1 p) (pairlis$-sv y (1- p) p)) nil p nil))))

(defun sv-constp (alist)
  (or (atom alist)
      (and (equal (caar alist) 1) (atom (cdr alist)))))

(defun sv-const (alist)
  (if (atom alist) 0 (cdar alist)))

(defun sv-monic (alist p)
  (if (atom alist) nil (sv-scale alist (minv (cdar alist) p) p)))

(defun canon-constraint (a b c p)
  (b* ((a (sv-canon a nil p))
       (b (sv-canon b nil p))
       (c (sv-canon c nil p)))
    (cond ((and (sv-constp a) (sv-constp b) (sv-constp c))
           (if (equal (mod (* (sv-const a) (sv-const b)) p) (sv-const c))
               :trivial
             (list :false a b c)))
          ((or (sv-constp a) (sv-constp b))
           (b* ((k (if (sv-constp a) (sv-const a) (sv-const b)))
                (x (if (sv-constp a) b a))
                (l (sv-sub (sv-scale x k p) c p)))
             (if (atom l) :trivial (list :lin (sv-monic l p)))))
          (t (b* ((ka (cdar a))
                  (kb (cdar b))
                  (a1 (sv-monic a p))
                  (b1 (sv-monic b p))
                  (c1 (sv-scale c (minv (* ka kb) p) p)))
               (if (lexorder a1 b1)
                   (list :bil a1 b1 c1)
                 (list :bil b1 a1 c1)))))))

; A substitution maps a wire to a constant or to a linear combination, given
; as a list of (coefficient wire) pairs.
(defun scale-vec (vec k)
  (if (atom vec)
      nil
    (cons (list (* k (ifix (first (car vec)))) (second (car vec)))
          (scale-vec (cdr vec) k))))

(defun subst-vec (vec subst)
  (if (atom vec)
      nil
    (b* ((coef (ifix (first (car vec))))
         (var (second (car vec)))
         (hit (assoc-equal var subst)))
      (append (cond ((not hit) (list (list coef var)))
                    ((consp (cdr hit)) (scale-vec (cdr hit) coef))
                    (t (list (list (* coef (ifix (cdr hit))) 1))))
              (subst-vec (cdr vec) subst)))))

(defun canon-constraints (constrs subst p)
  (if (atom constrs)
      nil
    (b* ((cn (car constrs))
         (k (canon-constraint (subst-vec (r1cs::r1cs-constraint->a cn) subst)
                              (subst-vec (r1cs::r1cs-constraint->b cn) subst)
                              (subst-vec (r1cs::r1cs-constraint->c cn) subst)
                              p)))
      (if (equal k :trivial)
          (canon-constraints (cdr constrs) subst p)
        (cons k (canon-constraints (cdr constrs) subst p))))))

; The extracted constraints and the gadget are the same circuit.
(defun same-circuit (ext gadget subst)
  (and (not (equal ext :fail))
       (equal (canon-constraints ext nil (base-prime))
              (canon-constraints gadget subst (base-prime)))))

; Same, up to the order of the constraints.
(defun canon-insert (k ks)
  (cond ((atom ks) (list k))
        ((lexorder k (car ks)) (cons k ks))
        (t (cons (car ks) (canon-insert k (cdr ks))))))

(defun canon-sort (ks)
  (if (atom ks) nil (canon-insert (car ks) (canon-sort (cdr ks)))))

(defun same-circuit-unordered (ext gadget subst)
  (and (not (equal ext :fail))
       (equal (canon-sort (canon-constraints ext nil (base-prime)))
              (canon-sort (canon-constraints gadget subst (base-prime))))))

; Every constraint of the gadget is one of the extracted constraints (counted
; with multiplicity), so the extracted circuit is at least as strong.
(defun canon-remove1 (k ks)
  (cond ((atom ks) :missing)
        ((equal k (car ks)) (cdr ks))
        (t (let ((rest (canon-remove1 k (cdr ks))))
             (if (equal rest :missing) :missing (cons (car ks) rest))))))

(defun canon-sub-multiset (ks big)
  (cond ((atom ks) t)
        (t (let ((rest (canon-remove1 (car ks) big)))
             (and (not (equal rest :missing))
                  (canon-sub-multiset (cdr ks) rest))))))

(defun contains-circuit (ext gadget subst)
  (and (not (equal ext :fail))
       (canon-sub-multiset (canon-constraints gadget subst (base-prime))
                           (canon-constraints ext nil (base-prime)))))

; Internal wires up to renaming. A gadget whose internal wires are fresh
; symbols is renamed onto the extracted circuit by pairing the internal
; wires of each side in order of first occurrence. Neither list has
; duplicates or inputs, and the lists have the same length, so the renaming
; is a bijection between the two sets of internal wires.

(defun vec-vars (vec)
  (if (atom vec) nil (cons (second (car vec)) (vec-vars (cdr vec)))))

(defun constraints-vars (constrs)
  (if (atom constrs)
      nil
    (b* ((cn (car constrs)))
      (append (vec-vars (r1cs::r1cs-constraint->a cn))
              (vec-vars (r1cs::r1cs-constraint->b cn))
              (vec-vars (r1cs::r1cs-constraint->c cn))
              (constraints-vars (cdr constrs))))))

(defun first-occurrences (vars known acc)
  (cond ((atom vars) (reverse acc))
        ((or (member-equal (car vars) known) (member-equal (car vars) acc))
         (first-occurrences (cdr vars) known acc))
        (t (first-occurrences (cdr vars) known (cons (car vars) acc)))))

(defun rename-vec (vec ren)
  (if (atom vec)
      nil
    (b* ((var (second (car vec)))
         (hit (assoc-equal var ren)))
      (cons (list (first (car vec)) (if hit (cdr hit) var))
            (rename-vec (cdr vec) ren)))))

(defun rename-constraints (constrs ren)
  (if (atom constrs)
      nil
    (b* ((cn (car constrs)))
      (cons (r1cs::make-r1cs-constraint
             :a (rename-vec (r1cs::r1cs-constraint->a cn) ren)
             :b (rename-vec (r1cs::r1cs-constraint->b cn) ren)
             :c (rename-vec (r1cs::r1cs-constraint->c cn) ren))
            (rename-constraints (cdr constrs) ren)))))

(defun internal-renaming (ext gadget inputs subst)
  (b* ((ext-int (first-occurrences (constraints-vars ext) (cons 1 inputs) nil))
       (gad-int (first-occurrences (constraints-vars gadget)
                                   (cons 1 (append inputs (strip-cars subst)))
                                   nil)))
    (and (equal (len ext-int) (len gad-int))
         (pairlis$ gad-int ext-int))))

; The extracted circuit on INPUTS is the gadget, up to a renaming of
; internal wires.
(defun same-circuit-renamed (ext gadget inputs subst)
  (and (not (equal ext :fail))
       (b* ((ren (internal-renaming ext gadget inputs subst)))
         (and (or ren (atom (first-occurrences (constraints-vars ext) (cons 1 inputs) nil)))
              (same-circuit ext (rename-constraints gadget ren) subst)))))

; Fresh gadget symbols PREFIX0, PREFIX1, ...
(defun gs (prefix n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (append (gs prefix (1- n)) (list (acl2::packn-pos (list prefix (1- n)) 'wv)))))

; For a failing check: the lengths, the index of the first difference, and the
; two canonical constraints there.
(defun first-diff (xs ys i)
  (declare (xargs :measure (+ (acl2-count xs) (acl2-count ys))))
  (cond ((and (atom xs) (atom ys)) nil)
        ((equal (car xs) (car ys)) (first-diff (cdr xs) (cdr ys) (1+ i)))
        (t (list i (car xs) (car ys)))))

(defun circuit-diff (ext gadget subst)
  (if (equal ext :fail)
      :fail
    (b* ((xs (canon-constraints ext nil (base-prime)))
         (ys (canon-constraints gadget subst (base-prime))))
      (list* (len xs) (len ys) (first-diff xs ys 0)))))

(defun circuit-diff-renamed (ext gadget inputs subst)
  (if (equal ext :fail)
      :fail
    (circuit-diff ext (rename-constraints gadget (internal-renaming ext gadget inputs subst))
                  subst)))

; A check is a ground theorem; it is proved by evaluation.
(defmacro defcheck (name form)
  `(defthm ,name ,form :rule-classes nil))
