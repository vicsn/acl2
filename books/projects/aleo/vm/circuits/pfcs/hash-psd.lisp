; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS for the Aleo opcodes hash.psd2 and hash.psd4.
;
; Both are Poseidon on the BLS12-377 scalar field, alpha 17, capacity 1,
; 4 full rounds, 31 partial rounds, 4 full rounds.  hash.psd2 is rate 2
; with domain separator "Poseidon2".  hash.psd4 is rate 4 with domain
; separator "Poseidon4"; its prefix is (domain, length, 0, 0), which is
; hash2's prefix with rate-2 zeros.  The specifications are poseidon::hash2
; and poseidon::hash4.
;
; snarkVM emits a constraint only for a product.  Additions, constant
; scalings, and the MDS matrix stay inside linear combinations.  An S-box
; whose input is a constant is evaluated and disappears.  The four samples
; under circuits/samples/psd_rate{2,4}_* therefore contain only the five
; multiplications of pow17, once per non-constant S-box:
;   rate 2, 1 input -> 53 S-boxes (265 constraints)
;   rate 2, 3 inputs -> 109
;   rate 4, 1 input -> 67
;   rate 4, 5 inputs -> 141
; This book builds the same sponge and constant-folds the same S-boxes.
; A linear combination that is about to be multiplied is bound with
; (lc)*(1) = (w), which is the explicit form used for on-the-fly linear
; combinations elsewhere in circuits-pfcs.  Inlining those binds recovers
; the sample.  The asserts below check the S-box counts.

(in-package "ALEOVM")

(include-book "poseidon-pow17")
(include-book "projects/poseidon/rate-2-alpha-17" :dir :system)
(include-book "projects/poseidon/rate-4-alpha-17" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hash-psd
  :parents (circuits-pfcs)
  :short "PFCS formalization of @('hash.psd2') and @('hash.psd4')."
  :long
  (xdoc::topstring
   (xdoc::p
    "One generator, @(tsee hash-psd-circuit), builds both opcodes.
     The rate, domain separator, round constants, and MDS matrix come from
     the Poseidon instantiation.  The padding that distinguishes rate 4
     from rate 2 is @($r-2$) zeros after the length, so rate 2 adds none.")
   (xdoc::p
    "The nonlinear gate is @(see poseidon-pow17).  Each call is on variables.
     If the S-box input is a linear combination, the circuit first binds it.
     Constant S-box inputs are folded, as in the snarkVM samples.")
   (xdoc::p
    "The intended correctness theorem, for every length @($n$) below the
     prime, is that @('hash_psd2(in_0, ..., in_{n-1}, out)') is satisfied
     iff @('out') is @('(poseidon::hash2 inputs)'), and likewise
     @('hash_psd4') with @('poseidon::hash4').  The S-box equivalence is
     proved in @(see poseidon-pow17).  The hash-level equivalence is the
     statement of this circuit; it is not discharged here.
     A comparison with the Axe proofs of the fixed-length samples is in
     @('books/projects/aleo/vm/circuits/hash-psd-axe-vs-pfcs.md')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Signals are constants, wires, or linear combinations k + sum coeff*wire,
; with coefficients in the field and the terms strictly sorted by name.

(defun psd-const (n)
  (declare (xargs :guard t :verify-guards nil))
  (cons :c (nfix n)))

(defun psd-wire (name)
  (declare (xargs :guard t :verify-guards nil))
  (cons :w name))

(defun psd-lin (k terms)
  (declare (xargs :guard t :verify-guards nil))
  (list* :l (nfix k) terms))

(defun psd-name< (a b)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((and (pfcs::name-case a :simple)
              (pfcs::name-case b :simple))
         (string< (pfcs::name-simple->string a)
                  (pfcs::name-simple->string b)))
        ((pfcs::name-case a :simple) t)
        ((pfcs::name-case b :simple) nil)
        (t (or (string< (pfcs::name-indexed->base a)
                        (pfcs::name-indexed->base b))
               (and (equal (pfcs::name-indexed->base a)
                           (pfcs::name-indexed->base b))
                    (< (pfcs::name-indexed->index a)
                       (pfcs::name-indexed->index b)))))))

(defun psd-terms-merge (x y p)
  (declare (xargs :guard t
                  :measure (+ (acl2-count x) (acl2-count y))
                  :verify-guards nil))
  (cond ((atom x) y)
        ((atom y) x)
        ((psd-name< (caar x) (caar y))
         (cons (car x) (psd-terms-merge (cdr x) y p)))
        ((psd-name< (caar y) (caar x))
         (cons (car y) (psd-terms-merge x (cdr y) p)))
        (t (let ((c (mod (+ (nfix (cdar x)) (nfix (cdar y))) p)))
             (if (zp c)
                 (psd-terms-merge (cdr x) (cdr y) p)
               (cons (cons (caar x) c)
                     (psd-terms-merge (cdr x) (cdr y) p)))))))

(defun psd-terms-scale (terms k p)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom terms) nil)
        (t (let ((c (mod (* (nfix k) (nfix (cdar terms))) p)))
             (if (zp c)
                 (psd-terms-scale (cdr terms) k p)
               (cons (cons (caar terms) c)
                     (psd-terms-scale (cdr terms) k p)))))))

(defun psd-normalize (k terms p)
  (declare (xargs :guard t :verify-guards nil))
  (let ((k (mod (nfix k) p)))
    (cond ((atom terms) (psd-const k))
          ((and (zp k)
                (atom (cdr terms))
                (equal (nfix (cdar terms)) 1))
           (psd-wire (caar terms)))
          (t (psd-lin k terms)))))

(defun psd-destruct (sig p)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((and (consp sig) (eq (car sig) :c))
         (mv (mod (nfix (cdr sig)) p) nil))
        ((and (consp sig) (eq (car sig) :w))
         (mv 0 (list (cons (cdr sig) 1))))
        ((and (consp sig) (eq (car sig) :l))
         (mv (mod (nfix (cadr sig)) p) (cddr sig)))
        (t (mv 0 nil))))

(defun psd-sig-add (a b p)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (ka ta) (psd-destruct a p)
    (mv-let (kb tb) (psd-destruct b p)
      (psd-normalize (mod (+ ka kb) p)
                     (psd-terms-merge ta tb p)
                     p))))

(defun psd-sig-scale (sig k p)
  (declare (xargs :guard t :verify-guards nil))
  (let ((k (mod (nfix k) p)))
    (if (zp k)
        (psd-const 0)
      (mv-let (ks terms) (psd-destruct sig p)
        (psd-normalize (mod (* k ks) p)
                       (psd-terms-scale terms k p)
                       p)))))

(defun psd-fe (n p)
  (declare (xargs :guard t :verify-guards nil))
  (psd-const (mod (nfix n) p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PFCS expressions and the builder state (next-wire . reversed-constraints).

(defun psd-monomial (coeff name)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (nfix coeff) 1)
      (pfcs::expression-var name)
    (pfcs::expression-mul (pfcs::expression-const (nfix coeff))
                          (pfcs::expression-var name))))

(defun psd-term-monomials (terms)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom terms)
      nil
    (cons (psd-monomial (cdar terms) (caar terms))
          (psd-term-monomials (cdr terms)))))

(defun psd-add-exprs (acc mons)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom mons) acc)
        ((null acc) (psd-add-exprs (car mons) (cdr mons)))
        (t (psd-add-exprs (pfcs::expression-add acc (car mons))
                          (cdr mons)))))

(defun psd-lin-expr (k terms)
  (declare (xargs :guard t :verify-guards nil))
  (let ((mons (psd-term-monomials terms)))
    (if (zp k)
        (if (atom mons)
            (pfcs::expression-const 0)
          (psd-add-exprs nil mons))
      (psd-add-exprs (pfcs::expression-const (nfix k)) mons))))

(defun psd-sig-expr (sig p)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((and (consp sig) (eq (car sig) :c))
         (pfcs::expression-const (mod (nfix (cdr sig)) p)))
        ((and (consp sig) (eq (car sig) :w))
         (pfcs::expression-var (cdr sig)))
        ((and (consp sig) (eq (car sig) :l))
         (psd-lin-expr (mod (nfix (cadr sig)) p) (cddr sig)))
        (t (pfcs::expression-const 0))))

(defun psd-emit (c st)
  (declare (xargs :guard t :verify-guards nil))
  (cons (nfix (car st)) (cons c (cdr st))))

(defun psd-fresh (st)
  (declare (xargs :guard t :verify-guards nil))
  (mv (pfcs::name-indexed "w" (nfix (car st)))
      (cons (+ 1 (nfix (car st))) (cdr st))))

(defun psd-bind-constr (sig w p)
  (declare (xargs :guard t :verify-guards nil))
  (pfcs::make-constraint-equal
   :left (pfcs::expression-mul (psd-sig-expr sig p)
                               (pfcs::expression-const 1))
   :right (pfcs::expression-var w)))

(defun psd-ensure (sig p st)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp sig) (eq (car sig) :w))
      (mv (cdr sig) st)
    (mv-let (w st) (psd-fresh st)
      (mv w (psd-emit (psd-bind-constr sig w p) st)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One Poseidon permutation.  Round order matches poseidon::round:
; add the round constants, apply the S-box, multiply by the MDS matrix.
; Partial rounds S-box only the first state word (partial-first-p).

(defun psd-sbox1 (sig p st)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp sig) (eq (car sig) :c))
      (mv (psd-const (pfield::pow (mod (nfix (cdr sig)) p) 17 p)) st)
    (mv-let (w st) (psd-ensure sig p st)
      (mv-let (a st) (psd-fresh st)
        (mv-let (b st) (psd-fresh st)
          (mv-let (c st) (psd-fresh st)
            (mv-let (d st) (psd-fresh st)
              (mv-let (y st) (psd-fresh st)
                (mv (psd-wire y)
                    (psd-emit
                     (pfcs::make-constraint-relation
                      :name (pfcs::name-simple "pow17")
                      :args (list (pfcs::expression-var w)
                                  (pfcs::expression-var a)
                                  (pfcs::expression-var b)
                                  (pfcs::expression-var c)
                                  (pfcs::expression-var d)
                                  (pfcs::expression-var y)))
                     st))))))))))

(defun psd-sbox-list (state p st)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom state)
      (mv nil st)
    (mv-let (s st) (psd-sbox1 (car state) p st)
      (mv-let (rest st) (psd-sbox-list (cdr state) p st)
        (mv (cons s rest) st)))))

(defun psd-sbox-state (fullp state p st)
  (declare (xargs :guard t :verify-guards nil))
  (if fullp
      (psd-sbox-list state p st)
    (if (atom state)
        (mv nil st)
      (mv-let (s0 st) (psd-sbox1 (car state) p st)
        (mv (cons s0 (cdr state)) st)))))

(defun psd-ark (state row p)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (atom state) (atom row))
      nil
    (cons (psd-sig-add (car state) (psd-fe (car row) p) p)
          (psd-ark (cdr state) (cdr row) p))))

(defun psd-dot (row state p)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (atom row) (atom state))
      (psd-const 0)
    (psd-sig-add (psd-sig-scale (car state) (car row) p)
                 (psd-dot (cdr row) (cdr state) p)
                 p)))

(defun psd-mds (state rows p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rows)
      nil
    (cons (psd-dot (car rows) state p)
          (psd-mds state (cdr rows) p))))

(defun psd-round (fullp state row mds p st)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (state st) (psd-sbox-state fullp (psd-ark state row p) p st)
    (mv (psd-mds state mds p) st)))

(defun psd-rounds (n fullp state rows mds p st)
  (declare (xargs :guard t
                  :measure (nfix n)
                  :verify-guards nil))
  (if (zp n)
      (mv state st rows)
    (mv-let (state st) (psd-round fullp state (car rows) mds p st)
      (psd-rounds (1- n) fullp state (cdr rows) mds p st))))

(defun psd-permute (state constants mds full-half partial p st)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (state st rows)
    (psd-rounds full-half t state constants mds p st)
    (mv-let (state st rows)
      (psd-rounds partial nil state rows mds p st)
      (mv-let (state st &)
        (psd-rounds full-half t state rows mds p st)
        (mv state st)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sponge.  Capacity words come first (rate-then-capacity-p is nil) and the
; rate index ascends, which is the Aleo instantiation.  absorb1 permutes
; when the rate is full or the mode is squeeze.  squeeze1 permutes when the
; rate is full or the mode is absorb.

(defun psd-set-nth (i v state)
  (declare (xargs :guard t
                  :measure (acl2-count state)
                  :verify-guards nil))
  (cond ((atom state) nil)
        ((zp i) (cons v (cdr state)))
        (t (cons (car state)
                 (psd-set-nth (1- i) v (cdr state))))))

(defun psd-zero-state (n)
  (declare (xargs :guard t
                  :measure (nfix n)
                  :verify-guards nil))
  (if (zp n)
      nil
    (cons (psd-const 0) (psd-zero-state (1- n)))))

(defun psd-absorb (sig state index mode rate cap constants mds full-half partial p st)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (state index st)
    (if (or (equal (nfix index) (nfix rate))
            (eq mode :squeeze))
        (mv-let (state st)
          (psd-permute state constants mds full-half partial p st)
          (mv state 0 st))
      (mv state (nfix index) st))
    (mv (psd-set-nth (+ (nfix cap) index)
                     (psd-sig-add (nth (+ (nfix cap) index) state) sig p)
                     state)
        (+ 1 index)
        :absorb
        st)))

(defun psd-absorb-list (sigs state index mode rate cap constants mds full-half partial p st)
  (declare (xargs :guard t
                  :measure (acl2-count sigs)
                  :verify-guards nil))
  (if (atom sigs)
      (mv state index mode st)
    (mv-let (state index mode st)
      (psd-absorb (car sigs) state index mode rate cap
                  constants mds full-half partial p st)
      (psd-absorb-list (cdr sigs) state index mode rate cap
                       constants mds full-half partial p st))))

(defun psd-squeeze-word (state index mode rate cap constants mds full-half partial p st)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (state index st)
    (if (or (equal (nfix index) (nfix rate))
            (eq mode :absorb))
        (mv-let (state st)
          (psd-permute state constants mds full-half partial p st)
          (mv state 0 st))
      (mv state (nfix index) st))
    (mv (nth (+ (nfix cap) index) state) st)))

(defun psd-input-names (i n)
  (declare (xargs :guard t
                  :measure (nfix (- (nfix n) (nfix i)))
                  :hints (("Goal" :in-theory (enable nfix)))
                  :verify-guards nil))
  (let ((i (nfix i))
        (n (nfix n)))
    (if (>= i n)
        nil
      (cons (pfcs::name-indexed "in" i)
            (psd-input-names (+ 1 i) n)))))

(defun psd-wires (names)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom names)
      nil
    (cons (psd-wire (car names))
          (psd-wires (cdr names)))))

(defun psd-fe-list (n val p)
  (declare (xargs :guard t
                  :measure (nfix n)
                  :verify-guards nil))
  (if (zp n)
      nil
    (cons (psd-fe val p)
          (psd-fe-list (1- n) val p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hash-psd-circuit-fn (relname param domain n)
  (declare (xargs :guard t :verify-guards nil))
  (b* ((p (poseidon::param->prime param))
       (rate (poseidon::param->rate param))
       (cap (poseidon::param->capacity param))
       (constants (poseidon::param->constants param))
       (mds (poseidon::param->mds param))
       (full-half (poseidon::param->full-rounds-half param))
       (partial (poseidon::param->partial-rounds param))
       (inputs (psd-input-names 0 n))
       (preimage (append (list (psd-fe domain p)
                               (psd-fe n p))
                         (psd-fe-list (nfix (- rate 2)) 0 p)
                         (psd-wires inputs)))
       (state (psd-zero-state (+ rate cap)))
       ((mv state index mode st)
        (psd-absorb-list preimage state 0 :absorb rate cap
                         constants mds full-half partial p
                         (cons 0 nil)))
       ((mv out-sig st)
        (psd-squeeze-word state index mode rate cap
                          constants mds full-half partial p st))
       (out (pfcs::name-simple "out"))
       (st (psd-emit (psd-bind-constr out-sig out p) st)))
    (pfcs::make-definition
     :name relname
     :para (append inputs (list out))
     :body (reverse (cdr st)))))

(define hash-psd-circuit ((relname pfcs::namep)
                          (param poseidon::paramp)
                          (domain natp)
                          (n natp))
  :verify-guards nil
  :short "PFCS definition of one Poseidon hash, for a fixed input length."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters must be an Aleo Poseidon instantiation:
     @($\\alpha = 17$), partial S-box on the first word, capacity words
     before rate words, ascending rate index.  Both @('hash.psd2') and
     @('hash.psd4') are of that form.  @('n') is the number of field inputs
     after the domain and length prefix."))
  (hash-psd-circuit-fn relname param (nfix domain) (nfix n)))

(define hash-psd2-circuit ((n natp))
  :verify-guards nil
  :short "PFCS definition of @('hash.psd2') on @('n') field elements."
  (hash-psd-circuit (pfcs::name-simple "hash_psd2")
                    (poseidon::rate-2-alpha-17-parameters)
                    (poseidon::rate-2-domain-fe)
                    (nfix n)))

(define hash-psd4-circuit ((n natp))
  :verify-guards nil
  :short "PFCS definition of @('hash.psd4') on @('n') field elements."
  (hash-psd-circuit (pfcs::name-simple "hash_psd4")
                    (poseidon::rate-4-alpha-17-parameters)
                    (poseidon::rate-4-domain-fe)
                    (nfix n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash-psd2-spec
  ((inputs (pfield::fe-listp inputs primes::*bls12-377-scalar-field-prime*))
   (out (pfield::fep out primes::*bls12-377-scalar-field-prime*)))
  :guard (pfield::fep (len inputs) primes::*bls12-377-scalar-field-prime*)
  :verify-guards nil
  :returns (yes/no booleanp)
  :short "Specification of @('hash.psd2'): @(tsee poseidon::hash2)."
  (equal out (poseidon::hash2 inputs)))

(define hash-psd4-spec
  ((inputs (pfield::fe-listp inputs primes::*bls12-377-scalar-field-prime*))
   (out (pfield::fep out primes::*bls12-377-scalar-field-prime*)))
  :guard (pfield::fep (len inputs) primes::*bls12-377-scalar-field-prime*)
  :verify-guards nil
  :returns (yes/no booleanp)
  :short "Specification of @('hash.psd4'): @(tsee poseidon::hash4)."
  (equal out (poseidon::hash4 inputs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun psd-count-rel (cs name)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom cs) 0)
        ((and (equal (pfcs::constraint-kind (car cs)) :relation)
              (equal (pfcs::constraint-relation->name (car cs)) name))
         (+ 1 (psd-count-rel (cdr cs) name)))
        (t (psd-count-rel (cdr cs) name))))

; S-box counts of the snarkVM samples.  Each pow17 call is one non-constant
; S-box.  The extra constraint is the binding of the output wire.

(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd2-circuit 0))
                                    (pfcs::name-simple "pow17"))
                     0))
(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd2-circuit 1))
                                    (pfcs::name-simple "pow17"))
                     53))
(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd2-circuit 3))
                                    (pfcs::name-simple "pow17"))
                     109))
(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd4-circuit 0))
                                    (pfcs::name-simple "pow17"))
                     0))
(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd4-circuit 1))
                                    (pfcs::name-simple "pow17"))
                     67))
(assert-event (equal (psd-count-rel (pfcs::definition->body (hash-psd4-circuit 5))
                                    (pfcs::name-simple "pow17"))
                     141))

(assert-event (equal (len (pfcs::definition->body (hash-psd2-circuit 1)))
                     107))
(assert-event (equal (len (pfcs::definition->body (hash-psd4-circuit 1)))
                     135))

(assert-event (pfcs::definitionp (hash-psd2-circuit 1)))
(assert-event (pfcs::definitionp (hash-psd4-circuit 5)))
(assert-event (pfcs::sr1cs-definitionp (hash-psd2-circuit 1)))
(assert-event (pfcs::sr1cs-definitionp (hash-psd4-circuit 1)))
(assert-event (pfcs::sr1cs-definitionp (hash-psd2-circuit 0)))
