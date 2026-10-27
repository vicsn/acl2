; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Poseidon duplex sponge and HashMany::hash_many circuits
; (circuit/algorithms/src/poseidon/hash_many.rs: absorb, squeeze,
; squeeze_internal, hash_many), generic over the parameters.
;
; Absorbing adds the input linear combinations into the rate part of the
; state (state[CAPACITY + i] += input[i], no constraint); squeezing copies
; state elements.  All constraints come from the permutations.  The sponge
; mode is host data and is computed exactly as in the spec.
;
; The circuit functions return (mv result cs vs asg), where result is
; (state . mode) for absorb and (outputs state mode) for squeeze.

(in-package "ALEOVM")

(include-book "hpos-perm")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable r1cs::r1cs-constraint-holdsp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lists of linear combinations.

(defrule hpos-lc-eval-list-of-update-nth
  (implies (< (nfix n) (len l))
           (equal (hpos-lc-eval-list (update-nth n v l) asg p)
                  (update-nth n (hpos-lc-eval v asg p)
                              (hpos-lc-eval-list l asg p))))
  :enable (hpos-lc-eval-list update-nth))

(defrule hpos-lc-eval-of-nth
  (implies (< (nfix n) (len l))
           (equal (hpos-lc-eval (nth n l) asg p)
                  (nth n (hpos-lc-eval-list l asg p))))
  :enable (hpos-lc-eval-list nth))

(defrule hpos-lc-eval-list-of-take
  (implies (<= (nfix n) (len l))
           (equal (hpos-lc-eval-list (take n l) asg p)
                  (take n (hpos-lc-eval-list l asg p))))
  :enable (hpos-lc-eval-list take))

(defrule hpos-lc-eval-list-of-nthcdr
  (equal (hpos-lc-eval-list (nthcdr n l) asg p)
         (nthcdr n (hpos-lc-eval-list l asg p)))
  :enable (hpos-lc-eval-list nthcdr))

(defrule hpos-lc-eval-list-of-append
  (equal (hpos-lc-eval-list (append x y) asg p)
         (append (hpos-lc-eval-list x asg p) (hpos-lc-eval-list y asg p)))
  :enable (hpos-lc-eval-list append))

(defrule hpos-lc-eval-list-of-repeat-const
  (implies (posp p)
           (equal (hpos-lc-eval-list (repeat n (hpos-lc-const c)) asg p)
                  (repeat n (mod (ifix c) p))))
  :enable (hpos-lc-eval-list repeat))

(defrule hpos-lc-eval-list-of-true-list-fix
  (equal (hpos-lc-eval-list (true-list-fix l) asg p)
         (hpos-lc-eval-list l asg p))
  :enable (hpos-lc-eval-list true-list-fix))

(defrule hpos-consp-of-hpos-lc-eval-list
  (equal (consp (hpos-lc-eval-list l asg p)) (consp l))
  :enable hpos-lc-eval-list)

(defrule hpos-lc-list-boundp-of-update-nth
  (implies (and (hpos-lc-list-boundp l asg)
                (hpos-lc-boundp v asg)
                (< (nfix n) (len l)))
           (hpos-lc-list-boundp (update-nth n v l) asg))
  :enable (hpos-lc-list-boundp update-nth))

(defrule hpos-lc-boundp-of-nth
  (implies (and (hpos-lc-list-boundp l asg) (< (nfix n) (len l)))
           (hpos-lc-boundp (nth n l) asg))
  :enable (hpos-lc-list-boundp nth))

(defrule hpos-lc-list-boundp-of-take
  (implies (and (hpos-lc-list-boundp l asg) (<= (nfix n) (len l)))
           (hpos-lc-list-boundp (take n l) asg))
  :enable (hpos-lc-list-boundp take))

(defrule hpos-lc-list-boundp-of-nthcdr
  (implies (hpos-lc-list-boundp l asg)
           (hpos-lc-list-boundp (nthcdr n l) asg))
  :enable (hpos-lc-list-boundp nthcdr))

(defrule hpos-lc-list-boundp-of-append
  (equal (hpos-lc-list-boundp (append x y) asg)
         (and (hpos-lc-list-boundp x asg) (hpos-lc-list-boundp y asg)))
  :enable (hpos-lc-list-boundp append))

(defrule hpos-lc-list-boundp-of-repeat-const
  (hpos-lc-list-boundp (repeat n (hpos-lc-const c)) asg)
  :enable (hpos-lc-list-boundp repeat))

(defrule hpos-lc-eval-list-of-repeat-zero
  (implies (posp p)
           (equal (hpos-lc-eval-list (repeat n '(0)) asg p)
                  (repeat n 0)))
  :use (:instance hpos-lc-eval-list-of-repeat-const (c 0)))

(defrule hpos-lc-list-boundp-of-repeat-zero
  (hpos-lc-list-boundp (repeat n '(0)) asg)
  :use (:instance hpos-lc-list-boundp-of-repeat-const (c 0)))

;; Squeezed outputs.

(defrule hpos-cdr-of-hpos-lc-eval-list
  (equal (cdr (hpos-lc-eval-list l asg p))
         (hpos-lc-eval-list (cdr l) asg p))
  :enable hpos-lc-eval-list)

(defrule hpos-lc-eval-list-when-atom
  (implies (atom l) (equal (hpos-lc-eval-list l asg p) nil))
  :enable hpos-lc-eval-list)

(defrule hpos-true-listp-of-hpos-lc-eval-list
  (true-listp (hpos-lc-eval-list l asg p))
  :rule-classes :type-prescription
  :enable hpos-lc-eval-list)

(defrule hpos-lc-eval-list-of-take-nthcdr
  (implies (<= (+ (nfix k) (nfix n)) (len l))
           (equal (hpos-lc-eval-list (take n (nthcdr k l)) asg p)
                  (take n (nthcdr k (hpos-lc-eval-list l asg p)))))
  :disable hpos-lc-eval-list-of-take
  :use (:instance hpos-lc-eval-list-of-take (l (nthcdr k l))))

(defrule hpos-lc-list-boundp-of-true-list-fix
  (equal (hpos-lc-list-boundp (true-list-fix l) asg)
         (hpos-lc-list-boundp l asg))
  :enable (hpos-lc-list-boundp true-list-fix))

(defrule hpos-lc-list-boundp-of-take-nthcdr
  (implies (and (hpos-lc-list-boundp l asg)
                (<= (+ (nfix k) (nfix n)) (len l)))
           (hpos-lc-list-boundp (take n (nthcdr k l)) asg))
  :disable hpos-lc-list-boundp-of-take
  :use (:instance hpos-lc-list-boundp-of-take (l (nthcdr k l))))

;; Repeated permutation bounds.

(defund hpos-mult (m pb)
  (declare (xargs :verify-guards nil))
  (if (zp m) 0 (+ (nfix pb) (hpos-mult (1- m) pb))))

(defrule hpos-natp-of-hpos-mult
  (natp (hpos-mult m pb))
  :rule-classes :type-prescription
  :enable hpos-mult)

(defrule hpos-mult-monotone
  (implies (and (natp a) (natp b) (< a b))
           (<= (+ (nfix pb) (hpos-mult a pb)) (hpos-mult b pb)))
  :rule-classes nil
  :induct (hpos-mult b pb)
  :enable hpos-mult)

(defrule hpos-mult-monotone-2
  (implies (and (natp a) (natp b) (<= a b))
           (<= (hpos-mult a pb) (hpos-mult b pb)))
  :rule-classes nil
  :induct (hpos-mult b pb)
  :enable hpos-mult)

(defrule hpos-mult-of-1+
  (implies (natp m)
           (equal (hpos-mult (+ 1 m) pb)
                  (+ (nfix pb) (hpos-mult m pb))))
  :enable hpos-mult)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; state[pos + i] += elems[i].  No constraints.

(defund hpos-c-add-into (st pos elems p)
  (declare (xargs :verify-guards nil))
  (if (atom elems)
      st
    (hpos-c-add-into (update-nth (nfix pos)
                                 (hpos-lc-add (nth (nfix pos) st) (car elems) p)
                                 st)
                     (1+ (nfix pos)) (cdr elems) p)))

(defrule hpos-len-of-hpos-c-add-into
  (implies (<= (+ (nfix pos) (len elems)) (len st))
           (equal (len (hpos-c-add-into st pos elems p)) (len st)))
  :enable hpos-c-add-into)

(defrule hpos-c-add-into-sound
  (implies (and (posp p)
                (<= (+ (nfix pos) (len elems)) (len st)))
           (equal (hpos-lc-eval-list (hpos-c-add-into st pos elems p) asg p)
                  (hpos-add-into (hpos-lc-eval-list st asg p)
                                 pos
                                 (hpos-lc-eval-list elems asg p)
                                 p)))
  :induct (hpos-c-add-into st pos elems p)
  :enable (hpos-c-add-into hpos-add-into))

(defrule hpos-c-add-into-bound
  (implies (and (hpos-lc-list-boundp st asg)
                (hpos-lc-list-boundp elems asg)
                (<= (+ (nfix pos) (len elems)) (len st)))
           (hpos-lc-list-boundp (hpos-c-add-into st pos elems p) asg))
  :induct (hpos-c-add-into st pos elems p)
  :enable hpos-c-add-into)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The loop of Poseidon::absorb.

(defund hpos-c-absorb-loop (st idx remaining rate params bits vs asg)
  (declare (xargs :verify-guards nil :measure (len remaining)))
  (let ((idx (nfix idx))
        (rate (nfix rate))
        (p (hpos-params->prime params)))
    (cond
     ((<= (+ idx (len remaining)) rate)
      (mv (cons (hpos-c-add-into st (+ 1 idx) remaining p)
                (cons :absorbing (+ idx (len remaining))))
          nil vs asg))
     ((<= rate idx) (mv (cons st (cons :absorbing idx)) nil vs asg))
     (t
      (b* ((k (- rate idx))
           (st (hpos-c-add-into st (+ 1 idx) (take k remaining) p))
           ((mv st cs1 vs asg) (hpos-c-permute st params bits vs asg))
           ((mv res cs2 vs asg)
            (hpos-c-absorb-loop st 0 (nthcdr k remaining) rate params bits vs asg)))
        (mv res (append cs1 cs2) vs asg))))))

(defrule hpos-c-absorb-loop-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-absorb-loop st idx remaining rate params bits vs asg))))
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable hpos-c-absorb-loop)

(hpos-def-mono hpos-c-absorb-loop
               (hpos-c-absorb-loop st idx remaining rate params bits vs asg))

(defrule hpos-len-of-hpos-c-absorb-loop
  (implies (and (equal (len st) (+ 1 (nfix rate)))
                (<= (nfix idx) (nfix rate)))
           (equal (len (car (mv-nth 0 (hpos-c-absorb-loop
                                       st idx remaining rate params bits vs asg))))
                  (len st)))
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable hpos-c-absorb-loop)

(defrule hpos-c-absorb-loop-sound
  (b* (((mv res cs & &)
        (hpos-c-absorb-loop st idx remaining rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv sst smode)
        (hpos-absorb-loop (hpos-lc-eval-list st asgx p) idx
                          (hpos-lc-eval-list remaining asgx p) rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix idx) (nfix rate))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal (hpos-lc-eval-list (car res) asgx p) sst)
                  (equal (cdr res) smode))))
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable (hpos-c-absorb-loop hpos-absorb-loop))

(defrule hpos-c-absorb-loop-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-absorb-loop st idx remaining rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix idx) (nfix rate)))
             (and (<= (- (len vs) (hpos-mult (len remaining) pb)) (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable hpos-c-absorb-loop
  :hints (("Subgoal *1/3" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))
          ("Subgoal *1/2" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))
          ("Subgoal *1/1" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))))

(defrule hpos-c-absorb-loop-complete
  (b* (((mv res cs vs2 asg2)
        (hpos-c-absorb-loop st idx remaining rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix idx) (nfix rate))
                  (<= (hpos-mult (len remaining) pb) (len vs))
                  (hpos-lc-list-boundp st asg)
                  (hpos-lc-list-boundp remaining asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp (car res) asg2))))
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable hpos-c-absorb-loop
  :disable hpos-c-permute-complete
  :hints (("Subgoal *1/3" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))
             (:instance hpos-c-permute-complete
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))
          ("Subgoal *1/2" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))
             (:instance hpos-c-permute-complete
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))
          ("Subgoal *1/1" :use ((:instance hpos-mult-monotone
                        (pb (hpos-perm-bound (len st) params bits))
                        (a (len (nthcdr (- (nfix rate) (nfix idx)) remaining)))
                        (b (len remaining)))
             (:instance hpos-c-permute-vs-len
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))
             (:instance hpos-c-permute-complete
                        (st (hpos-c-add-into st (+ 1 (nfix idx))
                                             (take (- (nfix rate) (nfix idx)) remaining)
                                             (hpos-params->prime params))))))))

(defrule hpos-car-mode-of-hpos-c-absorb-loop
  (equal (car (cdr (mv-nth 0 (hpos-c-absorb-loop
                              st idx remaining rate params bits vs asg))))
         :absorbing)
  :induct (hpos-c-absorb-loop st idx remaining rate params bits vs asg)
  :enable hpos-c-absorb-loop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Poseidon::absorb.

(defund hpos-c-absorb (st mode input rate params bits vs asg)
  (declare (xargs :verify-guards nil))
  (if (atom input)
      (mv (cons st mode) nil vs asg)
    (b* (((mv idx should-permute)
          (if (eq (car mode) :absorbing)
              (if (equal (cdr mode) (nfix rate))
                  (mv 0 t)
                (mv (cdr mode) nil))
            (mv 0 t)))
         ((mv st cs1 vs asg)
          (if should-permute
              (hpos-c-permute st params bits vs asg)
            (mv st nil vs asg)))
         ((mv res cs2 vs asg)
          (hpos-c-absorb-loop st idx input rate params bits vs asg)))
      (mv res (append cs1 cs2) vs asg))))

(defrule hpos-c-absorb-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-absorb st mode input rate params bits vs asg))))
  :enable hpos-c-absorb)

(hpos-def-mono hpos-c-absorb
               (hpos-c-absorb st mode input rate params bits vs asg))

(defrule hpos-len-of-hpos-c-absorb
  (implies (and (equal (len st) (+ 1 (nfix rate)))
                (<= (nfix (cdr mode)) (nfix rate)))
           (equal (len (car (mv-nth 0 (hpos-c-absorb
                                       st mode input rate params bits vs asg))))
                  (len st)))
  :enable hpos-c-absorb
  :disable hpos-len-of-hpos-c-absorb-loop
  :use ((:instance hpos-len-of-hpos-c-absorb-loop (idx (cdr mode)) (remaining input))
        (:instance hpos-len-of-hpos-c-absorb-loop (idx 0) (remaining input)
                   (st (mv-nth 0 (hpos-c-permute st params bits vs asg)))
                   (vs (mv-nth 2 (hpos-c-permute st params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-permute st params bits vs asg))))))

(defrule hpos-car-mode-of-hpos-c-absorb
  (implies (eq (car mode) :absorbing)
           (equal (car (cdr (mv-nth 0 (hpos-c-absorb
                                       st mode input rate params bits vs asg))))
                  :absorbing))
  :enable hpos-c-absorb)

(defrule hpos-c-absorb-sound
  (b* (((mv res cs & &)
        (hpos-c-absorb st mode input rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv sst smode)
        (hpos-absorb (hpos-lc-eval-list st asgx p) mode
                     (hpos-lc-eval-list input asgx p) rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal (hpos-lc-eval-list (car res) asgx p) sst)
                  (equal (cdr res) smode))))
  :enable (hpos-c-absorb hpos-absorb))

(defund hpos-absorb-bound (n pb)
  (declare (xargs :verify-guards nil))
  (+ (nfix pb) (hpos-mult n pb)))

(defrule hpos-c-absorb-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-absorb st mode input rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate)))
             (and (<= (- (len vs) (hpos-absorb-bound (len input) pb)) (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :enable (hpos-c-absorb hpos-absorb-bound)
  :disable hpos-c-absorb-loop-vs-len
  :use ((:instance hpos-c-absorb-loop-vs-len (idx (cdr mode)) (remaining input))
        (:instance hpos-c-absorb-loop-vs-len (idx 0) (remaining input)
                   (st (mv-nth 0 (hpos-c-permute st params bits vs asg)))
                   (vs (mv-nth 2 (hpos-c-permute st params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-permute st params bits vs asg))))))

(defrule hpos-c-absorb-complete
  (b* (((mv res cs vs2 asg2)
        (hpos-c-absorb st mode input rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate))
                  (<= (hpos-absorb-bound (len input) pb) (len vs))
                  (hpos-lc-list-boundp st asg)
                  (hpos-lc-list-boundp input asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp (car res) asg2))))
  :enable (hpos-c-absorb hpos-absorb-bound)
  :disable (hpos-c-permute-complete hpos-c-absorb-loop-complete)
  :use ((:instance hpos-c-permute-complete)
        (:instance hpos-c-absorb-loop-complete (idx 0)
                   (remaining input)
                   (st (mv-nth 0 (hpos-c-permute st params bits vs asg)))
                   (vs (mv-nth 2 (hpos-c-permute st params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-permute st params bits vs asg))))
        (:instance hpos-c-absorb-loop-complete (idx (cdr mode))
                   (remaining input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The loop of Poseidon::squeeze_internal.

(defund hpos-c-squeeze-loop (st idx n rate params bits vs asg)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (let ((idx (nfix idx))
        (n (nfix n))
        (rate (nfix rate)))
    (cond
     ((<= (+ idx n) rate)
      (mv (list (take n (nthcdr (+ 1 idx) st)) st (cons :squeezing (+ idx n)))
          nil vs asg))
     ((<= rate idx)
      (mv (list (repeat n (hpos-lc-const 0)) st (cons :squeezing idx)) nil vs asg))
     (t
      (b* ((k (- rate idx))
           (out1 (take k (nthcdr (+ 1 idx) st)))
           ((mv st cs1 vs asg) (hpos-c-permute st params bits vs asg))
           ((mv res cs2 vs asg)
            (hpos-c-squeeze-loop st 0 (- n k) rate params bits vs asg)))
        (mv (list (append out1 (car res)) (cadr res) (caddr res))
            (append cs1 cs2) vs asg))))))

(defrule hpos-c-squeeze-loop-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-squeeze-loop st idx n rate params bits vs asg))))
  :induct (hpos-c-squeeze-loop st idx n rate params bits vs asg)
  :enable hpos-c-squeeze-loop)

(hpos-def-mono hpos-c-squeeze-loop
               (hpos-c-squeeze-loop st idx n rate params bits vs asg))

(defrule hpos-c-squeeze-loop-sound
  (b* (((mv res cs & &)
        (hpos-c-squeeze-loop st idx n rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv souts sst smode)
        (hpos-squeeze-loop (hpos-lc-eval-list st asgx p) idx n rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal (hpos-lc-eval-list (car res) asgx p) souts)
                  (equal (hpos-lc-eval-list (cadr res) asgx p) sst)
                  (equal (caddr res) smode))))
  :induct (hpos-c-squeeze-loop st idx n rate params bits vs asg)
  :enable (hpos-c-squeeze-loop hpos-squeeze-loop))

(defrule hpos-c-squeeze-loop-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-squeeze-loop st idx n rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (equal (len st) (+ 1 (nfix rate)))
             (and (<= (- (len vs) (hpos-mult n pb)) (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :induct (hpos-c-squeeze-loop st idx n rate params bits vs asg)
  :enable hpos-c-squeeze-loop
  :hints (("Subgoal *1/3" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))))
          ("Subgoal *1/2" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))))
          ("Subgoal *1/1" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))))))

(defrule hpos-c-squeeze-loop-complete
  (b* (((mv res cs vs2 asg2)
        (hpos-c-squeeze-loop st idx n rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (hpos-mult n pb) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp (car res) asg2))))
  :induct (hpos-c-squeeze-loop st idx n rate params bits vs asg)
  :enable hpos-c-squeeze-loop
  :disable hpos-c-permute-complete
  :hints (("Subgoal *1/3" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))
                                (:instance hpos-c-permute-complete)))
          ("Subgoal *1/2" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))
                                (:instance hpos-c-permute-complete)))
          ("Subgoal *1/1" :use ((:instance hpos-mult-monotone
                                           (pb (hpos-perm-bound (len st) params bits))
                                           (a (- n (- (nfix rate) (nfix idx))))
                                           (b n))
                                (:instance hpos-c-permute-complete)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Poseidon::squeeze_internal and Poseidon::squeeze.

(defund hpos-c-squeeze-internal (st mode n rate params bits vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv idx should-permute)
        (if (eq (car mode) :absorbing)
            (mv 0 t)
          (if (equal (cdr mode) (nfix rate))
              (mv 0 t)
            (mv (cdr mode) nil))))
       ((mv st cs1 vs asg)
        (if should-permute
            (hpos-c-permute st params bits vs asg)
          (mv st nil vs asg)))
       ((mv res cs2 vs asg)
        (hpos-c-squeeze-loop st idx n rate params bits vs asg)))
    (mv res (append cs1 cs2) vs asg)))

(defund hpos-c-squeeze (st mode n rate params bits vs asg)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      (mv (list nil st mode) nil vs asg)
    (hpos-c-squeeze-internal st mode n rate params bits vs asg)))

(defrule hpos-c-squeeze-internal-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-squeeze-internal st mode n rate params bits vs asg))))
  :enable hpos-c-squeeze-internal)

(hpos-def-mono hpos-c-squeeze-internal
               (hpos-c-squeeze-internal st mode n rate params bits vs asg))

(defrule hpos-c-squeeze-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-squeeze st mode n rate params bits vs asg))))
  :enable hpos-c-squeeze)

(hpos-def-mono hpos-c-squeeze
               (hpos-c-squeeze st mode n rate params bits vs asg))

(defrule hpos-c-squeeze-internal-sound
  (b* (((mv res cs & &)
        (hpos-c-squeeze-internal st mode n rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv souts sst smode)
        (hpos-squeeze-internal (hpos-lc-eval-list st asgx p) mode n rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal (hpos-lc-eval-list (car res) asgx p) souts)
                  (equal (hpos-lc-eval-list (cadr res) asgx p) sst)
                  (equal (caddr res) smode))))
  :enable (hpos-c-squeeze-internal hpos-squeeze-internal))

(defrule hpos-c-squeeze-sound
  (b* (((mv res cs & &)
        (hpos-c-squeeze st mode n rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv souts sst smode)
        (hpos-squeeze (hpos-lc-eval-list st asgx p) mode n rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (and (equal (hpos-lc-eval-list (car res) asgx p) souts)
                  (equal (hpos-lc-eval-list (cadr res) asgx p) sst)
                  (equal (caddr res) smode))))
  :enable (hpos-c-squeeze hpos-squeeze))

(defrule hpos-c-squeeze-internal-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-squeeze-internal st mode n rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (equal (len st) (+ 1 (nfix rate)))
             (and (<= (- (len vs) (hpos-absorb-bound n pb)) (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :enable (hpos-c-squeeze-internal hpos-absorb-bound)
  :disable hpos-c-squeeze-loop-vs-len
  :use ((:instance hpos-c-squeeze-loop-vs-len (idx (cdr mode)))
        (:instance hpos-c-squeeze-loop-vs-len (idx 0)
                   (st (mv-nth 0 (hpos-c-permute st params bits vs asg)))
                   (vs (mv-nth 2 (hpos-c-permute st params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-permute st params bits vs asg))))))

(defrule hpos-c-squeeze-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-squeeze st mode n rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (equal (len st) (+ 1 (nfix rate)))
             (and (<= (- (len vs) (hpos-absorb-bound n pb)) (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :enable hpos-c-squeeze)

(defrule hpos-c-squeeze-internal-complete
  (b* (((mv res cs vs2 asg2)
        (hpos-c-squeeze-internal st mode n rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (hpos-absorb-bound n pb) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp (car res) asg2))))
  :enable (hpos-c-squeeze-internal hpos-absorb-bound)
  :disable (hpos-c-permute-complete hpos-c-squeeze-loop-complete)
  :use ((:instance hpos-c-permute-complete)
        (:instance hpos-c-squeeze-loop-complete (idx 0)
                   (st (mv-nth 0 (hpos-c-permute st params bits vs asg)))
                   (vs (mv-nth 2 (hpos-c-permute st params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-permute st params bits vs asg))))
        (:instance hpos-c-squeeze-loop-complete (idx (cdr mode)))))

(defrule hpos-c-squeeze-complete
  (b* (((mv res cs vs2 asg2)
        (hpos-c-squeeze st mode n rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (hpos-absorb-bound n pb) (len vs))
                  (hpos-lc-list-boundp st asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp (car res) asg2))))
  :enable hpos-c-squeeze)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; HashMany::hash_many.  DOMAIN is the (constant) domain field element and XS
;; the input linear combinations.

(defund hpos-c-preimage (domain xs rate p)
  (declare (xargs :verify-guards nil))
  (append (take (nfix rate)
                (list* (hpos-lc-const domain)
                       (hpos-lc-const (mod (len xs) p))
                       (repeat (nfix rate) (hpos-lc-const 0))))
          xs))

(defrule hpos-c-preimage-eval
  (implies (and (posp p) (pfield::fep domain p))
           (equal (hpos-lc-eval-list (hpos-c-preimage domain xs rate p) asg p)
                  (hpos-preimage domain (hpos-lc-eval-list xs asg p) rate p)))
  :enable (hpos-c-preimage hpos-preimage hpos-lc-eval-list pfield::fep))

(defrule hpos-len-of-hpos-c-preimage
  (equal (len (hpos-c-preimage domain xs rate p))
         (+ (nfix rate) (len xs)))
  :enable hpos-c-preimage)

(defrule hpos-c-preimage-bound
  (implies (hpos-lc-list-boundp xs asg)
           (hpos-lc-list-boundp (hpos-c-preimage domain xs rate p) asg))
  :enable (hpos-c-preimage hpos-lc-list-boundp))

(defund hpos-c-zero-state (rate)
  (declare (xargs :verify-guards nil))
  (repeat (+ 1 (nfix rate)) (hpos-lc-const 0)))

(defrule hpos-len-of-hpos-c-zero-state
  (equal (len (hpos-c-zero-state rate)) (+ 1 (nfix rate)))
  :enable hpos-c-zero-state)

(defrule hpos-c-zero-state-bound
  (hpos-lc-list-boundp (hpos-c-zero-state rate) asg)
  :enable hpos-c-zero-state)

(defrule hpos-c-zero-state-eval
  (implies (posp p)
           (equal (hpos-lc-eval-list (hpos-c-zero-state rate) asg p)
                  (repeat (+ 1 (nfix rate)) 0)))
  :enable hpos-c-zero-state)

;; Absorb INPUT and then squeeze NOUT elements.

(defund hpos-c-absorb-squeeze (st mode input nout rate params bits vs asg)
  (declare (xargs :verify-guards nil))
  (b* (((mv res1 cs1 vs asg)
        (hpos-c-absorb st mode input rate params bits vs asg))
       ((mv res2 cs2 vs asg)
        (hpos-c-squeeze (car res1) (cdr res1) nout rate params bits vs asg)))
    (mv (car res2) (append cs1 cs2) vs asg)))

(defrule hpos-c-absorb-squeeze-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-absorb-squeeze
                                    st mode input nout rate params bits vs asg))))
  :enable hpos-c-absorb-squeeze)

(hpos-def-mono hpos-c-absorb-squeeze
               (hpos-c-absorb-squeeze st mode input nout rate params bits vs asg))

(defrule hpos-c-absorb-squeeze-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-absorb-squeeze st mode input nout rate params bits vs asg))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate)))
             (and (<= (- (len vs) (+ (hpos-absorb-bound (len input) pb)
                                     (hpos-absorb-bound nout pb)))
                      (len vs2))
                  (<= (len vs2) (len vs)))))
  :rule-classes :linear
  :enable hpos-c-absorb-squeeze
  :disable (hpos-c-absorb-vs-len hpos-c-squeeze-vs-len hpos-len-of-hpos-c-absorb)
  :use ((:instance hpos-c-absorb-vs-len)
        (:instance hpos-len-of-hpos-c-absorb)
        (:instance hpos-c-squeeze-vs-len
                   (n nout)
                   (st (car (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (mode (cdr (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (vs (mv-nth 2 (hpos-c-absorb st mode input rate params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-absorb st mode input rate params bits vs asg))))))

(defrule hpos-c-absorb-squeeze-complete
  (b* (((mv outs cs vs2 asg2)
        (hpos-c-absorb-squeeze st mode input nout rate params bits vs asg))
       (p (hpos-params->prime params))
       (pb (hpos-perm-bound (len st) params bits)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate))
                  (<= (+ (hpos-absorb-bound (len input) pb)
                         (hpos-absorb-bound nout pb))
                      (len vs))
                  (hpos-lc-list-boundp st asg)
                  (hpos-lc-list-boundp input asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp outs asg2))))
  :enable hpos-c-absorb-squeeze
  :disable (hpos-c-absorb-complete hpos-c-squeeze-complete
                                   hpos-len-of-hpos-c-absorb hpos-c-absorb-vs-len)
  :use ((:instance hpos-c-absorb-complete)
        (:instance hpos-len-of-hpos-c-absorb)
        (:instance hpos-c-absorb-vs-len)
        (:instance hpos-c-squeeze-complete
                   (n nout)
                   (st (car (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (mode (cdr (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (vs (mv-nth 2 (hpos-c-absorb st mode input rate params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-absorb st mode input rate params bits vs asg))))))

(defrule hpos-c-absorb-squeeze-sound
  (b* (((mv outs cs & &)
        (hpos-c-absorb-squeeze st mode input nout rate params bits vs asg))
       (p (hpos-params->prime params))
       ((mv sst smode)
        (hpos-absorb (hpos-lc-eval-list st asgx p) mode
                     (hpos-lc-eval-list input asgx p) rate params))
       ((mv souts & &) (hpos-squeeze sst smode nout rate params)))
    (implies (and (dm::primep p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (equal (len st) (+ 1 (nfix rate)))
                  (<= (nfix (cdr mode)) (nfix rate))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list outs asgx p) souts)))
  :enable hpos-c-absorb-squeeze
  :disable (hpos-c-absorb-sound hpos-c-squeeze-sound hpos-len-of-hpos-c-absorb)
  :use ((:instance hpos-c-absorb-sound)
        (:instance hpos-len-of-hpos-c-absorb)
        (:instance hpos-c-squeeze-sound
                   (n nout)
                   (st (car (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (mode (cdr (mv-nth 0 (hpos-c-absorb st mode input rate params bits vs asg))))
                   (vs (mv-nth 2 (hpos-c-absorb st mode input rate params bits vs asg)))
                   (asg (mv-nth 3 (hpos-c-absorb st mode input rate params bits vs asg))))))

(defund hpos-c-hash-many (domain xs nout rate params bits vs asg)
  (declare (xargs :verify-guards nil))
  (hpos-c-absorb-squeeze (hpos-c-zero-state rate) (cons :absorbing 0)
                         (hpos-c-preimage domain xs rate (hpos-params->prime params))
                         nout rate params bits vs asg))

(defund hpos-hash-many-bound (rate nin nout params bits)
  (declare (xargs :verify-guards nil))
  (let ((pb (hpos-perm-bound (+ 1 (nfix rate)) params bits)))
    (+ (hpos-absorb-bound (+ (nfix rate) nin) pb)
       (hpos-absorb-bound nout pb))))

(defrule hpos-c-hash-many-ext
  (implies (hpos-ext-p a asg)
           (hpos-ext-p a (mv-nth 3 (hpos-c-hash-many domain xs nout rate params bits vs asg))))
  :enable hpos-c-hash-many)

(hpos-def-mono hpos-c-hash-many
               (hpos-c-hash-many domain xs nout rate params bits vs asg))

(defrule hpos-c-hash-many-sound
  (b* (((mv outs cs & &)
        (hpos-c-hash-many domain xs nout rate params bits vs asg))
       (p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (pfield::fep domain p)
                  (equal (hpos-bits-val 0 bits) (hpos-params->alpha params))
                  (r1cs::r1cs-constraints-holdp cs asgx p))
             (equal (hpos-lc-eval-list outs asgx p)
                    (hpos-hash-many domain (hpos-lc-eval-list xs asgx p)
                                    nout rate params))))
  :enable (hpos-c-hash-many hpos-hash-many))

(defrule hpos-c-hash-many-vs-len
  (b* (((mv & & vs2 &)
        (hpos-c-hash-many domain xs nout rate params bits vs asg)))
    (and (<= (- (len vs) (hpos-hash-many-bound rate (len xs) nout params bits))
             (len vs2))
         (<= (len vs2) (len vs))))
  :rule-classes :linear
  :enable (hpos-c-hash-many hpos-hash-many-bound))

(defrule hpos-c-hash-many-complete
  (b* (((mv outs cs vs2 asg2)
        (hpos-c-hash-many domain xs nout rate params bits vs asg))
       (p (hpos-params->prime params)))
    (implies (and (dm::primep p)
                  (r1cs::r1cs-valuationp asg p)
                  (hpos-supply-okp vs asg)
                  (<= (hpos-hash-many-bound rate (len xs) nout params bits) (len vs))
                  (hpos-lc-list-boundp xs asg))
             (and (hpos-wit-okp asg vs asg2 vs2 cs p)
                  (hpos-lc-list-boundp outs asg2))))
  :enable (hpos-c-hash-many hpos-hash-many-bound))
