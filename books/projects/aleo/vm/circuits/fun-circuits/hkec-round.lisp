; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keccak::rotate_left, Keccak::round and Keccak::permutation_f of
; circuit/algorithms/src/keccak/hash.rs on Boolean wires (hkec-gen.lisp).
;
; A U64 is its 64 Boolean wires (U64::from_bits_le and to_bits_le of exactly
; 64 bits add no constraint), and U64 not / and / xor act bit by bit, so
; rotate_left and the rho-pi lane permutation are list operations with no
; constraints: they are the spec functions themselves, applied to wires.
; theta, chi and iota are the gadgets below; iota xors constant round
; constant bits, which folds without constraints.
;
; For every gadget G the book proves
;   G-EXT    the constraint list only grows,
;   G-WF     the constraint list stays well formed (HKEC-WF), so
;            HKEC-SOLVE satisfies it (completeness),
;   G-OK     the output wires only use allocated variables,
;   G-SOUND  in every satisfying assignment where the inputs are bits, the
;            outputs are bits and equal the spec of hash-keccak.lisp applied
;            to the input values.
; Lanes are symbolic throughout; no 1600-bit state is expanded.

(in-package "ALEOVM")

(include-book "hkec-gen")


(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lists of wires.

(defun hkec-cdr-induct (k x)
  (if (zp k)
      x
    (hkec-cdr-induct (1- k) (cdr x))))

(defrule hkec-terms-ok-of-append
  (equal (hkec-terms-ok (append x y) n)
         (and (hkec-terms-ok x n)
              (hkec-terms-ok y n))))

(defrule hkec-wires-p-of-append
  (equal (hkec-wires-p (append x y) asg p)
         (and (hkec-wires-p x asg p)
              (hkec-wires-p y asg p))))

(defrule hkec-eval-list-of-append
  (equal (hkec-eval-list (append x y) asg p)
         (append (hkec-eval-list x asg p)
                 (hkec-eval-list y asg p))))

(defrule hkec-terms-ok-of-nthcdr
  (implies (hkec-terms-ok x n)
           (hkec-terms-ok (nthcdr k x) n))
  :induct (hkec-cdr-induct k x))

(defrule hkec-wires-p-of-nthcdr
  (implies (hkec-wires-p x asg p)
           (hkec-wires-p (nthcdr k x) asg p))
  :induct (hkec-cdr-induct k x))

(defrule hkec-eval-list-of-nthcdr
  (equal (hkec-eval-list (nthcdr k x) asg p)
         (nthcdr k (hkec-eval-list x asg p)))
  :induct (hkec-cdr-induct k x))

(defrule hkec-terms-ok-of-take
  (implies (and (hkec-terms-ok x n)
                (<= (nfix k) (len x)))
           (hkec-terms-ok (take k x) n))
  :induct (hkec-cdr-induct k x))

(defrule hkec-wires-p-of-take
  (implies (and (hkec-wires-p x asg p)
                (<= (nfix k) (len x)))
           (hkec-wires-p (take k x) asg p))
  :induct (hkec-cdr-induct k x))

(defrule hkec-eval-list-of-take
  (implies (<= (nfix k) (len x))
           (equal (hkec-eval-list (take k x) asg p)
                  (take k (hkec-eval-list x asg p))))
  :induct (hkec-cdr-induct k x))

(defrule hkec-terms-ok-of-rotate-left
  (implies (and (hkec-terms-ok x n)
                (<= (nfix k) (len x)))
           (hkec-terms-ok (hkec-rotate-left x k) n)))

(defrule hkec-wires-p-of-rotate-left
  (implies (and (hkec-wires-p x asg p)
                (<= (nfix k) (len x)))
           (hkec-wires-p (hkec-rotate-left x k) asg p)))

(defrule hkec-eval-list-of-rotate-left
  (implies (<= (nfix k) (len x))
           (equal (hkec-eval-list (hkec-rotate-left x k) asg p)
                  (hkec-rotate-left (hkec-eval-list x asg p) k))))

(defrule len-of-hkec-rotate-left
  (implies (<= (nfix k) (len x))
           (equal (len (hkec-rotate-left x k))
                  (len x))))

(in-theory (disable hkec-rotate-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lists of lanes.

(defun hkec-lanes-ok (ls n)
  (if (atom ls)
      t
    (and (hkec-terms-ok (car ls) n)
         (hkec-lanes-ok (cdr ls) n))))

(defun hkec-lanes-wires-p (ls asg p)
  (if (atom ls)
      t
    (and (hkec-wires-p (car ls) asg p)
         (hkec-lanes-wires-p (cdr ls) asg p))))

(defun hkec-eval-lanes (ls asg p)
  (if (atom ls)
      nil
    (cons (hkec-eval-list (car ls) asg p)
          (hkec-eval-lanes (cdr ls) asg p))))

(defun hkec-lanes-len (ls k)
  (if (atom ls)
      t
    (and (equal (len (car ls)) k)
         (hkec-lanes-len (cdr ls) k))))

(defrule hkec-lanes-ok-mono
  (implies (and (hkec-lanes-ok ls n)
                (natp n) (natp m) (<= n m))
           (hkec-lanes-ok ls m)))

(defrule hkec-terms-ok-of-nth-lane
  (implies (hkec-lanes-ok ls n)
           (hkec-terms-ok (nth i ls) n))
  :enable nth)

(defrule hkec-wires-p-of-nth-lane
  (implies (hkec-lanes-wires-p ls asg p)
           (hkec-wires-p (nth i ls) asg p))
  :enable nth)

(defrule nth-of-hkec-eval-lanes
  (equal (nth i (hkec-eval-lanes ls asg p))
         (hkec-eval-list (nth i ls) asg p))
  :enable nth)

(defrule len-of-nth-lane
  (implies (and (hkec-lanes-len ls k)
                (< (nfix i) (len ls)))
           (equal (len (nth i ls)) k))
  :enable nth)

(defrule hkec-terms-ok-of-car-lane
  (implies (hkec-lanes-ok ls n)
           (hkec-terms-ok (car ls) n)))

(defrule hkec-wires-p-of-car-lane
  (implies (hkec-lanes-wires-p ls asg p)
           (hkec-wires-p (car ls) asg p)))

(defrule car-of-hkec-eval-lanes
  (equal (car (hkec-eval-lanes ls asg p))
         (hkec-eval-list (car ls) asg p)))

(defrule len-of-car-lane
  (implies (and (hkec-lanes-len ls k)
                (consp ls))
           (equal (len (car ls)) k)))

(defrule len-of-hkec-eval-lanes
  (equal (len (hkec-eval-lanes ls asg p))
         (len ls)))

(defrule hkec-lanes-ok-of-update-nth
  (implies (and (hkec-lanes-ok ls n)
                (hkec-terms-ok v n))
           (hkec-lanes-ok (update-nth i v ls) n))
  :enable update-nth)

(defrule hkec-lanes-wires-p-of-update-nth
  (implies (and (hkec-lanes-wires-p ls asg p)
                (hkec-wires-p v asg p))
           (hkec-lanes-wires-p (update-nth i v ls) asg p))
  :enable update-nth)

(defrule hkec-eval-lanes-of-update-nth
  (equal (hkec-eval-lanes (update-nth i v ls) asg p)
         (update-nth i (hkec-eval-list v asg p) (hkec-eval-lanes ls asg p)))
  :enable update-nth)

(defrule hkec-lanes-len-of-update-nth
  (implies (and (hkec-lanes-len ls k)
                (equal (len v) k)
                (< (nfix i) (len ls)))
           (hkec-lanes-len (update-nth i v ls) k))
  :enable update-nth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lane gadgets: U64 xor, and, not.

(defun hkec-lane-and (xs ys)
  (if (endp xs)
      nil
    (cons (acl2::bitand (car xs) (car ys))
          (hkec-lane-and (cdr xs) (cdr ys)))))

(defun hkec-lane-not (xs)
  (if (endp xs)
      nil
    (cons (hkec-bnot (car xs))
          (hkec-lane-not (cdr xs)))))

(defrule hkec-lane-chi-as-xor-and-not
  (implies (equal (len bs) (len as))
           (equal (hkec-lane-chi as bs cs)
                  (hkec-lane-xor as (hkec-lane-and (hkec-lane-not bs) cs))))
  :induct (hkec-lane-chi as bs cs))

(defun hkec-g-lane-not (xs p)
  (if (endp xs)
      nil
    (cons (hkec-not (car xs) p)
          (hkec-g-lane-not (cdr xs) p))))

(defrule hkec-g-lane-not-props
  (and (implies (hkec-terms-ok xs n)
                (hkec-terms-ok (hkec-g-lane-not xs p) n))
       (implies (and (primep p)
                     (hkec-wires-p xs asg p))
                (and (hkec-wires-p (hkec-g-lane-not xs p) asg p)
                     (equal (hkec-eval-list (hkec-g-lane-not xs p) asg p)
                            (hkec-lane-not (hkec-eval-list xs asg p)))))
       (equal (len (hkec-g-lane-not xs p))
              (len xs))))

(defun hkec-g-lane-xor (xs ys cs p)
  (if (endp xs)
      (mv nil cs)
    (b* (((mv o cs) (hkec-xor (car xs) (car ys) cs p))
         ((mv os cs) (hkec-g-lane-xor (cdr xs) (cdr ys) cs p)))
      (mv (cons o os) cs))))

(defun hkec-g-lane-and (xs ys cs p)
  (if (endp xs)
      (mv nil cs)
    (b* (((mv o cs) (hkec-and (car xs) (car ys) cs p))
         ((mv os cs) (hkec-g-lane-and (cdr xs) (cdr ys) cs p)))
      (mv (cons o os) cs))))

(defmacro hkec-def-lane2 (g op spec)
  (let ((ext (acl2::packn-pos (list g '-ext) 'hkec))
        (wf (acl2::packn-pos (list g '-wf) 'hkec))
        (ok (acl2::packn-pos (list g '-ok) 'hkec))
        (sound (acl2::packn-pos (list g '-sound) 'hkec))
        (len (acl2::packn-pos (list 'len-of- g) 'hkec)))
    `(progn
       (defrule ,ext
         (implies (hkec-ext cs old)
                  (hkec-ext (mv-nth 1 (,g xs ys cs p)) old)))
       (defrule ,len
         (equal (len (mv-nth 0 (,g xs ys cs p)))
                (len xs)))
       (defrule ,(acl2::packn-pos (list g '-len-mono) 'hkec)
         (<= (len cs) (len (mv-nth 1 (,g xs ys cs p))))
         :rule-classes :linear)
       (defrule ,wf
         (implies (and (primep p)
                       (hkec-wf cs p)
                       (hkec-terms-ok xs (len cs))
                       (hkec-terms-ok ys (len cs))
                       (equal (len xs) (len ys)))
                  (hkec-wf (mv-nth 1 (,g xs ys cs p)) p)))
       (defrule ,ok
         (implies (and (hkec-terms-ok xs (len cs))
                       (hkec-terms-ok ys (len cs))
                       (equal (len xs) (len ys))
                       (natp m)
                       (<= (len (mv-nth 1 (,g xs ys cs p))) m))
                  (hkec-terms-ok (mv-nth 0 (,g xs ys cs p)) m))
         :induct (,g xs ys cs p))
       (defrule ,sound
         (implies (and (primep p)
                       (r1cs::r1cs-constraints-holdp (mv-nth 1 (,g xs ys cs p)) asg p)
                       (hkec-wires-p xs asg p)
                       (hkec-wires-p ys asg p)
                       (equal (len xs) (len ys)))
                  (and (hkec-wires-p (mv-nth 0 (,g xs ys cs p)) asg p)
                       (equal (hkec-eval-list (mv-nth 0 (,g xs ys cs p)) asg p)
                              (,spec (hkec-eval-list xs asg p)
                                     (hkec-eval-list ys asg p)))))
         :induct (,g xs ys cs p)
         :hints (("Subgoal *1/2" :use ((:instance ,(acl2::packn-pos (list op '-sound) 'hkec)
                                        (a (car xs)) (b (car ys)))))))
       (in-theory (disable ,g)))))

(hkec-def-lane2 hkec-g-lane-xor hkec-xor hkec-lane-xor)
(hkec-def-lane2 hkec-g-lane-and hkec-and hkec-lane-and)

;; chi on one lane: U64 not, then U64 and, then U64 xor.

(defun hkec-g-lane-chi (as bs cl cs p)
  (b* ((nb (hkec-g-lane-not bs p))
       ((mv tt cs) (hkec-g-lane-and nb cl cs p))
       ((mv o cs) (hkec-g-lane-xor as tt cs p)))
    (mv o cs)))

(defrule hkec-g-lane-chi-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-lane-chi as bs cl cs p)) old))
  :enable hkec-g-lane-chi)

(defrule hkec-g-lane-chi-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-lane-chi as bs cl cs p))))
  :rule-classes :linear
  :enable hkec-g-lane-chi)

(defrule hkec-g-lane-chi-shape
  (implies (and (equal (len bs) (len as))
                (equal (len cl) (len as)))
           (and (equal (len (mv-nth 0 (hkec-g-lane-chi as bs cl cs p))) (len as))))
  :enable hkec-g-lane-chi)

(defrule hkec-g-lane-chi-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-terms-ok as (len cs))
                (hkec-terms-ok bs (len cs))
                (hkec-terms-ok cl (len cs))
                (equal (len bs) (len as))
                (equal (len cl) (len as)))
           (hkec-wf (mv-nth 1 (hkec-g-lane-chi as bs cl cs p)) p))
  :enable hkec-g-lane-chi)

(defrule hkec-g-lane-chi-ok
  (implies (and (hkec-terms-ok as (len cs))
                (hkec-terms-ok bs (len cs))
                (hkec-terms-ok cl (len cs))
                (equal (len bs) (len as))
                (equal (len cl) (len as))
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-lane-chi as bs cl cs p))) m))
           (hkec-terms-ok (mv-nth 0 (hkec-g-lane-chi as bs cl cs p)) m))
  :enable hkec-g-lane-chi)

(defrule hkec-g-lane-chi-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-lane-chi as bs cl cs p)) asg p)
                (hkec-wires-p as asg p)
                (hkec-wires-p bs asg p)
                (hkec-wires-p cl asg p)
                (equal (len bs) (len as))
                (equal (len cl) (len as)))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-lane-chi as bs cl cs p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-lane-chi as bs cl cs p)) asg p)
                       (hkec-lane-chi (hkec-eval-list as asg p) (hkec-eval-list bs asg p) (hkec-eval-list cl asg p)))))
  :enable hkec-g-lane-chi)

(in-theory (disable hkec-g-lane-chi))

;; theta, C[x] = a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20].

(defun hkec-g-theta-c-lane (a x cs p)
  (b* (((mv t1 cs) (hkec-g-lane-xor (nth x a) (nth (+ x 5) a) cs p))
       ((mv t2 cs) (hkec-g-lane-xor t1 (nth (+ x 10) a) cs p))
       ((mv t3 cs) (hkec-g-lane-xor t2 (nth (+ x 15) a) cs p))
       ((mv t4 cs) (hkec-g-lane-xor t3 (nth (+ x 20) a) cs p)))
    (mv t4 cs)))

(defrule hkec-g-theta-c-lane-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-theta-c-lane a x cs p)) old))
  :enable hkec-g-theta-c-lane)

(defrule hkec-g-theta-c-lane-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-theta-c-lane a x cs p))))
  :rule-classes :linear
  :enable hkec-g-theta-c-lane)

(defrule hkec-g-theta-c-lane-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp x)
                (< x 5))
           (and (equal (len (mv-nth 0 (hkec-g-theta-c-lane a x cs p))) 64)))
  :enable hkec-g-theta-c-lane)

(defrule hkec-g-theta-c-lane-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp x)
                (< x 5))
           (hkec-wf (mv-nth 1 (hkec-g-theta-c-lane a x cs p)) p))
  :enable hkec-g-theta-c-lane)

(defrule hkec-g-theta-c-lane-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp x)
                (< x 5)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-theta-c-lane a x cs p))) m))
           (hkec-terms-ok (mv-nth 0 (hkec-g-theta-c-lane a x cs p)) m))
  :enable hkec-g-theta-c-lane)

(defrule hkec-g-theta-c-lane-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-theta-c-lane a x cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp x)
                (< x 5))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-theta-c-lane a x cs p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-theta-c-lane a x cs p)) asg p)
                       (hkec-theta-c-lane (hkec-eval-lanes a asg p) x))))
  :enable hkec-g-theta-c-lane)

(in-theory (disable hkec-g-theta-c-lane))

(defun hkec-g-theta-c (a cs p)
  (b* (((mv c0 cs) (hkec-g-theta-c-lane a 0 cs p))
       ((mv c1 cs) (hkec-g-theta-c-lane a 1 cs p))
       ((mv c2 cs) (hkec-g-theta-c-lane a 2 cs p))
       ((mv c3 cs) (hkec-g-theta-c-lane a 3 cs p))
       ((mv c4 cs) (hkec-g-theta-c-lane a 4 cs p)))
    (mv (list c0 c1 c2 c3 c4) cs)))

(defrule hkec-g-theta-c-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-theta-c a cs p)) old))
  :enable hkec-g-theta-c)

(defrule hkec-g-theta-c-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-theta-c a cs p))))
  :rule-classes :linear
  :enable hkec-g-theta-c)

(defrule hkec-g-theta-c-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-theta-c a cs p)) 64) (equal (len (mv-nth 0 (hkec-g-theta-c a cs p))) 5)))
  :enable hkec-g-theta-c)

(defrule hkec-g-theta-c-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25))
           (hkec-wf (mv-nth 1 (hkec-g-theta-c a cs p)) p))
  :enable hkec-g-theta-c)

(defrule hkec-g-theta-c-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-theta-c a cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-theta-c a cs p)) m))
  :enable hkec-g-theta-c)

(defrule hkec-g-theta-c-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-theta-c a cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-theta-c a cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-theta-c a cs p)) asg p)
                       (hkec-theta-c (hkec-eval-lanes a asg p)))))
  :enable hkec-g-theta-c)

(in-theory (disable hkec-g-theta-c))

;; theta, D[x] = C[x-1] ^ rotate_left(C[x+1], 63).

(defun hkec-g-theta-d (c cs p)
  (b* (((mv d0 cs) (hkec-g-lane-xor (nth 4 c) (hkec-rotate-left (nth 1 c) 63) cs p))
       ((mv d1 cs) (hkec-g-lane-xor (nth 0 c) (hkec-rotate-left (nth 2 c) 63) cs p))
       ((mv d2 cs) (hkec-g-lane-xor (nth 1 c) (hkec-rotate-left (nth 3 c) 63) cs p))
       ((mv d3 cs) (hkec-g-lane-xor (nth 2 c) (hkec-rotate-left (nth 4 c) 63) cs p))
       ((mv d4 cs) (hkec-g-lane-xor (nth 3 c) (hkec-rotate-left (nth 0 c) 63) cs p)))
    (mv (list d0 d1 d2 d3 d4) cs)))

(defrule hkec-g-theta-d-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-theta-d c cs p)) old))
  :enable hkec-g-theta-d)

(defrule hkec-g-theta-d-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-theta-d c cs p))))
  :rule-classes :linear
  :enable hkec-g-theta-d)

(defrule hkec-g-theta-d-shape
  (implies (and (hkec-lanes-len c 64)
                (equal (len c) 5))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-theta-d c cs p)) 64) (equal (len (mv-nth 0 (hkec-g-theta-d c cs p))) 5)))
  :enable hkec-g-theta-d)

(defrule hkec-g-theta-d-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok c (len cs))
                (hkec-lanes-len c 64)
                (equal (len c) 5))
           (hkec-wf (mv-nth 1 (hkec-g-theta-d c cs p)) p))
  :enable hkec-g-theta-d)

(defrule hkec-g-theta-d-ok
  (implies (and (hkec-lanes-ok c (len cs))
                (hkec-lanes-len c 64)
                (equal (len c) 5)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-theta-d c cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-theta-d c cs p)) m))
  :enable hkec-g-theta-d)

(defrule hkec-g-theta-d-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-theta-d c cs p)) asg p)
                (hkec-lanes-wires-p c asg p)
                (hkec-lanes-len c 64)
                (equal (len c) 5))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-theta-d c cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-theta-d c cs p)) asg p)
                       (hkec-theta-d (hkec-eval-lanes c asg p)))))
  :enable hkec-g-theta-d)

(in-theory (disable hkec-g-theta-d))

(defruled hkec-theta-apply-unroll
  (equal (hkec-theta-apply a d 0)
         (list (hkec-lane-xor (nth 0 a) (nth 0 d)) (hkec-lane-xor (nth 1 a) (nth 1 d)) (hkec-lane-xor (nth 2 a) (nth 2 d)) (hkec-lane-xor (nth 3 a) (nth 3 d)) (hkec-lane-xor (nth 4 a) (nth 4 d)) (hkec-lane-xor (nth 5 a) (nth 0 d)) (hkec-lane-xor (nth 6 a) (nth 1 d)) (hkec-lane-xor (nth 7 a) (nth 2 d)) (hkec-lane-xor (nth 8 a) (nth 3 d)) (hkec-lane-xor (nth 9 a) (nth 4 d)) (hkec-lane-xor (nth 10 a) (nth 0 d)) (hkec-lane-xor (nth 11 a) (nth 1 d)) (hkec-lane-xor (nth 12 a) (nth 2 d)) (hkec-lane-xor (nth 13 a) (nth 3 d)) (hkec-lane-xor (nth 14 a) (nth 4 d)) (hkec-lane-xor (nth 15 a) (nth 0 d)) (hkec-lane-xor (nth 16 a) (nth 1 d)) (hkec-lane-xor (nth 17 a) (nth 2 d)) (hkec-lane-xor (nth 18 a) (nth 3 d)) (hkec-lane-xor (nth 19 a) (nth 4 d)) (hkec-lane-xor (nth 20 a) (nth 0 d)) (hkec-lane-xor (nth 21 a) (nth 1 d)) (hkec-lane-xor (nth 22 a) (nth 2 d)) (hkec-lane-xor (nth 23 a) (nth 3 d)) (hkec-lane-xor (nth 24 a) (nth 4 d))))
  :expand ((hkec-theta-apply a d 0) (hkec-theta-apply a d 1) (hkec-theta-apply a d 2) (hkec-theta-apply a d 3) (hkec-theta-apply a d 4) (hkec-theta-apply a d 5) (hkec-theta-apply a d 6) (hkec-theta-apply a d 7) (hkec-theta-apply a d 8) (hkec-theta-apply a d 9) (hkec-theta-apply a d 10) (hkec-theta-apply a d 11) (hkec-theta-apply a d 12) (hkec-theta-apply a d 13) (hkec-theta-apply a d 14) (hkec-theta-apply a d 15) (hkec-theta-apply a d 16) (hkec-theta-apply a d 17) (hkec-theta-apply a d 18) (hkec-theta-apply a d 19) (hkec-theta-apply a d 20) (hkec-theta-apply a d 21) (hkec-theta-apply a d 22) (hkec-theta-apply a d 23) (hkec-theta-apply a d 24) (hkec-theta-apply a d 25)))

;; theta, a_1[x + 5y] = a[x + 5y] ^ D[x].

(defun hkec-g-theta-apply (a d cs p)
  (b* (((mv e0 cs) (hkec-g-lane-xor (nth 0 a) (nth 0 d) cs p))
       ((mv e1 cs) (hkec-g-lane-xor (nth 1 a) (nth 1 d) cs p))
       ((mv e2 cs) (hkec-g-lane-xor (nth 2 a) (nth 2 d) cs p))
       ((mv e3 cs) (hkec-g-lane-xor (nth 3 a) (nth 3 d) cs p))
       ((mv e4 cs) (hkec-g-lane-xor (nth 4 a) (nth 4 d) cs p))
       ((mv e5 cs) (hkec-g-lane-xor (nth 5 a) (nth 0 d) cs p))
       ((mv e6 cs) (hkec-g-lane-xor (nth 6 a) (nth 1 d) cs p))
       ((mv e7 cs) (hkec-g-lane-xor (nth 7 a) (nth 2 d) cs p))
       ((mv e8 cs) (hkec-g-lane-xor (nth 8 a) (nth 3 d) cs p))
       ((mv e9 cs) (hkec-g-lane-xor (nth 9 a) (nth 4 d) cs p))
       ((mv e10 cs) (hkec-g-lane-xor (nth 10 a) (nth 0 d) cs p))
       ((mv e11 cs) (hkec-g-lane-xor (nth 11 a) (nth 1 d) cs p))
       ((mv e12 cs) (hkec-g-lane-xor (nth 12 a) (nth 2 d) cs p))
       ((mv e13 cs) (hkec-g-lane-xor (nth 13 a) (nth 3 d) cs p))
       ((mv e14 cs) (hkec-g-lane-xor (nth 14 a) (nth 4 d) cs p))
       ((mv e15 cs) (hkec-g-lane-xor (nth 15 a) (nth 0 d) cs p))
       ((mv e16 cs) (hkec-g-lane-xor (nth 16 a) (nth 1 d) cs p))
       ((mv e17 cs) (hkec-g-lane-xor (nth 17 a) (nth 2 d) cs p))
       ((mv e18 cs) (hkec-g-lane-xor (nth 18 a) (nth 3 d) cs p))
       ((mv e19 cs) (hkec-g-lane-xor (nth 19 a) (nth 4 d) cs p))
       ((mv e20 cs) (hkec-g-lane-xor (nth 20 a) (nth 0 d) cs p))
       ((mv e21 cs) (hkec-g-lane-xor (nth 21 a) (nth 1 d) cs p))
       ((mv e22 cs) (hkec-g-lane-xor (nth 22 a) (nth 2 d) cs p))
       ((mv e23 cs) (hkec-g-lane-xor (nth 23 a) (nth 3 d) cs p))
       ((mv e24 cs) (hkec-g-lane-xor (nth 24 a) (nth 4 d) cs p)))
    (mv (list e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24) cs)))

(defrule hkec-g-theta-apply-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-theta-apply a d cs p)) old))
  :enable hkec-g-theta-apply)

(defrule hkec-g-theta-apply-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-theta-apply a d cs p))))
  :rule-classes :linear
  :enable hkec-g-theta-apply)

(defrule hkec-g-theta-apply-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-lanes-len d 64)
                (equal (len d) 5))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-theta-apply a d cs p)) 64) (equal (len (mv-nth 0 (hkec-g-theta-apply a d cs p))) 25)))
  :enable hkec-g-theta-apply)

(defrule hkec-g-theta-apply-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-lanes-ok d (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-lanes-len d 64)
                (equal (len d) 5))
           (hkec-wf (mv-nth 1 (hkec-g-theta-apply a d cs p)) p))
  :enable hkec-g-theta-apply)

(defrule hkec-g-theta-apply-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-lanes-ok d (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-lanes-len d 64)
                (equal (len d) 5)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-theta-apply a d cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-theta-apply a d cs p)) m))
  :enable hkec-g-theta-apply)

(defrule hkec-g-theta-apply-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-theta-apply a d cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-lanes-wires-p d asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-lanes-len d 64)
                (equal (len d) 5))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-theta-apply a d cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-theta-apply a d cs p)) asg p)
                       (hkec-theta-apply (hkec-eval-lanes a asg p) (hkec-eval-lanes d asg p) 0))))
  :enable hkec-g-theta-apply
  :hints (("Goal" :in-theory (enable hkec-theta-apply-unroll))))

(in-theory (disable hkec-g-theta-apply))

(defun hkec-g-theta (a cs p)
  (b* (((mv c cs) (hkec-g-theta-c a cs p))
       ((mv d cs) (hkec-g-theta-d c cs p))
       ((mv a1 cs) (hkec-g-theta-apply a d cs p)))
    (mv a1 cs)))

(defrule hkec-g-theta-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-theta a cs p)) old))
  :enable hkec-g-theta)

(defrule hkec-g-theta-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-theta a cs p))))
  :rule-classes :linear
  :enable hkec-g-theta)

(defrule hkec-g-theta-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-theta a cs p)) 64) (equal (len (mv-nth 0 (hkec-g-theta a cs p))) 25)))
  :enable hkec-g-theta)

(defrule hkec-g-theta-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25))
           (hkec-wf (mv-nth 1 (hkec-g-theta a cs p)) p))
  :enable hkec-g-theta)

(defrule hkec-g-theta-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-theta a cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-theta a cs p)) m))
  :enable hkec-g-theta)

(defrule hkec-g-theta-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-theta a cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-theta a cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-theta a cs p)) asg p)
                       (hkec-theta (hkec-eval-lanes a asg p)))))
  :enable hkec-g-theta)

(in-theory (disable hkec-g-theta))

;; rho and pi: rotate_left and a permutation of the lanes, no constraints.

(defruled hkec-rho-pi-unroll
  (equal (hkec-rho-pi a1)
         (list (hkec-rotate-left (nth 0 a1) 0) (hkec-rotate-left (nth 6 a1) 20) (hkec-rotate-left (nth 12 a1) 21) (hkec-rotate-left (nth 18 a1) 43) (hkec-rotate-left (nth 24 a1) 50) (hkec-rotate-left (nth 3 a1) 36) (hkec-rotate-left (nth 9 a1) 44) (hkec-rotate-left (nth 10 a1) 61) (hkec-rotate-left (nth 16 a1) 19) (hkec-rotate-left (nth 22 a1) 3) (hkec-rotate-left (nth 1 a1) 63) (hkec-rotate-left (nth 7 a1) 58) (hkec-rotate-left (nth 13 a1) 39) (hkec-rotate-left (nth 19 a1) 56) (hkec-rotate-left (nth 20 a1) 46) (hkec-rotate-left (nth 4 a1) 37) (hkec-rotate-left (nth 5 a1) 28) (hkec-rotate-left (nth 11 a1) 54) (hkec-rotate-left (nth 17 a1) 49) (hkec-rotate-left (nth 23 a1) 8) (hkec-rotate-left (nth 2 a1) 2) (hkec-rotate-left (nth 8 a1) 9) (hkec-rotate-left (nth 14 a1) 25) (hkec-rotate-left (nth 15 a1) 23) (hkec-rotate-left (nth 21 a1) 62)))
  :expand ((:free (a2) (hkec-rho-pi-aux 0 a1 a2)) (:free (a2) (hkec-rho-pi-aux 1 a1 a2)) (:free (a2) (hkec-rho-pi-aux 2 a1 a2)) (:free (a2) (hkec-rho-pi-aux 3 a1 a2)) (:free (a2) (hkec-rho-pi-aux 4 a1 a2)) (:free (a2) (hkec-rho-pi-aux 5 a1 a2)) (:free (a2) (hkec-rho-pi-aux 6 a1 a2)) (:free (a2) (hkec-rho-pi-aux 7 a1 a2)) (:free (a2) (hkec-rho-pi-aux 8 a1 a2)) (:free (a2) (hkec-rho-pi-aux 9 a1 a2)) (:free (a2) (hkec-rho-pi-aux 10 a1 a2)) (:free (a2) (hkec-rho-pi-aux 11 a1 a2)) (:free (a2) (hkec-rho-pi-aux 12 a1 a2)) (:free (a2) (hkec-rho-pi-aux 13 a1 a2)) (:free (a2) (hkec-rho-pi-aux 14 a1 a2)) (:free (a2) (hkec-rho-pi-aux 15 a1 a2)) (:free (a2) (hkec-rho-pi-aux 16 a1 a2)) (:free (a2) (hkec-rho-pi-aux 17 a1 a2)) (:free (a2) (hkec-rho-pi-aux 18 a1 a2)) (:free (a2) (hkec-rho-pi-aux 19 a1 a2)) (:free (a2) (hkec-rho-pi-aux 20 a1 a2)) (:free (a2) (hkec-rho-pi-aux 21 a1 a2)) (:free (a2) (hkec-rho-pi-aux 22 a1 a2)) (:free (a2) (hkec-rho-pi-aux 23 a1 a2)) (:free (a2) (hkec-rho-pi-aux 24 a1 a2)) (:free (a2) (hkec-rho-pi-aux 25 a1 a2))))

(defrule hkec-rho-pi-props
  (implies (and (hkec-lanes-len a1 64)
                (equal (len a1) 25))
           (and (implies (hkec-lanes-ok a1 n)
                         (hkec-lanes-ok (hkec-rho-pi a1) n))
                (implies (hkec-lanes-wires-p a1 asg p)
                         (hkec-lanes-wires-p (hkec-rho-pi a1) asg p))
                (equal (hkec-eval-lanes (hkec-rho-pi a1) asg p)
                       (hkec-rho-pi (hkec-eval-lanes a1 asg p)))
                (hkec-lanes-len (hkec-rho-pi a1) 64)
                (equal (len (hkec-rho-pi a1)) 25)))
  :in-theory (e/d (hkec-rho-pi-unroll) (hkec-rho-pi)))

(in-theory (disable hkec-rho-pi))

(defruled hkec-chi-unroll
  (equal (hkec-chi a2)
         (list (hkec-lane-chi (nth 0 a2) (nth 1 a2) (nth 2 a2)) (hkec-lane-chi (nth 1 a2) (nth 2 a2) (nth 3 a2)) (hkec-lane-chi (nth 2 a2) (nth 3 a2) (nth 4 a2)) (hkec-lane-chi (nth 3 a2) (nth 4 a2) (nth 0 a2)) (hkec-lane-chi (nth 4 a2) (nth 0 a2) (nth 1 a2)) (hkec-lane-chi (nth 5 a2) (nth 6 a2) (nth 7 a2)) (hkec-lane-chi (nth 6 a2) (nth 7 a2) (nth 8 a2)) (hkec-lane-chi (nth 7 a2) (nth 8 a2) (nth 9 a2)) (hkec-lane-chi (nth 8 a2) (nth 9 a2) (nth 5 a2)) (hkec-lane-chi (nth 9 a2) (nth 5 a2) (nth 6 a2)) (hkec-lane-chi (nth 10 a2) (nth 11 a2) (nth 12 a2)) (hkec-lane-chi (nth 11 a2) (nth 12 a2) (nth 13 a2)) (hkec-lane-chi (nth 12 a2) (nth 13 a2) (nth 14 a2)) (hkec-lane-chi (nth 13 a2) (nth 14 a2) (nth 10 a2)) (hkec-lane-chi (nth 14 a2) (nth 10 a2) (nth 11 a2)) (hkec-lane-chi (nth 15 a2) (nth 16 a2) (nth 17 a2)) (hkec-lane-chi (nth 16 a2) (nth 17 a2) (nth 18 a2)) (hkec-lane-chi (nth 17 a2) (nth 18 a2) (nth 19 a2)) (hkec-lane-chi (nth 18 a2) (nth 19 a2) (nth 15 a2)) (hkec-lane-chi (nth 19 a2) (nth 15 a2) (nth 16 a2)) (hkec-lane-chi (nth 20 a2) (nth 21 a2) (nth 22 a2)) (hkec-lane-chi (nth 21 a2) (nth 22 a2) (nth 23 a2)) (hkec-lane-chi (nth 22 a2) (nth 23 a2) (nth 24 a2)) (hkec-lane-chi (nth 23 a2) (nth 24 a2) (nth 20 a2)) (hkec-lane-chi (nth 24 a2) (nth 20 a2) (nth 21 a2))))
  :expand ((hkec-chi-aux a2 0) (hkec-chi-aux a2 1) (hkec-chi-aux a2 2) (hkec-chi-aux a2 3) (hkec-chi-aux a2 4) (hkec-chi-aux a2 5) (hkec-chi-aux a2 6) (hkec-chi-aux a2 7) (hkec-chi-aux a2 8) (hkec-chi-aux a2 9) (hkec-chi-aux a2 10) (hkec-chi-aux a2 11) (hkec-chi-aux a2 12) (hkec-chi-aux a2 13) (hkec-chi-aux a2 14) (hkec-chi-aux a2 15) (hkec-chi-aux a2 16) (hkec-chi-aux a2 17) (hkec-chi-aux a2 18) (hkec-chi-aux a2 19) (hkec-chi-aux a2 20) (hkec-chi-aux a2 21) (hkec-chi-aux a2 22) (hkec-chi-aux a2 23) (hkec-chi-aux a2 24) (hkec-chi-aux a2 25)))

;; chi, a_3[x + 5y] = a[x, y] ^ (!a[x+1, y] & a[x+2, y]).

(defun hkec-g-chi (a2 cs p)
  (b* (((mv f0 cs) (hkec-g-lane-chi (nth 0 a2) (nth 1 a2) (nth 2 a2) cs p))
       ((mv f1 cs) (hkec-g-lane-chi (nth 1 a2) (nth 2 a2) (nth 3 a2) cs p))
       ((mv f2 cs) (hkec-g-lane-chi (nth 2 a2) (nth 3 a2) (nth 4 a2) cs p))
       ((mv f3 cs) (hkec-g-lane-chi (nth 3 a2) (nth 4 a2) (nth 0 a2) cs p))
       ((mv f4 cs) (hkec-g-lane-chi (nth 4 a2) (nth 0 a2) (nth 1 a2) cs p))
       ((mv f5 cs) (hkec-g-lane-chi (nth 5 a2) (nth 6 a2) (nth 7 a2) cs p))
       ((mv f6 cs) (hkec-g-lane-chi (nth 6 a2) (nth 7 a2) (nth 8 a2) cs p))
       ((mv f7 cs) (hkec-g-lane-chi (nth 7 a2) (nth 8 a2) (nth 9 a2) cs p))
       ((mv f8 cs) (hkec-g-lane-chi (nth 8 a2) (nth 9 a2) (nth 5 a2) cs p))
       ((mv f9 cs) (hkec-g-lane-chi (nth 9 a2) (nth 5 a2) (nth 6 a2) cs p))
       ((mv f10 cs) (hkec-g-lane-chi (nth 10 a2) (nth 11 a2) (nth 12 a2) cs p))
       ((mv f11 cs) (hkec-g-lane-chi (nth 11 a2) (nth 12 a2) (nth 13 a2) cs p))
       ((mv f12 cs) (hkec-g-lane-chi (nth 12 a2) (nth 13 a2) (nth 14 a2) cs p))
       ((mv f13 cs) (hkec-g-lane-chi (nth 13 a2) (nth 14 a2) (nth 10 a2) cs p))
       ((mv f14 cs) (hkec-g-lane-chi (nth 14 a2) (nth 10 a2) (nth 11 a2) cs p))
       ((mv f15 cs) (hkec-g-lane-chi (nth 15 a2) (nth 16 a2) (nth 17 a2) cs p))
       ((mv f16 cs) (hkec-g-lane-chi (nth 16 a2) (nth 17 a2) (nth 18 a2) cs p))
       ((mv f17 cs) (hkec-g-lane-chi (nth 17 a2) (nth 18 a2) (nth 19 a2) cs p))
       ((mv f18 cs) (hkec-g-lane-chi (nth 18 a2) (nth 19 a2) (nth 15 a2) cs p))
       ((mv f19 cs) (hkec-g-lane-chi (nth 19 a2) (nth 15 a2) (nth 16 a2) cs p))
       ((mv f20 cs) (hkec-g-lane-chi (nth 20 a2) (nth 21 a2) (nth 22 a2) cs p))
       ((mv f21 cs) (hkec-g-lane-chi (nth 21 a2) (nth 22 a2) (nth 23 a2) cs p))
       ((mv f22 cs) (hkec-g-lane-chi (nth 22 a2) (nth 23 a2) (nth 24 a2) cs p))
       ((mv f23 cs) (hkec-g-lane-chi (nth 23 a2) (nth 24 a2) (nth 20 a2) cs p))
       ((mv f24 cs) (hkec-g-lane-chi (nth 24 a2) (nth 20 a2) (nth 21 a2) cs p)))
    (mv (list f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24) cs)))

(defrule hkec-g-chi-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-chi a2 cs p)) old))
  :enable hkec-g-chi)

(defrule hkec-g-chi-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-chi a2 cs p))))
  :rule-classes :linear
  :enable hkec-g-chi)

(defrule hkec-g-chi-shape
  (implies (and (hkec-lanes-len a2 64)
                (equal (len a2) 25))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-chi a2 cs p)) 64) (equal (len (mv-nth 0 (hkec-g-chi a2 cs p))) 25)))
  :enable hkec-g-chi)

(defrule hkec-g-chi-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a2 (len cs))
                (hkec-lanes-len a2 64)
                (equal (len a2) 25))
           (hkec-wf (mv-nth 1 (hkec-g-chi a2 cs p)) p))
  :enable hkec-g-chi)

(defrule hkec-g-chi-ok
  (implies (and (hkec-lanes-ok a2 (len cs))
                (hkec-lanes-len a2 64)
                (equal (len a2) 25)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-chi a2 cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-chi a2 cs p)) m))
  :enable hkec-g-chi)

(defrule hkec-g-chi-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-chi a2 cs p)) asg p)
                (hkec-lanes-wires-p a2 asg p)
                (hkec-lanes-len a2 64)
                (equal (len a2) 25))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-chi a2 cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-chi a2 cs p)) asg p)
                       (hkec-chi (hkec-eval-lanes a2 asg p)))))
  :enable hkec-g-chi
  :hints (("Goal" :in-theory (enable hkec-chi-unroll))))

(in-theory (disable hkec-g-chi))

;; iota: lane 0 xor the constant round constant bits (folds, no constraints).

(defun hkec-g-iota (a3 rc cs p)
  (b* (((mv l cs) (hkec-g-lane-xor (nth 0 a3) rc cs p)))
    (mv (update-nth 0 l a3) cs)))

(defrule hkec-g-iota-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-iota a3 rc cs p)) old))
  :enable hkec-g-iota)

(defrule hkec-g-iota-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-iota a3 rc cs p))))
  :rule-classes :linear
  :enable hkec-g-iota)

(defrule hkec-g-iota-shape
  (implies (and (hkec-lanes-len a3 64)
                (equal (len a3) 25)
                (equal (len rc) 64))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-iota a3 rc cs p)) 64) (equal (len (mv-nth 0 (hkec-g-iota a3 rc cs p))) 25)))
  :enable hkec-g-iota)

(defrule hkec-g-iota-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a3 (len cs))
                (hkec-terms-ok rc (len cs))
                (hkec-lanes-len a3 64)
                (equal (len a3) 25)
                (equal (len rc) 64))
           (hkec-wf (mv-nth 1 (hkec-g-iota a3 rc cs p)) p))
  :enable hkec-g-iota)

(defrule hkec-g-iota-ok
  (implies (and (hkec-lanes-ok a3 (len cs))
                (hkec-terms-ok rc (len cs))
                (hkec-lanes-len a3 64)
                (equal (len a3) 25)
                (equal (len rc) 64)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-iota a3 rc cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-iota a3 rc cs p)) m))
  :enable hkec-g-iota)

(defrule hkec-g-iota-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-iota a3 rc cs p)) asg p)
                (hkec-lanes-wires-p a3 asg p)
                (hkec-wires-p rc asg p)
                (hkec-lanes-len a3 64)
                (equal (len a3) 25)
                (equal (len rc) 64))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-iota a3 rc cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-iota a3 rc cs p)) asg p)
                       (hkec-iota (hkec-eval-lanes a3 asg p) (hkec-eval-list rc asg p)))))
  :enable hkec-g-iota)

(in-theory (disable hkec-g-iota))

;; Keccak::round.

(defun hkec-g-round (a rc cs p)
  (b* (((mv a1 cs) (hkec-g-theta a cs p))
       (a2 (hkec-rho-pi a1))
       ((mv a3 cs) (hkec-g-chi a2 cs p))
       ((mv a4 cs) (hkec-g-iota a3 rc cs p)))
    (mv a4 cs)))

(defrule hkec-g-round-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-round a rc cs p)) old))
  :enable hkec-g-round)

(defrule hkec-g-round-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-round a rc cs p))))
  :rule-classes :linear
  :enable hkec-g-round)

(defrule hkec-g-round-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25)
                (equal (len rc) 64))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-round a rc cs p)) 64) (equal (len (mv-nth 0 (hkec-g-round a rc cs p))) 25)))
  :enable hkec-g-round)

(defrule hkec-g-round-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-terms-ok rc (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (equal (len rc) 64))
           (hkec-wf (mv-nth 1 (hkec-g-round a rc cs p)) p))
  :enable hkec-g-round)

(defrule hkec-g-round-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-terms-ok rc (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (equal (len rc) 64)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-round a rc cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-round a rc cs p)) m))
  :enable hkec-g-round)

(defrule hkec-g-round-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-round a rc cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-wires-p rc asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (equal (len rc) 64))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-round a rc cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-round a rc cs p)) asg p)
                       (hkec-round (hkec-eval-lanes a asg p) (hkec-eval-list rc asg p)))))
  :enable hkec-g-round
  :hints (("Goal" :in-theory (enable hkec-round))))

(in-theory (disable hkec-g-round))
