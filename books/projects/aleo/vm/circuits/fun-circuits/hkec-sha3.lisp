; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Keccak spec of hash-keccak.lisp (snarkVM's circuit structure: 25 U64
; lanes, rotate_left, a combined rho-pi table, round constant lanes) agrees
; with the FIPS 202 spec of kestrel/crypto/sha-3:
;
;   HKEC-ROUND           = SHA3::RND on the state array (HKEC-RND-IS-SHA3-RND)
;   HKEC-PERMUTATION-F   = (SHA3::KECCAK-P 1600 24 .)
;   HKEC-SPONGE          = HKEC-KECCAK-FAMILY-HASH, i.e. SHA3::KECCAK with
;                          c = 2 VARIANT, on the byte-padded input (with the
;                          SHA-3 domain bits 0 1 for TYPE 1).
;
; Every step is proved lane by lane: a lane of a kestrel step is the NTHCDR 0
; of a z-indexed recursion, which is shown equal to the list operation of
; hash-keccak.lisp by induction on z; only the 25 lane positions and the 24
; round numbers are unrolled, never the 1600 state bits.

(in-package "ALEOVM")

(include-book "../fun-specs/hash-keccak")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/group" :dir :system))
(local (include-book "kestrel/bv/bitxor" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lists.

(defruled hkec-cons-nth-nthcdr
  (implies (and (natp z)
                (< z (len x)))
           (equal (cons (nth z x) (nthcdr (+ 1 z) x))
                  (nthcdr z x)))
  :induct (nthcdr z x)
  :enable nthcdr)

(defrule hkec-true-listp-of-lane-xor
  (true-listp (hkec-lane-xor xs ys)))

(defrule hkec-len-of-lane-xor
  (equal (len (hkec-lane-xor xs ys))
         (len xs)))

(defrule hkec-nth-of-lane-xor
  (implies (< (nfix z) (len xs))
           (equal (nth z (hkec-lane-xor xs ys))
                  (acl2::bitxor (nth z xs) (nth z ys))))
  :induct (hkec-cdr-nth-induct z xs ys)
  :prep-lemmas
  ((defun hkec-cdr-nth-induct (z xs ys)
     (if (or (zp z) (atom xs))
         (list z xs ys)
       (hkec-cdr-nth-induct (1- z) (cdr xs) (cdr ys))))))

(defrule hkec-true-listp-of-lane-chi
  (true-listp (hkec-lane-chi as bs cs)))

(defrule hkec-len-of-lane-chi
  (equal (len (hkec-lane-chi as bs cs))
         (len as)))

(defun hkec-cdr-nth-induct3 (z as bs cs)
  (if (or (zp z) (atom as))
      (list z as bs cs)
    (hkec-cdr-nth-induct3 (1- z) (cdr as) (cdr bs) (cdr cs))))

(defrule hkec-nth-of-lane-chi
  (implies (< (nfix z) (len as))
           (equal (nth z (hkec-lane-chi as bs cs))
                  (acl2::bitxor (nth z as)
                                (acl2::bitand (acl2::bitxor (nth z bs) 1)
                                              (nth z cs)))))
  :induct (hkec-cdr-nth-induct3 z as bs cs))

(defrule hkec-true-listp-of-rotate-left
  (implies (true-listp x)
           (true-listp (hkec-rotate-left x n))))

(defrule hkec-len-of-rotate-left
  (implies (<= (nfix n) (len x))
           (equal (len (hkec-rotate-left x n))
                  (len x))))

(defrule hkec-nth-of-rotate-left
  (implies (and (natp z)
                (natp n)
                (< z (len x))
                (< n (len x)))
           (equal (nth z (hkec-rotate-left x n))
                  (nth (mod (+ z n) (len x)) x)))
  :cases ((< (+ z n) (len x)))
  :hints (("Subgoal 2" :use ((:instance acl2::mod-of-+-of---same
                              (x (+ z n)) (y (len x)))))))

(defruled hkec-nthcdr-when-len-<=
  (implies (and (true-listp x)
                (<= (len x) (nfix z)))
           (equal (nthcdr z x) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A list of 25 lanes as a kestrel state array (planes y, lanes x).

(defund hkec-k (l)
  (list (list (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l) (nth 4 l))
        (list (nth 5 l) (nth 6 l) (nth 7 l) (nth 8 l) (nth 9 l))
        (list (nth 10 l) (nth 11 l) (nth 12 l) (nth 13 l) (nth 14 l))
        (list (nth 15 l) (nth 16 l) (nth 17 l) (nth 18 l) (nth 19 l))
        (list (nth 20 l) (nth 21 l) (nth 22 l) (nth 23 l) (nth 24 l))))

(defrule hkec-nth-nth-of-hkec-k
  (implies (and (natp x) (< x 5)
                (natp y) (< y 5))
           (equal (nth x (nth y (hkec-k l)))
                  (nth (+ x (* 5 y)) l)))
  :enable hkec-k
  :cases ((and (equal x 0) (equal y 0)) (and (equal x 1) (equal y 0)) (and (equal x 2) (equal y 0)) (and (equal x 3) (equal y 0)) (and (equal x 4) (equal y 0)) (and (equal x 0) (equal y 1)) (and (equal x 1) (equal y 1)) (and (equal x 2) (equal y 1)) (and (equal x 3) (equal y 1)) (and (equal x 4) (equal y 1)) (and (equal x 0) (equal y 2)) (and (equal x 1) (equal y 2)) (and (equal x 2) (equal y 2)) (and (equal x 3) (equal y 2)) (and (equal x 4) (equal y 2)) (and (equal x 0) (equal y 3)) (and (equal x 1) (equal y 3)) (and (equal x 2) (equal y 3)) (and (equal x 3) (equal y 3)) (and (equal x 4) (equal y 3)) (and (equal x 0) (equal y 4)) (and (equal x 1) (equal y 4)) (and (equal x 2) (equal y 4)) (and (equal x 3) (equal y 4)) (and (equal x 4) (equal y 4))))

(defrule hkec-sha3-a-of-hkec-k
  (implies (and (natp x) (< x 5)
                (natp y) (< y 5))
           (equal (sha3::a x y z (hkec-k l) w)
                  (nth z (nth (+ x (* 5 y)) l))))
  :enable (sha3::a sha3::nth-bit sha3::nth-lane sha3::nth-plane))

(defrule hkec-get-lane-of-hkec-k
  (implies (and (natp x) (< x 5)
                (natp y) (< y 5))
           (equal (sha3::get-lane x y (hkec-k l) w)
                  (nth (+ x (* 5 y)) l)))
  :enable (sha3::nth-lane sha3::nth-plane))

(defun hkec-lanes-shape (l)
  (if (atom l)
      (null l)
    (and (true-listp (car l))
         (equal (len (car l)) 64)
         (hkec-lanes-shape (cdr l)))))

(defrule hkec-lane-shape-of-nth
  (implies (and (hkec-lanes-shape l)
                (< (nfix i) (len l)))
           (and (true-listp (nth i l))
                (equal (len (nth i l)) 64)))
  :induct (nth i l)
  :in-theory (e/d (nth) (acl2::nth-of-cdr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; theta.

(defrule hkec-theta-c-lane-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (natp x) (< x 5)
                (natp z))
           (equal (sha3::theta-c-lane z x (hkec-k l) 64)
                  (nthcdr z (hkec-theta-c-lane l x))))
  :induct (sha3::theta-c-lane z x (hkec-k l) 64)
  :enable (sha3::theta-c-lane hkec-nthcdr-when-len-<=)
  :hints (("Subgoal *1/2" :use ((:instance hkec-cons-nth-nthcdr
                                 (x (hkec-theta-c-lane l x)))))))

(defrule hkec-theta-c-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::theta-c (hkec-k l) 64)
                  (hkec-theta-c l)))
  :expand ((:free (x) (sha3::theta-c-lanes x (hkec-k l) 64)))
  :disable hkec-theta-c-lane)

(defrule hkec-lanes-shape-of-cons
  (equal (hkec-lanes-shape (cons a l))
         (and (true-listp a)
              (equal (len a) 64)
              (hkec-lanes-shape l))))

(defruled hkec-mod-63
  (implies (integerp z)
           (equal (mod (+ 63 z) 64)
                  (mod (+ -1 z) 64)))
  :enable acl2::mod-sum-cases)

(defruled hkec-mod-4
  (implies (integerp x)
           (equal (mod (+ -1 x) 5)
                  (mod (+ 4 x) 5)))
  :enable acl2::mod-sum-cases)

(defrule hkec-theta-d-lane-is-sha3
  (implies (and (hkec-lanes-shape c)
                (equal (len c) 5)
                (natp x) (< x 5)
                (natp z))
           (equal (sha3::theta-d-lane z x c 64)
                  (nthcdr z (hkec-theta-d-lane c x))))
  :induct (sha3::theta-d-lane z x c 64)
  :enable (sha3::theta-d-lane hkec-nthcdr-when-len-<= sha3::nth-bit sha3::nth-lane
                              hkec-mod-63 hkec-mod-4)
  :disable hkec-rotate-left
  :hints (("Subgoal *1/2" :use ((:instance hkec-cons-nth-nthcdr
                                 (x (hkec-theta-d-lane c x)))))))

(defrule hkec-theta-c-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (and (hkec-lanes-shape (hkec-theta-c l))
                (equal (len (hkec-theta-c l)) 5))))

(defrule hkec-theta-d-shape
  (implies (and (hkec-lanes-shape c)
                (equal (len c) 5))
           (and (hkec-lanes-shape (hkec-theta-d c))
                (equal (len (hkec-theta-d c)) 5))))

(defrule hkec-theta-d-is-sha3
  (implies (and (hkec-lanes-shape c)
                (equal (len c) 5))
           (equal (sha3::theta-d c 64)
                  (hkec-theta-d c)))
  :enable sha3::theta-d
  :expand ((:free (x) (sha3::theta-d-lanes x c 64)))
  :disable hkec-theta-d-lane)

(defrule hkec-theta-lane-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (hkec-lanes-shape d)
                (equal (len d) 5)
                (natp x) (< x 5)
                (natp y) (< y 5)
                (natp z))
           (equal (sha3::theta-lane z x y (hkec-k l) d 64)
                  (nthcdr z (hkec-lane-xor (nth (+ x (* 5 y)) l) (nth x d)))))
  :induct (sha3::theta-lane z x y (hkec-k l) d 64)
  :enable (sha3::theta-lane hkec-nthcdr-when-len-<= sha3::nth-bit sha3::nth-lane)
  :hints (("Subgoal *1/2" :use ((:instance hkec-cons-nth-nthcdr
                                 (x (hkec-lane-xor (nth (+ x (* 5 y)) l) (nth x d))))))))

(defruled hkec-theta-apply-unroll
  (equal (hkec-theta-apply a d 0)
         (list (hkec-lane-xor (nth 0 a) (nth 0 d)) (hkec-lane-xor (nth 1 a) (nth 1 d))
               (hkec-lane-xor (nth 2 a) (nth 2 d)) (hkec-lane-xor (nth 3 a) (nth 3 d))
               (hkec-lane-xor (nth 4 a) (nth 4 d)) (hkec-lane-xor (nth 5 a) (nth 0 d))
               (hkec-lane-xor (nth 6 a) (nth 1 d)) (hkec-lane-xor (nth 7 a) (nth 2 d))
               (hkec-lane-xor (nth 8 a) (nth 3 d)) (hkec-lane-xor (nth 9 a) (nth 4 d))
               (hkec-lane-xor (nth 10 a) (nth 0 d)) (hkec-lane-xor (nth 11 a) (nth 1 d))
               (hkec-lane-xor (nth 12 a) (nth 2 d)) (hkec-lane-xor (nth 13 a) (nth 3 d))
               (hkec-lane-xor (nth 14 a) (nth 4 d)) (hkec-lane-xor (nth 15 a) (nth 0 d))
               (hkec-lane-xor (nth 16 a) (nth 1 d)) (hkec-lane-xor (nth 17 a) (nth 2 d))
               (hkec-lane-xor (nth 18 a) (nth 3 d)) (hkec-lane-xor (nth 19 a) (nth 4 d))
               (hkec-lane-xor (nth 20 a) (nth 0 d)) (hkec-lane-xor (nth 21 a) (nth 1 d))
               (hkec-lane-xor (nth 22 a) (nth 2 d)) (hkec-lane-xor (nth 23 a) (nth 3 d))
               (hkec-lane-xor (nth 24 a) (nth 4 d))))
  :expand ((:free (i) (hkec-theta-apply a d i))))

(defrule hkec-k-of-cons
  (implies (syntaxp (and (consp l) (eq (car l) 'cons)))
           (equal (hkec-k l)
                  (list (list (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l) (nth 4 l)) (list (nth 5 l) (nth 6 l) (nth 7 l) (nth 8 l) (nth 9 l)) (list (nth 10 l) (nth 11 l) (nth 12 l) (nth 13 l) (nth 14 l)) (list (nth 15 l) (nth 16 l) (nth 17 l) (nth 18 l) (nth 19 l)) (list (nth 20 l) (nth 21 l) (nth 22 l) (nth 23 l) (nth 24 l)))))
  :enable hkec-k)

(defrule hkec-theta-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::theta (hkec-k l) 64)
                  (hkec-k (hkec-theta l))))
  :enable (sha3::theta hkec-theta-apply-unroll)
  :expand ((:free (y d) (sha3::theta-planes y (hkec-k l) d 64))
           (:free (x y d) (sha3::theta-lanes x y (hkec-k l) d 64)))
  :disable (hkec-theta-d hkec-theta-c sha3::theta-c))

(defrule hkec-theta-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (and (hkec-lanes-shape (hkec-theta l))
                (equal (len (hkec-theta l)) 25)))
  :enable hkec-theta-apply-unroll
  :disable (hkec-theta-d hkec-theta-c))


;; rho and pi.

(defrule hkec-sha3-a-is-nth-get-lane
  (equal (sha3::a x y z a w)
         (nth z (sha3::get-lane x y a w)))
  :enable (sha3::a sha3::nth-bit sha3::get-lane))

(defrule hkec-get-lane-of-set-lane
  (implies (and (natp x) (natp y) (natp x2) (natp y2))
           (equal (sha3::get-lane x2 y2 (sha3::set-lane x y lane a w) w)
                  (if (and (equal x2 x) (equal y2 y))
                      lane
                    (sha3::get-lane x2 y2 a w))))
  :enable (sha3::set-lane sha3::update-nth-plane sha3::update-nth-lane
                          sha3::nth-plane sha3::nth-lane))

(defrule hkec-get-lane-of-update-bit
  (implies (and (natp x) (natp y) (natp x2) (natp y2))
           (equal (sha3::get-lane x2 y2 (sha3::update-bit x y z bit a w) w)
                  (if (and (equal x2 x) (equal y2 y))
                      (update-nth z bit (sha3::get-lane x y a w))
                    (sha3::get-lane x2 y2 a w))))
  :enable (sha3::update-bit sha3::update-nth-bit)
  :disable sha3::get-lane)

(defruled hkec-take-of-update-nth-same
  (implies (and (natp z)
                (< z (len x)))
           (equal (take (+ 1 z) (update-nth z v x))
                  (append (take z x) (list v))))
  :induct (nth z x)
  :in-theory (e/d (nth update-nth take) (acl2::nth-of-cdr)))

(defruled hkec-rho-mod
  (implies (and (integerp z) (integerp off))
           (equal (mod (+ z (mod (- off) 64)) 64)
                  (mod (- z off) 64)))
  :enable acl2::mod-sum-cases)

(defrule hkec-rho-aux-aux-other-lane
  (implies (and (natp x) (natp y) (natp x2) (natp y2)
                (not (and (equal x2 x) (equal y2 y))))
           (equal (sha3::get-lane x2 y2 (sha3::rho-aux-aux z tv x y a1 a 64) 64)
                  (sha3::get-lane x2 y2 a1 64)))
  :induct (sha3::rho-aux-aux z tv x y a1 a 64)
  :enable sha3::rho-aux-aux
  :disable (sha3::get-lane hkec-sha3-a-is-nth-get-lane))

(defun hkec-raa (z off x y a1 a)
  (declare (xargs :measure (nfix (- 64 z))))
  (if (or (not (natp z)) (<= 64 z))
      a1
    (hkec-raa (+ 1 z) off x y
              (sha3::update-bit x y z (sha3::a x y (mod (- z off) 64) a 64) a1 64)
              a)))

(acl2::with-prover-time-limit 120
(defruled hkec-rho-aux-aux-is-raa
  (equal (sha3::rho-aux-aux z tv x y a1 a 64)
         (hkec-raa z (* (+ tv 1) (+ tv 2) 1/2) x y a1 a))
  :induct (sha3::rho-aux-aux z tv x y a1 a 64)
  :in-theory '(sha3::rho-aux-aux hkec-raa natp)))

(acl2::with-prover-time-limit 300
(defrule hkec-raa-same-lane
  (implies (and (natp x) (natp y) (integerp off)
                (natp z) (<= z 64)
                (true-listp (sha3::get-lane x y a1 64))
                (equal (len (sha3::get-lane x y a1 64)) 64)
                (true-listp (sha3::get-lane x y a 64))
                (equal (len (sha3::get-lane x y a 64)) 64))
           (equal (sha3::get-lane x y (hkec-raa z off x y a1 a) 64)
                  (append (take z (sha3::get-lane x y a1 64))
                          (nthcdr z (hkec-rotate-left
                                     (sha3::get-lane x y a 64)
                                     (mod (- off) 64))))))
  :induct (hkec-raa z off x y a1 a)
  :enable (hkec-take-of-update-nth-same hkec-nthcdr-when-len-<=)
  :disable (sha3::get-lane hkec-rotate-left)
  :hints (("Subgoal *1/2"
           :use ((:instance hkec-cons-nth-nthcdr
                  (x (hkec-rotate-left
                      (sha3::get-lane x y a 64)
                      (mod (- off) 64))))
                 (:instance hkec-rho-mod))))))

(defrule hkec-rho-aux-aux-same-lane
  (implies (and (natp x) (natp y) (natp tv)
                (integerp (* (+ tv 1) (+ tv 2) 1/2))
                (true-listp (sha3::get-lane x y a1 64))
                (equal (len (sha3::get-lane x y a1 64)) 64)
                (true-listp (sha3::get-lane x y a 64))
                (equal (len (sha3::get-lane x y a 64)) 64))
           (equal (sha3::get-lane x y (sha3::rho-aux-aux 0 tv x y a1 a 64) 64)
                  (hkec-rotate-left
                   (sha3::get-lane x y a 64)
                   (mod (- (* (+ tv 1) (+ tv 2) 1/2)) 64))))
  :in-theory '(hkec-rho-aux-aux-is-raa natp take nthcdr binary-append (:e zp) (:e take) (:e nthcdr))
  :use ((:instance hkec-raa-same-lane (z 0) (off (* (+ tv 1) (+ tv 2) 1/2)))
        (:instance hkec-true-listp-of-rotate-left
         (x (sha3::get-lane x y a 64)) (n (mod (- (* (+ tv 1) (+ tv 2) 1/2)) 64)))))

(defrule hkec-rotate-left-0
  (implies (true-listp x)
           (equal (hkec-rotate-left x 0) x)))

(defruled hkec-rho-pi-unroll
  (equal (hkec-rho-pi a1)
         (list (hkec-rotate-left (nth 0 a1) 0) (hkec-rotate-left (nth 6 a1) 20) (hkec-rotate-left (nth 12 a1) 21) (hkec-rotate-left (nth 18 a1) 43) (hkec-rotate-left (nth 24 a1) 50) (hkec-rotate-left (nth 3 a1) 36) (hkec-rotate-left (nth 9 a1) 44) (hkec-rotate-left (nth 10 a1) 61) (hkec-rotate-left (nth 16 a1) 19) (hkec-rotate-left (nth 22 a1) 3) (hkec-rotate-left (nth 1 a1) 63) (hkec-rotate-left (nth 7 a1) 58) (hkec-rotate-left (nth 13 a1) 39) (hkec-rotate-left (nth 19 a1) 56) (hkec-rotate-left (nth 20 a1) 46) (hkec-rotate-left (nth 4 a1) 37) (hkec-rotate-left (nth 5 a1) 28) (hkec-rotate-left (nth 11 a1) 54) (hkec-rotate-left (nth 17 a1) 49) (hkec-rotate-left (nth 23 a1) 8) (hkec-rotate-left (nth 2 a1) 2) (hkec-rotate-left (nth 8 a1) 9) (hkec-rotate-left (nth 14 a1) 25) (hkec-rotate-left (nth 15 a1) 23) (hkec-rotate-left (nth 21 a1) 62)))
  :expand ((:free (i a2) (hkec-rho-pi-aux i a1 a2)))
  :disable hkec-rotate-left)

(defrule hkec-rho-pi-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::pi-fn (sha3::rho (hkec-k l) 64) 64)
                  (hkec-k (hkec-rho-pi l))))
  :enable (sha3::rho sha3::pi-fn hkec-rho-pi-unroll)
  :expand ((:free (tv x y a1) (sha3::rho-aux tv x y a1 (hkec-k l) 64))
           (:free (y a) (sha3::pi-planes y a 64))
           (:free (x y a) (sha3::pi-lanes x y a 64)))
  :disable (hkec-rotate-left sha3::get-lane hkec-rho-pi))

(defrule hkec-rho-pi-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (and (hkec-lanes-shape (hkec-rho-pi l))
                (equal (len (hkec-rho-pi l)) 25)))
  :enable hkec-rho-pi-unroll
  :disable (hkec-rotate-left hkec-rho-pi))


;; chi.

(defrule hkec-chi-lane-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (natp x) (< x 5)
                (natp y) (< y 5)
                (natp z))
           (equal (sha3::chi-lane z x y (hkec-k l) 64)
                  (nthcdr z (hkec-lane-chi (nth (+ x (* 5 y)) l)
                                           (nth (+ (mod (+ x 1) 5) (* 5 y)) l)
                                           (nth (+ (mod (+ x 2) 5) (* 5 y)) l)))))
  :induct (sha3::chi-lane z x y (hkec-k l) 64)
  :enable (sha3::chi-lane hkec-nthcdr-when-len-<=)
  :hints (("Subgoal *1/2" :use ((:instance hkec-cons-nth-nthcdr
                                 (x (hkec-lane-chi (nth (+ x (* 5 y)) l)
                                                   (nth (+ (mod (+ x 1) 5) (* 5 y)) l)
                                                   (nth (+ (mod (+ x 2) 5) (* 5 y)) l))))))))

(defruled hkec-chi-unroll
  (equal (hkec-chi a2)
         (list (hkec-lane-chi (nth 0 a2) (nth 1 a2) (nth 2 a2)) (hkec-lane-chi (nth 1 a2) (nth 2 a2) (nth 3 a2)) (hkec-lane-chi (nth 2 a2) (nth 3 a2) (nth 4 a2)) (hkec-lane-chi (nth 3 a2) (nth 4 a2) (nth 0 a2)) (hkec-lane-chi (nth 4 a2) (nth 0 a2) (nth 1 a2))
               (hkec-lane-chi (nth 5 a2) (nth 6 a2) (nth 7 a2)) (hkec-lane-chi (nth 6 a2) (nth 7 a2) (nth 8 a2)) (hkec-lane-chi (nth 7 a2) (nth 8 a2) (nth 9 a2)) (hkec-lane-chi (nth 8 a2) (nth 9 a2) (nth 5 a2)) (hkec-lane-chi (nth 9 a2) (nth 5 a2) (nth 6 a2))
               (hkec-lane-chi (nth 10 a2) (nth 11 a2) (nth 12 a2)) (hkec-lane-chi (nth 11 a2) (nth 12 a2) (nth 13 a2)) (hkec-lane-chi (nth 12 a2) (nth 13 a2) (nth 14 a2)) (hkec-lane-chi (nth 13 a2) (nth 14 a2) (nth 10 a2)) (hkec-lane-chi (nth 14 a2) (nth 10 a2) (nth 11 a2))
               (hkec-lane-chi (nth 15 a2) (nth 16 a2) (nth 17 a2)) (hkec-lane-chi (nth 16 a2) (nth 17 a2) (nth 18 a2)) (hkec-lane-chi (nth 17 a2) (nth 18 a2) (nth 19 a2)) (hkec-lane-chi (nth 18 a2) (nth 19 a2) (nth 15 a2)) (hkec-lane-chi (nth 19 a2) (nth 15 a2) (nth 16 a2))
               (hkec-lane-chi (nth 20 a2) (nth 21 a2) (nth 22 a2)) (hkec-lane-chi (nth 21 a2) (nth 22 a2) (nth 23 a2)) (hkec-lane-chi (nth 22 a2) (nth 23 a2) (nth 24 a2)) (hkec-lane-chi (nth 23 a2) (nth 24 a2) (nth 20 a2)) (hkec-lane-chi (nth 24 a2) (nth 20 a2) (nth 21 a2))))
  :expand ((:free (i) (hkec-chi-aux a2 i))))

(defrule hkec-chi-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::chi (hkec-k l) 64)
                  (hkec-k (hkec-chi l))))
  :enable (sha3::chi hkec-chi-unroll)
  :expand ((:free (y) (sha3::chi-planes y (hkec-k l) 64))
           (:free (x y) (sha3::chi-lanes x y (hkec-k l) 64)))
  :disable (hkec-chi hkec-lane-chi))

(defrule hkec-chi-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (and (hkec-lanes-shape (hkec-chi l))
                (equal (len (hkec-chi l)) 25)))
  :enable hkec-chi-unroll
  :disable (hkec-chi hkec-lane-chi))

;; iota.

(defrule hkec-set-lane-of-set-lane
  (equal (sha3::set-lane x y l2 (sha3::set-lane x y l1 a w) w)
         (sha3::set-lane x y l2 a w))
  :enable (sha3::set-lane sha3::update-nth-plane sha3::update-nth-lane
                          sha3::nth-plane))

(defrule hkec-set-lane-of-get-lane
  (implies (and (natp x) (natp y)
                (< y (len a))
                (< x (len (nth y a))))
           (equal (sha3::set-lane x y (sha3::get-lane x y a w) a w)
                  a))
  :enable (sha3::set-lane sha3::update-nth-plane sha3::update-nth-lane
                          sha3::nth-plane sha3::nth-lane))

(defrule hkec-update-bit-as-set-lane
  (equal (sha3::update-bit x y z bit a w)
         (sha3::set-lane x y (update-nth z bit (sha3::get-lane x y a w)) a w))
  :enable (sha3::update-bit sha3::update-nth-bit)
  :disable sha3::get-lane)

(defrule hkec-len-of-set-lane
  (implies (and (natp y) (< y (len a)))
           (equal (len (sha3::set-lane x y l a w))
                  (len a)))
  :enable (sha3::set-lane sha3::update-nth-plane))

(defrule hkec-len-nth-of-set-lane
  (implies (and (natp x) (natp y) (< x (len (nth y a))))
           (equal (len (nth y (sha3::set-lane x y l a w)))
                  (len (nth y a))))
  :enable (sha3::set-lane sha3::update-nth-plane sha3::update-nth-lane sha3::nth-plane))

(acl2::with-prover-time-limit 300
(defrule hkec-iota-aux2-is-set-lane
  (implies (and (natp z) (<= z 64)
                (< 0 (len a1))
                (< 0 (len (nth 0 a1)))
                (true-listp (sha3::get-lane 0 0 a1 64))
                (equal (len (sha3::get-lane 0 0 a1 64)) 64)
                (equal (len (sha3::get-lane 0 0 a 64)) 64))
           (equal (sha3::iota-aux2 z a1 a rc 64)
                  (sha3::set-lane 0 0
                                  (append (take z (sha3::get-lane 0 0 a1 64))
                                          (nthcdr z (hkec-lane-xor (sha3::get-lane 0 0 a 64) rc)))
                                  a1 64)))
  :induct (sha3::iota-aux2 z a1 a rc 64)
  :enable (sha3::iota-aux2 hkec-take-of-update-nth-same hkec-nthcdr-when-len-<=)
  :disable (sha3::get-lane sha3::set-lane)
  :hints (("Subgoal *1/2"
           :use ((:instance hkec-cons-nth-nthcdr
                  (x (hkec-lane-xor (sha3::get-lane 0 0 a 64) rc))))))))

(defund hkec-sha3-rc (i)
  (sha3::iota-aux 0 6 (acl2::repeat 64 0) i 64))

(defrule hkec-len-of-sha3-rc
  (equal (len (hkec-sha3-rc i)) 64)
  :enable (hkec-sha3-rc sha3::w-valp))

(defrule hkec-len-of-hkec-k
  (and (equal (len (hkec-k l)) 5)
       (equal (len (nth 0 (hkec-k l))) 5))
  :enable hkec-k)

(defrule hkec-set-lane-0-of-hkec-k
  (equal (sha3::set-lane 0 0 x (hkec-k l) w)
         (hkec-k (update-nth 0 x l)))
  :enable (hkec-k sha3::set-lane sha3::update-nth-plane sha3::update-nth-lane
                  sha3::nth-plane))

(defrule hkec-iota-is-sha3
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::iota (hkec-k l) i 64)
                  (hkec-k (hkec-iota l (hkec-sha3-rc i)))))
  :enable (sha3::iota hkec-sha3-rc)
  :use ((:instance hkec-iota-aux2-is-set-lane
         (z 0) (a1 (hkec-k l)) (a (hkec-k l))
         (rc (hkec-sha3-rc i))))
  :disable (hkec-iota-aux2-is-set-lane))

(defrule hkec-sha3-rc-is-round-constant
  (implies (and (natp i) (< i 24))
           (equal (hkec-sha3-rc i)
                  (nth i *hkec-round-constant-bits*)))
  :cases ((equal i 0) (equal i 1) (equal i 2) (equal i 3) (equal i 4) (equal i 5)
          (equal i 6) (equal i 7) (equal i 8) (equal i 9) (equal i 10) (equal i 11)
          (equal i 12) (equal i 13) (equal i 14) (equal i 15) (equal i 16) (equal i 17)
          (equal i 18) (equal i 19) (equal i 20) (equal i 21) (equal i 22) (equal i 23)))


;; One round.

(defrule hkec-lanes-shape-of-update-nth
  (implies (and (hkec-lanes-shape l)
                (< (nfix n) (len l))
                (true-listp v)
                (equal (len v) 64))
           (hkec-lanes-shape (update-nth n v l)))
  :induct (update-nth n v l)
  :enable update-nth)

(defrule hkec-round-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (equal (len rc) 64))
           (and (hkec-lanes-shape (hkec-round l rc))
                (equal (len (hkec-round l rc)) 25)))
  :enable hkec-round
  :disable (hkec-theta hkec-rho-pi hkec-chi))

(defrule hkec-rnd-is-sha3-rnd
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (natp i)
                (< i 24))
           (equal (sha3::rnd (hkec-k l) i 64)
                  (hkec-k (hkec-round l (nth i *hkec-round-constant-bits*)))))
  :enable hkec-round
  :disable (hkec-theta hkec-rho-pi hkec-chi hkec-iota sha3::rho sha3::pi-fn
                       sha3::theta sha3::chi sha3::iota))

(defrule hkec-len-of-round-constant-bits
  (implies (and (natp i) (< i 24))
           (equal (len (nth i *hkec-round-constant-bits*)) 64))
  :cases ((equal i 0) (equal i 1) (equal i 2) (equal i 3) (equal i 4) (equal i 5)
          (equal i 6) (equal i 7) (equal i 8) (equal i 9) (equal i 10) (equal i 11)
          (equal i 12) (equal i 13) (equal i 14) (equal i 15) (equal i 16) (equal i 17)
          (equal i 18) (equal i 19) (equal i 20) (equal i 21) (equal i 22) (equal i 23)))

;; The 24 rounds.

(defun hkec-kp-induct (i l)
  (declare (xargs :measure (nfix (- 24 i))))
  (if (or (not (natp i)) (< 23 i))
      l
    (hkec-kp-induct (+ 1 i) (hkec-round l (nth i *hkec-round-constant-bits*)))))

(defrule hkec-keccak-p-aux-is-rounds
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (natp i)
                (<= i 24))
           (equal (sha3::keccak-p-aux i 23 (hkec-k l) 64)
                  (hkec-k (hkec-rounds l (nthcdr i *hkec-round-constant-bits*)))))
  :induct (hkec-kp-induct i l)
  :enable hkec-rounds
  :disable (sha3::rnd hkec-round)
  :hints (("Subgoal *1/2" :expand ((sha3::keccak-p-aux i 23 (hkec-k l) 64)))))

;; Bits and state arrays.

(defrule hkec-take-5
  (implies (<= 5 (len x))
           (equal (take 5 x)
                  (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x))))
  :expand ((take 5 x) (take 4 (cdr x)) (take 3 (cddr x)) (take 2 (cdddr x))
           (take 1 (cddddr x)))
  :in-theory (e/d (nth) (acl2::nth-of-cdr)))

(defrule hkec-nthcdr-20
  (implies (and (true-listp l)
                (equal (len l) 25))
           (equal (nthcdr 20 l)
                  (list (nth 20 l) (nth 21 l) (nth 22 l) (nth 23 l) (nth 24 l))))
  :use ((:instance hkec-take-5 (x (nthcdr 20 l)))
        (:instance acl2::take-does-nothing (acl2::n 5) (acl2::lst (nthcdr 20 l))))
  :disable (hkec-take-5 acl2::take-does-nothing))

(defrule hkec-group-5-is-hkec-k
  (implies (and (true-listp l)
                (equal (len l) 25))
           (equal (acl2::group 5 l)
                  (hkec-k l)))
  :enable hkec-k
  :expand ((:free (x) (acl2::group 5 x))
           (:free (n x) (acl2::firstn n x))))

(defruled hkec-map-planes-of-group
  (implies (equal (mod (len s) 320) 0)
           (equal (sha3::map-bit-string-to-plane (acl2::group 320 s) 64)
                  (acl2::group 5 (acl2::group 64 s))))
  :induct (hkec-nthcdr-320-induct s)
  :in-theory (e/d (sha3::bit-string-to-plane)
                  (acl2::car-of-group acl2::cdr-of-group acl2::group-of-cons
                                      acl2::nth-of-group acl2::len-of-group hkec-take-5
                                      acl2::firstn-becomes-take acl2::firstn-becomes-take-gen))
  :expand ((acl2::group 320 s)
           (acl2::group 5 (acl2::group 64 s)))
  :prep-lemmas
  ((defun hkec-nthcdr-320-induct (s)
     (declare (xargs :measure (len s)))
     (if (atom s)
         s
       (hkec-nthcdr-320-induct (nthcdr 320 s))))))

(defrule hkec-lanes-shape-of-group-64
  (implies (and (true-listp s)
                (equal (mod (len s) 64) 0))
           (hkec-lanes-shape (acl2::group 64 s)))
  :induct (acl2::group 64 s)
  :enable acl2::group)

(defrule hkec-bits-to-state-array
  (implies (and (true-listp s)
                (equal (len s) 1600))
           (equal (sha3::bits-to-state-array s 64)
                  (hkec-k (acl2::group 64 s))))
  :enable (sha3::bits-to-state-array hkec-map-planes-of-group)
  :use ((:instance acl2::len-of-group (acl2::n 64) (acl2::list s))))

(defruled hkec-flatten-of-nthcdr
  (implies (and (natp k) (< k (len l)))
           (equal (hkec-flatten (nthcdr k l))
                  (append (nth k l) (hkec-flatten (nthcdr (+ 1 k) l)))))
  :use ((:instance hkec-cons-nth-nthcdr (z k) (x l)))
  :in-theory (e/d (hkec-flatten) (hkec-cons-nth-nthcdr)))

(defruledl hkec-flatten-25-aux
  (implies (and (true-listp l)
                (equal (len l) 25))
           (equal (hkec-flatten (nthcdr 0 l))
                  (append (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l) (nth 4 l)
                          (nth 5 l) (nth 6 l) (nth 7 l) (nth 8 l) (nth 9 l)
                          (nth 10 l) (nth 11 l) (nth 12 l) (nth 13 l) (nth 14 l)
                          (nth 15 l) (nth 16 l) (nth 17 l) (nth 18 l) (nth 19 l)
                          (nth 20 l) (nth 21 l) (nth 22 l) (nth 23 l) (nth 24 l) nil)))
  :in-theory '(hkec-flatten-of-nthcdr hkec-nthcdr-when-len-<= nfix natp
               (:e hkec-flatten) (:e <) (:e +) (:e natp) (:e nfix) (:e binary-append)))

(defruled hkec-flatten-25
  (implies (and (true-listp l)
                (equal (len l) 25))
           (equal (hkec-flatten l)
                  (append (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l) (nth 4 l)
                          (nth 5 l) (nth 6 l) (nth 7 l) (nth 8 l) (nth 9 l)
                          (nth 10 l) (nth 11 l) (nth 12 l) (nth 13 l) (nth 14 l)
                          (nth 15 l) (nth 16 l) (nth 17 l) (nth 18 l) (nth 19 l)
                          (nth 20 l) (nth 21 l) (nth 22 l) (nth 23 l) (nth 24 l) nil)))
  :use hkec-flatten-25-aux)

(defrule hkec-true-listp-when-lanes-shape
  (implies (hkec-lanes-shape l)
           (true-listp l))
  :rule-classes :forward-chaining)

(acl2::with-prover-time-limit 300
(defrule hkec-state-array-to-bits
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25))
           (equal (sha3::state-array-to-bits (hkec-k l) 64)
                  (hkec-flatten l)))
  :enable (sha3::state-array-to-bits sha3::plane-to-bit-string hkec-k hkec-flatten-25)
  :expand ((:free (n x) (acl2::ungroup n x)))))

;; permutation_f.

(defun hkec-rcs-len-64 (rcs)
  (if (atom rcs)
      t
    (and (equal (len (car rcs)) 64)
         (hkec-rcs-len-64 (cdr rcs)))))

(defrule hkec-rounds-shape
  (implies (and (hkec-lanes-shape l)
                (equal (len l) 25)
                (hkec-rcs-len-64 rcs))
           (and (hkec-lanes-shape (hkec-rounds l rcs))
                (equal (len (hkec-rounds l rcs)) 25)))
  :induct (hkec-rounds l rcs)
  :enable hkec-rounds
  :disable hkec-round)

(defrule hkec-permutation-f-is-keccak-p
  (implies (and (true-listp s)
                (equal (len s) 1600))
           (equal (hkec-permutation-f s)
                  (sha3::keccak-p 1600 24 s)))
  :enable (sha3::keccak-p hkec-permutation-f)
  :use ((:instance acl2::len-of-group (acl2::n 64) (acl2::list s)))
  :disable (hkec-rounds hkec-round))


;; Absorbing.

(defrule hkec-bvxor-list-is-xor-prefix
  (implies (and (bit-listp s)
                (bit-listp b)
                (equal (len s) (+ (len b) (nfix c))))
           (equal (acl2::bvxor-list 1 s (append b (acl2::repeat c 0)))
                  (hkec-xor-prefix s b)))
  :induct (hkec-xor-prefix s b)
  :enable (acl2::bvxor-list acl2::repeat)
  :prep-lemmas
  ((defun hkec-cdr-dec-induct (s n)
     (if (atom s)
         (list s n)
       (hkec-cdr-dec-induct (cdr s) (1- n))))
   (defrule hkec-bvxor-list-of-repeat-0
     (implies (bit-listp s)
              (equal (acl2::bvxor-list 1 s (acl2::repeat n 0))
                     s))
     :induct (hkec-cdr-dec-induct s n)
     :enable (acl2::bvxor-list acl2::repeat))))

(defrule hkec-xor-prefix-props
  (implies (and (<= (len b) (len s)))
           (and (equal (len (hkec-xor-prefix s b)) (len s))
                (implies (bit-listp s)
                         (bit-listp (hkec-xor-prefix s b))))))

(defrule hkec-true-listp-of-keccak-p
  (true-listp (sha3::keccak-p b n s))
  :enable (sha3::keccak-p sha3::state-array-to-bits))

(defrule hkec-bit-listp-of-keccak-p
  (implies (and (bit-listp s)
                (equal (len s) 1600))
           (and (bit-listp (sha3::keccak-p 1600 24 s))
                (equal (len (sha3::keccak-p 1600 24 s)) 1600)))
  :use ((:instance sha3::all-unsigned-byte-p-of-keccak-p (sha3::b 1600) (sha3::n_r 24) (sha3::s s))
        (:instance sha3::len-of-keccak-p (sha3::b 1600) (sha3::n_r 24) (sha3::s s))
        (:instance hkec-bit-listp-when-sha3-bit-stringp (x (sha3::keccak-p 1600 24 s)))
        (:instance hkec-sha3-bit-stringp-when-bit-listp (x s)))
  :disable (sha3::all-unsigned-byte-p-of-keccak-p sha3::len-of-keccak-p
                                                  hkec-bit-listp-when-sha3-bit-stringp)
  :prep-lemmas
  ((defruled hkec-sha3-bit-stringp-when-bit-listp
     (implies (bit-listp x)
              (sha3::bit-stringp x))
     :induct (bit-listp x)
     :enable (bit-listp acl2::all-unsigned-byte-p bitp unsigned-byte-p))))

(defun hkec-blocks-ok (blocks r)
  (if (atom blocks)
      t
    (and (bit-listp (car blocks))
         (equal (len (car blocks)) r)
         (hkec-blocks-ok (cdr blocks) r))))

(defrule hkec-true-listp-of-xor-prefix
  (implies (true-listp s)
           (true-listp (hkec-xor-prefix s b))))

(defrule hkec-cdr-of-nthcdr
  (equal (cdr (nthcdr i p))
         (nthcdr (+ 1 (nfix i)) p))
  :enable nthcdr)

(defrule hkec-sponge-aux-is-absorb
  (implies (and (natp i)
                (natp r) (<= r 1600)
                (bit-listp s)
                (equal (len s) 1600)
                (hkec-blocks-ok p r))
           (equal (sha3::keccak-sponge-aux 1600 24 r i (+ -1 (len p)) s p (- 1600 r))
                  (hkec-absorb s (nthcdr i p))))
  :induct (sha3::keccak-sponge-aux 1600 24 r i (+ -1 (len p)) s p (- 1600 r))
  :enable hkec-absorb
  :expand ((hkec-absorb s (nthcdr i p)))
  :prep-lemmas
  ((defrule hkec-blocks-ok-nth
     (implies (and (hkec-blocks-ok p r)
                   (< (nfix i) (len p)))
              (and (bit-listp (nth i p))
                   (equal (len (nth i p)) r)))
     :induct (nth i p)
     :in-theory (e/d (nth) (acl2::nth-of-cdr)))))

(defrule hkec-sponge-aux2-is-take
  (implies (and (posp r) (natp d) (<= d r) (<= r (len s)))
           (equal (sha3::keccak-sponge-aux2 1600 24 r nil s d)
                  (take d (take r s))))
  :enable sha3::keccak-sponge-aux2)


;; The sponge of kestrel's KECCAK.

(defrule hkec-blocks-ok-of-group
  (implies (and (posp r)
                (bit-listp p)
                (equal (mod (len p) r) 0))
           (hkec-blocks-ok (acl2::group r p) r))
  :induct (acl2::group r p)
  :enable acl2::group
  :prep-lemmas
  ((defrule hkec-bit-listp-of-nthcdr
     (implies (bit-listp p)
              (bit-listp (nthcdr n p)))
     :enable nthcdr)
   (defrule hkec-bit-listp-of-take
     (implies (and (bit-listp p)
                   (<= (nfix n) (len p)))
              (bit-listp (take n p)))
     :enable take)))

(defruled hkec-sponge-aux-is-absorb-gen
  (implies (and (equal nm1 (+ -1 (len p)))
                (natp r) (<= r 1600)
                (bit-listp s)
                (equal (len s) 1600)
                (hkec-blocks-ok p r))
           (equal (sha3::keccak-sponge-aux 1600 24 r 0 nm1 s p (- 1600 r))
                  (hkec-absorb s p)))
  :use ((:instance hkec-sponge-aux-is-absorb (i 0))))

(defrule hkec-bit-listp-of-repeat-0
  (bit-listp (acl2::repeat n 0))
  :enable acl2::repeat)

(defrule hkec-bit-listp-of-pad10*1
  (bit-listp (sha3::pad10*1 x m))
  :enable sha3::pad10*1)

(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))

(defruled hkec-sponge-of-padded
  (implies (and (posp r) (< r 1600)
                (natp d) (<= d r)
                (bit-listp pp)
                (equal (mod (len pp) r) 0))
           (equal (sha3::keccak-sponge-aux2
                   1600 24 r nil
                   (sha3::keccak-sponge-aux 1600 24 r 0 (- (/ (len pp) r) 1)
                                            (acl2::repeat 1600 0) (acl2::group r pp) (- 1600 r))
                   d)
                  (take d (take r (hkec-absorb (acl2::repeat 1600 0) (acl2::group r pp))))))
  :use ((:instance hkec-sponge-aux-is-absorb-gen
         (s (acl2::repeat 1600 0))
         (p (acl2::group r pp))
         (nm1 (- (/ (len pp) r) 1)))
        (:instance acl2::len-of-group (acl2::n r) (acl2::list pp))
        (:instance hkec-len-of-absorb (s (acl2::repeat 1600 0)) (blocks (acl2::group r pp))))
  :in-theory (e/d (acl2::equal-of-0-and-mod) (acl2::len-of-group hkec-len-of-absorb (:e acl2::repeat)))
  :prep-lemmas
  ((defrule hkec-len-of-absorb
     (implies (and (bit-listp s)
                   (equal (len s) 1600)
                   (hkec-blocks-ok blocks r)
                   (<= r 1600))
              (and (equal (len (hkec-absorb s blocks)) 1600)
                   (bit-listp (hkec-absorb s blocks))))
     :induct (hkec-absorb s blocks)
     :enable hkec-absorb)))

(defrule hkec-bit-listp-of-append-pad10*1
  (implies (bit-listp n)
           (bit-listp (append n (sha3::pad10*1 r m)))))

(defrule hkec-mod-len-of-append-pad10*1
  (implies (and (posp r) (natp m) (equal m (len n)))
           (equal (mod (len (append n (sha3::pad10*1 r m))) r) 0))
  :use ((:instance sha3::pad10*1-correct-1 (sha3::x r) (sha3::m m))))


(defruled hkec-natp-of-len (natp (len x)))

(defrule hkec-keccak-is-absorb
  (implies (and (posp (- 1600 c)) (< (- 1600 c) 1600)
                (natp d) (<= d (- 1600 c))
                (bit-listp n))
           (equal (sha3::keccak c n d)
                  (take d (take (- 1600 c)
                                (hkec-absorb (acl2::repeat 1600 0)
                                             (acl2::group (- 1600 c)
                                                          (append n (sha3::pad10*1 (- 1600 c) (len n)))))))))
  :use ((:instance hkec-sponge-of-padded
         (r (- 1600 c))
         (pp (append n (sha3::pad10*1 (- 1600 c) (len n)))))
        (:instance hkec-mod-len-of-append-pad10*1 (r (- 1600 c)) (m (len n)))
        (:instance hkec-natp-of-len (x n)))
  :in-theory '(sha3::keccak sha3::keccak-sponge hkec-bit-listp-of-append-pad10*1
                            (:t len) natp (:e posp) hkec-natp-of-len))

(defrule hkec-mod-len-byte-pad
  (equal (mod (len (hkec-byte-pad bits)) 8) 0)
  :enable (hkec-byte-pad acl2::mod-sum-cases))

(defrule hkec-mod-sha3-shift
  (implies (and (integerp l) (equal (mod l 8) 0)
                (posp r) (equal (mod r 8) 0))
           (equal (mod (+ -4 (- l)) r)
                  (+ 1 (mod (+ -5 (- l)) r))))
  :use ((:instance acl2::mod-sum-cases (acl2::k -1) (acl2::x (+ -4 (- l))) (acl2::y r))
        (:instance acl2::mod-of-mod-when-multiple (acl2::x (+ -4 (- l))) (acl2::y1 r) (acl2::y2 8))
        (:instance acl2::mod-sum-cases (acl2::k -4) (acl2::x (- l)) (acl2::y 8)))
  :disable (acl2::mod-of-mod-when-multiple))

(defrule hkec-mod-keccak-shift
  (implies (and (integerp l) (posp r))
           (equal (mod (- (- r 1) (+ l 1)) r)
                  (mod (+ -2 (- l)) r)))
  :use ((:instance acl2::mod-of-+-same-arg1 (acl2::x (+ -2 (- l))) (acl2::y r)))
  :disable acl2::mod-of-+-same-arg1)

(defruled hkec-mod-sha3-shift2
  (implies (and (integerp l) (equal (mod l 8) 0)
                (posp r) (equal (mod r 8) 0))
           (equal (mod (- (- r 1) (+ l 4)) r)
                  (+ -1 (mod (+ -2 (- (+ 2 l))) r))))
  :use ((:instance hkec-mod-sha3-shift)
        (:instance acl2::mod-of-+-same-arg1 (acl2::x (+ -5 (- l))) (acl2::y r)))
  :disable (acl2::mod-of-+-same-arg1 hkec-mod-sha3-shift))

(defrule hkec-pad-keccak-is-pad10*1
  (implies (posp r)
           (equal (hkec-pad-keccak input r)
                  (acl2::group r (append (hkec-byte-pad input)
                                         (sha3::pad10*1 r (len (hkec-byte-pad input)))))))
  :in-theory '(hkec-pad-keccak hkec-pos sha3::pad10*1 hkec-mod-keccak-shift
               (:t len) posp natp integerp acl2::associativity-of-append))

(defruled hkec-mod-sha3-shift3
  (implies (and (integerp l) (equal (mod l 8) 0)
                (posp r) (equal (mod r 8) 0))
           (equal (mod (+ -2 (- (+ 2 l))) r)
                  (+ 1 (mod (- (- r 1) (+ l 4)) r))))
  :use hkec-mod-sha3-shift2)

(defruled hkec-repeat-1+
  (implies (natp k)
           (equal (acl2::repeat (+ 1 k) x) (cons x (acl2::repeat k x))))
  :enable acl2::repeat)

(defrule hkec-pad-sha3-is-pad10*1
  (implies (and (posp r) (equal (mod r 8) 0))
           (equal (hkec-pad-sha3 input r)
                  (acl2::group r (append (append (hkec-byte-pad input) '(0 1))
                                         (sha3::pad10*1 r (len (append (hkec-byte-pad input) '(0 1))))))))
  :use ((:instance hkec-mod-sha3-shift3 (l (len (hkec-byte-pad input))))
        (:instance hkec-repeat-1+ (x 0) (k (mod (- (- r 1) (+ (len (hkec-byte-pad input)) 4)) r))))
  :in-theory '(hkec-pad-sha3 hkec-pos sha3::pad10*1 hkec-mod-len-byte-pad
               (:t len) posp natp acl2::associativity-of-append acl2::len-of-append
               (:e len) (:t mod) acl2::nonneg-of-mod-type-2 acl2::integerp-of-mod-type
               car-cons cdr-cons binary-append (:e binary-append) commutativity-of-+))

(defruled hkec-variant-cases
  (implies (hkec-variant-p variant)
           (or (equal variant '(0 . 224)) (equal variant '(0 . 256))
               (equal variant '(0 . 384)) (equal variant '(0 . 512))
               (equal variant '(1 . 224)) (equal variant '(1 . 256))
               (equal variant '(1 . 384)) (equal variant '(1 . 512))))
  :enable hkec-variant-p)

(defrule hkec-bit-listp-of-byte-pad
  (implies (bit-listp bits)
           (bit-listp (hkec-byte-pad bits)))
  :enable hkec-byte-pad)

(defrule hkec-bit-listp-of-true-list-fix
  (implies (bit-listp x) (bit-listp (true-list-fix x)))
  :induct (true-list-fix x)
  :enable (bit-listp true-list-fix))

(defruled hkec-sponge-is-keccak-family-hash-generic
  (implies (and (hkec-variant-p variant)
                (bit-listp input))
           (equal (hkec-sponge variant input)
                  (hkec-keccak-family-hash variant input)))
  :use ((:instance hkec-variant-cases)
        (:instance hkec-keccak-is-absorb
                   (c (* 2 (hkec-variant-bits variant)))
                   (d (hkec-variant-bits variant))
                   (n (hkec-byte-pad input)))
        (:instance hkec-keccak-is-absorb
                   (c (* 2 (hkec-variant-bits variant)))
                   (d (hkec-variant-bits variant))
                   (n (append (hkec-byte-pad input) '(0 1)))))
  :in-theory '(hkec-sponge hkec-keccak-family-hash hkec-pad-keccak-is-pad10*1
               hkec-pad-sha3-is-pad10*1 hkec-bit-listp-of-byte-pad
               (:e hkec-variant-p) (:e hkec-variant-bits) (:e hkec-variant-type)
               (:e hkec-bitrate) (:e posp) (:e natp) (:e mod) (:e <) (:e binary-*)
               (:e unary--) (:e binary-+) (:e equal) (:e cdr) (:e car)
               acl2::bit-listp-of-append (:e bit-listp) hkec-bit-listp-of-true-list-fix))

(defrule hkec-sponge-is-keccak-family-hash
  (implies (and (hkec-variant-p variant)
                (bit-listp input))
           (equal (hkec-sponge variant input)
                  (hkec-keccak-family-hash variant input)))
  :use hkec-sponge-is-keccak-family-hash-generic)

