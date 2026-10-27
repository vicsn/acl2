; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keccak::permutation_f of circuit/algorithms/src/keccak/hash.rs: the state
; bits are chunked into 25 U64 lanes (no constraints), 24 rounds are applied
; (hkec-round.lisp), and the lanes are written back as bits (no constraints).
; The fold is proved by induction over the list of round constants, so no
; state is ever expanded.

(in-package "ALEOVM")

(include-book "hkec-round")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constant wires.

(defrule hkec-terms-ok-when-bit-listp
  (implies (bit-listp xs)
           (hkec-terms-ok xs n)))

(defrule hkec-wires-p-when-bit-listp
  (implies (bit-listp xs)
           (hkec-wires-p xs asg p)))

(defrule hkec-eval-list-when-bit-listp
  (implies (bit-listp xs)
           (equal (hkec-eval-list xs asg p)
                  (true-list-fix xs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Chunking into lanes and writing back.

(defrule hkec-terms-ok-of-firstn
  (implies (hkec-terms-ok xs n)
           (hkec-terms-ok (acl2::firstn k xs) n))
  :enable acl2::firstn)

(defrule hkec-wires-p-of-firstn
  (implies (hkec-wires-p xs asg p)
           (hkec-wires-p (acl2::firstn k xs) asg p))
  :enable acl2::firstn)

(defrule hkec-eval-list-of-firstn
  (equal (hkec-eval-list (acl2::firstn k xs) asg p)
         (acl2::firstn k (hkec-eval-list xs asg p)))
  :enable acl2::firstn)

(defrule hkec-lanes-ok-of-group
  (implies (hkec-terms-ok xs n)
           (hkec-lanes-ok (acl2::group k xs) n))
  :enable acl2::group)

(defrule hkec-lanes-wires-p-of-group
  (implies (hkec-wires-p xs asg p)
           (hkec-lanes-wires-p (acl2::group k xs) asg p))
  :enable acl2::group)

(defrule hkec-eval-lanes-of-group
  (equal (hkec-eval-lanes (acl2::group k xs) asg p)
         (acl2::group k (hkec-eval-list xs asg p)))
  :enable acl2::group)

(defrule hkec-lanes-len-of-group
  (implies (and (posp k)
                (equal (mod (len xs) k) 0))
           (hkec-lanes-len (acl2::group k xs) k))
  :enable acl2::group)

(defrule hkec-len-of-group-1600
  (implies (equal (len xs) 1600)
           (equal (len (acl2::group 64 xs)) 25))
  :use (:instance acl2::len-of-group (acl2::n 64) (acl2::list xs)))

(defrule hkec-terms-ok-of-flatten
  (implies (hkec-lanes-ok ls n)
           (hkec-terms-ok (hkec-flatten ls) n)))

(defrule hkec-wires-p-of-flatten
  (implies (hkec-lanes-wires-p ls asg p)
           (hkec-wires-p (hkec-flatten ls) asg p)))

(defrule hkec-eval-list-of-flatten
  (equal (hkec-eval-list (hkec-flatten ls) asg p)
         (hkec-flatten (hkec-eval-lanes ls asg p))))

(defrule hkec-len-of-flatten
  (implies (hkec-lanes-len ls k)
           (equal (len (hkec-flatten ls))
                  (* k (len ls)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The 24-round fold, over any list of constant round constant lanes.

(defun hkec-rcs-p (rcs)
  (if (atom rcs)
      t
    (and (bit-listp (car rcs))
         (equal (len (car rcs)) 64)
         (hkec-rcs-p (cdr rcs)))))

(defrule hkec-rcs-p-of-round-constant-bits
  (hkec-rcs-p *hkec-round-constant-bits*))

(defun hkec-g-rounds (a rcs cs p)
  (if (atom rcs)
      (mv a cs)
    (b* (((mv a cs) (hkec-g-round a (car rcs) cs p)))
      (hkec-g-rounds a (cdr rcs) cs p))))

(defrule hkec-g-rounds-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-rounds a rcs cs p)) old)))

(defrule hkec-g-rounds-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-rounds a rcs cs p))))
  :rule-classes :linear)

(defrule hkec-g-rounds-shape
  (implies (and (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-rcs-p rcs))
           (and (hkec-lanes-len (mv-nth 0 (hkec-g-rounds a rcs cs p)) 64)
                (equal (len (mv-nth 0 (hkec-g-rounds a rcs cs p))) 25))))

(defrule hkec-g-rounds-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-rcs-p rcs))
           (hkec-wf (mv-nth 1 (hkec-g-rounds a rcs cs p)) p))
  :hints (("Goal" :induct (hkec-g-rounds a rcs cs p))
          ("Subgoal *1/2" :use ((:instance hkec-g-round-ok
                                 (rc (car rcs))
                                 (m (len (mv-nth 1 (hkec-g-round a (car rcs) cs p)))))))))

(defrule hkec-g-rounds-ok
  (implies (and (hkec-lanes-ok a (len cs))
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-rcs-p rcs)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-rounds a rcs cs p))) m))
           (hkec-lanes-ok (mv-nth 0 (hkec-g-rounds a rcs cs p)) m))
  :hints (("Goal" :induct (hkec-g-rounds a rcs cs p))
          ("Subgoal *1/2" :use ((:instance hkec-g-round-ok
                                 (rc (car rcs))
                                 (m (len (mv-nth 1 (hkec-g-round a (car rcs) cs p)))))))
          ("Subgoal *1/1" :use ((:instance hkec-lanes-ok-mono
                                 (ls a) (n (len cs)))))))

(defrule hkec-g-rounds-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-rounds a rcs cs p)) asg p)
                (hkec-lanes-wires-p a asg p)
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (hkec-rcs-p rcs))
           (and (hkec-lanes-wires-p (mv-nth 0 (hkec-g-rounds a rcs cs p)) asg p)
                (equal (hkec-eval-lanes (mv-nth 0 (hkec-g-rounds a rcs cs p)) asg p)
                       (hkec-rounds (hkec-eval-lanes a asg p) rcs))))
  :hints (("Goal" :induct (hkec-g-rounds a rcs cs p)
                  :in-theory (enable hkec-rounds))
          ("Subgoal *1/2" :use ((:instance hkec-holdp-when-ext
                                 (new (mv-nth 1 (hkec-g-rounds
                                                 (mv-nth 0 (hkec-g-round a (car rcs) cs p))
                                                 (cdr rcs)
                                                 (mv-nth 1 (hkec-g-round a (car rcs) cs p))
                                                 p)))
                                 (old (mv-nth 1 (hkec-g-round a (car rcs) cs p))))))))

(in-theory (disable hkec-g-rounds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keccak::permutation_f on 1600 state wires.

(defun hkec-g-permutation-f (s cs p)
  (b* (((mv a cs) (hkec-g-rounds (acl2::group 64 s) *hkec-round-constant-bits* cs p)))
    (mv (hkec-flatten a) cs)))

(defrule hkec-g-permutation-f-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-permutation-f s cs p)) old)))

(defrule hkec-g-permutation-f-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-permutation-f s cs p))))
  :rule-classes :linear)

(defrule hkec-g-permutation-f-shape
  (implies (equal (len s) 1600)
           (equal (len (mv-nth 0 (hkec-g-permutation-f s cs p))) 1600))
  :use (:instance hkec-g-rounds-shape
        (a (acl2::group 64 s)) (rcs *hkec-round-constant-bits*))
  :disable hkec-g-rounds-shape)

(defrule hkec-g-permutation-f-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-terms-ok s (len cs))
                (equal (len s) 1600))
           (hkec-wf (mv-nth 1 (hkec-g-permutation-f s cs p)) p)))

(defrule hkec-g-permutation-f-ok
  (implies (and (hkec-terms-ok s (len cs))
                (equal (len s) 1600)
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-permutation-f s cs p))) m))
           (hkec-terms-ok (mv-nth 0 (hkec-g-permutation-f s cs p)) m)))

(defrule hkec-g-permutation-f-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-permutation-f s cs p)) asg p)
                (hkec-wires-p s asg p)
                (equal (len s) 1600))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-permutation-f s cs p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-permutation-f s cs p)) asg p)
                       (hkec-permutation-f (hkec-eval-list s asg p)))))
  :enable hkec-permutation-f)

(in-theory (disable hkec-g-permutation-f))
