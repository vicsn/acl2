; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keccak::pad_keccak, Keccak::pad_sha3 and Keccak::hash of
; circuit/algorithms/src/keccak/hash.rs.
;
; Padding appends constant Boolean wires and chunks the result, so it adds no
; constraints: the gadget is the spec function applied to wires.  The sponge
; starts from 1600 constant false wires, xors each block into a prefix of the
; state (constant xors fold) and applies permutation_f; the bitrate is at
; least VARIANT, so the output is a prefix of the state after absorbing.
;
; Completeness: from the empty constraint list the generated list is well
; formed, so HKEC-SOLVE extends any assignment of the input wires to one that
; satisfies every constraint, without changing the input values.

(in-package "ALEOVM")

(include-book "hkec-perm")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Solving keeps the values of the input wires.

(defrule hkec-dot-product-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-lc-old-p lc 0))
           (equal (r1cs::dot-product lc (hkec-solve cs asg p) p)
                  (r1cs::dot-product lc asg p)))
  :induct (hkec-solve cs asg p)
  :hints (("Subgoal *1/2" :use ((:instance hkec-lc-old-p-mono
                                 (lc lc) (n 0) (m (len (cdr cs)))))
                  :in-theory (disable hkec-lc-old-p-mono))))

(defrule hkec-eval-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-term-ok x 0))
           (equal (hkec-eval x (hkec-solve cs asg p) p)
                  (hkec-eval x asg p)))
  :enable (hkec-eval hkec-term-ok))

(defrule hkec-eval-list-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-terms-ok xs 0))
           (equal (hkec-eval-list xs (hkec-solve cs asg p) p)
                  (hkec-eval-list xs asg p))))

(defrule hkec-wires-p-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-terms-ok xs 0))
           (equal (hkec-wires-p xs (hkec-solve cs asg p) p)
                  (hkec-wires-p xs asg p)))
  :enable (hkec-wire-p hkec-term-ok))

(defrule hkec-eval-lanes-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-lanes-ok ls 0))
           (equal (hkec-eval-lanes ls (hkec-solve cs asg p) p)
                  (hkec-eval-lanes ls asg p))))

(defrule hkec-lanes-wires-p-of-solve
  (implies (and (hkec-wf cs p)
                (hkec-lanes-ok ls 0))
           (equal (hkec-lanes-wires-p ls (hkec-solve cs asg p) p)
                  (hkec-lanes-wires-p ls asg p))))

(defrule hkec-terms-ok-of-repeat-0-early
  (hkec-terms-ok (acl2::repeat k 0) n)
  :enable acl2::repeat)

(defrule hkec-wf-of-nil
  (hkec-wf nil p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness of Keccak::round and Keccak::permutation_f.

(defrule hkec-g-round-complete
  (implies (and (primep p)
                (hkec-lanes-ok a 0)
                (hkec-lanes-len a 64)
                (equal (len a) 25)
                (bit-listp rc)
                (equal (len rc) 64)
                (hkec-lanes-wires-p a asg p))
           (b* (((mv out cs) (hkec-g-round a rc nil p))
                (asg2 (hkec-solve cs asg p)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-lanes a asg2 p)
                         (hkec-eval-lanes a asg p))
                  (equal (hkec-eval-lanes out asg2 p)
                         (hkec-round (hkec-eval-lanes a asg p) rc)))))
  :use ((:instance hkec-g-round-sound
         (cs nil)
         (asg (hkec-solve (mv-nth 1 (hkec-g-round a rc nil p)) asg p))))
  :disable hkec-g-round-sound)

(defrule hkec-g-permutation-f-complete
  (implies (and (primep p)
                (hkec-terms-ok s 0)
                (equal (len s) 1600)
                (hkec-wires-p s asg p))
           (b* (((mv out cs) (hkec-g-permutation-f s nil p))
                (asg2 (hkec-solve cs asg p)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-list s asg2 p)
                         (hkec-eval-list s asg p))
                  (equal (hkec-eval-list out asg2 p)
                         (hkec-permutation-f (hkec-eval-list s asg p))))))
  :use ((:instance hkec-g-permutation-f-sound
         (cs nil)
         (asg (hkec-solve (mv-nth 1 (hkec-g-permutation-f s nil p)) asg p))))
  :disable hkec-g-permutation-f-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Padding on wires (no constraints).

;; The padded bit strings, kept closed so that group rules never see appends.

(defund hkec-pad-keccak-bits (input r)
  (b* ((m (hkec-byte-pad input)))
    (append m
            '(1)
            (acl2::repeat (mod (- (- (hkec-pos r) 1) (+ (len m) 1)) (hkec-pos r)) 0)
            '(1))))

(defund hkec-pad-sha3-bits (input r)
  (b* ((m (hkec-byte-pad input)))
    (append m
            '(0 1 1 0)
            (acl2::repeat (mod (- (- (hkec-pos r) 1) (+ (len m) 4)) (hkec-pos r)) 0)
            '(1))))

(defruled hkec-pad-keccak-as-group
  (equal (hkec-pad-keccak input r)
         (acl2::group (hkec-pos r) (hkec-pad-keccak-bits input r)))
  :enable (hkec-pad-keccak hkec-pad-keccak-bits))

(defruled hkec-pad-sha3-as-group
  (equal (hkec-pad-sha3 input r)
         (acl2::group (hkec-pos r) (hkec-pad-sha3-bits input r)))
  :enable (hkec-pad-sha3 hkec-pad-sha3-bits))

(defrule hkec-terms-ok-of-repeat-0
  (hkec-terms-ok (acl2::repeat k 0) n)
  :enable acl2::repeat)

(defrule hkec-wires-p-of-repeat-0
  (hkec-wires-p (acl2::repeat k 0) asg p)
  :enable acl2::repeat)

(defrule hkec-eval-list-of-repeat-0
  (equal (hkec-eval-list (acl2::repeat k 0) asg p)
         (acl2::repeat k 0))
  :enable acl2::repeat)

(defruledl hkec-pad-len-mod
  (implies (and (posp r) (integerp x))
           (equal (mod (+ x (mod (- r x) r)) r)
                  0)))

(defrule hkec-pad-keccak-bits-props
  (and (implies (hkec-terms-ok input n)
                (hkec-terms-ok (hkec-pad-keccak-bits input r) n))
       (implies (hkec-wires-p input asg p)
                (hkec-wires-p (hkec-pad-keccak-bits input r) asg p))
       (equal (hkec-eval-list (hkec-pad-keccak-bits input r) asg p)
              (hkec-pad-keccak-bits (hkec-eval-list input asg p) r))
       (implies (posp r)
                (equal (mod (len (hkec-pad-keccak-bits input r)) r) 0)))
  :enable (hkec-pad-keccak-bits hkec-byte-pad)
  :use ((:instance hkec-pad-len-mod
         (x (+ 2 (len (hkec-byte-pad input)))))))

(defrule hkec-pad-sha3-bits-props
  (and (implies (hkec-terms-ok input n)
                (hkec-terms-ok (hkec-pad-sha3-bits input r) n))
       (implies (hkec-wires-p input asg p)
                (hkec-wires-p (hkec-pad-sha3-bits input r) asg p))
       (equal (hkec-eval-list (hkec-pad-sha3-bits input r) asg p)
              (hkec-pad-sha3-bits (hkec-eval-list input asg p) r))
       (implies (posp r)
                (equal (mod (len (hkec-pad-sha3-bits input r)) r) 0)))
  :enable (hkec-pad-sha3-bits hkec-byte-pad)
  :use ((:instance hkec-pad-len-mod
         (x (+ 5 (len (hkec-byte-pad input)))))))

(defrule hkec-pad-keccak-wires
  (and (implies (posp r)
                (hkec-lanes-len (hkec-pad-keccak input r) r))
       (implies (hkec-terms-ok input n)
                (hkec-lanes-ok (hkec-pad-keccak input r) n))
       (implies (hkec-wires-p input asg p)
                (hkec-lanes-wires-p (hkec-pad-keccak input r) asg p))
       (equal (hkec-eval-lanes (hkec-pad-keccak input r) asg p)
              (hkec-pad-keccak (hkec-eval-list input asg p) r)))
  :enable (hkec-pad-keccak-as-group hkec-pos))

(defrule hkec-pad-sha3-wires
  (and (implies (posp r)
                (hkec-lanes-len (hkec-pad-sha3 input r) r))
       (implies (hkec-terms-ok input n)
                (hkec-lanes-ok (hkec-pad-sha3 input r) n))
       (implies (hkec-wires-p input asg p)
                (hkec-lanes-wires-p (hkec-pad-sha3 input r) asg p))
       (equal (hkec-eval-lanes (hkec-pad-sha3 input r) asg p)
              (hkec-pad-sha3 (hkec-eval-list input asg p) r)))
  :enable (hkec-pad-sha3-as-group hkec-pos))

;;;;;;;;

;; Xoring a block into a prefix of the state.

(defun hkec-g-xor-prefix (s block cs p)
  (if (endp block)
      (mv s cs)
    (b* (((mv o cs) (hkec-xor (car s) (car block) cs p))
         ((mv os cs) (hkec-g-xor-prefix (cdr s) (cdr block) cs p)))
      (mv (cons o os) cs))))

(defrule hkec-g-xor-prefix-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-xor-prefix s block cs p)) old)))

(defrule hkec-g-xor-prefix-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-xor-prefix s block cs p))))
  :rule-classes :linear)

(defrule len-of-hkec-g-xor-prefix
  (implies (<= (len block) (len s))
           (equal (len (mv-nth 0 (hkec-g-xor-prefix s block cs p)))
                  (len s))))

(defrule hkec-g-xor-prefix-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-terms-ok s (len cs))
                (hkec-terms-ok block (len cs))
                (<= (len block) (len s)))
           (hkec-wf (mv-nth 1 (hkec-g-xor-prefix s block cs p)) p)))

(defrule hkec-g-xor-prefix-ok
  (implies (and (hkec-terms-ok s (len cs))
                (hkec-terms-ok block (len cs))
                (<= (len block) (len s))
                (natp m)
                (<= (len (mv-nth 1 (hkec-g-xor-prefix s block cs p))) m))
           (hkec-terms-ok (mv-nth 0 (hkec-g-xor-prefix s block cs p)) m))
  :induct (hkec-g-xor-prefix s block cs p))

(defrule hkec-g-xor-prefix-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-xor-prefix s block cs p)) asg p)
                (hkec-wires-p s asg p)
                (hkec-wires-p block asg p)
                (<= (len block) (len s)))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-xor-prefix s block cs p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-xor-prefix s block cs p)) asg p)
                       (hkec-xor-prefix (hkec-eval-list s asg p)
                                        (hkec-eval-list block asg p)))))
  :induct (hkec-g-xor-prefix s block cs p)
  :hints (("Subgoal *1/2" :use ((:instance hkec-xor-sound
                                 (a (car s)) (b (car block)))))))

(in-theory (disable hkec-g-xor-prefix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Absorbing the blocks.

(defun hkec-g-absorb (s blocks cs p)
  (if (endp blocks)
      (mv s cs)
    (b* (((mv s cs) (hkec-g-xor-prefix s (car blocks) cs p))
         ((mv s cs) (hkec-g-permutation-f s cs p)))
      (hkec-g-absorb s (cdr blocks) cs p))))

(defrule hkec-g-absorb-ext
  (implies (hkec-ext cs old)
           (hkec-ext (mv-nth 1 (hkec-g-absorb s blocks cs p)) old)))

(defrule hkec-g-absorb-len-mono
  (<= (len cs) (len (mv-nth 1 (hkec-g-absorb s blocks cs p))))
  :rule-classes :linear)

(defrule hkec-g-absorb-wf
  (implies (and (primep p)
                (hkec-wf cs p)
                (hkec-terms-ok s (len cs))
                (hkec-lanes-ok blocks (len cs))
                (equal (len s) 1600)
                (hkec-lanes-len blocks r)
                (<= r 1600))
           (hkec-wf (mv-nth 1 (hkec-g-absorb s blocks cs p)) p))
  :hints (("Goal" :induct (hkec-g-absorb s blocks cs p))
          ("Subgoal *1/2"
           :use ((:instance hkec-g-xor-prefix-ok
                  (block (car blocks))
                  (m (len (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p)))))
                 (:instance hkec-g-permutation-f-ok
                  (s (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p)))
                  (cs (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p)))
                  (m (len (mv-nth 1 (hkec-g-permutation-f
                                     (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                     (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                     p)))))
                 (:instance hkec-lanes-ok-mono
                  (ls (cdr blocks)) (n (len cs))
                  (m (len (mv-nth 1 (hkec-g-permutation-f
                                     (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                     (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                     p)))))))))

(defrule hkec-g-absorb-sound
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-absorb s blocks cs p)) asg p)
                (hkec-wires-p s asg p)
                (hkec-lanes-wires-p blocks asg p)
                (equal (len s) 1600)
                (hkec-lanes-len blocks r)
                (<= r 1600))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-absorb s blocks cs p)) asg p)
                (equal (len (mv-nth 0 (hkec-g-absorb s blocks cs p))) 1600)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-absorb s blocks cs p)) asg p)
                       (hkec-absorb (hkec-eval-list s asg p)
                                    (hkec-eval-lanes blocks asg p)))))
  :hints (("Goal" :induct (hkec-g-absorb s blocks cs p)
                  :in-theory (enable hkec-absorb))
          ("Subgoal *1/2"
           :use ((:instance hkec-holdp-when-ext
                  (new (mv-nth 1 (hkec-g-absorb
                                  (mv-nth 0 (hkec-g-permutation-f
                                             (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                             (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                             p))
                                  (cdr blocks)
                                  (mv-nth 1 (hkec-g-permutation-f
                                             (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                             (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                             p))
                                  p)))
                  (old (mv-nth 1 (hkec-g-permutation-f
                                  (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                  (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                  p))))
                 (:instance hkec-holdp-when-ext
                  (new (mv-nth 1 (hkec-g-permutation-f
                                  (mv-nth 0 (hkec-g-xor-prefix s (car blocks) cs p))
                                  (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))
                                  p)))
                  (old (mv-nth 1 (hkec-g-xor-prefix s (car blocks) cs p))))))))

(in-theory (disable hkec-g-absorb))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keccak<TYPE, VARIANT>::hash.

(defun hkec-g-pad (variant input)
  (b* ((r (hkec-bitrate (hkec-variant-bits variant))))
    (if (equal (hkec-variant-type variant) 0)
        (hkec-pad-keccak input r)
      (hkec-pad-sha3 input r))))

(defun hkec-g-hash (variant input p)
  (b* ((d (hkec-variant-bits variant))
       (r (hkec-bitrate d))
       ((mv s cs) (hkec-g-absorb (acl2::repeat 1600 0) (hkec-g-pad variant input) nil p)))
    (mv (take d (take r s)) cs)))

(defrule hkec-variant-bitrate
  (implies (hkec-variant-p variant)
           (and (< 0 (hkec-bitrate (hkec-variant-bits variant)))
                (<= (hkec-bitrate (hkec-variant-bits variant)) 1600)
                (< 0 (hkec-variant-bits variant))
                (<= (hkec-variant-bits variant)
                    (hkec-bitrate (hkec-variant-bits variant)))))
  :rule-classes (:rewrite :linear)
  :enable (hkec-variant-p hkec-variant-bits hkec-bitrate))

(defruledl hkec-g-pad-props
  (implies (hkec-variant-p variant)
           (and (hkec-lanes-len (hkec-g-pad variant input)
                                (hkec-bitrate (hkec-variant-bits variant)))
                (implies (hkec-terms-ok input n)
                         (hkec-lanes-ok (hkec-g-pad variant input) n))
                (implies (hkec-wires-p input asg p)
                         (hkec-lanes-wires-p (hkec-g-pad variant input) asg p))
                (equal (hkec-eval-lanes (hkec-g-pad variant input) asg p)
                       (hkec-g-pad variant (hkec-eval-list input asg p)))))
  :use hkec-variant-bitrate)

(defruledl hkec-sponge-as-g-pad
  (equal (hkec-sponge variant input)
         (if (hkec-variant-p variant)
             (take (hkec-variant-bits variant)
                   (take (hkec-bitrate (hkec-variant-bits variant))
                         (hkec-absorb (acl2::repeat 1600 0)
                                      (hkec-g-pad variant input))))
           nil))
  :enable hkec-sponge)

(defrule hkec-g-hash-sound
  (implies (and (primep p)
                (hkec-variant-p variant)
                (r1cs::r1cs-constraints-holdp (mv-nth 1 (hkec-g-hash variant input p)) asg p)
                (hkec-wires-p input asg p))
           (and (hkec-wires-p (mv-nth 0 (hkec-g-hash variant input p)) asg p)
                (equal (hkec-eval-list (mv-nth 0 (hkec-g-hash variant input p)) asg p)
                       (hkec-sponge variant (hkec-eval-list input asg p)))))
  :enable hkec-sponge-as-g-pad
  :do-not-induct t
  :disable (hkec-g-pad (:e acl2::repeat) hkec-g-absorb-sound)
  :use (hkec-variant-bitrate
        (:instance hkec-g-pad-props (n 0))
        (:instance hkec-g-absorb-sound
         (s (acl2::repeat 1600 0))
         (blocks (hkec-g-pad variant input))
         (cs nil)
         (r (hkec-bitrate (hkec-variant-bits variant))))))

(defrule hkec-g-hash-wf
  (implies (and (primep p)
                (hkec-variant-p variant)
                (hkec-terms-ok input 0))
           (hkec-wf (mv-nth 1 (hkec-g-hash variant input p)) p))
  :do-not-induct t
  :disable (hkec-g-pad (:e acl2::repeat) hkec-g-absorb-wf)
  :use (hkec-variant-bitrate
        (:instance hkec-g-pad-props (n 0))
        (:instance hkec-g-absorb-wf
         (s (acl2::repeat 1600 0))
         (blocks (hkec-g-pad variant input))
         (cs nil)
         (r (hkec-bitrate (hkec-variant-bits variant))))))

(defrule hkec-g-hash-complete
  (implies (and (primep p)
                (hkec-variant-p variant)
                (hkec-terms-ok input 0)
                (hkec-wires-p input asg p))
           (b* (((mv out cs) (hkec-g-hash variant input p))
                (asg2 (hkec-solve cs asg p)))
             (and (r1cs::r1cs-constraints-holdp cs asg2 p)
                  (equal (hkec-eval-list input asg2 p)
                         (hkec-eval-list input asg p))
                  (equal (hkec-eval-list out asg2 p)
                         (hkec-sponge variant (hkec-eval-list input asg p))))))
  :use ((:instance hkec-g-hash-sound
         (asg (hkec-solve (mv-nth 1 (hkec-g-hash variant input p)) asg p))))
  :disable (hkec-g-hash-sound hkec-g-hash))

(in-theory (disable hkec-g-hash hkec-g-pad))
