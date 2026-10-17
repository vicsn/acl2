; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Variable-mode signed shr_wrapped for every width other than 128.
;
; snarkVM starts from the big-endian weighing R of the value bits and, for
; each low exponent bit i, selects between cur and
;   cur * 2^(2^i) + (2^(2^i) - 1) * msb
; with Field::ternary.  The product and the mask are linear combinations,
; so each select is one constraint
;   (bit) * ((2^(2^i) - 1) * cur + (2^(2^i) - 1) * msb) = (next - cur)
; (for i = 0 the scale is 1 and cur is the big-endian combination).  The
; msb wire is the last value wire; snarkVM merges its two occurrences in
; the first linear combination, which has the same dot product as the two
; separate terms here.  Then Field::to_lower_bits_le(2n), and the low n
; bits reversed are the result.
;
; With c' = cur + msb each select is the plain shift step on c', so the
; final value is (R + msb) * 2^s - msb, s = e mod n, whose low n bits
; reversed are the arithmetic right shift of x.

(in-package "ALEOVM")

(include-book "int-divshift-shr-unsigned")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/last" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-divshift-sshr-var-step ((bit symbolp)
                                    (cur symbolp)
                                    (next symbolp)
                                    (m symbolp)
                                    (i natp)
                                    (p primep))
  :short "One masked select after the first."
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 bit))
         :b (list (list (int-shift-scale i) cur)
                  (list (int-shift-scale i) m))
         :c (list (list 1 next)
                  (list (- p 1) cur)))))

(define int-divshift-sshr-var-chain ((prev symbolp)
                                     (ebits symbol-listp)
                                     (nexts symbol-listp)
                                     (m symbolp)
                                     (i natp)
                                     (p primep))
  (if (or (endp ebits) (endp nexts))
      nil
    (append (int-divshift-sshr-var-step (car ebits) prev (car nexts) m i p)
            (int-divshift-sshr-var-chain (car nexts) (cdr ebits) (cdr nexts)
                                         m (+ 1 (nfix i)) p))))

(define int-divshift-sshr-first-step ((bit symbolp)
                                      (xs symbol-listp)
                                      (next symbolp)
                                      (m symbolp)
                                      (p primep))
  :short "First masked select; @('cur') is the big-endian combination."
  (b* ((vec (int-be-pow2sum-vector xs (nfix (1- (len xs))))))
    (list (r1cs::make-r1cs-constraint
           :a (list (list 1 bit))
           :b (append vec (list (list 1 m)))
           :c (append (list (list 1 next))
                      (vector-neg-prime vec p))))))

(define int-divshift-shr-signed-gadget ((xs symbol-listp)
                                        (ebits symbol-listp)
                                        (nexts symbol-listp)
                                        (zs symbol-listp)
                                        (p primep))
  :verify-guards nil
  :short "Signed @('shr_wrapped') for a width other than 128."
  (if (endp ebits)
      (int-shift-lower-gadget (car (last nexts)) zs p)
    (append (int-divshift-sshr-first-step (car ebits) xs (car nexts)
                                          (car (last xs)) p)
            (int-divshift-sshr-var-chain (car nexts) (cdr ebits) (cdr nexts)
                                         (car (last xs)) 1 p)
            (int-shift-lower-gadget (car (last nexts)) zs p))))

(define int-divshift-sub-each ((vals nat-listp) (m natp))
  :short "Subtract the sign bit from every running value."
  (if (endp vals)
      nil
    (cons (- (car vals) m) (int-divshift-sub-each (cdr vals) m))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl int-divshift-sshr-core-k
  (implies (and (integerp p)
                (< 1 p)
                (natp c)
                (< c p)
                (bitp b)
                (bitp mv)
                (natp next)
                (< next p)
                (posp k)
                (< (if (equal b 1) (* (+ c mv) k) (+ c mv)) p))
           (equal (equal (mod (* b (+ -1 k) (+ c mv)) p)
                         (mod (+ next (- c)) p))
                  (equal next (- (if (equal b 1) (* (+ c mv) k) (+ c mv))
                                 mv))))
  :do-not-induct t
  :cases ((and (equal b 1) (equal mv 1))
          (and (equal b 1) (equal mv 0))
          (and (equal b 0) (equal mv 1))
          (and (equal b 0) (equal mv 0)))
  :use ((:instance core-helper (d (* (+ -1 k) (+ c mv))))
        (:instance core-helper (d 0)))
  :in-theory (e/d (bitp acl2::distributivity) (mod))
  :prep-lemmas
  ((defruled core-helper
     (implies (and (integerp p) (< 1 p)
                   (natp c) (natp next) (natp d)
                   (< c p) (< next p) (< (+ c d) p))
              (equal (equal (mod d p) (mod (+ next (- c)) p))
                     (equal next (+ c d))))
     :cases ((<= c next))
     :enable (acl2::mod-when-< acl2::mod-of-+-of-constant-copy)
     :prep-lemmas
     ((defruled acl2::mod-of-+-of-constant-copy
        (implies (and (integerp x) (integerp p) (< 1 p)
                      (< x 0) (<= (- p) x))
                 (equal (mod x p) (+ x p)))
        :enable (mod acl2::floor-when-<-and-negative-copy)
        :prep-lemmas
        ((defrule acl2::floor-when-<-and-negative-copy
           (implies (and (integerp x) (integerp p) (< 1 p)
                         (< x 0) (<= (- p) x))
                    (equal (floor x p) -1))
           :enable acl2::floor-unique-equal-version-copy
           :prep-lemmas
           ((defruled acl2::floor-unique-equal-version-copy
              (implies (and (integerp x) (integerp p) (< 1 p)
                            (< x 0) (<= (- p) x))
                       (equal (floor x p) -1))
              :use (:instance acl2::floor-unique (i x) (j p) (n -1)))))))))))


(defruledl int-divshift-sshr-core
  (implies (and (integerp p)
                (< 1 p)
                (natp c)
                (< c p)
                (bitp b)
                (bitp mv)
                (natp next)
                (< next p)
                (natp i)
                (< (int-shift-after (+ c mv) b i) p))
           (equal (equal (mod (* b (int-shift-scale i) (+ c mv)) p)
                         (mod (+ next (- c)) p))
                  (equal next (- (int-shift-after (+ c mv) b i) mv))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-core-k (k (int-shift-pow i)))
        (:instance pow-pos))
  :in-theory (union-theories '(int-shift-after int-shift-scale nfix fix
                               (:e binary-+) bitp natp posp)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defruled pow-pos
     (posp (int-shift-pow i))
     :enable int-shift-pow)))

(defruledl int-divshift-sshr-after-mono
  (implies (and (natp c) (bitp b) (natp i))
           (<= c (int-shift-after c b i)))
  :enable (int-shift-after int-shift-pow bitp))

(defruledl int-divshift-sshr-run-mono
  (implies (and (natp c) (bit-listp bits) (natp i))
           (<= c (int-shift-run c bits i)))
  :hints (("Goal" :induct (int-shift-run c bits i)
           :in-theory (enable int-shift-run bit-listp))
          ("Subgoal *1/2" :use ((:instance int-divshift-sshr-after-mono
                                           (b (car bits)))))))

(defruledl int-divshift-sshr-var-step-iff
  (implies (and (primep p)
                (symbolp bit) (symbolp cur) (symbolp next) (symbolp m)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-bindsp asg cur)
                (r1cs::valuation-bindsp asg next)
                (r1cs::valuation-bindsp asg m)
                (bitp (lookup-equal bit asg))
                (bitp (lookup-equal m asg))
                (natp i)
                (< (int-shift-after (+ (lookup-equal cur asg)
                                       (lookup-equal m asg))
                                    (lookup-equal bit asg) i)
                   p))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-sshr-var-step bit cur next m i p) asg p)
                  (equal (lookup-equal next asg)
                         (- (int-shift-after (+ (lookup-equal cur asg)
                                                (lookup-equal m asg))
                                             (lookup-equal bit asg) i)
                            (lookup-equal m asg)))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-core
                   (c (lookup-equal cur asg))
                   (b (lookup-equal bit asg))
                   (mv (lookup-equal m asg))
                   (next (lookup-equal next asg))))
  :in-theory (e/d (int-divshift-sshr-var-step
                   r1cs::r1cs-constraints-holdp
                   r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product
                   pfield::mul pfield::add pfield::neg pfield::sub
                   acl2::mod-when-< bitp)
                  (mod floor lookup-equal int-divshift-sshr-core
                   int-shift-after int-shift-scale)))
